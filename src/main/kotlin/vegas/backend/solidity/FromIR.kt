package vegas.backend.solidity

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.*

fun genSolidityFromIR(g: GameIR): String {
    val roles = g.roles.joinToString(", ") { it.name }

    return """
pragma solidity ^0.8.31;

contract ${g.name} {
    constructor() {
        lastTs = block.timestamp;
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32) {
        return keccak256(abi.encodePacked(x, salt));
    }

    // Step
    uint256 public constant STEP_TIME = 500;
    uint256 public step;
    uint256 public lastTs;

    modifier at_step(uint256 _step) {
        require(step == _step, "wrong step");
        _;
    }
    
    // roles
    enum RoleId { None, $roles }
    mapping(address => RoleId) public role;
    mapping(address => uint256) public balanceOf;

    modifier by(RoleId r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
${genPhases(g)}

    // Reject stray ETH by default
    receive() external payable {
        revert("direct ETH not allowed");
    }
}
""".replace(Regex("( *\n){2,}"), "\n")
}

private fun genPhases(g: GameIR): String {
    // Build index to track parameter history
    val paramHistory = buildParamHistory(g)

    val steps = g.phases.mapIndexed { stepIdx, phase ->
        genPhase(phase, stepIdx, paramHistory)
    }.joinToString("\n")

    val withdrawals = genWithdrawals(g, g.phases.size)

    return steps + "\n" + withdrawals
}

private data class ParamHistory(
    val occurrences: Map<FieldRef, List<Pair<Int, Boolean>>> // (role, param) -> [(phase, visible)]
)

private fun buildParamHistory(g: GameIR): ParamHistory {
    val history = mutableMapOf<FieldRef, MutableList<Pair<Int, Boolean>>>()

    g.phases.forEachIndexed { phaseIdx, phase ->
        phase.forEach { (role, sig) ->
            sig.parameters.forEach { param ->
                val key = FieldRef(role, param.name)
                history.getOrPut(key) { mutableListOf() }.add(phaseIdx to param.visible)
            }
        }
    }

    return ParamHistory(history.mapValues { it.value.toList() })
}

private fun genPhase(phase: Phase, stepIdx: Int, history: ParamHistory): String {
    val items = phase.map { (role, sig) ->
        genSignature(role, sig, stepIdx, history)
    }.joinToString("\n")

    return """
    // step $stepIdx

$items

    event Broadcast$stepIdx();
    function __nextStep$stepIdx() public {
        require(step == $stepIdx, "wrong step");
        emit Broadcast$stepIdx();
        step = ${stepIdx + 1};
        lastTs = block.timestamp;
    }

    // end $stepIdx
    """
}

private fun genSignature(role: RoleId, sig: Signature, step: Int, history: ParamHistory): String {
    // Detect kind: JOIN, YIELD, or REVEAL
    val isReveal = sig.parameters.any { param ->
        val occurrences = history.occurrences[FieldRef(role, param.name)] ?: emptyList()
        val priorCommit = occurrences.any { (phase, visible) -> phase < step && !visible }
        priorCommit && param.visible
    }

    return when {
        isReveal -> genReveal(role, sig, step)
        sig.join -> genJoin(role, sig, step, history)
        else -> genYield(role, sig, step)
    }
}

private fun genJoin(role: RoleId, sig: Signature, step: Int, history: ParamHistory): String {
    val deposit = 0 // Deposits not tracked in IR currently
    val payable = if (deposit != 0) "payable " else ""
    val requirePayment = if (deposit != 0) "require(msg.value == $deposit, \"bad stake\"); " else ""

    val hasHiddenParams = sig.parameters.any { !it.visible }

    if (sig.parameters.isNotEmpty() && hasHiddenParams) {
        // Commit-reveal pattern for hidden parameters
        val vars = sig.parameters.map { param ->
            val name = if (!param.visible) "hidden_${param.name.name}" else param.name.name
            val type = typeOf(param.type)
            name to type
        }

        val revealArgs = (vars.map { (name, type) -> "$type _$name" } + "uint256 salt").joinToString(", ")
        val reveals = (vars.map { (name, _) -> "_$name" } + "salt").joinToString(", ")

        val decls = vars.map { (name, type) -> "$type public ${role.name}_$name;" }.declarations()
        val declsDone = vars.map { (name, _) -> "bool public ${role.name}_${name}_done;" }.declarations()
        val assignments = vars.map { (name, _) -> "${role.name}_$name = _$name;" }.statements()
        val inits = vars.map { (name, _) -> "${role.name}_${name}_done = true;" }.statements()

        val typeWheres = sig.parameters.zip(vars).map { (param, nameType) ->
            whereof("_${nameType.first}", param.type)
        }.filter { it.isNotEmpty() }.joinToString("\n        ")

        val where = expr(sig.requires.condition)

        return """
            |    mapping(address => bytes32) private commits${role.name};
            |    mapping(address => uint256) private times${role.name};
            |    bool public halfStep${role.name};
            |
            |    function join_commit_${role.name}(bytes32 c) public at_step($step) {
            |        require(commits${role.name}[msg.sender] == bytes32(0), "already committed");
            |        require(!halfStep${role.name}, "half step passed");
            |        commits${role.name}[msg.sender] = c;
            |        times${role.name}[msg.sender] = block.timestamp;
            |    }
            |
            |    event BroadcastHalf${role.name}();
            |    function __nextHalfStep${role.name}() public at_step($step) {
            |        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
            |        require(halfStep${role.name} == false, "already advanced");
            |        emit BroadcastHalf${role.name}();
            |        halfStep${role.name} = true;
            |        lastTs = block.timestamp;
            |    }
            |
            |    $decls
            |    $declsDone
            |
            |    function join_${role.name}($revealArgs) public ${payable}at_step($step) {
            |        require(keccak256(abi.encodePacked($reveals)) == commits${role.name}[msg.sender], "bad reveal");
            |        role[msg.sender] = RoleId.${role.name};
            |        ${requirePayment}balanceOf[msg.sender] = msg.value;
            |        $typeWheres
            |        require($where, "where");
            |        $assignments
            |        $inits
            |    }
            |""".trimMargin()
    } else if (sig.parameters.isEmpty()) {
        // Simple join with no parameters
        val where = expr(sig.requires.condition)

        return """
            |    bool public done${role.name};
            |    function join_${role.name}() public ${payable}by(RoleId.None) at_step($step) {
            |        require(!done${role.name}, "already joined");
            |        role[msg.sender] = RoleId.${role.name};
            |        ${requirePayment}balanceOf[msg.sender] = msg.value;
            |        require($where, "where");
            |        done${role.name} = true;
            |    }
            |""".trimMargin()
    } else {
        // Join with public parameters only
        return genYield(role, sig, step)
    }
}

private fun genYield(role: RoleId, sig: Signature, step: Int): String {
    val vars = sig.parameters.map { param ->
        val name = if (!param.visible) "hidden_${param.name.name}" else param.name.name
        val type = typeOf(param.type)
        name to type
    }

    val params = vars.joinToString(", ") { (name, type) -> "$type _$name" }
    val decls = vars.map { (name, type) -> "$type public ${role.name}_$name;" }.declarations()
    val declsDone = vars.map { (name, _) -> "bool public ${role.name}_${name}_done;" }.declarations()
    val assignments = vars.map { (name, _) -> "${role.name}_$name = _$name;" }.statements()
    val inits = vars.map { (name, _) -> "${role.name}_${name}_done = true;" }.statements()
    val doneRole = "done_${role.name}_$step"

    val typeWheres = sig.parameters.zip(vars).map { (param, nameType) ->
        whereof("_${nameType.first}", param.type)
    }.filter { it.isNotEmpty() }.joinToString("\n        ")

    val where = expr(sig.requires.condition)

    return """
            |    $decls
            |    $declsDone
            |    bool public $doneRole;
            |
            |    function yield_${role.name}$step($params) public by(RoleId.${role.name}) at_step($step) {
            |        require(!$doneRole, "done");
            |        $typeWheres
            |        require($where, "where");
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |""".trimMargin()
}

private fun genReveal(role: RoleId, sig: Signature, step: Int): String {
    val vars = sig.parameters.map { param ->
        val name = param.name.name
        val type = typeOf(param.type)
        name to type
    }

    val params = (vars.map { (name, type) -> "$type _$name" } + "uint256 salt").joinToString(", ")
    val decls = vars.map { (name, type) -> "$type public ${role.name}_$name;" }.declarations()
    val declsDone = vars.map { (name, _) -> "bool public ${role.name}_${name}_done;" }.declarations()
    val assignments = vars.map { (name, _) -> "${role.name}_$name = _$name;" }.statements()
    val inits = vars.map { (name, _) -> "${role.name}_${name}_done = true;" }.statements()
    val doneRole = "done_${role.name}_$step"

    val reveals = vars.joinToString("\n        ") { (name, _) ->
        "require(keccak256(abi.encodePacked(_$name, salt)) == bytes32(${role.name}_hidden_$name), \"bad reveal\");"
    }

    val typeWheres = sig.parameters.zip(vars).map { (param, nameType) ->
        whereof("_${nameType.first}", param.type)
    }.filter { it.isNotEmpty() }.joinToString("\n        ")

    val where = expr(sig.requires.condition)

    return """
            |    $decls
            |    $declsDone
            |    bool public $doneRole;
            |
            |    function reveal_${role.name}$step($params) public by(RoleId.${role.name}) at_step($step) {
            |        require(!$doneRole, "done");
            |        $typeWheres
            |        $reveals
            |        require($where, "where");
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |""".trimMargin()
}

private fun genWithdrawals(g: GameIR, finalStep: Int): String {
    return g.payoffs.map { (role, payoffExpr) ->
        """
        |    function withdraw_${finalStep}_${role.name}() public by(RoleId.${role.name}) at_step($finalStep) {
        |        int256 delta = ${expr(payoffExpr)};
        |        uint256 bal = balanceOf[msg.sender];
        |
        |        uint256 amount;
        |        if (delta >= 0) {
        |            amount = bal + uint256(delta);
        |        } else {
        |            uint256 d = uint256(-delta);
        |            require(bal >= d, "insufficient");
        |            amount = bal - d;
        |        }
        |
        |        // Effects first
        |        balanceOf[msg.sender] = 0;
        |
        |        // Interaction
        |        (bool ok, ) = payable(msg.sender).call{value: amount}("");
        |        require(ok, "ETH send failed");
        |    }
        """.trimMargin()
    }.joinToString("\n")
}

// ========== Expression Compilation ==========

private fun expr(e: Expr): String = when (e) {
    is Expr.IntLit -> "int256(${e.v})"
    is Expr.BoolLit -> "${e.v}"

    is Expr.Field -> "${e.field.role.name}_${e.field.param.name}"

    is Expr.IsDefined -> {
        val f = e.field
        "${f.role.name}_${f.param.name}_done"
    }

    is Expr.Add -> "(${expr(e.l)} + ${expr(e.r)})"
    is Expr.Sub -> "(${expr(e.l)} - ${expr(e.r)})"
    is Expr.Mul -> "(${expr(e.l)} * ${expr(e.r)})"
    is Expr.Div -> "(${expr(e.l)} / ${expr(e.r)})"
    is Expr.Neg -> "(-${expr(e.x)})"

    is Expr.Eq -> "(${expr(e.l)} == ${expr(e.r)})"
    is Expr.Ne -> "(${expr(e.l)} != ${expr(e.r)})"
    is Expr.Lt -> "(${expr(e.l)} < ${expr(e.r)})"
    is Expr.Le -> "(${expr(e.l)} <= ${expr(e.r)})"
    is Expr.Gt -> "(${expr(e.l)} > ${expr(e.r)})"
    is Expr.Ge -> "(${expr(e.l)} >= ${expr(e.r)})"

    is Expr.And -> "(${expr(e.l)} && ${expr(e.r)})"
    is Expr.Or -> "(${expr(e.l)} || ${expr(e.r)})"
    is Expr.Not -> "(!${expr(e.x)})"

    is Expr.Ite -> "((${expr(e.c)}) ? ${expr(e.t)} : ${expr(e.e)})"
}

// ========== Type Compilation ==========

private fun typeOf(t: Type): String = when (t) {
    Type.IntType -> "int256"
    Type.BoolType -> "bool"
    is Type.SetType -> "int256"
}

private fun whereof(v: String, t: Type): String = when (t) {
    is Type.SetType -> {
        if (t.values.isEmpty()) ""
        else "require(${t.values.joinToString(" || ") { "$v == $it" }});"
    }
    else -> ""
}

// ========== Utilities ==========

private fun Iterable<String>.declarations() = joinToString("\n    ")
private fun Iterable<String>.statements() = joinToString("\n        ")
