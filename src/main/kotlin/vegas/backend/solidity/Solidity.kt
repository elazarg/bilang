package vegas.backend.solidity

import vegas.frontend.*
import vegas.ir.desugar
import vegas.join
import vegas.StaticError

fun genGame(p: GameAst): String {
    val roles = findRoleIdsWithChance(p.game).join(", ")
    return """
pragma solidity ^0.8.31;

contract ${p.desc} {
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
        // require(block.timestamp < lastTs + STEP_TIME, "step expired");
        _;
    }
    
    // roles
    enum Role { None, $roles }
    mapping(address => Role) public role;
    mapping(address => uint256) public balanceOf;

    modifier by(Role r) {
        require(role[msg.sender] == r, "bad role");
        _;
    }
${genExt(p.game, 0)}

    // Reject stray ETH by default
    receive() external payable {
        revert("direct ETH not allowed");
    }
}
""".replace(Regex("( *\n){2,}"), "\n")
}

private fun allDiffExpr(args: List<String>): String {
    if (args.size <= 1) return "true"
    val pairs = ArrayList<String>(args.size * (args.size - 1) / 2)
    for (i in 0 until args.size) {
        for (j in i + 1 until args.size) {
            pairs += "${args[i]} != ${args[j]}"
        }
    }
    return pairs.joinToString(separator = " && ", prefix = "(", postfix = ")")
}

private fun genExt(ext: Ext, step: Int): String = when (ext) {
    is Ext.Bind -> makeStep(ext.kind, ext.qs, step) + "\n" + genExt(ext.ext, step + 1)
    is Ext.BindSingle -> makeStep(ext.kind, listOf(ext.q), step) + "\n" + genExt(ext.ext, step + 1)
    is Ext.Value -> genOutcome(desugar(ext.outcome), step)
}

private fun makeStep(kind: Kind, qs: List<Query>, step: Int): String {
    val items = qs.map { makeQuery(kind, it, step) }.join("\n")
    return """
    // step $step

$items

    event Broadcast$step(); // TODO: add params
    function __nextStep$step() public {
        require(step == $step, "wrong step");
        // require(block.timestamp >= lastTs + STEP_TIME, "not yet");
        emit Broadcast$step();
        step = ${step + 1};
        lastTs = block.timestamp;
    }

    // end $step
    """
}

private fun makeQuery(kind: Kind, q: Query, step: Int): String {
    val role = q.role
    val where = exp(q.where)

    val typeWheres = q.params.map { (v, type) -> whereof(varname(v.id.name, type), type) }.statements()
    val vars = q.params.map { (v, type) -> Pair(varname(v.id.name, type), typeOf(type)) }
    val params = vars.map { (name, type) -> "$type _$name" }.join(", ")
    val decls = vars.map { (name, type) -> "$type public ${role}_$name;" }.declarations()

    val names = vars.names()
    val declsDone = names.map { "bool public ${role}_${it}_done;" }.declarations()
    val assignments = names.map { "${role}_$it = _$it;" }.statements()
    val inits = names.map { "${role}_${it}_done = true;" }.statements()
    val doneRole = "done_${role}_$step"

    val deposit = q.deposit.n
    val payable = if (deposit != 0) "payable " else ""
    val requirePayment = if (deposit != 0) "require(msg.value == $deposit, \"bad stake\"); " else ""

    return when (kind) {
        Kind.JOIN_CHANCE -> makeQuery(Kind.JOIN, q, step)

        Kind.JOIN -> {
            if (q.params.isNotEmpty()) {
                val revealArgs = (vars.map { (name, type) -> "$type _$name" } + "uint256 salt").join(", ")
                val reveals = (names.map { "_$it" } + "salt").join(", ")
                val (updateChosen, checkChosen) = Pair("", "")
                """
            |    mapping(address => bytes32) private commits$role;
            |    mapping(address => uint256) private times$role;
            |    bool public halfStep$role;
            |
            |    function join_commit_$role(bytes32 c) public at_step($step) {
            |        require(commits$role[msg.sender] == bytes32(0), "already committed");
            |        require(!halfStep$role, "half step passed");
            |        commits$role[msg.sender] = c;
            |        times$role[msg.sender] = block.timestamp;
            |    }
            |
            |    event BroadcastHalf$role();
            |    function __nextHalfStep$role() public at_step($step) {
            |        require(block.timestamp >= lastTs + STEP_TIME, "too soon");
            |        require(halfStep$role == false, "already advanced");
            |        emit BroadcastHalf$role();
            |        halfStep$role = true;
            |        lastTs = block.timestamp;
            |    }
            |
            |    $decls
            |    $declsDone
            |
            |    function join_$role($revealArgs) public ${payable}at_step($step) {
            |        require(keccak256(abi.encodePacked($reveals)) == commits$role[msg.sender], "bad reveal");
            |        $checkChosen
            |        role[msg.sender] = Role.$role;
            |        ${requirePayment}balanceOf[msg.sender] = msg.value;
            |        $updateChosen
            |        $typeWheres
            |        require($where, "where");
            |        $assignments
            |        $inits
            |    }
            |""".trimMargin()
            } else {
                val (checkDone, makeDone) = Pair("require(!done$role, \"already joined\");", "done$role = true;")
                """
            |    bool public done$role;
            |    function join_$role() public ${payable}by(Role.None) at_step($step) {
            |        $checkDone
            |        role[msg.sender] = Role.$role;
            |        ${requirePayment}balanceOf[msg.sender] = msg.value;
            |        require($where, "where");
            |        $inits
            |        $makeDone
            |    }
            |""".trimMargin()
            }
        }

        Kind.YIELD -> {
            """
            |    $decls
            |    $declsDone
            |    bool public $doneRole;
            |
            |    function yield_${role}${step}($params) public by(Role.$role) at_step($step) {
            |        require(!$doneRole, "done");
            |        $typeWheres
            |        require($where, "where");
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |""".trimMargin()
        }

        Kind.REVEAL -> {
            val reveals = vars.names().map { name ->
                "require(keccak256(abi.encodePacked(_$name, salt)) == bytes32(${role}_hidden_$name), \"bad reveal\");"
            }.statements()
            """
            |    $decls
            |    $declsDone
            |    bool public $doneRole;
            |
            |    function reveal_${role}${step}($params, uint256 salt) public by(Role.$role) at_step($step) {
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
    }
}

private fun varname(name: String, type: TypeExp) =
    if (type is TypeExp.Hidden) "hidden_$name" else name

private fun genOutcome(switch: Outcome.Value, step: Int): String {
    // New: safe uint balance +/- int delta, CEI, call-based payout
    return switch.ts.entries.map { (role: Role, money: Exp) ->
        """
        |    function withdraw_${step}_$role() public by(Role.$role) at_step($step) {
        |        int256 delta = ${exp(money)};
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
    }.join("\n")
}

private fun exp(e: Exp): String = when (e) {
    is Exp.Call -> {
        if (e.target.id.name == "alldiff") {
            // Detect the synthetic _alldiff(...) and expand in-line
            allDiffExpr(e.args.map { exp(it) })
        } else {
            "${exp(e.target)}(${e.args.joinToString(",") { exp(it) }})"
        }
    }
    is Exp.UnOp -> when (e.op) {
        "isUndefined" -> {
            val operand = (e.operand as Exp.Field).fieldRef
            "! ${operand.role.name}_${operand.param.name}_done"
        }
        "isDefined" -> {
            val operand = (e.operand as Exp.Field).fieldRef
            "${operand.role.name}_${operand.param.name}_done"
        }
        else -> "(${e.op} ${exp(e.operand)})"
    }
    is Exp.BinOp -> {
        val op = if (e.op == "<->") "==" else if (e.op == "<-!->") "!=" else e.op
        "(${exp(e.left)} $op ${exp(e.right)})"
    }
    is Exp.Var -> "_${e.id.name}"
    is Exp.Field -> "${e.fieldRef.role}_${e.fieldRef.param}"
    is Exp.Cond -> "((${exp(e.cond)}) ? ${exp(e.ifTrue)} : ${exp(e.ifFalse)})"
    is Exp.Const.Num -> "int256(${e.n})"
    is Exp.Const.Bool -> "${e.truth}"
    is Exp.Const.Address -> "address(${e.n.toString(16)})" // todo hex
    is Exp.Const.Hidden -> exp(e.value as Exp)
    is Exp.Let -> TODO()
    Exp.Const.UNDEFINED -> throw StaticError("Undefined", e)
}

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int256"
    TypeExp.BOOL -> "bool"
    TypeExp.ADDRESS -> "address"
    TypeExp.EMPTY -> throw AssertionError()
    is TypeExp.Hidden -> "uint256"
    is TypeExp.TypeId -> "int256" // keep for now
    is TypeExp.Subset -> "int256"
    is TypeExp.Range -> "int256"
    is TypeExp.Opt -> typeOf(t.type)
}

private fun whereof(v: String, t: TypeExp): String = when (t) {
    is TypeExp.Subset -> "require(${t.values.map { "$v == $it" }.join(" || ")});"
    is TypeExp.Range -> "require(${t.min} <= $v && $v <= ${t.max});"
    else -> ""
}

private fun Iterable<String>.declarations() = join("\n    ")
private fun Iterable<String>.statements() = join("\n        ")
private fun List<Pair<String, String>>.names() = this.map { it.first }