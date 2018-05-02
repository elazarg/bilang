package bilang

fun genGame(p: ExpProgram): String {
    val roles = findRoles(p.game).join(", ")
    return """pragma solidity ^0.4.22;

contract ${p.desc} {
    constructor() public {
        lastBlock = block.timestamp;
    }

    function keccak(bool x, uint salt) pure public returns(bytes32) {
        return keccak256(x, salt);
    }

    // Step
    uint constant STEP_TIME = 500;
    int step;
    uint lastBlock;

    modifier at_step(int _step) {
        require(step == _step);
        //require(block.timestamp < lastBlock + STEP_TIME);
        _;
    }
    
    // roles
    enum Role { None, $roles }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;

    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }
${genExt(p.game, 0)}

}
""".replace(Regex("( *\n){2,}"), "\n")
}


private fun genExt(ext: Ext, step: Int): String = when (ext) {
    is Ext.Bind -> makeStep(ext.kind, ext.qs, step) + "\n" + genExt(ext.ext, step + 1)
    is Ext.BindSingle -> makeStep(ext.kind, listOf(ext.q), step) + "\n" + genExt(ext.ext, step + 1)
    is Ext.Value -> genOutcome(ext.exp, step)
}

private fun makeStep(kind: Kind, qs: List<Query>, step: Int): String {
    val items = qs.map { makeQuery(kind, it, step) }.join("\n")
    return """
    // step $step

$items

    event Broadcast$step(); // TODO: add params
    function __nextStep$step() public {
        require(step == $step);
        //require(block.timestamp >= lastBlock + STEP_TIME);
        emit Broadcast$step();
        step = ${step + 1};
        lastBlock = block.timestamp;
    }

    // end $step
    """
}

private fun makeQuery(kind: Kind, q: Query, step: Int): String {
    val role = q.role
    val where = exp(q.where)

    val typeWheres = q.params.map { (name, type) -> whereof(varname(name, type), type) }.statements()
    val vars = q.params.map { (name, type) -> Pair(varname(name, type), typeOf(type)) }
    val params = vars.map { (name, type) -> "$type _$name" }.join(", ")
    val decls = vars.map { (name, type) -> "$type ${role}_$name;" }.declarations()

    val names = vars.names()
    val declsDone = names.map { "bool ${role}_${it}_done;" }.declarations()
    val assignments = names.map { "${role}_$it = _$it;" }.statements()
    val inits = names.map { "${role}_${it}_done = true;" }.statements()
    val doneRole = "done_${role}_$step"

    val deposit = q.deposit.n
    val payable = if (deposit != 0) "payable " else ""
    val requirePayment = if (deposit != 0) "require(msg.value == $deposit); " else ""

    return when (kind) {
        Kind.JOIN_CHANCE -> makeQuery(Kind.JOIN, q, step)
        Kind.JOIN, Kind.MANY -> {
            if (q.params.isNotEmpty()) {
                val revealArgs = (vars.map { (name, type) -> "$type _$name" } + "uint salt").join(", ")
                val reveals = (names.map { "_$it" } + "salt").join(", ")
                val (updateChosen, checkChosen) = if (kind == Kind.MANY)
                    Pair("chosenRole$role = msg.sender;", "if (chosenRole$role != address(0x0)) require(times$role[msg.sender] < times$role[chosenRole$role]);")
                else
                    Pair("", "")
                val declChosen = if (kind == Kind.MANY) "address chosenRole$role;" else ""
            """
            |    mapping(address => bytes32) commits$role;
            |    mapping(address => uint) times$role;
            |    bool halfStep$role;
            |
            |    function join_commit_$role(bytes32 c) at_step($step) public {
            |        require(commits$role[msg.sender] == bytes32(0));
            |        require(!halfStep$role);
            |        commits$role[msg.sender] = c;
            |        times$role[msg.sender] = block.timestamp;
            |    }
            |
            |    event BroadcastHalf$role();
            |    function __nextHalfStep$role() at_step($step) public {
            |        require(block.timestamp >= lastBlock + STEP_TIME);
            |        require(halfStep$role == false);
            |        emit BroadcastHalf$role();
            |        halfStep$role = true;
            |        lastBlock = block.timestamp;
            |    }
            |
            |    $declChosen
            |    $decls
            |    $declsDone
            |
            |    function join_$role($revealArgs) at_step($step) public $payable{
            |        require(keccak256($reveals) == bytes32(commits$role[msg.sender]));
            |        $checkChosen
            |        role[msg.sender] = Role.$role;
            |        $requirePayment
            |        balanceOf[msg.sender] = msg.value;
            |        $updateChosen
            |        $typeWheres
            |        require($where);
            |        $assignments
            |        $inits
            |    }
            |""".trimMargin()
            } else {
                val (checkDone, makeDone) = if (kind == Kind.JOIN) Pair("require(!done$role);", "done$role = true;") else Pair("", "")
                """
            |    bool done$role;
            |    function join_$role() at_step($step) public by(Role.None) $payable{
            |        $checkDone
            |        role[msg.sender] = Role.$role;
            |        $requirePayment
            |        balanceOf[msg.sender] = msg.value;
            |        require($where);
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
            |    bool $doneRole;
            |
            |    function yield_$role$step($params) by (Role.$role) at_step($step) public {
            |        require(!$doneRole);
            |        $typeWheres
            |        require($where);
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |""".trimMargin()
        }

        Kind.REVEAL -> {
            val reveals = vars.names().map {
                name -> "require(keccak256(_$name, salt) == bytes32(${role}_hidden_$name));"
            }.statements()
            """
            |    $decls
            |    $declsDone
            |    bool $doneRole;
            |
            |    function reveal_$role$step($params, uint salt) by(Role.$role) at_step($step) public {
            |        require(!$doneRole);
            |        $typeWheres
            |        $reveals
            |        require($where);
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |""".trimMargin()
        }
    }
}

private fun varname(name: String, type: TypeExp) =
        if (type is TypeExp.Hidden) "hidden_$name"
        else name

private fun genOutcome(switch: Outcome.Value, step: Int): String {
    // TODO: many
    return switch.ts.entries.map { (role: String, money: Exp) ->
        """
        |    function withdraw_${step}_$role() by(Role.$role) at_step($step) public {
        |        int amount = ${exp(money)};
        |        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
        |        delete balanceOf[msg.sender];
        |    }
        """.trimMargin()
        }.join("\n")
}

private fun exp(e: Exp): String = when (e) {
    is Exp.Call -> "${exp(e.target)}(${e.args.map { exp(it) }.join(",")})"
    is Exp.UnOp -> if (e.op == "isUndefined") {
        val operand = e.operand as Exp.Member
        "! ${operand.target}_${operand.field}_done"
    } else "(${e.op} ${exp(e.operand)})"
    is Exp.BinOp -> {
        val op = if (e.op == "<->") "==" else if (e.op == "<-!->") "!=" else e.op
        "(${exp(e.left)} $op ${exp(e.right)})"
    }
    is Exp.Var -> "_${e.name}"
    is Exp.Member -> "${e.target}_${e.field}"
    is Exp.Cond -> "((${exp(e.cond)}) ? ${exp(e.ifTrue)} : ${exp(e.ifFalse)})"
    is Exp.Const.Num -> "int(${e.n})"
    is Exp.Const.Bool -> "${e.truth}"
    is Exp.Const.Address -> "address(${e.n.toString(16)})" // todo hex
    is Exp.Const.Hidden -> exp(e.value as Exp)
    is Exp.Let -> TODO()
    Exp.Const.UNDEFINED -> throw StaticError("Undefined")
}

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "Role"
    TypeExp.ROLESET -> "mapping(address => bool)"
    TypeExp.ADDRESS -> "address"
    is TypeExp.Hidden -> "uint"
    is TypeExp.TypeId -> "int" // FIX: either inline or declare types
    is TypeExp.Subset -> "int"
    is TypeExp.Range -> "int"
    is TypeExp.Opt -> typeOf(t.type)
}

private fun whereof(v: String, t: TypeExp): String = when (t) {
    is TypeExp.Subset -> "require(${t.values.map { "$v == $it" }.join(" || ")})"
    is TypeExp.Range -> "require(${t.min} <= $v && $v <= ${t.max});"
    else -> ""
}

private fun Iterable<String>.declarations() = join("\n    ")
private fun Iterable<String>.statements() = join("\n        ")
