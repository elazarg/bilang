package bilang

fun genGame(p: ExpProgram): String {
    val roles = findRoles(p.game).join(", ")
    return """pragma solidity ^0.4.22;

contract ${p.desc} {

    // roles
    enum Role { None, $roles }
    mapping(address => Role) role;
    mapping(address => uint) balanceOf;

    modifier by(Role r) {
        require(role[msg.sender] == r);
        _;
    }

    // Step
    uint constant STEP_TIME = 500;
    int step;
    uint __lastStep;

    modifier at_step(int _step) {
        require(step == _step);
        require(block.timestamp < __lastStep + STEP_TIME);
        _;
    }
${genExt(p.game, 0)}

}
""".replace(Regex("( *\n){2,}"), "\n")
}


fun makeStep(kind: Kind, qs: List<Query>, step: Int): String {
    val items = qs.map { makeQuery(kind, it, step) }.join("\n")
    return """
    // step $step

$items

    event Broadcast$step(); // TODO: add params
    function __nextStep$step() at_step($step) public {
        require(block.timestamp >= __lastStep + STEP_TIME);
        emit Broadcast$step();
        step += 1;
        __lastStep = block.timestamp;
    }

    // end $step
    """
}

fun makeQuery(kind: Kind, q: Query, step: Int): String {
    val role = q.role.name
    val where = exp(q.where)

    val typeWheres = q.params.map { whereof(varname(it), it.type) }.statements()
    val vars = q.params.map { Pair(typeOf(it.type), varname(it)) }
    val params = vars.map { (type, name) -> "$type _$name" }.join(", ")
    val decls = vars.map { (type, name) -> "$type ${role}_$name;" }.declarations()

    val names = vars.map { (_, name) -> name }
    val declsDone = names.map { "bool ${role}_${it}_done;" }.declarations()
    val assignments = names.map { "${role}_$it = _$it;" }.statements()
    val inits = names.map { "${role}_${it}_done = true;" }.statements()
    val args = names.map{ "_$it" }.join(", ")
    val doneRole = "done_${role}_$step"

    return when (kind) {
        Kind.JOIN -> {
            val revealArgs = (vars.map { (type, name) -> "$type _$name" } + "uint salt").join(", ")
            val reveals = (vars.map { (type, name) -> "_$name" } + "salt").join(", ")
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
            |        require(block.timestamp >= __lastStep + STEP_TIME);
            |        require(halfStep$role == false);
            |        emit BroadcastHalf$role();
            |        halfStep$role = true;
            |        __lastStep = block.timestamp;
            |    }
            |
            |    address chosenRole$role;
            |    $decls
            |    $declsDone
            |
            |    function join_$role($revealArgs) at_step($step) public payable {
            |        require(keccak256($reveals) == bytes32(commits$role[msg.sender]));
            |        if (chosenRole$role != address(0x0))
            |             require(times$role[msg.sender] < times$role[chosenRole$role]);
            |        role[msg.sender] = Role.$role;
            |        balanceOf[msg.sender] = msg.value;
            |        chosenRole$role = msg.sender;
            |        $typeWheres
            |        require($where);
            |        $assignments
            |        $inits
            |    }
            |"""
        }

        Kind.YIELD -> {
            """
            |    $decls
            |    $declsDone
            |    bool $doneRole;
            |
            |    function yield_$role$step($params) at_step($step) public {
            |        require(role[msg.sender] == Role.$role);
            |        require(!$doneRole);
            |        $typeWheres
            |        require($where);
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |"""
        }

        Kind.REVEAL -> {
            val reveals = vars.map {
                (_, name) -> "require(keccak256(_$name, salt) == bytes32(${role}_hidden_$name));"
            }.statements()
            """
            |    $decls
            |    $declsDone
            |    bool $doneRole;
            |
            |    function reveal_$role$step($params, uint salt) at_step($step) public {
            |        require(role[msg.sender] == Role.$role);
            |        require(!$doneRole);
            |        $typeWheres
            |        $reveals
            |        require($where);
            |        $assignments
            |        $inits
            |        $doneRole = true;
            |    }
            |"""
        }

        Kind.MANY -> TODO()
    }.trimMargin()
}

private fun varname(it: VarDec) =
        if (it.type is TypeExp.Hidden) "hidden_${it.name.name}"
        else it.name.name

fun exp(e: Exp, outvar: String, type: String): List<String> {
    try {
        return listOf("$outvar = ${exp(e)};")
    } catch (ex: StaticError) {}
    return when (e) {
        is Exp.Call -> TODO("${exp(e.target)}(${e.args.map { exp(it) }.join(",")})")
        is Exp.UnOp -> {
            if (e.op == "isUndefined") {
                val member = exp(e.operand)
                listOf("$outvar = ${member}_done;")
            } else {
                if (e.operand is Exp.Const || e.operand is Exp.Var)
                    listOf("$outvar = ${e.op} ${exp(e.operand)};")
                else {
                    val fresh = Fresh.vvar()
                    val freshType = if (e.op == "!") "bool" else "int"
                    val prev = exp(e.operand, fresh, freshType)
                    listOf("{", "$freshType $fresh;") + prev + listOf("$outvar = ${e.op} $fresh;", "}")
                }
            }
        }
        is Exp.BinOp -> {
            val freshType = when (e.op) {
                "+", "-", "*", "/" -> "int"
                ">", ">=", "<", "<=" -> "int"
                "||", "&&" -> "bool"
                "==", "!=" -> "int"
                "<->", "<-!->" -> "bool"
                else -> throw IllegalArgumentException(e.op)
            }

            val (left, leftInit) = if (e.left is Exp.Const || e.left is Exp.Var) Pair(exp(e.left), listOf())
            else {
                val v = Fresh.vvar()
                Pair(v, listOf("$freshType $v;") + exp(e.left, v, freshType))
            }
            val (right, rightInit) = if (e.right is Exp.Const || e.right is Exp.Var) Pair(exp(e.right), listOf())
            else {
                val v = Fresh.vvar()
                Pair(v, listOf("$freshType $v;") + exp(e.right, v, freshType))
            }

            val op = if (e.op == "<->") "==" else if (e.op == "<-!->") "!=" else e.op
            listOf("{") + leftInit + rightInit + listOf("$outvar = $left $op $right;", "}")
        }
        is Exp.Var -> listOf("$outvar = ${e.name};")
        is Exp.Member -> listOf("$outvar = ${e.target}_${e.field};")
        is Exp.Cond -> {
            val condVar = Fresh.vvar()
            listOf("bool $condVar;") + exp(e.cond, condVar, "bool") +
                    "if ($condVar) { " + exp(e.ifTrue, outvar, type) + "} else {" + exp(e.ifFalse, outvar, type) + "}"
        }
        is Exp.Const -> listOf("$outvar = ${exp(e)};")
        is Exp.Let -> {
            exp(e.init, e.dec.name.name, (e.dec.type as TypeExp.TypeId).name) + exp(e.exp, outvar, type)
        }
    }
}

fun exp(e: Exp): String = when (e) {
    is Exp.Call -> "${exp(e.target)}(${e.args.map { exp(it) }.join(",")})"
    is Exp.UnOp -> if (e.op == "isUndefined") throw StaticError(0, "Undefined")
                    else "(${e.op} ${exp(e.operand)})"
    is Exp.BinOp -> {
        val op = if (e.op == "<->") "==" else if (e.op == "<-!->") "!=" else e.op
        "(${exp(e.left)} $op ${exp(e.right)})"
    }
    is Exp.Var -> "_${e.name}"
    is Exp.Member -> "${e.target}_${e.field}"
    is Exp.Cond -> "((${exp(e.cond)}) ? ${exp(e.ifTrue)} : ${exp(e.ifFalse)})"
    is Exp.Const.Num -> "int(${e.n})"
    is Exp.Const.Bool -> "${e.truth}"
    is Exp.Const.Address -> "${e.n}" // todo hex
    is Exp.Const.Hidden -> exp(e.value as Exp)
    is Exp.Let -> TODO()
    Exp.Const.UNDEFINED -> throw StaticError(0, "Undefined")
}

fun genExt(ext: Ext, step: Int): String = when (ext) {
    is Ext.Bind -> makeStep(ext.kind, ext.qs, step) + "\n" + genExt(ext.ext, step + 1)
    is Ext.BindSingle -> makeStep(ext.kind, listOf(ext.q), step) + "\n" + genExt(ext.ext, step + 1)
    is Ext.Value -> genPayoff(ext.exp, step)
}

fun genPayoff(switch: Payoff.Value, step: Int): String {
    // idea: evaluate keys one by one; when the value equals to the value of the sender
    // evaluate the value and withdraw
    // so this is a "switch" expression...
    return switch.ts.entries.map { (role: String, money: Exp) ->
        """
    |    function withdraw_${step}_$role() by(Role.$role) public at_step($step) {
    |        require(role[msg.sender] == Role.$role);
    |        int amount;
    |        ${exp(money, "amount", "int").statements()}
    |        msg.sender.transfer(uint(int(balanceOf[msg.sender]) + amount));
    |        delete balanceOf[msg.sender];
    |    }
    """.trimMargin()
    }.join("\n")
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
private fun Iterable<String>.join(sep: String) = joinToString(sep)

object Fresh {
    private var v = 0
    fun vvar(): String {
        v += 1
        return "freshVar$v"
    }
}
