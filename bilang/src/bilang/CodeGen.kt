package bilang

fun join(role: String, decls: String, declsDone: String, params: String, where: String, assignments: String, inits: String, step: Int): String {
    return """
    $decls
    $declsDone

    function join_$role($params) at_step($step) public {
        require(role[msg.sender] == Role.None);
        role[msg.sender] = Role.$role;

        require($where);

        $assignments

        $inits
    }
    """
}

fun yield(role: String, decls: String, declsDone: String, params: String, where: String, assignments: String, inits: String, step: Int): String {
    return """
    $decls
    $declsDone

    function yield_$role$step($params) at_step($step) public {
        require(role[msg.sender] == Role.$role);

        require($where);

        $assignments

        $inits
    }
    """
}

fun reveal(q: Query, step: Int) : String {
    val vars = q.params.map { Pair(typeOf(it.type), varname(it)) }
    val role = q.role.name
    val params = vars.map { (type, name) -> "$type _$name" }.joinToString(", ")
    val decls = vars.map { (type, name) -> "$type ${role}_$name;" }.joinToString("\n    ")
    val declsDone = vars.map { (type, name) -> "bool ${role}_${name}_done;" }.joinToString("\n    ")
    val reveals = vars.map { (_, name) -> "require(keccak256(_$name, salt) == bytes32(${role}_hidden_$name));" }.joinToString(";\n    ")
    val where = exp(q.where)
    val assignments = vars.map { (_, name) -> "${role}_$name = _$name;" }.joinToString("\n    ")
    val inits = vars.map { (_, name) -> "${role}_${name}_done = true;" }.joinToString("\n    ")
    return """
    $decls
    $declsDone

    function reveal_$role$step($params, uint salt) at_step($step) public {
        require(role[msg.sender] == Role.$role);

        $reveals

        require($where);

        $assignments

        $inits
    }
    """
}

fun makeQuery(q: Query, step: Int): String {
    val vars = q.params.map { Pair(typeOf(it.type), varname(it)) }
    val role = q.role.name
    val params = vars.map { (type, name) -> "$type _$name" }.joinToString(", ")
    val decls = vars.map { (type, name) -> "$type ${role}_$name;" }.joinToString("    \n")
    val declsDone = vars.map { (type, name) -> "bool ${role}_${name}_done;" }.joinToString("\n    ")
    val where = exp(q.where)
    val assignments = vars.map { (_, name) -> "${role}_$name = _$name;" }.joinToString("\n    ")
    val inits = vars.map { (_, name) -> "${role}_${name}_done = true;" }.joinToString("\n    ")
    return when (q.kind) {
        Kind.JOIN -> join(role, decls, declsDone, params, where, assignments, inits, step)
        Kind.YIELD -> yield(role, decls, declsDone, params, where, assignments, inits, step)
        Kind.REVEAL -> reveal(q, step)
        Kind.MANY -> TODO()
    }
}

private fun varname(it: VarDec) =
    if (it.type is TypeExp.Hidden) "hidden_${it.name.name}"
    else it.name.name

fun makeStep(qs: List<Query>, step: Int): String {
    val items = qs.map {  makeQuery(it, step) }.joinToString("\n")
    return """
    // step $step

    $items

    event Broadcast$step(); // TODO: add params
    function __nextStep$step() public {
        emit Broadcast$step();
    }

    // end $step
    """
}


fun exp(e: Exp): String = when (e) {
    is Exp.Call -> "${exp(e.target)}(${e.args.map { exp(it) }.joinToString(",")})"
    is Exp.UnOp -> "(${e.op} ${exp(e.operand)})"
    is Exp.BinOp -> "(${exp(e.left)} ${e.op} ${exp(e.right)})"
    is Exp.Var -> e.name
    is Exp.Member -> "${exp(e.target)}_${e.field}"
    is Exp.Cond -> "((${exp(e.cond)}) ? ${exp(e.ifTrue)} : ${exp(e.ifFalse)})"
    Exp.UNDEFINED -> "throwAssertUndefined()"
    is Exp.Num -> "${e.n}"
    is Exp.Bool -> "${e.truth}"
    is Exp.Address -> "${e.n}" // todo hex
    is Exp.Hidden -> exp(e.value as Exp)
    is Exp.Let -> TODO()
    is Exp.Payoff -> "SomePayoff" // TODO()
}

fun genExt(ext: Ext, step: Int): String {
    return when (ext) {
        is Ext.Bind -> makeStep(ext.qs, step) + "\n" + genExt(ext.exp, step+1)
        is Ext.BindSingle -> makeStep(listOf(ext.q), step) + "\n" + genExt(ext.exp, step+1)
        is Ext.Value -> ""
    }
}

private fun typeOf(t: TypeExp): String = when (t) {
    TypeExp.INT -> "int"
    TypeExp.BOOL -> "bool"
    TypeExp.ROLE -> "Role"
    TypeExp.ROLESET -> "map(Role)bool"
    TypeExp.ADDRESS -> "address"
    TypeExp.UNIT -> "unit"
    is TypeExp.Hidden -> "uint"
    is TypeExp.TypeId -> "int" // FIX: either inline or declare types
    is TypeExp.Subset -> "int"
    is TypeExp.Range -> "int"
    is TypeExp.Opt -> typeOf(t.type)
}

fun genGame(p: ExpProgram): String {
    val roles = findRoles(p.game).joinToString(", ")
    return """
pragma solidity ^0.4.22;

contract ${p.desc} {

    // roles
    enum Role { None, $roles }
    mapping(address => Role) role;

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
        require(block.timestamp == __lastStep + STEP_TIME);
        _;
        __lastStep = block.timestamp;
    }
${genExt(p.game, 0)}

}
""".replace("( *\n){2,}".toRegex(), "\n")
}
