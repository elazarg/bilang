package bilang

fun join(role: String, decls: String, params: String, where: String, assignments: String, inits: String, step: Int): String {
    return """
    $decls

    function join_$role($params) at_step($step) {
        require(role[msg.sender] == address(0x0));
        role[msg.sender] = Role.$role;

        require($where);

        $assignments

        $inits
    }
    """
}

fun yield(role: String, decls: String, params: String, where: String, assignments: String, inits: String, step: Int): String {
    return """
    $decls

    function yield_$role$step($params) at_step($step) {
        require(role[msg.sender] == Role.$role);

        require($where);

        $assignments

        $inits
    }
    """
}

fun reveal(q: Query, step: Int) : String {
    val vars = q.params.map { Pair(typeOf(it.type), it.name.name) }
    val role = q.role.name
    val params = vars.map { (type, name) -> "$type _$name" }.joinToString(", ")
    val decls = vars.map { (type, name) -> "$type ${role}_$name;" }.joinToString("    \n")
    val reveals = vars.map { (_, name) -> "require(sha3(_$name, salt) == bytes32(hidden_$name));" }.joinToString(";\n    ")
    val where = exp(q.where)
    val assignments = vars.map { (_, name) -> "${role}_$name = _$name;" }.joinToString("\n    ")
    val inits = vars.map { (_, name) -> "${name}_done = true;" }.joinToString("\n    ")
    return """
    $decls

    function reveal_$role$step($params, uint salt) at_step($step) {
        require(role[msg.sender] == Role.$role);

        $reveals

        require($where);

        $assignments

        $inits
    }
    """
}

fun makeQuery(q: Query, step: Int): String {
    val vars = q.params.map { Pair(typeOf(it.type), it.name.name) }
    val role = q.role.name
    val params = vars.map { (type, name) -> "$type _$name" }.joinToString(", ")
    val decls = vars.map { (type, name) -> "$type $name;" }.joinToString("    \n")
    val where = exp(q.where)
    val assignments = vars.map { (_, name) -> "${role}_$name = _$name;" }.joinToString("\n    ")
    val inits = vars.map { (_, name) -> "${role}_${name}_done = true;" }.joinToString("\n    ")
    return when (q.kind) {
        Kind.JOIN -> join(role, decls, params, where, assignments, inits, step)
        Kind.YIELD -> yield(role, decls, params, where, assignments, inits, step)
        Kind.REVEAL -> reveal(q, step)
        Kind.MANY -> TODO()
    }
}

fun makeStep(qs: List<Query>, step: Int): String {
    val items = qs.map {  makeQuery(it, step) }.joinToString("\n")
    return items + """
    event Broadcast$step();
    function __nextStep$step() {
        require(block.timestamp == __lastStep + STEP_TIME);
        Broadcast$step();
        __lastStep = block.timestamp;
    }

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
contract ${p.desc} {

    // roles
    enum Role { $roles }
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
        _;
    }
${genExt(p.game, 0)}

}
""".replace("( *\n){2,}".toRegex(), "\n")
}
