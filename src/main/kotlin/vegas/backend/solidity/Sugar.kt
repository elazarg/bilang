package vegas.backend.solidity

/**
* DSL helpers for building Solidity AST.
* Makes code more readable and less verbose.
*/
// ===== Literals =====

fun int(value: Int) = SolExpr.IntLit(value)
fun uint(value: Int) = SolExpr.Cast(SolType.Uint256, SolExpr.IntLit(value))
fun bool(value: Boolean) = SolExpr.BoolLit(value)
fun str(value: String) = SolExpr.StringLit(value)
fun addr(hex: String) = SolExpr.AddressLit(hex)

// ===== Variables =====

fun v(name: String) = SolExpr.Var(name)

// ===== Member Access =====

infix fun SolExpr.dot(member: String) = SolExpr.Member(this, member)
operator fun SolExpr.get(index: SolExpr) = SolExpr.Index(this, index)

// Convenience for common patterns
fun index(base: String, idx: SolExpr) = SolExpr.Index(v(base), idx)
fun member(base: String, field: String) = SolExpr.Member(v(base), field)

// ===== Comparisons =====

infix fun SolExpr.eq(other: SolExpr) = SolExpr.Eq(this, other)
infix fun SolExpr.ne(other: SolExpr) = SolExpr.Ne(this, other)
infix fun SolExpr.lt(other: SolExpr) = SolExpr.Lt(this, other)
infix fun SolExpr.le(other: SolExpr) = SolExpr.Le(this, other)
infix fun SolExpr.gt(other: SolExpr) = SolExpr.Gt(this, other)
infix fun SolExpr.ge(other: SolExpr) = SolExpr.Ge(this, other)

// ===== Boolean Logic =====

infix fun SolExpr.and(other: SolExpr) = SolExpr.And(this, other)
infix fun SolExpr.or(other: SolExpr) = SolExpr.Or(this, other)
fun not(expr: SolExpr) = SolExpr.Not(expr)

// ===== Arithmetic =====
fun neg(expr: SolExpr) = SolExpr.Neg(expr)
operator fun SolExpr.plus(other: SolExpr) = SolExpr.Add(this, other)
operator fun SolExpr.minus(other: SolExpr) = SolExpr.Sub(this, other)
operator fun SolExpr.times(other: SolExpr) = SolExpr.Mul(this, other)
operator fun SolExpr.div(other: SolExpr) = SolExpr.Div(this, other)
operator fun SolExpr.rem(other: SolExpr) = SolExpr.Mod(this, other)
operator fun SolExpr.unaryMinus() = SolExpr.Neg(this)

// ===== Ternary =====

fun ite(cond: SolExpr, ifTrue: SolExpr, ifFalse: SolExpr) =
    SolExpr.Ternary(cond, ifTrue, ifFalse)

// ===== Casts =====

fun cast(type: SolType, expr: SolExpr) = SolExpr.Cast(type, expr)
fun toInt256(expr: SolExpr) = SolExpr.Cast(SolType.Int256, expr)
fun toUint256(expr: SolExpr) = SolExpr.Cast(SolType.Uint256, expr)
fun toAddress(expr: SolExpr) = SolExpr.Cast(SolType.Address, expr)

// ===== Function Calls =====

fun call(name: String, vararg args: SolExpr) =
    SolExpr.Call(name, args.toList())

fun SolExpr.call(method: String, vararg args: SolExpr) =
    SolExpr.MemberCall(this, method, args.toList())

fun SolExpr.callWithValue(method: String, value: SolExpr, vararg args: SolExpr) =
    SolExpr.CallWithOptions(this, method, mapOf("value" to value), args.toList())

// ===== Built-ins =====

val msgSender = SolExpr.BuiltIn.MsgSender
val msgValue = SolExpr.BuiltIn.MsgValue
val blockTimestamp = SolExpr.BuiltIn.BlockTimestamp
val thisAddress = SolExpr.BuiltIn.ThisAddress
val bytes32Zero = SolExpr.BuiltIn.Bytes32Zero

// ===== Solidity-Specific =====

fun enumVal(enumType: String, value: String) = SolExpr.EnumValue(enumType, value)
fun payable(address: SolExpr) = SolExpr.Payable(address)
fun keccak256(data: SolExpr) = SolExpr.Keccak256(data)
fun abiEncodePacked(vararg args: SolExpr) = SolExpr.AbiEncodePacked(args.toList())

// ===== Statements =====

fun require(condition: SolExpr, message: String) =
    Statement.Require(condition, message)

fun assign(lhs: SolExpr, rhs: SolExpr) =
    Statement.Assign(lhs, rhs)

fun emit(event: String, vararg args: SolExpr) =
    Statement.Emit(event, args.toList())

fun ifStmt(
    condition: SolExpr,
    thenBranch: List<Statement>,
    elseBranch: List<Statement> = emptyList()
) = Statement.If(condition, thenBranch, elseBranch)

fun ret(value: SolExpr? = null) = Statement.Return(value)

fun block(vararg statements: Statement) =
    Statement.Block(statements.toList())

// ===== Common Patterns =====

/**
 * Common pattern: role[msg.sender] = Role.X
 */
fun assignRole(role: String) = assign(
    lhs = index(ROLE_MAPPING, msgSender),
    rhs = enumVal(ROLE_ENUM, role)
)

/**
 * Common pattern: balanceOf[msg.sender] = msg.value
 */
fun setBalance() = assign(
    lhs = index(BALANCE_MAPPING, msgSender),
    rhs = msgValue
)

/**
 * Common pattern: require(msg.value == amount, "bad stake")
 */
fun requireDeposit(amount: Int) = require(
    msgValue eq int(amount),
    "bad stake"
)
