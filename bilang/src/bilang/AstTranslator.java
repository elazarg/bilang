package bilang;

import generated.BiLangBaseVisitor;
import generated.BiLangParser.*;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.function.Function;

import static java.util.stream.Collectors.*;

class AstTranslator extends BiLangBaseVisitor<Ast> {

    @Override
    public Program visitProgram(ProgramContext ctx) {
        return new Program(list(ctx.typeDec(), this::visitTypeDec), this.visitStmtList(ctx.stmt()));
    }

    private Stmt makeStmt(StmtContext ctx) {
        Stmt res = (Stmt)ctx.accept(this);
        if (res == null) throw new AssertionError(ctx.getText());
        return res;
    }

    @Override
    public TypeDec visitTypeDec(TypeDecContext ctx) {
        return new TypeDec(ctx.name.getText(), makeType(ctx));
    }

    private TypeExp makeType(TypeDecContext ctx) {
        return (TypeExp)ctx.typeExp().accept(this);
    }

    @Override
    public TypeExp.Subset visitSubsetTypeExp(SubsetTypeExpContext ctx) {
        return new TypeExp.Subset(ctx.vals.stream().map(this::num).collect(toSet()));
    }

    private Exp.Num num(Token v) {
        return new Exp.Num(Integer.parseInt(v.getText()));
    }

    @Override
    public TypeExp.Range visitRangeTypeExp(RangeTypeExpContext ctx) {
        return new TypeExp.Range(num(ctx.start), num(ctx.end));
    }

    private Stmt.Block visitStmtList(List<? extends StmtContext> stmts) {
        return new Stmt.Block(list(stmts, this::makeStmt));
    }

    @Override
    public Stmt.Block visitBlockStmt(BlockStmtContext ctx) {
        return this.visitStmtList(ctx.stmt());
    }

    private Exp exp(ExpContext ctx) {
        return (Exp)ctx.accept(this);
    }

    @Override
    public Exp.UNDEFINED visitUndefExp(UndefExpContext ctx) {
        return Exp.UNDEFINED.INSTANCE;
    }

    @Override
    public Exp.UnOp visitUnOpExp(UnOpExpContext ctx) {
        return new Exp.UnOp(ctx.op.getText(), exp(ctx.exp()));
    }

    @Override
    public Exp.Var visitIdExp(IdExpContext ctx) {
        return new Exp.Var(ctx.name.getText());
    }

    @Override
    public Exp.Member visitMemberExp(MemberExpContext ctx) {
        return new Exp.Member(new Exp.Var(ctx.role.getText()), ctx.field.getText());
    }

    @Override
    public Exp.Call visitCallExp(CallExpContext ctx) {
        return new Exp.Call(new Exp.Var(ctx.callee.getText()), list(ctx.args, this::exp));
    }

    @Override
    public Exp.Cond visitIfExp(IfExpContext ctx) {
        return new Exp.Cond(exp(ctx.cond), exp(ctx.ifTrue), exp(ctx.ifFalse));
    }

    @Override
    public Exp.BinOp visitBinOpEqExp(BinOpEqExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpAddExp(BinOpAddExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpCompExp(BinOpCompExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpBoolExp(BinOpBoolExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpMultExp(BinOpMultExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }

    private Exp.BinOp binop(Token op, ExpContext left, ExpContext right) {
        return new Exp.BinOp(op.getText(), exp(left), exp(right));
    }

    @Override
    public Exp visitParenExp(ParenExpContext ctx) {
        return exp(ctx.exp());
    }

    @Override
    public Exp.Address visitAddressLiteralExp(AddressLiteralExpContext ctx) {
        return new Exp.Address(Integer.parseInt(ctx.ADDRESS().getText().substring(2), 16));
    }

    @Override
    public Exp.Num visitNumLiteralExp(NumLiteralExpContext ctx) {
        return num(ctx.INT().getSymbol());
    }

    @Override
    public Exp.Bool visitBoolLiteralExp(BoolLiteralExpContext ctx) {
        return new Exp.Bool(Boolean.parseBoolean(ctx.BOOL().getSymbol().getText()));
    }

    @Override
    public Stmt.VarDef visitVarDef(VarDefContext ctx) {
        return new Stmt.VarDef(this.visitVarDec(ctx.dec), exp(ctx.init));
    }

    @Override
    public Stmt.YieldDef visitYieldDef(YieldDefContext ctx) {
        return new Stmt.YieldDef(list(ctx.packet(), this::visitPacket), ctx.hidden != null);
    }

    @Override
    public Stmt.JoinDef visitJoinDef(JoinDefContext ctx) {
        return new Stmt.JoinDef(list(ctx.packet(), this::visitPacket), false);
    }

    @Override
    public Stmt.JoinManyDef visitJoinManyDef(JoinManyDefContext ctx) {
        return new Stmt.JoinManyDef(var(ctx.role));
    }

    @Override
    public Stmt.Assign visitAssignStmt(AssignStmtContext ctx) {
        Token target = ctx.target;
        return new Stmt.Assign(var(target), exp(ctx.exp()));
    }

    @NotNull
    private Exp.Var var(Token target) {
        return new Exp.Var(target.getText());
    }

    @Override
    public Stmt.Reveal visitRevealStmt(RevealStmtContext ctx) {
        return new Stmt.Reveal(var(ctx.target), this.visitWhereClause(ctx.where));
    }

    @Override
    public Stmt.If visitIfStmt(IfStmtContext ctx) {
        return new Stmt.If(exp(ctx.exp()),
                makeStmt(ctx.ifTrue),
                ctx.ifFalse == null ? new Stmt.Block(List.of()) : makeStmt(ctx.ifFalse)
        );
    }

    @Override
    public Stmt.ForYield visitForYieldStmt(ForYieldStmtContext ctx) {
        return new Stmt.ForYield(
                new Exp.Var(ctx.from.getText()),
                this.visitPacket(ctx.packet()),
                makeStmt(ctx.stmt())
        );
    }

    @Override
    public Stmt.Transfer visitTransferStmt(TransferStmtContext ctx) {
        return new Stmt.Transfer(exp(ctx.amount), var(ctx.from), var(ctx.to));
    }

    private <T1, T2> List<T2> list(List<T1> iterable, Function<T1, T2> f) {
        return iterable.stream().map(f).collect(toList());
    }

    @Override
    public Exp visitWhereClause(WhereClauseContext ctx) {
        return ctx.cond != null ? exp(ctx.cond) : new Exp.Var("true");
    }

    @Override
    public Packet visitPacket(PacketContext ctx) {
        return new Packet(var(ctx.role), list(ctx.decls, this::visitVarDec), this.visitWhereClause(ctx.whereClause()));
    }

    @Override
    public VarDec visitVarDec(VarDecContext ctx) {
        return new VarDec(var(ctx.name), new TypeExp.TypeId(ctx.type.getText()));
    }
}
