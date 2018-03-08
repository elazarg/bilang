package bilang;

import bilang.generated.BiLangBaseVisitor;
import bilang.generated.BiLangParser.*;
import org.antlr.v4.runtime.Token;

import java.util.List;
import java.util.function.Function;

import static java.util.stream.Collectors.*;

class AstTranslator extends BiLangBaseVisitor<Ast> {

    @Override
    public Program visitProgram(ProgramContext ctx) {
        return new Program(list(ctx.typeDec(), this::visitTypeDec), this.visitBlock(ctx.block()));
    }

    private Stmt makeStmt(StmtContext ctx) {
        return (Stmt)ctx.accept(this);
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

    @Override
    public Block visitBlock(BlockContext ctx) {
        return new Block(list(ctx.stmt(), this::makeStmt));
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
        return new Exp.Address(Integer.parseInt(ctx.ADDRESS().getText(), 16));
    }

    @Override
    public Exp.Num visitNumLiteralExp(NumLiteralExpContext ctx) {
        return num(ctx.INT().getSymbol());
    }

    @Override
    public Stmt.Def.VarDef visitVarDef(VarDefContext ctx) {
        return new Stmt.Def.VarDef(this.visitVarDec(ctx.dec), exp(ctx.init));
    }

    @Override
    public Stmt.Def.YieldDef visitYieldDef(YieldDefContext ctx) {
        return new Stmt.Def.YieldDef(this.visitPackets(ctx.packets()), ctx.hidden != null);
    }

    @Override
    public Stmt.Def.JoinDef visitJoinDef(JoinDefContext ctx) {
        return new Stmt.Def.JoinDef(this.visitPacketsBind(ctx.packetsBind()), false);
    }

    @Override
    public Stmt.Def.JoinManyDef visitJoinManyDef(JoinManyDefContext ctx) {
        return new Stmt.Def.JoinManyDef(ctx.role.getText());
    }

    @Override
    public Stmt.Assign visitAssignStmt(AssignStmtContext ctx) {
        return new Stmt.Assign(ctx.target.getText(), exp(ctx.exp()));
    }

    @Override
    public Stmt.Reveal visitRevealStmt(RevealStmtContext ctx) {
        return new Stmt.Reveal(ctx.target.getText(), this.visitWhereClause(ctx.where));
    }

    @Override
    public Stmt.If visitIfStmt(IfStmtContext ctx) {
        return new Stmt.If(exp(ctx.exp()), this.visitBlock(ctx.ifTrue), this.visitBlock(ctx.ifFalse));
    }

    @Override
    public Stmt.ForYield visitForYieldStmt(ForYieldStmtContext ctx) {
        return new Stmt.ForYield(
                ctx.from.getText(),
                this.visitPacketsBind(ctx.packetsBind()),
                this.visitBlock(ctx.block())
        );
    }

    @Override
    public Stmt.Transfer visitTransferStmt(TransferStmtContext ctx) {
        return new Stmt.Transfer(exp(ctx.amount), exp(ctx.from), exp(ctx.to));
    }

    @Override
    public Packets visitPacketsBind(PacketsBindContext ctx) {
        return this.visitPackets(ctx.packets());
    }

    @Override
    public Packets visitPackets(PacketsContext ctx) {
        return new Packets(list(ctx.packet(), this::visitPacket), this.visitWhereClause(ctx.where));
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
        return new Packet(ctx.role.getText(), list(ctx.decls, this::visitVarDec));
    }

    @Override
    public Ast visitVarRef(VarRefContext ctx) {
        return new Exp.Var(ctx.ID().getText());
    }

    @Override
    public VarDec visitVarDec(VarDecContext ctx) {
        return new VarDec(ctx.name.getText(), new TypeExp.TypeId(ctx.type.getText()));
    }
}
