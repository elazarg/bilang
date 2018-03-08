package bilang;

import bilang.generated.BiLangBaseVisitor;
import bilang.generated.BiLangParser;
import bilang.generated.BiLangParser.*;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.NotNull;

import static java.util.stream.Collectors.*;

class AstTranslator extends BiLangBaseVisitor<Ast> {

    @Override
    public Program visitProgram(BiLangParser.ProgramContext ctx) {
        return new Program(
                ctx.typeDec().stream().map(this::visitTypeDec).collect(toList()),
                this.visitBlock(ctx.block())
        );
    }

    private Stmt makeStmt(StmtContext ctx) {
        return (Stmt)ctx.accept(this);
    }

    @Override
    public TypeDec visitTypeDec(BiLangParser.TypeDecContext ctx) {
        return new TypeDec(ctx.name.getText(), makeType(ctx));
    }

    private TypeExp makeType(TypeDecContext ctx) {
        return (TypeExp)ctx.typeExp().accept(this);
    }

    @Override
    public TypeExp.Subset visitSubsetTypeExp(BiLangParser.SubsetTypeExpContext ctx) {
        return new TypeExp.Subset(ctx.vals.stream().map(this::makeNum).collect(toSet()));
    }

    private Exp.Num makeNum(Token v) {
        return new Exp.Num(Integer.parseInt(v.getText()));
    }

    @Override
    public TypeExp.Range visitRangeTypeExp(BiLangParser.RangeTypeExpContext ctx) {
        return new TypeExp.Range(makeNum(ctx.start), makeNum(ctx.end));
    }

    @Override
    public Block visitBlock(BiLangParser.BlockContext ctx) {
        return new Block(ctx.stmt().stream().map(this::makeStmt).collect(toList()));
    }

    private Exp makeExp(ExpContext ctx) {
        return (Exp)ctx.accept(this);
    }

    @Override
    public Exp.UNDEFINED visitUndefExp(BiLangParser.UndefExpContext ctx) {
        return Exp.UNDEFINED.INSTANCE;
    }

    @Override
    public Exp.UnOp visitUnOpExp(BiLangParser.UnOpExpContext ctx) {
        return new Exp.UnOp(ctx.op.getText(), makeExp(ctx.exp()));
    }

    @Override
    public Exp.Var visitIdExp(BiLangParser.IdExpContext ctx) {
        return new Exp.Var(ctx.name.getText());
    }

    @Override
    public Exp.Member visitMemberExp(BiLangParser.MemberExpContext ctx) {
        return new Exp.Member(new Exp.Var(ctx.role.getText()), ctx.field.getText());
    }

    @Override
    public Exp.Call visitCallExp(BiLangParser.CallExpContext ctx) {
        return new Exp.Call(new Exp.Var(ctx.callee.getText()), ctx.args.stream().map(this::makeExp).collect(toList()));
    }

    @Override
    public Exp.Cond visitIfExp(BiLangParser.IfExpContext ctx) {
        return new Exp.Cond(makeExp(ctx.cond), makeExp(ctx.ifTrue), makeExp(ctx.ifFalse));
    }

    @Override
    public Exp.BinOp visitBinOpEqExp(BiLangParser.BinOpEqExpContext ctx) {
        return makeBinOp(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpAddExp(BiLangParser.BinOpAddExpContext ctx) {
        return makeBinOp(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpCompExp(BiLangParser.BinOpCompExpContext ctx) {
        return makeBinOp(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpBoolExp(BiLangParser.BinOpBoolExpContext ctx) {
        return makeBinOp(ctx.op, ctx.left, ctx.right);
    }
    @Override
    public Exp.BinOp visitBinOpMultExp(BiLangParser.BinOpMultExpContext ctx) {
        return makeBinOp(ctx.op, ctx.left, ctx.right);
    }

    @NotNull
    private Exp.BinOp makeBinOp(Token op, ExpContext left, ExpContext right) {
        return new Exp.BinOp(op.getText(), makeExp(left), makeExp(right));
    }

    @Override
    public Exp visitParenExp(BiLangParser.ParenExpContext ctx) {
        return makeExp(ctx.exp());
    }

    @Override
    public Exp.Address visitAddressLiteralExp(BiLangParser.AddressLiteralExpContext ctx) {
        return new Exp.Address(Integer.parseInt(ctx.ADDRESS().getText(), 16));
    }

    @Override
    public Exp.Num visitNumLiteralExp(BiLangParser.NumLiteralExpContext ctx) {
        return makeNum(ctx.INT().getSymbol());
    }

    @Override
    public Stmt.Def.VarDef visitVarDef(BiLangParser.VarDefContext ctx) {
        return new Stmt.Def.VarDef(this.visitVarDec(ctx.dec), makeExp(ctx.init));
    }

    @Override
    public Stmt.Def.YieldDef visitYieldDef(BiLangParser.YieldDefContext ctx) {
        return new Stmt.Def.YieldDef(this.visitPackets(ctx.packets()), ctx.hidden != null);
    }

    @Override
    public Stmt.Def.JoinDef visitJoinDef(BiLangParser.JoinDefContext ctx) {
        return new Stmt.Def.JoinDef(this.visitPacketsBind(ctx.packetsBind()), false);
    }

    @Override
    public Stmt.Def.JoinManyDef visitJoinManyDef(BiLangParser.JoinManyDefContext ctx) {
        return new Stmt.Def.JoinManyDef(ctx.role.getText());
    }

    @Override
    public Stmt.Assign visitAssignStmt(BiLangParser.AssignStmtContext ctx) {
        return new Stmt.Assign(ctx.target.getText(), makeExp(ctx.exp()));
    }

    @Override
    public Stmt.Reveal visitRevealStmt(BiLangParser.RevealStmtContext ctx) {
        return new Stmt.Reveal(ctx.target.getText(), this.visitWhereClause(ctx.where));
    }

    @Override
    public Stmt.If visitIfStmt(BiLangParser.IfStmtContext ctx) {
        return new Stmt.If(makeExp(ctx.exp()), this.visitBlock(ctx.ifTrue), this.visitBlock(ctx.ifFalse));
    }

    @Override
    public Stmt.ForYield visitForYieldStmt(BiLangParser.ForYieldStmtContext ctx) {
        return new Stmt.ForYield(
                ctx.from.getText(),
                this.visitPacketsBind(ctx.packetsBind()),
                this.visitBlock(ctx.block())
        );
    }

    @Override
    public Stmt.Transfer visitTransferStmt(BiLangParser.TransferStmtContext ctx) {
        return new Stmt.Transfer(makeExp(ctx.amount), makeExp(ctx.from), makeExp(ctx.to));
    }

    @Override
    public Packets visitPacketsBind(BiLangParser.PacketsBindContext ctx) {
        return this.visitPackets(ctx.packets());
    }

    @Override
    public Packets visitPackets(BiLangParser.PacketsContext ctx) {
        return new Packets(ctx.packet().stream().map(this::visitPacket).collect(toList()), this.visitWhereClause(ctx.where));
    }

    @Override
    public Exp visitWhereClause(BiLangParser.WhereClauseContext ctx) {
        return makeExp(ctx.cond);
    }

    @Override
    public Packet visitPacket(BiLangParser.PacketContext ctx) {
        return new Packet(ctx.role.getText(), ctx.decls.stream().map(this::visitVarDec).collect(toList()));
    }

    @Override
    public Ast visitVarRef(BiLangParser.VarRefContext ctx) {
        return super.visitVarRef(ctx);
    }

    @Override
    public VarDec visitVarDec(BiLangParser.VarDecContext ctx) {
        return new VarDec(ctx.name.getText(), new TypeExp.TypeId(ctx.type.getText()));
    }
}
