package bilang;

import generated.BiLangBaseVisitor;
import generated.BiLangParser.*;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static java.util.stream.Collectors.*;

class AstTranslator extends BiLangBaseVisitor<Ast> {

    @Override
    public ExpProgram visitProgram(ProgramContext ctx) {
        return new ExpProgram("", "", list(ctx.typeDec(), this::visitTypeDec), ext(ctx.ext()));
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

    private Exp exp(ExpContext ctx) {
        return (Exp)ctx.accept(this);
    }

    private Ext ext(ExtContext ctx) {
        return (Ext)ctx.accept(this);
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

    @NotNull
    private Exp.Var var(Token target) {
        return new Exp.Var(target.getText());
    }

    @Override
    public Exp.Q.Payoff visitTransfer(TransferContext ctx) {
        Map<Exp.Var, Exp> m = ctx.items.stream().collect(toMap(e -> var(e.ID().getSymbol()), e -> exp(e.exp())));
        return new Exp.Q.Payoff(m);
    }

    private <T1, T2> List<T2> list(List<T1> iterable, Function<T1, T2> f) {
        return iterable.stream().map(f).collect(toList());
    }

    @Override
    public Exp visitWhereClause(WhereClauseContext ctx) {
        return ctx.cond != null ? exp(ctx.cond) : new Exp.Var("true");
    }

    @Override
    public Query visitPacket(PacketContext ctx) {
        return new Query(toKind(ctx.kind), var(ctx.role), list(ctx.decls, this::visitVarDec), this.visitWhereClause(ctx.whereClause()));
    }

    @NotNull
    private Kind toKind(Token kind) {
        switch (kind.getText()) {
            case "join" : return Kind.JOIN;
            case "yield" : return Kind.YIELD;
            case "reveal" : return Kind.REVEAL;
            case "many" : return Kind.MANY;
        }
        throw new AssertionError();
    }

    @Override
    public VarDec visitVarDec(VarDecContext ctx) {
        return new VarDec(var(ctx.name), new TypeExp.TypeId(ctx.type.getText()));
    }
}
