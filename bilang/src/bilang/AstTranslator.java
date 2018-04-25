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
        return new ExpProgram("", map(ctx.typeDec()), ext(ctx.ext()));
    }

    private Map<String, TypeExp> map(List<TypeDecContext> ctxs) {
        return ctxs.stream().collect(toMap(ctx -> ctx.name.getText(), this::makeType));
    }

    private TypeExp makeType(TypeDecContext ctx) {
        return (TypeExp) ctx.typeExp().accept(this);
    }

    @Override
    public TypeExp.Subset visitSubsetTypeExp(SubsetTypeExpContext ctx) {
        return new TypeExp.Subset(ctx.vals.stream().map(this::num).collect(toSet()));
    }

    private Exp.Const.Num num(Token v) {
        String text = v == null ? "0" : v.getText();
        return new Exp.Const.Num(Integer.parseInt(text));
    }

    @Override
    public TypeExp.Range visitRangeTypeExp(RangeTypeExpContext ctx) {
        return new TypeExp.Range(num(ctx.start), num(ctx.end));
    }

    private Exp exp(ExpContext ctx) {
        return (Exp) ctx.accept(this);
    }

    private Ext ext(ExtContext ctx) {
        return (Ext) ctx.accept(this);
    }

    @Override
    public Ext visitReceiveExt(ReceiveExtContext ctx) {
        Ext ext = ext(ctx.ext());
        Kind kind = toKind(ctx.kind);
        if (ctx.query().size() == 1)
            return new Ext.BindSingle(kind, query(ctx.query().get(0)), ext);
        else
            return new Ext.Bind(kind, list(ctx.query(), this::query), ext);
    }

    private Query query(QueryContext ctx) {
        return new Query(var(ctx.role), list(ctx.decls, this::visitVarDec), num(ctx.deposit), where(ctx.cond));
    }

    private Exp where(ExpContext cond) {
        return cond != null ? exp(cond) : new Exp.Const.Bool(true);
    }

    @Override
    public Ext.Value visitWithdrawExt(WithdrawExtContext ctx) {
        return new Ext.Value(bilang.AstKt.desugar(outcome(ctx.outcome())));
    }

    @Override
    public Exp.UnOp visitUndefExp(UndefExpContext ctx) {
        Exp.UnOp isUndefined = new Exp.UnOp("isUndefined", exp(ctx.exp()));
        return ctx.op.getText().equals("==") ? isUndefined : new Exp.UnOp("!", isUndefined);
    }

    @Override
    public Exp.UnOp visitUnOpExp(UnOpExpContext ctx) {
        return new Exp.UnOp(ctx.op.getText(), exp(ctx.exp()));
    }

    @Override
    public Exp visitIdExp(IdExpContext ctx) {
        String name = ctx.name.getText();
        switch (name) {
            case "true":
            case "false":
                assert false;
        }
        return new Exp.Var(name);
    }

    @Override
    public Exp.Const.Bool visitBoolLiteralExp(BoolLiteralExpContext ctx) {
        return new Exp.Const.Bool(Boolean.parseBoolean(ctx.getText()));
    }

    @Override
    public Exp.Member visitMemberExp(MemberExpContext ctx) {
        return new Exp.Member(ctx.role.getText(), ctx.field.getText());
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
    public Exp.Let visitLetExp(LetExpContext ctx) {
        return new Exp.Let(visitVarDec(ctx.dec), exp(ctx.init), exp(ctx.body));
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
    public Outcome visitParenOutcome(ParenOutcomeContext ctx) {
        return outcome(ctx.outcome());
    }
    @Override
    public Exp.Const.Address visitAddressLiteralExp(AddressLiteralExpContext ctx) {
        return new Exp.Const.Address(Integer.parseInt(ctx.ADDRESS().getText().substring(2), 16));
    }

    @Override
    public Exp.Const.Num visitNumLiteralExp(NumLiteralExpContext ctx) {
        return num(ctx.INT().getSymbol());
    }


    @NotNull
    private Exp.Var var(Token target) {
        return new Exp.Var(target.getText());
    }

    @Override
    public Outcome visitOutcomeExp(OutcomeExpContext ctx) {
        Map<String, Exp> m = ctx.items.stream().collect(toMap(e -> e.ID().getText(), e -> exp(e.exp())));
        return new Outcome.Value(m);
    }

    @Override
    public Outcome visitIfOutcome(IfOutcomeContext ctx) {
        return new Outcome.Cond(exp(ctx.cond), outcome(ctx.ifTrue), outcome(ctx.ifFalse));
    }

    @Override
    public Outcome visitLetOutcome(LetOutcomeContext ctx) {
        return new Outcome.Let(visitVarDec(ctx.dec), exp(ctx.init), outcome(ctx.outcome()));
    }

    private Outcome outcome(OutcomeContext ctx) {
        return (Outcome) ctx.accept(this);
    }

    private <T1, T2> List<T2> list(List<T1> iterable, Function<T1, T2> f) {
        return iterable.stream().map(f).collect(toList());
    }


    @NotNull
    private Kind toKind(Token kind) {
        switch (kind.getText()) {
            case "join":
                return Kind.JOIN;
            case "yield":
                return Kind.YIELD;
            case "reveal":
                return Kind.REVEAL;
            case "many":
                return Kind.MANY;
            case "random":
                return Kind.JOIN_CHANCE;
        }
        throw new AssertionError();
    }

    @Override
    public VarDec visitVarDec(VarDecContext ctx) {
        TypeExp type = type(ctx);
        return new VarDec(var(ctx.name), (ctx.hidden != null) ? new TypeExp.Hidden(type) : type);
    }

    @NotNull
    private TypeExp type(VarDecContext ctx) {
        switch (ctx.type.getText()) {
            case "bool":
                return TypeExp.BOOL.INSTANCE;
            case "int":
                return TypeExp.INT.INSTANCE;
        }
        return new TypeExp.TypeId(ctx.type.getText());
    }
}
