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
    public Ext.Bind visitReceiveExt(ReceiveExtContext ctx) {
        return new Ext.Bind(list(ctx.query(), this::visitQuery), ext(ctx.ext()));
    }

    @Override
    public Ext.Value visitExpExt(ExpExtContext ctx) {
        return new Ext.Value(exp(ctx.exp()));
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
    public Exp visitIdExp(IdExpContext ctx) {
        String name = ctx.name.getText();
        switch (name) {
            case "true": case "false": assert false;
        }
        return new Exp.Var(name);
    }

    @Override
    public Exp.Bool visitBoolLiteralExp(BoolLiteralExpContext ctx) {
        return new Exp.Bool(Boolean.parseBoolean(ctx.getText()));
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
    public Exp.Address visitAddressLiteralExp(AddressLiteralExpContext ctx) {
        return new Exp.Address(Integer.parseInt(ctx.ADDRESS().getText().substring(2), 16));
    }

    @Override
    public Exp.Num visitNumLiteralExp(NumLiteralExpContext ctx) {
        return num(ctx.INT().getSymbol());
    }


    @NotNull
    private Exp.Var var(Token target) {
        return new Exp.Var(target.getText());
    }

    @Override
    public Exp.Payoff visitPayoffExp(PayoffExpContext ctx) {
        Map<Exp.Var, Exp> m = ctx.items.stream().collect(toMap(e -> var(e.ID().getSymbol()), e -> exp(e.exp())));
        return new Exp.Payoff(m);
    }

    private <T1, T2> List<T2> list(List<T1> iterable, Function<T1, T2> f) {
        return iterable.stream().map(f).collect(toList());
    }

    @Override
    public Exp visitWhereClause(WhereClauseContext ctx) {
        return ctx.cond != null ? exp(ctx.cond) : new Exp.Bool(true);
    }

    @Override
    public Query visitQuery(QueryContext ctx) {
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
        TypeExp type = type(ctx);
        return new VarDec(var(ctx.name), (ctx.hidden != null) ? new TypeExp.Hidden(type) : type);
    }

    @NotNull
    private TypeExp type(VarDecContext ctx) {
        switch (ctx.type.getText()) {
            case "bool": return TypeExp.BOOL.INSTANCE;
            case "int": return TypeExp.INT.INSTANCE;
        }
        return new TypeExp.TypeId(ctx.type.getText());
    }
}
