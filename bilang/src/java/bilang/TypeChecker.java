package bilang;

import java.util.*;
import java.util.stream.Collectors;

import bilang.generated.BiLangParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import bilang.generated.BiLangBaseVisitor;

import static bilang.generated.BiLangParser.*;
import static bilang.Type.compatible;
import static bilang.Main.require;


class TypeChecker extends BiLangBaseVisitor<Void> {
    private final Map<String, Type> types = new HashMap<>(Map.of(
            "role", Value.ROLE,
            "address", Value.ROLE,
            "int", Value.INT,
            "bool", Value.BOOL
    ));

    private final SymbolTable symbolTable = new SymbolTable(Map.of());

    private final ExpTypeChecker expChecker = new ExpTypeChecker();
    private final TypeDefiner typedef = new TypeDefiner();

    private void accept(ParserRuleContext ctx) {
        if (ctx != null)
            ctx.accept(this);
    }

    @Override
    public Void visitProgram(ProgramContext ctx)  {
        symbolTable.push();
        super.visitProgram(ctx);
        symbolTable.pop();
        return null;
    }

    @Override
    public Void visitBlock(BlockContext ctx)  {
        symbolTable.push();
        super.visitBlock(ctx);
        symbolTable.pop();
        return null;
    }

    @Override
    public Void visitVarDef(VarDefContext ctx) {
        // reorder visit, to prohibit "int x = x"
        Type initType = (ctx.init != null) ? expChecker.accept(ctx.init) : null;
        accept(ctx.dec);
        if (initType != null) {
            Type lvalueType = lookupTypename(ctx.dec.type.getText(), ctx);
            require(compatible(initType, lvalueType), "Incompatible initializer", ctx.init);
        }
        return null;
    }

    @Override
    public Void visitYieldDef(YieldDefContext ctx) {
        ctx.packets.forEach(d->requireCompatible(Value.ROLE, d.role));
        ctx.packets.forEach(this::accept);
        return null;
    }

    @Override
    public Void visitForYieldStmt(ForYieldStmtContext ctx) {
        accept(ctx.where);
        //declare(ctx.packet.role, Value.ROLE);
        return null;
    }

    @Override
    public Void visitJoinDef(JoinDefContext ctx) {
        declare(ctx.role, Value.ROLE);
        return null;
    }

    @Override
    public Void visitWhereClause(WhereClauseContext ctx) {
        requireCompatible(Value.BOOL, ctx.exp());
        return null;
    }

    @Override
    public Void visitVarDec(VarDecContext ctx) {
        declare(ctx.name, lookupTypename(ctx.type.getText(), ctx));
        return null;
    }

    private void declare(Token ctx, Type type) {
        String name = ctx.getText();
        Map<String, Type> scope = symbolTable.currentScope();
        require(!scope.containsKey(name),"Name already declared", ctx);
        require(!types.containsKey(name),"Cannot redeclare type name as name", ctx);
        scope.put(name, type);
    }

    @Override
    public Void visitTypeDec(TypeDecContext typeDec) {
        String name = typeDec.name.getText();
        require(!types.containsKey(name),
                "Type name already declared", typeDec.name);
        types.put(name, typedef.visit(typeDec.typeDef()));
        return null;
    }

    @Override
    public Void visitAssignStmt(AssignStmtContext ctx) {
        requireCompatible(symbolTable.lookup(ctx.lvalue.getText()), ctx.exp());
        return null;
    }

    @Override
    public Void visitTransferStmt(TransferStmtContext ctx) {
        requireCompatible(Value.ROLE, ctx.from, ctx.to);
        return null;
    }

    private Type lookupTypename(String typename, ParserRuleContext ctx) {
        if (typename == null) return null;
        Type res = types.get(typename);
        require(res != null, "Unknown type name", ctx);
        return res;
    }

    private void requireCompatible(Type t, ExpContext ... exps) {
        for (ExpContext exp : exps) {
            require(expChecker.accept(exp).isCompatible(t), "Expression must be " + t, exp);
        }
    }

    public class TypeDefiner extends BiLangBaseVisitor<Type> {
        @Override
        public Type visitSubsetTypeDef(SubsetTypeDefContext ctx)  {
            return new Subset(ctx.vals.stream().map(x->Integer.parseInt(x.getText())).collect(Collectors.toSet()));
        }
        @Override
        public Type visitRangeTypeDef(RangeTypeDefContext ctx)  {
            return new Range(Integer.parseInt(ctx.start.getText()), Integer.parseInt(ctx.end.getText()));
        }
    }

    class ExpTypeChecker extends BiLangBaseVisitor<Type> {

        @Override
        public Type visitParenExp(ParenExpContext ctx) {
            return accept(ctx.exp());
        }

        @Override
        public Type visitIdExp(IdExpContext ctx) {
            String name = ctx.name.getText();
            Type t = symbolTable.lookup(name);
            require(t != null, "Undefined name " + name, ctx);
            return t;
        }

        @Override
        public Type visitUndefExp(UndefExpContext ctx) {
            return Value.UNDEF;
        }

        @Override
        public Type visitNumLiteralExp(NumLiteralExpContext ctx) {
            return Value.INT;
        }

        @Override
        public Type visitAddressLiteralExp(AddressLiteralExpContext ctx) {
            return Value.ROLE;
        }

        @Override
        public Type visitBinOpMultExp(BinOpMultExpContext ctx) {
            binopInt(ctx.left, ctx.right);
            return Value.INT;
        }

        @Override
        public Type visitBinOpAddExp(BinOpAddExpContext ctx) {
            binopInt(ctx.left, ctx.right);
            return Value.INT;
        }

        @Override
        public Type visitBinOpCompExp(BinOpCompExpContext ctx) {
            binopInt(ctx.left, ctx.right);
            return Value.BOOL;
        }

        @Override
        public Type visitUnOpExp(UnOpExpContext ctx) {
            switch (ctx.op.getText()) {
                case "!":
                    requireCompatible(Value.BOOL, ctx.exp());
                    return Value.BOOL;
                case "-":
                    requireCompatible(Value.INT, ctx.exp());
                    return Value.BOOL;
            }
            assert false;
            return null;
        }

        @Override
        public Type visitCallExp(CallExpContext ctx) {
            switch (ctx.callee.getText()) {
                case "abs":
                    require(ctx.args.size() == 1, "abs should have 1 arg", ctx);
                    requireCompatible(Value.INT, ctx.args.get(0));
                    return Value.INT;
            }
            assert false;
            return null;
        }

        @Override
        public Type visitIfExp(IfExpContext ctx) {
            requireCompatible(Value.BOOL, ctx.cond);
            Type t = accept(ctx.ifTrue);
            Type f = accept(ctx.ifFalse);
            require(compatible(t, f) && compatible(f, t),"Unrelated condition operands", ctx);
            return t;
        }

        @Override
        public Type visitBinOpBoolExp(BinOpBoolExpContext ctx) {
            requireCompatible(Value.BOOL, ctx.left, ctx.right);
            return Value.BOOL;
        }

        @Override
        public Type visitBinOpEqExp(BinOpEqExpContext ctx) {
            Type leftType = accept(ctx.left);
            Type rightType = accept(ctx.right);
            require(related(leftType, rightType),
                    String.format("Unrelated equality operands %s:%s and %s:%s",
                            ctx.left.getText(), leftType, ctx.right.getText(), rightType),
                    ctx);
            return Value.BOOL;
        }

        private void binopInt(ExpContext left, ExpContext right) {
            requireCompatible(Value.INT, left, right);
        }

        private boolean related(Type left, Type right) {
            return compatible(left, right) || compatible(right, left);
        }

        private Type accept(ParserRuleContext ctx) {
            assert ctx != null;
            Type result = ctx.accept(this);
            assert result != null;
            return result;
        }

    }

}
