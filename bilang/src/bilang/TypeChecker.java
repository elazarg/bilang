package bilang;

import java.util.*;
import static java.util.Collections.singletonList;
import static java.util.stream.Collectors.toList;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import bilang.generated.BiLangBaseVisitor;

import static bilang.generated.BiLangParser.*;
import static bilang.Type.compatible;
import static bilang.Main.require;


class TypeChecker extends BiLangBaseVisitor<Void> {
    private final Map<String, Type> types = new HashMap<>();
    {
        types.put("void", Value.VOID);
        types.put("int", Value.INT);
    }

    private final SymbolTable symbolTable;
    {
        Map<String, Type> builtins = new HashMap<>();
        symbolTable = new SymbolTable(builtins);
    }

    private final ExpTypeChecker expChecker = new ExpTypeChecker();

    private Void accept(ParserRuleContext ctx) {
        if (ctx != null)
            return ctx.accept(this);
        return defaultResult();
    }

    private Type ret = null;

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
        accept(ctx.varDec());
        if (initType != null) {
            Type lvalueType = lookupTypename(ctx.dec.type.getText(), ctx);
            require(compatible(initType, lvalueType), "Incompatible initializer", ctx.init);
        }
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
        require(type != Value.VOID, "Cannot declare void variables", ctx);
        scope.put(name, type);
    }

    private void declareType(String name, Type itemType, Token ctx) {
        require(!types.containsKey(name),
                "Type name already declared", ctx);
        require(symbolTable.lookup(name) == null,
                "Cannot redeclare name as type name", ctx);
        types.put(name, itemType);
    }

    @Override
    public Void visitAssignStmt(AssignStmtContext ctx) {
        require(compatible(expChecker.accept(ctx.exp()), expChecker.accept(ctx.exp())),
                "Incompatible rvalue", ctx.exp());
        return null;
    }

    private Type lookupTypename(String typename, ParserRuleContext ctx) {
        if (typename == null) return null;
        Type res = types.get(typename);
        require(res != null, "Unknown type name", ctx);
        return res;
    }

    class ExpTypeChecker extends BiLangBaseVisitor<Type> {

        @Override
        public Type visitParenExp(ParenExpContext ctx) {
            return accept(ctx.exp());
        }

        @Override
        public Type visitUndefExp(UndefExpContext ctx) {
            return Value.UNDEF;
        }

        @Override
        public Type visitNumLiteral(NumLiteralContext ctx) {
            return Value.INT;
        }

        @Override
        public Type visitBinOpMultExp(BinOpMultExpContext ctx) {
            require(isInteger(ctx.left), "Left operand must be int", ctx);
            require(isInteger(ctx.right), "Right operand must be int", ctx);
            return Value.INT;
        }

        @Override
        public Type visitBinOpCompExp(BinOpCompExpContext ctx) {
            require(isInteger(ctx.left), "Left operand must be int", ctx);
            require(isInteger(ctx.right), "Right operand must be int", ctx);
            return Value.INT;
        }

        @Override
        public Type visitBinOpAddExp(BinOpAddExpContext ctx) {
            final Type left = accept(ctx.left);
            final Type right = accept(ctx.right);
            if (left == Value.INT) {
                require(right == Value.INT, "Invalid rhs type, got " + right.getClass(), ctx.right);
                return Value.INT;
            }
            require(false, "Invalid left argument", ctx.left);
            assert false;
            return null;
        }

        @Override
        public Type visitBinOpEqExp(BinOpEqExpContext ctx) {
            require(related(accept(ctx.left), accept(ctx.right)),"Unrelated '=' operands", ctx.right);
            return Value.INT;
        }

        private boolean related(Type left, Type right) {
            return compatible(left, right) || compatible(right, left);
        }

        private boolean isInteger(ExpContext left) {
            return compatible(accept(left), Value.INT);
        }


        private Type accept(ExpContext exp) {
            return _accept(exp);
        }

        private Type _accept(ParserRuleContext ctx) {
            assert ctx != null;
            Type result = ctx.accept(this);
            assert result != null;
            require(result != Value.VOID, "Expression cannot be void", ctx);
            return result;
        }

    }

}
