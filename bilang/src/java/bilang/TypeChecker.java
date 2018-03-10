package bilang;

import java.util.*;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import bilang.generated.BiLangBaseVisitor;

import static bilang.generated.BiLangParser.*;
import static bilang.Type.compatible;
import static bilang.Main.require;


class TypeChecker extends BiLangBaseVisitor<Void> {
    private final Map<String, Type> types = new HashMap<>(Map.of(
            "role", ValueType.ROLE,
            "address", ValueType.ROLE,
            "int", ValueType.INT,
            "bool", ValueType.BOOL
    ));

    private final SymbolTable<Type> symbolTable = new SymbolTable<>(Map.of());

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
        Type initType = (ctx.init != null) ? expChecker.accept(ctx.init) : null;
        accept(ctx.dec);
        if (initType != null) {
            Type lvalueType = lookupTypename(ctx.dec.type.getText(), ctx);
            require(compatible(initType, lvalueType), "Incompatible initializer", ctx.init);
        }
        return null;
    }

    private boolean hidden = false;
    @Override
    public Void visitYieldDef(YieldDefContext ctx) {
        this.hidden = ctx.hidden != null;
        super.visitYieldDef(ctx);
        this.hidden = false;
        return null;
    }

    @Override
    public Void visitJoinDef(JoinDefContext ctx) {
        ctx.packet().forEach(this::bindPacket);
        return null;
    }

    @Override
    public Void visitJoinManyDef(JoinManyDefContext ctx) {
        declare(ctx.role, ValueType.ROLE_SET);
        return null;
    }

    @Override
    public Void visitForYieldStmt(ForYieldStmtContext ctx) {
        symbolTable.push();
        declare(ctx.packet().role, ValueType.ROLE);
        accept(ctx.packet());
        require(symbolTable.lookup(ctx.from.getText()).isCompatible(ValueType.ROLE_SET),
                "Variable must refer to a role set", ctx.from);
        accept(ctx.block());
        symbolTable.pop();
        return null;
    }

    private void bindPacket(PacketContext packet) {
        declare(packet.role, ValueType.ROLE);
        accept(packet);
    }

    @Override
    public Void visitWhereClause(WhereClauseContext ctx) {
        if (ctx.cond != null)
            requireCompatible(ValueType.BOOL, ctx.cond);
        return null;
    }

    @Override
    public Void visitPacket(PacketContext ctx) {
        require(symbolTable.lookup(ctx.role.getText()).isCompatible(ValueType.ROLE),
                "Variable must refer to a role", ctx.role);
        super.visitPacket(ctx);
        return null;
    }

    @Override
    public Void visitVarDec(VarDecContext ctx) {
        declare(ctx.name, lookupTypename(ctx.type.getText(), ctx));
        return null;
    }

    private void declare(Token ctx, Type type) {
        if (hidden && type != ValueType.ROLE) {
            type = new HiddenType(type);
        }
        String name = ctx.getText();
        require(!types.containsKey(name),"Cannot redeclare type name as name", ctx);
        Map<String, Type> scope = symbolTable.currentScope();
        require(!scope.containsKey(name),"Name already declared", ctx);
        scope.put(name, type);
    }

    @Override
    public Void visitTypeDec(TypeDecContext typeDec) {
        String name = typeDec.name.getText();
        require(!types.containsKey(name),
                "Type name already declared", typeDec.name);
        types.put(name, typedef.visit(typeDec.typeExp()));
        return null;
    }

    @Override
    public Void visitSubsetTypeExp(SubsetTypeExpContext ctx) {
        assert false;
        return null;
    }

    @Override
    public Void visitRangeTypeExp(RangeTypeExpContext ctx) {
        assert false;
        return null;
    }

    @Override
    public Void visitAssignStmt(AssignStmtContext ctx) {
        requireCompatible(symbolTable.lookup(ctx.target.getText()), ctx.exp());
        return null;
    }

    @Override
    public Void visitRevealStmt(RevealStmtContext ctx) {
        Type t = symbolTable.lookup(ctx.target.getText());
        require(t != null, "Undefined variable", ctx.target);
        require(t instanceof HiddenType, "Expression must be hidden", ctx);
        symbolTable.currentScope().put(ctx.target.getText(), ((HiddenType) t).t);
        return super.visitRevealStmt(ctx);
    }

    @Override
    public Void visitTransferStmt(TransferStmtContext ctx) {
        requireCompatible(ValueType.ROLE, ctx.from, ctx.to);
        requireCompatible(ValueType.INT, ctx.amount);
        return null;
    }

    @Override
    public Void visitIfStmt(IfStmtContext ctx) {
        requireCompatible(ValueType.BOOL, ctx.exp());
        accept(ctx.ifTrue);
        accept(ctx.ifFalse);
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
            Type t1 = expChecker.accept(exp);
            require(t1.isCompatible(t),
                    String.format("Expression \"%s\" must be %s not %s", exp.getText(), t, t1),
                    exp);
        }
    }
    private void requireCompatible(Type t, Token token) {
        Type t1 = symbolTable.lookup(token.getText());
        require(t1.isCompatible(t),
                String.format("Expression \"%s\" must be %s not %s", token.getText(), t, t1),
                token);
    }
    
    public class TypeDefiner extends BiLangBaseVisitor<Type> {
        @Override
        public Type visitSubsetTypeExp(SubsetTypeExpContext ctx)  {
            return new Subset(ctx.vals.stream().map(x->Integer.parseInt(x.getText())).collect(Collectors.toSet()));
        }
        @Override
        public Type visitRangeTypeExp(RangeTypeExpContext ctx)  {
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
        public Type visitMemberExp(MemberExpContext ctx) {
            requireCompatible(ValueType.ROLE, ctx.role);
            return ValueType.UNDEF;
        }

        @Override
        public Type visitUndefExp(UndefExpContext ctx) {
            return ValueType.UNDEF;
        }

        @Override
        public Type visitNumLiteralExp(NumLiteralExpContext ctx) {
            return ValueType.INT;
        }

        @Override
        public Type visitAddressLiteralExp(AddressLiteralExpContext ctx) {
            return ValueType.ROLE;
        }

        @Override
        public Type visitBinOpMultExp(BinOpMultExpContext ctx) {
            binopInt(ctx.left, ctx.right);
            return ValueType.INT;
        }

        @Override
        public Type visitBinOpAddExp(BinOpAddExpContext ctx) {
            binopInt(ctx.left, ctx.right);
            return ValueType.INT;
        }

        @Override
        public Type visitBinOpCompExp(BinOpCompExpContext ctx) {
            binopInt(ctx.left, ctx.right);
            return ValueType.BOOL;
        }

        @Override
        public Type visitUnOpExp(UnOpExpContext ctx) {
            switch (ctx.op.getText()) {
                case "!":
                    requireCompatible(ValueType.BOOL, ctx.exp());
                    return ValueType.BOOL;
                case "-":
                    requireCompatible(ValueType.INT, ctx.exp());
                    return ValueType.INT;
            }
            assert false;
            return null;
        }

        @Override
        public Type visitCallExp(CallExpContext ctx) {
            switch (ctx.callee.getText()) {
                case "abs":
                    require(ctx.args.size() == 1, "abs should have 1 arg", ctx);
                    requireCompatible(ValueType.INT, ctx.args.get(0));
                    return ValueType.INT;
            }
            assert false;
            return null;
        }

        @Override
        public Type visitIfExp(IfExpContext ctx) {
            requireCompatible(ValueType.BOOL, ctx.cond);
            Type t = accept(ctx.ifTrue);
            Type f = accept(ctx.ifFalse);
            require(compatible(t, f) && compatible(f, t),"Unrelated condition operands", ctx);
            return t;
        }

        @Override
        public Type visitBinOpBoolExp(BinOpBoolExpContext ctx) {
            requireCompatible(ValueType.BOOL, ctx.left, ctx.right);
            return ValueType.BOOL;
        }


        @Override
        public Type visitBinOpEqExp(BinOpEqExpContext ctx) {
            Type leftType = accept(ctx.left);
            Type rightType = accept(ctx.right);
            require(related(leftType, rightType),
                    String.format("Unrelated equality operands %s:%s and %s:%s",
                            ctx.left.getText(), leftType, ctx.right.getText(), rightType),
                    ctx);
            return ValueType.BOOL;
        }

        private void binopInt(ExpContext left, ExpContext right) {
            requireCompatible(ValueType.INT, left, right);
        }

        private boolean related(Type left, Type right) {
            return compatible(left, right) || compatible(right, left);
        }

        Type accept(ParserRuleContext ctx) {
            assert ctx != null;
            Type result = ctx.accept(this);
            assert result != null;
            return result;
        }

    }

}
