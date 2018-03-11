package bilang;

import bilang.generated.BiLangBaseVisitor;
import org.antlr.v4.runtime.Token;

import java.util.*;

import static bilang.Main.require;
import static bilang.generated.BiLangParser.*;

interface Value {}

enum Vals implements Value {
    UNDEFINED
}

final class BoolVals implements Value {
    boolean value;
    private BoolVals(boolean b) { this.value = b;}
    static final BoolVals TRUE = new BoolVals(true);
    static final BoolVals FALSE = new BoolVals(false);
    @Override
    public String toString() {
        return this == TRUE ? "TRUE" : "FALSE";
    }
}

final class IntVals implements Value {
    int value;
    IntVals(int i) { this.value = i;}
    @Override
    public String toString() {
        return Integer.toString(value);
    }
}

final class Address implements Value {
    int value;
    Address(int i) { this.value = i;}
    public String toString() {
        return Integer.toHexString(value);
    }
}

final class AddressSet implements Value {
    List<Address> addresses;
    AddressSet(List<Address> addresses) { this.addresses = addresses;}
    public String toString() {
        return "Set(" + addresses + ")";
    }
}
final class Hidden<T extends Value> implements Value {
    T v;
    Hidden(T v) { this.v = v;}
    public String toString() {
        return "[" + v + "]";
    }
}

interface Strategy {
    List<Map<String,Value>> respondTo(List<Map<String, Value>> last);
}

final class Interpreter extends BiLangBaseVisitor<Void> {
    private SymbolTable<Value> state = new SymbolTable<>(Map.of());

    private Evaluator evaluator = new Evaluator();

    private Strategy players;
    Interpreter(Strategy players) {
        this.players = players;
    }

    private Value eval(ExpContext exp) {
        Value res = exp.accept(evaluator);
        require(res != null);
        return res;
    }

    private Value evalDefined(ExpContext exp) {
        Value res = eval(exp);
        require(res != Vals.UNDEFINED);
        return res;
    }

    @Override
    public Void visitProgram(ProgramContext ctx) {
        return ctx.block().accept(this);
    }

    @Override
    public Void visitTypeDec(TypeDecContext ctx) {
        require(false);
        return super.visitTypeDec(ctx);
    }

    @Override
    public Void visitSubsetTypeExp(SubsetTypeExpContext ctx) {
        require(false);
        return super.visitSubsetTypeExp(ctx);
    }

    @Override
    public Void visitRangeTypeExp(RangeTypeExpContext ctx) {
        require(false);
        return super.visitRangeTypeExp(ctx);
    }

    @Override
    public Void visitBlock(BlockContext ctx) {
        state.push();
        for (StmtContext x : ctx.stmt())
            x.accept(this);
        state.pop();
        return null;
    }

    final class Evaluator extends BiLangBaseVisitor<Value> {
        @Override
        public BoolVals visitBinOpEqExp(BinOpEqExpContext ctx) {
            Value left = eval(ctx.left);
            Value right = eval(ctx.right);
            return "==".equals(ctx.op.getText()) == left.equals(right) ? BoolVals.TRUE : BoolVals.FALSE;
        }

        @Override
        public Value visitUndefExp(UndefExpContext ctx) {
            return Vals.UNDEFINED;
        }

        @Override
        public IntVals visitBinOpAddExp(BinOpAddExpContext ctx) {
            return binOpInt(ctx.op, ctx.left, ctx.right);
        }

        @Override
        public Value visitBinOpMultExp(BinOpMultExpContext ctx) {
            return binOpInt(ctx.op, ctx.left, ctx.right);
        }

        private IntVals binOpInt(Token op, ExpContext _1, ExpContext _2) {
            int left = ((IntVals)evalDefined(_1)).value;
            int right = ((IntVals)evalDefined(_2)).value;
            switch (op.getText()) {
                case "+": return new IntVals(left + right);
                case "-": return new IntVals(left - right);
                case "*": return new IntVals(left * right);
                case "/": return new IntVals(left / right);
            }
            assert false;
            return null;
        }

        @Override
        public Value visitBinOpCompExp(BinOpCompExpContext ctx) {
            return super.visitBinOpCompExp(ctx);
        }

        @Override
        public Value visitUnOpExp(UnOpExpContext ctx) {
            Value val = evalDefined(ctx.exp());
            switch (ctx.op.getText()) {
                case "-": return new IntVals(-((IntVals)val).value);
                case "!": return ((BoolVals)val).value ? BoolVals.FALSE : BoolVals.TRUE;
            }
            assert false;
            return null;
        }

        @Override
        public Value visitIdExp(IdExpContext ctx) {
            Value res = state.lookup(ctx.name.getText());
            require(res != null);
            return res;
        }

        @Override
        public Value visitMemberExp(MemberExpContext ctx) {
            require(false);
            return null;
        }

        @Override
        public Value visitCallExp(CallExpContext ctx) {
            require(false);
            return null;
        }

        @Override
        public Value visitIfExp(IfExpContext ctx) {
            BoolVals b = (BoolVals)eval(ctx.cond);
            return eval(b.value ? ctx.ifTrue : ctx.ifFalse);
        }

        @Override
        public Value visitBinOpBoolExp(BinOpBoolExpContext ctx) {
            return binOpBool(ctx.op, ctx.left, ctx.right);
        }

        @Override
        public Value visitParenExp(ParenExpContext ctx) {
            return eval(ctx.exp());
        }

        private BoolVals binOpBool(Token op, ExpContext _left, ExpContext _right) {
            boolean left = ((BoolVals) evalDefined(_left)).value;
            switch (op.getText()) {
                case "&&": if (!left) return BoolVals.FALSE;
                case "||": if (left) return BoolVals.TRUE;
                default: assert false;
            }
            return ((BoolVals) evalDefined(_right)).value ? BoolVals.TRUE : BoolVals.FALSE;
        }

        @Override
        public Value visitAddressLiteralExp(AddressLiteralExpContext ctx) {
            return new Address(Integer.parseInt(ctx.ADDRESS().getText(), 16));
        }

        @Override
        public Value visitNumLiteralExp(NumLiteralExpContext ctx) {
            return new IntVals(Integer.parseInt(ctx.INT().getText()));
        }
    }

    @Override
    public Void visitVarDef(VarDefContext ctx) {
        defineVar(ctx.dec, eval(ctx.init));
        return null;
    }

    private void defineVar(VarDecContext dec, Value value) {
        dec.accept(this);
        updateVar(varName(dec), value);
    }

    private Value updateVar(String var, Value value) {
        return state.currentScope().put(var, value);
    }

    List<Map<String, Value>> last = new LinkedList<>();
    @Override
    public Void visitYieldDef(YieldDefContext ctx) {
        this.last = players.respondTo(this.last);
        List<PacketContext> packets = ctx.packet();
        require(this.last.size() == packets.size());
        for (int i = 0; i < last.size(); i++) {
            Map<String, Value> msg = last.get(i);
            state.currentScope().putAll(msg);
            // check for matching
            PacketContext p = packets.get(i);
            require(p.decls.size() == msg.size());
            if (!checkWhereClause(p.whereClause())) {
                msg.replaceAll((k, v) -> Vals.UNDEFINED);
                state.currentScope().putAll(msg);
            }
        }
        return null;
    }

    private String varName(VarDecContext dec) {
        return dec.name.getText();
    }

    @Override
    public Void visitJoinDef(JoinDefContext ctx) {
        awaitResponse();
        String var = ctx.packet(0).role.getText();
        Address a = (Address)last.get(0).get(var);
        state.currentScope().put(var, a);
        // TODO: put the rest of the msg
        return super.visitJoinDef(ctx);
    }

    @Override
    public Void visitJoinManyDef(JoinManyDefContext ctx) {
        awaitResponse();
        require(last.size() == 1 && last.get(0).size() == 1);
        String var = ctx.role.getText();
        AddressSet a = (AddressSet)last.get(0).get(var);
        state.currentScope().put(var, a);
        return null;
    }

    private void awaitResponse() {
        this.last = players.respondTo(last);
    }

    @Override
    public Void visitRevealStmt(RevealStmtContext ctx) {
        String var = ctx.target.getText();
        Value _h = state.lookup(var);
        require(_h != null);
        require(_h instanceof Hidden);

        awaitResponse();
        require(last.size() == 1 && last.get(0).size() == 1);
        Hidden<Value> h = (Hidden<Value>)_h;
        boolean reveal = ((BoolVals)last.get(0).get(var)).value;
        state.update(var, reveal ? h.v : Vals.UNDEFINED);
        return null;
    }

    @Override
    public Void visitAssignStmt(AssignStmtContext ctx) {
        state.update(ctx.target.getText(), eval(ctx.exp()));
        return super.visitAssignStmt(ctx);
    }

    @Override
    public Void visitIfStmt(IfStmtContext ctx) {
        BoolVals cond = (BoolVals)eval(ctx.exp());
        return (cond.value ? ctx.ifTrue : ctx.ifFalse).accept(this);
    }

    private Address joinFrom(String var, AddressSet ads) {
        awaitResponse();
        require(last.size() == 1 && last.get(0).size() == 1);
        Address a = (Address)last.get(0).get(var);
        require(ads.addresses.contains(a));
        return a;
    }

    @Override
    public Void visitForYieldStmt(ForYieldStmtContext ctx) {
        awaitResponse();

        return super.visitForYieldStmt(ctx);
    }

    @Override
    public Void visitTransferStmt(TransferStmtContext ctx) {
        IntVals amount = (IntVals)eval(ctx.amount);
        Address from = (Address)eval(ctx.from);
        Address to = (Address)eval(ctx.to);
        // TODO: actual transfer
        return null;
    }

    private boolean checkWhereClause(WhereClauseContext ctx) {
        ExpContext cond = ctx.cond;
        return cond == null || eval(cond) == BoolVals.TRUE;
    }

    @Override
    public Void visitVarDec(VarDecContext ctx) {
        updateVar(varName(ctx), Vals.UNDEFINED);
        return null;
    }
    
    private void require(boolean b) {
        if (!b)
            throw new RuntimeException();
    }
}


class PredefinedStrategy implements Strategy {
    Iterator<List<Map<String, Value>>> it;

    PredefinedStrategy(Iterable<List<Map<String, Value>>> msgs) {
        it = msgs.iterator();
    }

    @Override
    public List<Map<String, Value>> respondTo(List<Map<String, Value>> last) {
        return it.next();
    }
}
