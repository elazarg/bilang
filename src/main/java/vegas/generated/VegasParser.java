// Generated from Vegas.g4 by ANTLR 4.13.2
package vegas.generated;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class VegasParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		T__31=32, T__32=33, T__33=34, T__34=35, T__35=36, T__36=37, T__37=38, 
		T__38=39, T__39=40, T__40=41, T__41=42, ROLE_ID=43, LOWER_ID=44, INT=45, 
		ADDRESS=46, STRING=47, BlockComment=48, LineComment=49, WS=50;
	public static final int
		RULE_program = 0, RULE_typeDec = 1, RULE_typeExp = 2, RULE_ext = 3, RULE_query = 4, 
		RULE_outcome = 5, RULE_item = 6, RULE_exp = 7, RULE_varDec = 8, RULE_typeId = 9, 
		RULE_varId = 10, RULE_roleId = 11;
	private static String[] makeRuleNames() {
		return new String[] {
			"program", "typeDec", "typeExp", "ext", "query", "outcome", "item", "exp", 
			"varDec", "typeId", "varId", "roleId"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'type'", "'='", "'{'", "','", "'}'", "'..'", "'join'", "'yield'", 
			"'reveal'", "'random'", "';'", "'withdraw'", "'('", "')'", "'$'", "'where'", 
			"'?'", "':'", "'let'", "'in'", "'->'", "'.'", "'-'", "'!'", "'*'", "'/'", 
			"'+'", "'!='", "'=='", "'null'", "'<'", "'<='", "'>='", "'>'", "'<->'", 
			"'<-!->'", "'&&'", "'||'", "'true'", "'false'", "'let!'", "'hidden'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, "ROLE_ID", "LOWER_ID", "INT", 
			"ADDRESS", "STRING", "BlockComment", "LineComment", "WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Vegas.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public VegasParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ProgramContext extends ParserRuleContext {
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public TerminalNode EOF() { return getToken(VegasParser.EOF, 0); }
		public List<TypeDecContext> typeDec() {
			return getRuleContexts(TypeDecContext.class);
		}
		public TypeDecContext typeDec(int i) {
			return getRuleContext(TypeDecContext.class,i);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitProgram(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_program);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(27);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(24);
				typeDec();
				}
				}
				setState(29);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(30);
			ext();
			setState(31);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TypeDecContext extends ParserRuleContext {
		public TypeIdContext name;
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public TypeIdContext typeId() {
			return getRuleContext(TypeIdContext.class,0);
		}
		public TypeDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitTypeDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeDecContext typeDec() throws RecognitionException {
		TypeDecContext _localctx = new TypeDecContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_typeDec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(33);
			match(T__0);
			setState(34);
			((TypeDecContext)_localctx).name = typeId();
			setState(35);
			match(T__1);
			setState(36);
			typeExp();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TypeExpContext extends ParserRuleContext {
		public TypeExpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeExp; }
	 
		public TypeExpContext() { }
		public void copyFrom(TypeExpContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IdTypeExpContext extends TypeExpContext {
		public TypeIdContext name;
		public TypeIdContext typeId() {
			return getRuleContext(TypeIdContext.class,0);
		}
		public IdTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIdTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class SubsetTypeExpContext extends TypeExpContext {
		public Token INT;
		public List<Token> vals = new ArrayList<Token>();
		public List<TerminalNode> INT() { return getTokens(VegasParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(VegasParser.INT, i);
		}
		public SubsetTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitSubsetTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class RangeTypeExpContext extends TypeExpContext {
		public Token start;
		public Token end;
		public List<TerminalNode> INT() { return getTokens(VegasParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(VegasParser.INT, i);
		}
		public RangeTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRangeTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeExpContext typeExp() throws RecognitionException {
		TypeExpContext _localctx = new TypeExpContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_typeExp);
		int _la;
		try {
			setState(54);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				_localctx = new SubsetTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(38);
				match(T__2);
				setState(39);
				((SubsetTypeExpContext)_localctx).INT = match(INT);
				((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
				setState(44);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(40);
					match(T__3);
					setState(41);
					((SubsetTypeExpContext)_localctx).INT = match(INT);
					((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
					}
					}
					setState(46);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(47);
				match(T__4);
				}
				break;
			case 2:
				_localctx = new RangeTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(48);
				match(T__2);
				setState(49);
				((RangeTypeExpContext)_localctx).start = match(INT);
				setState(50);
				match(T__5);
				setState(51);
				((RangeTypeExpContext)_localctx).end = match(INT);
				setState(52);
				match(T__4);
				}
				break;
			case 3:
				_localctx = new IdTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(53);
				((IdTypeExpContext)_localctx).name = typeId();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExtContext extends ParserRuleContext {
		public ExtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ext; }
	 
		public ExtContext() { }
		public void copyFrom(ExtContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ReceiveExtContext extends ExtContext {
		public Token kind;
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public List<QueryContext> query() {
			return getRuleContexts(QueryContext.class);
		}
		public QueryContext query(int i) {
			return getRuleContext(QueryContext.class,i);
		}
		public ReceiveExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitReceiveExt(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class WithdrawExtContext extends ExtContext {
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public WithdrawExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitWithdrawExt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExtContext ext() throws RecognitionException {
		ExtContext _localctx = new ExtContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_ext);
		int _la;
		try {
			setState(67);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__6:
			case T__7:
			case T__8:
			case T__9:
				_localctx = new ReceiveExtContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(56);
				((ReceiveExtContext)_localctx).kind = _input.LT(1);
				_la = _input.LA(1);
				if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 1920L) != 0)) ) {
					((ReceiveExtContext)_localctx).kind = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(58); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(57);
					query();
					}
					}
					setState(60); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(62);
				match(T__10);
				setState(63);
				ext();
				}
				break;
			case T__11:
				_localctx = new WithdrawExtContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(65);
				match(T__11);
				setState(66);
				outcome();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class QueryContext extends ParserRuleContext {
		public RoleIdContext role;
		public VarDecContext varDec;
		public List<VarDecContext> decls = new ArrayList<VarDecContext>();
		public Token deposit;
		public ExpContext cond;
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<VarDecContext> varDec() {
			return getRuleContexts(VarDecContext.class);
		}
		public VarDecContext varDec(int i) {
			return getRuleContext(VarDecContext.class,i);
		}
		public QueryContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_query; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitQuery(this);
			else return visitor.visitChildren(this);
		}
	}

	public final QueryContext query() throws RecognitionException {
		QueryContext _localctx = new QueryContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_query);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(69);
			((QueryContext)_localctx).role = roleId();
			setState(82);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__12) {
				{
				setState(70);
				match(T__12);
				setState(79);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==LOWER_ID) {
					{
					setState(71);
					((QueryContext)_localctx).varDec = varDec();
					((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
					setState(76);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__3) {
						{
						{
						setState(72);
						match(T__3);
						setState(73);
						((QueryContext)_localctx).varDec = varDec();
						((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
						}
						}
						setState(78);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(81);
				match(T__13);
				}
			}

			setState(86);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__14) {
				{
				setState(84);
				match(T__14);
				setState(85);
				((QueryContext)_localctx).deposit = match(INT);
				}
			}

			setState(90);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__15) {
				{
				setState(88);
				match(T__15);
				setState(89);
				((QueryContext)_localctx).cond = exp(0);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class OutcomeContext extends ParserRuleContext {
		public OutcomeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_outcome; }
	 
		public OutcomeContext() { }
		public void copyFrom(OutcomeContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class OutcomeExpContext extends OutcomeContext {
		public ItemContext item;
		public List<ItemContext> items = new ArrayList<ItemContext>();
		public List<ItemContext> item() {
			return getRuleContexts(ItemContext.class);
		}
		public ItemContext item(int i) {
			return getRuleContext(ItemContext.class,i);
		}
		public OutcomeExpContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitOutcomeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IfOutcomeContext extends OutcomeContext {
		public ExpContext cond;
		public OutcomeContext ifTrue;
		public OutcomeContext ifFalse;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<OutcomeContext> outcome() {
			return getRuleContexts(OutcomeContext.class);
		}
		public OutcomeContext outcome(int i) {
			return getRuleContext(OutcomeContext.class,i);
		}
		public IfOutcomeContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIfOutcome(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class LetOutcomeContext extends OutcomeContext {
		public VarDecContext dec;
		public ExpContext init;
		public OutcomeContext body;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public LetOutcomeContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitLetOutcome(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ParenOutcomeContext extends OutcomeContext {
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public ParenOutcomeContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitParenOutcome(this);
			else return visitor.visitChildren(this);
		}
	}

	public final OutcomeContext outcome() throws RecognitionException {
		OutcomeContext _localctx = new OutcomeContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_outcome);
		int _la;
		try {
			setState(117);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				_localctx = new IfOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(92);
				((IfOutcomeContext)_localctx).cond = exp(0);
				setState(93);
				match(T__16);
				setState(94);
				((IfOutcomeContext)_localctx).ifTrue = outcome();
				setState(95);
				match(T__17);
				setState(96);
				((IfOutcomeContext)_localctx).ifFalse = outcome();
				}
				break;
			case 2:
				_localctx = new LetOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(98);
				match(T__18);
				setState(99);
				((LetOutcomeContext)_localctx).dec = varDec();
				setState(100);
				match(T__1);
				setState(101);
				((LetOutcomeContext)_localctx).init = exp(0);
				setState(102);
				match(T__19);
				setState(103);
				((LetOutcomeContext)_localctx).body = outcome();
				}
				break;
			case 3:
				_localctx = new ParenOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(105);
				match(T__12);
				setState(106);
				outcome();
				setState(107);
				match(T__13);
				}
				break;
			case 4:
				_localctx = new OutcomeExpContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(109);
				match(T__2);
				setState(111); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(110);
					((OutcomeExpContext)_localctx).item = item();
					((OutcomeExpContext)_localctx).items.add(((OutcomeExpContext)_localctx).item);
					}
					}
					setState(113); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(115);
				match(T__4);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ItemContext extends ParserRuleContext {
		public RoleIdContext role;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public ItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_item; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ItemContext item() throws RecognitionException {
		ItemContext _localctx = new ItemContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_item);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(119);
			((ItemContext)_localctx).role = roleId();
			setState(120);
			match(T__20);
			setState(121);
			exp(0);
			setState(123);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__10) {
				{
				setState(122);
				match(T__10);
				}
			}

			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExpContext extends ParserRuleContext {
		public ExpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_exp; }
	 
		public ExpContext() { }
		public void copyFrom(ExpContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpEqExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpEqExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpEqExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class UndefExpContext extends ExpContext {
		public Token op;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public UndefExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitUndefExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpAddExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpAddExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpAddExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpCompExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpCompExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpCompExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class UnOpExpContext extends ExpContext {
		public Token op;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public UnOpExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitUnOpExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class MemberExpContext extends ExpContext {
		public RoleIdContext role;
		public VarIdContext field;
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public MemberExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitMemberExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IdExpContext extends ExpContext {
		public VarIdContext name;
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public IdExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIdExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class CallExpContext extends ExpContext {
		public VarIdContext callee;
		public ExpContext exp;
		public List<ExpContext> args = new ArrayList<ExpContext>();
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public CallExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitCallExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IfExpContext extends ExpContext {
		public ExpContext cond;
		public ExpContext ifTrue;
		public ExpContext ifFalse;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public IfExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIfExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpBoolExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpBoolExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpBoolExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ParenExpContext extends ExpContext {
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public ParenExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitParenExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BoolLiteralExpContext extends ExpContext {
		public BoolLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBoolLiteralExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class LetExpContext extends ExpContext {
		public VarDecContext dec;
		public ExpContext init;
		public ExpContext body;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public LetExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitLetExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class AddressLiteralExpContext extends ExpContext {
		public TerminalNode ADDRESS() { return getToken(VegasParser.ADDRESS, 0); }
		public AddressLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitAddressLiteralExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpMultExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpMultExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpMultExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NumLiteralExpContext extends ExpContext {
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public NumLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitNumLiteralExp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExpContext exp() throws RecognitionException {
		return exp(0);
	}

	private ExpContext exp(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ExpContext _localctx = new ExpContext(_ctx, _parentState);
		ExpContext _prevctx = _localctx;
		int _startState = 14;
		enterRecursionRule(_localctx, 14, RULE_exp, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(161);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				{
				_localctx = new ParenExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(126);
				match(T__12);
				setState(127);
				exp(0);
				setState(128);
				match(T__13);
				}
				break;
			case 2:
				{
				_localctx = new MemberExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(130);
				((MemberExpContext)_localctx).role = roleId();
				setState(131);
				match(T__21);
				setState(132);
				((MemberExpContext)_localctx).field = varId();
				}
				break;
			case 3:
				{
				_localctx = new CallExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(134);
				((CallExpContext)_localctx).callee = varId();
				setState(135);
				match(T__12);
				setState(144);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 135789711204352L) != 0)) {
					{
					setState(136);
					((CallExpContext)_localctx).exp = exp(0);
					((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
					setState(141);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__3) {
						{
						{
						setState(137);
						match(T__3);
						setState(138);
						((CallExpContext)_localctx).exp = exp(0);
						((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
						}
						}
						setState(143);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(146);
				match(T__13);
				}
				break;
			case 4:
				{
				_localctx = new UnOpExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(148);
				((UnOpExpContext)_localctx).op = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__22 || _la==T__23) ) {
					((UnOpExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(149);
				exp(13);
				}
				break;
			case 5:
				{
				_localctx = new BoolLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(150);
				_la = _input.LA(1);
				if ( !(_la==T__38 || _la==T__39) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				break;
			case 6:
				{
				_localctx = new IdExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(151);
				((IdExpContext)_localctx).name = varId();
				}
				break;
			case 7:
				{
				_localctx = new NumLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(152);
				match(INT);
				}
				break;
			case 8:
				{
				_localctx = new AddressLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(153);
				match(ADDRESS);
				}
				break;
			case 9:
				{
				_localctx = new LetExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(154);
				match(T__40);
				setState(155);
				((LetExpContext)_localctx).dec = varDec();
				setState(156);
				match(T__1);
				setState(157);
				((LetExpContext)_localctx).init = exp(0);
				setState(158);
				match(T__19);
				setState(159);
				((LetExpContext)_localctx).body = exp(1);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(189);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,17,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(187);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
					case 1:
						{
						_localctx = new BinOpMultExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpMultExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(163);
						if (!(precpred(_ctx, 12))) throw new FailedPredicateException(this, "precpred(_ctx, 12)");
						setState(164);
						((BinOpMultExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__24 || _la==T__25) ) {
							((BinOpMultExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(165);
						((BinOpMultExpContext)_localctx).right = exp(13);
						}
						break;
					case 2:
						{
						_localctx = new BinOpAddExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpAddExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(166);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(167);
						((BinOpAddExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__22 || _la==T__26) ) {
							((BinOpAddExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(168);
						((BinOpAddExpContext)_localctx).right = exp(12);
						}
						break;
					case 3:
						{
						_localctx = new BinOpCompExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpCompExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(169);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(170);
						((BinOpCompExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 32212254720L) != 0)) ) {
							((BinOpCompExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(171);
						((BinOpCompExpContext)_localctx).right = exp(10);
						}
						break;
					case 4:
						{
						_localctx = new BinOpEqExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpEqExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(172);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(173);
						((BinOpEqExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 103884521472L) != 0)) ) {
							((BinOpEqExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(174);
						((BinOpEqExpContext)_localctx).right = exp(9);
						}
						break;
					case 5:
						{
						_localctx = new BinOpBoolExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpBoolExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(175);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(176);
						((BinOpBoolExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__36 || _la==T__37) ) {
							((BinOpBoolExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(177);
						((BinOpBoolExpContext)_localctx).right = exp(8);
						}
						break;
					case 6:
						{
						_localctx = new IfExpContext(new ExpContext(_parentctx, _parentState));
						((IfExpContext)_localctx).cond = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(178);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(179);
						match(T__16);
						setState(180);
						((IfExpContext)_localctx).ifTrue = exp(0);
						setState(181);
						match(T__17);
						setState(182);
						((IfExpContext)_localctx).ifFalse = exp(6);
						}
						break;
					case 7:
						{
						_localctx = new UndefExpContext(new ExpContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(184);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(185);
						((UndefExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__27 || _la==T__28) ) {
							((UndefExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(186);
						match(T__29);
						}
						break;
					}
					} 
				}
				setState(191);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,17,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VarDecContext extends ParserRuleContext {
		public VarIdContext name;
		public Token hidden;
		public TypeExpContext type;
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public VarDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitVarDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarDecContext varDec() throws RecognitionException {
		VarDecContext _localctx = new VarDecContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_varDec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(192);
			((VarDecContext)_localctx).name = varId();
			setState(193);
			match(T__17);
			setState(195);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__41) {
				{
				setState(194);
				((VarDecContext)_localctx).hidden = match(T__41);
				}
			}

			setState(197);
			((VarDecContext)_localctx).type = typeExp();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TypeIdContext extends ParserRuleContext {
		public TerminalNode LOWER_ID() { return getToken(VegasParser.LOWER_ID, 0); }
		public TypeIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitTypeId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeIdContext typeId() throws RecognitionException {
		TypeIdContext _localctx = new TypeIdContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_typeId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(199);
			match(LOWER_ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VarIdContext extends ParserRuleContext {
		public TerminalNode LOWER_ID() { return getToken(VegasParser.LOWER_ID, 0); }
		public VarIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitVarId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarIdContext varId() throws RecognitionException {
		VarIdContext _localctx = new VarIdContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_varId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(201);
			match(LOWER_ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class RoleIdContext extends ParserRuleContext {
		public TerminalNode ROLE_ID() { return getToken(VegasParser.ROLE_ID, 0); }
		public RoleIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_roleId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRoleId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RoleIdContext roleId() throws RecognitionException {
		RoleIdContext _localctx = new RoleIdContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_roleId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(203);
			match(ROLE_ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 7:
			return exp_sempred((ExpContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean exp_sempred(ExpContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 12);
		case 1:
			return precpred(_ctx, 11);
		case 2:
			return precpred(_ctx, 9);
		case 3:
			return precpred(_ctx, 8);
		case 4:
			return precpred(_ctx, 7);
		case 5:
			return precpred(_ctx, 6);
		case 6:
			return precpred(_ctx, 10);
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u00012\u00ce\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0001"+
		"\u0000\u0005\u0000\u001a\b\u0000\n\u0000\f\u0000\u001d\t\u0000\u0001\u0000"+
		"\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002"+
		"+\b\u0002\n\u0002\f\u0002.\t\u0002\u0001\u0002\u0001\u0002\u0001\u0002"+
		"\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003\u00027\b\u0002"+
		"\u0001\u0003\u0001\u0003\u0004\u0003;\b\u0003\u000b\u0003\f\u0003<\u0001"+
		"\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0003\u0003D\b"+
		"\u0003\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0005"+
		"\u0004K\b\u0004\n\u0004\f\u0004N\t\u0004\u0003\u0004P\b\u0004\u0001\u0004"+
		"\u0003\u0004S\b\u0004\u0001\u0004\u0001\u0004\u0003\u0004W\b\u0004\u0001"+
		"\u0004\u0001\u0004\u0003\u0004[\b\u0004\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0004\u0005p\b"+
		"\u0005\u000b\u0005\f\u0005q\u0001\u0005\u0001\u0005\u0003\u0005v\b\u0005"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0003\u0006|\b\u0006"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0005\u0007\u008c\b\u0007\n\u0007\f\u0007\u008f"+
		"\t\u0007\u0003\u0007\u0091\b\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0003\u0007\u00a2\b\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0005\u0007\u00bc\b\u0007\n\u0007\f\u0007\u00bf"+
		"\t\u0007\u0001\b\u0001\b\u0001\b\u0003\b\u00c4\b\b\u0001\b\u0001\b\u0001"+
		"\t\u0001\t\u0001\n\u0001\n\u0001\u000b\u0001\u000b\u0001\u000b\u0000\u0001"+
		"\u000e\f\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0000"+
		"\t\u0001\u0000\u0007\n\u0001\u0000\u0017\u0018\u0001\u0000\'(\u0001\u0000"+
		"\u0019\u001a\u0002\u0000\u0017\u0017\u001b\u001b\u0001\u0000\u001f\"\u0002"+
		"\u0000\u001c\u001d#$\u0001\u0000%&\u0001\u0000\u001c\u001d\u00e3\u0000"+
		"\u001b\u0001\u0000\u0000\u0000\u0002!\u0001\u0000\u0000\u0000\u00046\u0001"+
		"\u0000\u0000\u0000\u0006C\u0001\u0000\u0000\u0000\bE\u0001\u0000\u0000"+
		"\u0000\nu\u0001\u0000\u0000\u0000\fw\u0001\u0000\u0000\u0000\u000e\u00a1"+
		"\u0001\u0000\u0000\u0000\u0010\u00c0\u0001\u0000\u0000\u0000\u0012\u00c7"+
		"\u0001\u0000\u0000\u0000\u0014\u00c9\u0001\u0000\u0000\u0000\u0016\u00cb"+
		"\u0001\u0000\u0000\u0000\u0018\u001a\u0003\u0002\u0001\u0000\u0019\u0018"+
		"\u0001\u0000\u0000\u0000\u001a\u001d\u0001\u0000\u0000\u0000\u001b\u0019"+
		"\u0001\u0000\u0000\u0000\u001b\u001c\u0001\u0000\u0000\u0000\u001c\u001e"+
		"\u0001\u0000\u0000\u0000\u001d\u001b\u0001\u0000\u0000\u0000\u001e\u001f"+
		"\u0003\u0006\u0003\u0000\u001f \u0005\u0000\u0000\u0001 \u0001\u0001\u0000"+
		"\u0000\u0000!\"\u0005\u0001\u0000\u0000\"#\u0003\u0012\t\u0000#$\u0005"+
		"\u0002\u0000\u0000$%\u0003\u0004\u0002\u0000%\u0003\u0001\u0000\u0000"+
		"\u0000&\'\u0005\u0003\u0000\u0000\',\u0005-\u0000\u0000()\u0005\u0004"+
		"\u0000\u0000)+\u0005-\u0000\u0000*(\u0001\u0000\u0000\u0000+.\u0001\u0000"+
		"\u0000\u0000,*\u0001\u0000\u0000\u0000,-\u0001\u0000\u0000\u0000-/\u0001"+
		"\u0000\u0000\u0000.,\u0001\u0000\u0000\u0000/7\u0005\u0005\u0000\u0000"+
		"01\u0005\u0003\u0000\u000012\u0005-\u0000\u000023\u0005\u0006\u0000\u0000"+
		"34\u0005-\u0000\u000047\u0005\u0005\u0000\u000057\u0003\u0012\t\u0000"+
		"6&\u0001\u0000\u0000\u000060\u0001\u0000\u0000\u000065\u0001\u0000\u0000"+
		"\u00007\u0005\u0001\u0000\u0000\u00008:\u0007\u0000\u0000\u00009;\u0003"+
		"\b\u0004\u0000:9\u0001\u0000\u0000\u0000;<\u0001\u0000\u0000\u0000<:\u0001"+
		"\u0000\u0000\u0000<=\u0001\u0000\u0000\u0000=>\u0001\u0000\u0000\u0000"+
		">?\u0005\u000b\u0000\u0000?@\u0003\u0006\u0003\u0000@D\u0001\u0000\u0000"+
		"\u0000AB\u0005\f\u0000\u0000BD\u0003\n\u0005\u0000C8\u0001\u0000\u0000"+
		"\u0000CA\u0001\u0000\u0000\u0000D\u0007\u0001\u0000\u0000\u0000ER\u0003"+
		"\u0016\u000b\u0000FO\u0005\r\u0000\u0000GL\u0003\u0010\b\u0000HI\u0005"+
		"\u0004\u0000\u0000IK\u0003\u0010\b\u0000JH\u0001\u0000\u0000\u0000KN\u0001"+
		"\u0000\u0000\u0000LJ\u0001\u0000\u0000\u0000LM\u0001\u0000\u0000\u0000"+
		"MP\u0001\u0000\u0000\u0000NL\u0001\u0000\u0000\u0000OG\u0001\u0000\u0000"+
		"\u0000OP\u0001\u0000\u0000\u0000PQ\u0001\u0000\u0000\u0000QS\u0005\u000e"+
		"\u0000\u0000RF\u0001\u0000\u0000\u0000RS\u0001\u0000\u0000\u0000SV\u0001"+
		"\u0000\u0000\u0000TU\u0005\u000f\u0000\u0000UW\u0005-\u0000\u0000VT\u0001"+
		"\u0000\u0000\u0000VW\u0001\u0000\u0000\u0000WZ\u0001\u0000\u0000\u0000"+
		"XY\u0005\u0010\u0000\u0000Y[\u0003\u000e\u0007\u0000ZX\u0001\u0000\u0000"+
		"\u0000Z[\u0001\u0000\u0000\u0000[\t\u0001\u0000\u0000\u0000\\]\u0003\u000e"+
		"\u0007\u0000]^\u0005\u0011\u0000\u0000^_\u0003\n\u0005\u0000_`\u0005\u0012"+
		"\u0000\u0000`a\u0003\n\u0005\u0000av\u0001\u0000\u0000\u0000bc\u0005\u0013"+
		"\u0000\u0000cd\u0003\u0010\b\u0000de\u0005\u0002\u0000\u0000ef\u0003\u000e"+
		"\u0007\u0000fg\u0005\u0014\u0000\u0000gh\u0003\n\u0005\u0000hv\u0001\u0000"+
		"\u0000\u0000ij\u0005\r\u0000\u0000jk\u0003\n\u0005\u0000kl\u0005\u000e"+
		"\u0000\u0000lv\u0001\u0000\u0000\u0000mo\u0005\u0003\u0000\u0000np\u0003"+
		"\f\u0006\u0000on\u0001\u0000\u0000\u0000pq\u0001\u0000\u0000\u0000qo\u0001"+
		"\u0000\u0000\u0000qr\u0001\u0000\u0000\u0000rs\u0001\u0000\u0000\u0000"+
		"st\u0005\u0005\u0000\u0000tv\u0001\u0000\u0000\u0000u\\\u0001\u0000\u0000"+
		"\u0000ub\u0001\u0000\u0000\u0000ui\u0001\u0000\u0000\u0000um\u0001\u0000"+
		"\u0000\u0000v\u000b\u0001\u0000\u0000\u0000wx\u0003\u0016\u000b\u0000"+
		"xy\u0005\u0015\u0000\u0000y{\u0003\u000e\u0007\u0000z|\u0005\u000b\u0000"+
		"\u0000{z\u0001\u0000\u0000\u0000{|\u0001\u0000\u0000\u0000|\r\u0001\u0000"+
		"\u0000\u0000}~\u0006\u0007\uffff\uffff\u0000~\u007f\u0005\r\u0000\u0000"+
		"\u007f\u0080\u0003\u000e\u0007\u0000\u0080\u0081\u0005\u000e\u0000\u0000"+
		"\u0081\u00a2\u0001\u0000\u0000\u0000\u0082\u0083\u0003\u0016\u000b\u0000"+
		"\u0083\u0084\u0005\u0016\u0000\u0000\u0084\u0085\u0003\u0014\n\u0000\u0085"+
		"\u00a2\u0001\u0000\u0000\u0000\u0086\u0087\u0003\u0014\n\u0000\u0087\u0090"+
		"\u0005\r\u0000\u0000\u0088\u008d\u0003\u000e\u0007\u0000\u0089\u008a\u0005"+
		"\u0004\u0000\u0000\u008a\u008c\u0003\u000e\u0007\u0000\u008b\u0089\u0001"+
		"\u0000\u0000\u0000\u008c\u008f\u0001\u0000\u0000\u0000\u008d\u008b\u0001"+
		"\u0000\u0000\u0000\u008d\u008e\u0001\u0000\u0000\u0000\u008e\u0091\u0001"+
		"\u0000\u0000\u0000\u008f\u008d\u0001\u0000\u0000\u0000\u0090\u0088\u0001"+
		"\u0000\u0000\u0000\u0090\u0091\u0001\u0000\u0000\u0000\u0091\u0092\u0001"+
		"\u0000\u0000\u0000\u0092\u0093\u0005\u000e\u0000\u0000\u0093\u00a2\u0001"+
		"\u0000\u0000\u0000\u0094\u0095\u0007\u0001\u0000\u0000\u0095\u00a2\u0003"+
		"\u000e\u0007\r\u0096\u00a2\u0007\u0002\u0000\u0000\u0097\u00a2\u0003\u0014"+
		"\n\u0000\u0098\u00a2\u0005-\u0000\u0000\u0099\u00a2\u0005.\u0000\u0000"+
		"\u009a\u009b\u0005)\u0000\u0000\u009b\u009c\u0003\u0010\b\u0000\u009c"+
		"\u009d\u0005\u0002\u0000\u0000\u009d\u009e\u0003\u000e\u0007\u0000\u009e"+
		"\u009f\u0005\u0014\u0000\u0000\u009f\u00a0\u0003\u000e\u0007\u0001\u00a0"+
		"\u00a2\u0001\u0000\u0000\u0000\u00a1}\u0001\u0000\u0000\u0000\u00a1\u0082"+
		"\u0001\u0000\u0000\u0000\u00a1\u0086\u0001\u0000\u0000\u0000\u00a1\u0094"+
		"\u0001\u0000\u0000\u0000\u00a1\u0096\u0001\u0000\u0000\u0000\u00a1\u0097"+
		"\u0001\u0000\u0000\u0000\u00a1\u0098\u0001\u0000\u0000\u0000\u00a1\u0099"+
		"\u0001\u0000\u0000\u0000\u00a1\u009a\u0001\u0000\u0000\u0000\u00a2\u00bd"+
		"\u0001\u0000\u0000\u0000\u00a3\u00a4\n\f\u0000\u0000\u00a4\u00a5\u0007"+
		"\u0003\u0000\u0000\u00a5\u00bc\u0003\u000e\u0007\r\u00a6\u00a7\n\u000b"+
		"\u0000\u0000\u00a7\u00a8\u0007\u0004\u0000\u0000\u00a8\u00bc\u0003\u000e"+
		"\u0007\f\u00a9\u00aa\n\t\u0000\u0000\u00aa\u00ab\u0007\u0005\u0000\u0000"+
		"\u00ab\u00bc\u0003\u000e\u0007\n\u00ac\u00ad\n\b\u0000\u0000\u00ad\u00ae"+
		"\u0007\u0006\u0000\u0000\u00ae\u00bc\u0003\u000e\u0007\t\u00af\u00b0\n"+
		"\u0007\u0000\u0000\u00b0\u00b1\u0007\u0007\u0000\u0000\u00b1\u00bc\u0003"+
		"\u000e\u0007\b\u00b2\u00b3\n\u0006\u0000\u0000\u00b3\u00b4\u0005\u0011"+
		"\u0000\u0000\u00b4\u00b5\u0003\u000e\u0007\u0000\u00b5\u00b6\u0005\u0012"+
		"\u0000\u0000\u00b6\u00b7\u0003\u000e\u0007\u0006\u00b7\u00bc\u0001\u0000"+
		"\u0000\u0000\u00b8\u00b9\n\n\u0000\u0000\u00b9\u00ba\u0007\b\u0000\u0000"+
		"\u00ba\u00bc\u0005\u001e\u0000\u0000\u00bb\u00a3\u0001\u0000\u0000\u0000"+
		"\u00bb\u00a6\u0001\u0000\u0000\u0000\u00bb\u00a9\u0001\u0000\u0000\u0000"+
		"\u00bb\u00ac\u0001\u0000\u0000\u0000\u00bb\u00af\u0001\u0000\u0000\u0000"+
		"\u00bb\u00b2\u0001\u0000\u0000\u0000\u00bb\u00b8\u0001\u0000\u0000\u0000"+
		"\u00bc\u00bf\u0001\u0000\u0000\u0000\u00bd\u00bb\u0001\u0000\u0000\u0000"+
		"\u00bd\u00be\u0001\u0000\u0000\u0000\u00be\u000f\u0001\u0000\u0000\u0000"+
		"\u00bf\u00bd\u0001\u0000\u0000\u0000\u00c0\u00c1\u0003\u0014\n\u0000\u00c1"+
		"\u00c3\u0005\u0012\u0000\u0000\u00c2\u00c4\u0005*\u0000\u0000\u00c3\u00c2"+
		"\u0001\u0000\u0000\u0000\u00c3\u00c4\u0001\u0000\u0000\u0000\u00c4\u00c5"+
		"\u0001\u0000\u0000\u0000\u00c5\u00c6\u0003\u0004\u0002\u0000\u00c6\u0011"+
		"\u0001\u0000\u0000\u0000\u00c7\u00c8\u0005,\u0000\u0000\u00c8\u0013\u0001"+
		"\u0000\u0000\u0000\u00c9\u00ca\u0005,\u0000\u0000\u00ca\u0015\u0001\u0000"+
		"\u0000\u0000\u00cb\u00cc\u0005+\u0000\u0000\u00cc\u0017\u0001\u0000\u0000"+
		"\u0000\u0013\u001b,6<CLORVZqu{\u008d\u0090\u00a1\u00bb\u00bd\u00c3";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}