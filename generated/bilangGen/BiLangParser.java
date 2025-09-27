// Generated from D:/workspace/bilang/BiLang.g4 by ANTLR 4.13.2
package bilangGen;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class BiLangParser extends Parser {
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
		T__38=39, T__39=40, T__40=41, T__41=42, T__42=43, T__43=44, ID=45, INT=46, 
		ADDRESS=47, STRING=48, BlockComment=49, LineComment=50, WS=51;
	public static final int
		RULE_program = 0, RULE_typeDec = 1, RULE_typeExp = 2, RULE_ext = 3, RULE_query = 4, 
		RULE_outcome = 5, RULE_item = 6, RULE_exp = 7, RULE_varDec = 8;
	private static String[] makeRuleNames() {
		return new String[] {
			"program", "typeDec", "typeExp", "ext", "query", "outcome", "item", "exp", 
			"varDec"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'type'", "'='", "'{'", "','", "'}'", "'..'", "'join'", "'yield'", 
			"'reveal'", "'many'", "'random'", "';'", "'let'", "'fold'", "'->'", "'withdraw'", 
			"'('", "')'", "'$'", "'where'", "'?'", "':'", "'in'", "'.'", "'-'", "'!'", 
			"'*'", "'/'", "'+'", "'!='", "'=='", "'null'", "'<'", "'<='", "'>='", 
			"'>'", "'<->'", "'<-!->'", "'&&'", "'||'", "'true'", "'false'", "'let!'", 
			"'hidden'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, "ID", "INT", "ADDRESS", 
			"STRING", "BlockComment", "LineComment", "WS"
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
	public String getGrammarFileName() { return "BiLang.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public BiLangParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ProgramContext extends ParserRuleContext {
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public TerminalNode EOF() { return getToken(BiLangParser.EOF, 0); }
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterProgram(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitProgram(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitProgram(this);
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
			setState(21);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(18);
				typeDec();
				}
				}
				setState(23);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(24);
			ext();
			setState(25);
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
		public Token name;
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public TypeDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeDec; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterTypeDec(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitTypeDec(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitTypeDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeDecContext typeDec() throws RecognitionException {
		TypeDecContext _localctx = new TypeDecContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_typeDec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(27);
			match(T__0);
			setState(28);
			((TypeDecContext)_localctx).name = match(ID);
			setState(29);
			match(T__1);
			setState(30);
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
	public static class TypeIdContext extends TypeExpContext {
		public Token name;
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public TypeIdContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterTypeId(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitTypeId(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitTypeId(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class SubsetTypeExpContext extends TypeExpContext {
		public Token INT;
		public List<Token> vals = new ArrayList<Token>();
		public List<TerminalNode> INT() { return getTokens(BiLangParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(BiLangParser.INT, i);
		}
		public SubsetTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterSubsetTypeExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitSubsetTypeExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitSubsetTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class RangeTypeExpContext extends TypeExpContext {
		public Token start;
		public Token end;
		public List<TerminalNode> INT() { return getTokens(BiLangParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(BiLangParser.INT, i);
		}
		public RangeTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterRangeTypeExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitRangeTypeExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitRangeTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeExpContext typeExp() throws RecognitionException {
		TypeExpContext _localctx = new TypeExpContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_typeExp);
		int _la;
		try {
			setState(48);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				_localctx = new SubsetTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(32);
				match(T__2);
				setState(33);
				((SubsetTypeExpContext)_localctx).INT = match(INT);
				((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
				setState(38);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(34);
					match(T__3);
					setState(35);
					((SubsetTypeExpContext)_localctx).INT = match(INT);
					((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
					}
					}
					setState(40);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(41);
				match(T__4);
				}
				break;
			case 2:
				_localctx = new RangeTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(42);
				match(T__2);
				setState(43);
				((RangeTypeExpContext)_localctx).start = match(INT);
				setState(44);
				match(T__5);
				setState(45);
				((RangeTypeExpContext)_localctx).end = match(INT);
				setState(46);
				match(T__4);
				}
				break;
			case 3:
				_localctx = new TypeIdContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(47);
				((TypeIdContext)_localctx).name = match(ID);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterReceiveExt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitReceiveExt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitReceiveExt(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterWithdrawExt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitWithdrawExt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitWithdrawExt(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class FoldExtContext extends ExtContext {
		public Token from;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public List<QueryContext> query() {
			return getRuleContexts(QueryContext.class);
		}
		public QueryContext query(int i) {
			return getRuleContext(QueryContext.class,i);
		}
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public FoldExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterFoldExt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitFoldExt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitFoldExt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExtContext ext() throws RecognitionException {
		ExtContext _localctx = new ExtContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_ext);
		int _la;
		try {
			setState(81);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__6:
			case T__7:
			case T__8:
			case T__9:
			case T__10:
				_localctx = new ReceiveExtContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(50);
				((ReceiveExtContext)_localctx).kind = _input.LT(1);
				_la = _input.LA(1);
				if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 3968L) != 0)) ) {
					((ReceiveExtContext)_localctx).kind = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(52); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(51);
					query();
					}
					}
					setState(54); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID );
				setState(56);
				match(T__11);
				setState(57);
				ext();
				}
				break;
			case T__12:
				_localctx = new FoldExtContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(59);
				match(T__12);
				setState(60);
				varDec();
				setState(61);
				match(T__1);
				setState(62);
				match(T__13);
				setState(63);
				((FoldExtContext)_localctx).from = match(ID);
				setState(64);
				match(T__2);
				setState(71); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(65);
					query();
					setState(66);
					match(T__14);
					setState(67);
					exp(0);
					setState(69);
					_errHandler.sync(this);
					_la = _input.LA(1);
					if (_la==T__11) {
						{
						setState(68);
						match(T__11);
						}
					}

					}
					}
					setState(73); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID );
				setState(75);
				match(T__4);
				setState(76);
				match(T__11);
				setState(77);
				ext();
				}
				break;
			case T__15:
				_localctx = new WithdrawExtContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(79);
				match(T__15);
				setState(80);
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
		public Token role;
		public VarDecContext varDec;
		public List<VarDecContext> decls = new ArrayList<VarDecContext>();
		public Token deposit;
		public ExpContext cond;
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public TerminalNode INT() { return getToken(BiLangParser.INT, 0); }
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterQuery(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitQuery(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitQuery(this);
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
			setState(83);
			((QueryContext)_localctx).role = match(ID);
			setState(96);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__16) {
				{
				setState(84);
				match(T__16);
				setState(93);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==ID) {
					{
					setState(85);
					((QueryContext)_localctx).varDec = varDec();
					((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
					setState(90);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__3) {
						{
						{
						setState(86);
						match(T__3);
						setState(87);
						((QueryContext)_localctx).varDec = varDec();
						((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
						}
						}
						setState(92);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(95);
				match(T__17);
				}
			}

			setState(100);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__18) {
				{
				setState(98);
				match(T__18);
				setState(99);
				((QueryContext)_localctx).deposit = match(INT);
				}
			}

			setState(104);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__19) {
				{
				setState(102);
				match(T__19);
				setState(103);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterOutcomeExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitOutcomeExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitOutcomeExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterIfOutcome(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitIfOutcome(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitIfOutcome(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterLetOutcome(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitLetOutcome(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitLetOutcome(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterParenOutcome(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitParenOutcome(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitParenOutcome(this);
			else return visitor.visitChildren(this);
		}
	}

	public final OutcomeContext outcome() throws RecognitionException {
		OutcomeContext _localctx = new OutcomeContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_outcome);
		int _la;
		try {
			setState(131);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,13,_ctx) ) {
			case 1:
				_localctx = new IfOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(106);
				((IfOutcomeContext)_localctx).cond = exp(0);
				setState(107);
				match(T__20);
				setState(108);
				((IfOutcomeContext)_localctx).ifTrue = outcome();
				setState(109);
				match(T__21);
				setState(110);
				((IfOutcomeContext)_localctx).ifFalse = outcome();
				}
				break;
			case 2:
				_localctx = new LetOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(112);
				match(T__12);
				setState(113);
				((LetOutcomeContext)_localctx).dec = varDec();
				setState(114);
				match(T__1);
				setState(115);
				((LetOutcomeContext)_localctx).init = exp(0);
				setState(116);
				match(T__22);
				setState(117);
				((LetOutcomeContext)_localctx).body = outcome();
				}
				break;
			case 3:
				_localctx = new ParenOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(119);
				match(T__16);
				setState(120);
				outcome();
				setState(121);
				match(T__17);
				}
				break;
			case 4:
				_localctx = new OutcomeExpContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(123);
				match(T__2);
				setState(125); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(124);
					((OutcomeExpContext)_localctx).item = item();
					((OutcomeExpContext)_localctx).items.add(((OutcomeExpContext)_localctx).item);
					}
					}
					setState(127); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID );
				setState(129);
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
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public ItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_item; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterItem(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitItem(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitItem(this);
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
			setState(133);
			match(ID);
			setState(134);
			match(T__14);
			setState(135);
			exp(0);
			setState(137);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11) {
				{
				setState(136);
				match(T__11);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBinOpEqExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBinOpEqExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBinOpEqExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterUndefExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitUndefExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitUndefExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBinOpAddExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBinOpAddExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBinOpAddExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBinOpCompExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBinOpCompExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBinOpCompExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterUnOpExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitUnOpExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitUnOpExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class MemberExpContext extends ExpContext {
		public Token role;
		public Token field;
		public List<TerminalNode> ID() { return getTokens(BiLangParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(BiLangParser.ID, i);
		}
		public MemberExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterMemberExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitMemberExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitMemberExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IdExpContext extends ExpContext {
		public Token name;
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public IdExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterIdExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitIdExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitIdExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class CallExpContext extends ExpContext {
		public Token callee;
		public ExpContext exp;
		public List<ExpContext> args = new ArrayList<ExpContext>();
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public CallExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterCallExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitCallExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitCallExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterIfExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitIfExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitIfExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBinOpBoolExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBinOpBoolExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBinOpBoolExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterParenExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitParenExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitParenExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BoolLiteralExpContext extends ExpContext {
		public BoolLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBoolLiteralExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBoolLiteralExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBoolLiteralExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterLetExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitLetExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitLetExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class AddressLiteralExpContext extends ExpContext {
		public TerminalNode ADDRESS() { return getToken(BiLangParser.ADDRESS, 0); }
		public AddressLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterAddressLiteralExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitAddressLiteralExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitAddressLiteralExp(this);
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
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBinOpMultExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBinOpMultExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBinOpMultExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NumLiteralExpContext extends ExpContext {
		public TerminalNode INT() { return getToken(BiLangParser.INT, 0); }
		public NumLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterNumLiteralExp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitNumLiteralExp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitNumLiteralExp(this);
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
			setState(173);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,17,_ctx) ) {
			case 1:
				{
				_localctx = new ParenExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(140);
				match(T__16);
				setState(141);
				exp(0);
				setState(142);
				match(T__17);
				}
				break;
			case 2:
				{
				_localctx = new MemberExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(144);
				((MemberExpContext)_localctx).role = match(ID);
				setState(145);
				match(T__23);
				setState(146);
				((MemberExpContext)_localctx).field = match(ID);
				}
				break;
			case 3:
				{
				_localctx = new CallExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(147);
				((CallExpContext)_localctx).callee = match(ID);
				setState(148);
				match(T__16);
				setState(157);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 261683868205056L) != 0)) {
					{
					setState(149);
					((CallExpContext)_localctx).exp = exp(0);
					((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
					setState(154);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__3) {
						{
						{
						setState(150);
						match(T__3);
						setState(151);
						((CallExpContext)_localctx).exp = exp(0);
						((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
						}
						}
						setState(156);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(159);
				match(T__17);
				}
				break;
			case 4:
				{
				_localctx = new UnOpExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(160);
				((UnOpExpContext)_localctx).op = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__24 || _la==T__25) ) {
					((UnOpExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(161);
				exp(13);
				}
				break;
			case 5:
				{
				_localctx = new BoolLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(162);
				_la = _input.LA(1);
				if ( !(_la==T__40 || _la==T__41) ) {
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
				setState(163);
				((IdExpContext)_localctx).name = match(ID);
				}
				break;
			case 7:
				{
				_localctx = new NumLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(164);
				match(INT);
				}
				break;
			case 8:
				{
				_localctx = new AddressLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(165);
				match(ADDRESS);
				}
				break;
			case 9:
				{
				_localctx = new LetExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(166);
				match(T__42);
				setState(167);
				((LetExpContext)_localctx).dec = varDec();
				setState(168);
				match(T__1);
				setState(169);
				((LetExpContext)_localctx).init = exp(0);
				setState(170);
				match(T__22);
				setState(171);
				((LetExpContext)_localctx).body = exp(1);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(201);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,19,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(199);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,18,_ctx) ) {
					case 1:
						{
						_localctx = new BinOpMultExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpMultExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(175);
						if (!(precpred(_ctx, 12))) throw new FailedPredicateException(this, "precpred(_ctx, 12)");
						setState(176);
						((BinOpMultExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__26 || _la==T__27) ) {
							((BinOpMultExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(177);
						((BinOpMultExpContext)_localctx).right = exp(13);
						}
						break;
					case 2:
						{
						_localctx = new BinOpAddExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpAddExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(178);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(179);
						((BinOpAddExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__24 || _la==T__28) ) {
							((BinOpAddExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(180);
						((BinOpAddExpContext)_localctx).right = exp(12);
						}
						break;
					case 3:
						{
						_localctx = new BinOpCompExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpCompExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(181);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(182);
						((BinOpCompExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 128849018880L) != 0)) ) {
							((BinOpCompExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(183);
						((BinOpCompExpContext)_localctx).right = exp(10);
						}
						break;
					case 4:
						{
						_localctx = new BinOpEqExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpEqExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(184);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(185);
						((BinOpEqExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 415538085888L) != 0)) ) {
							((BinOpEqExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(186);
						((BinOpEqExpContext)_localctx).right = exp(9);
						}
						break;
					case 5:
						{
						_localctx = new BinOpBoolExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpBoolExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(187);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(188);
						((BinOpBoolExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__38 || _la==T__39) ) {
							((BinOpBoolExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(189);
						((BinOpBoolExpContext)_localctx).right = exp(8);
						}
						break;
					case 6:
						{
						_localctx = new IfExpContext(new ExpContext(_parentctx, _parentState));
						((IfExpContext)_localctx).cond = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(190);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(191);
						match(T__20);
						setState(192);
						((IfExpContext)_localctx).ifTrue = exp(0);
						setState(193);
						match(T__21);
						setState(194);
						((IfExpContext)_localctx).ifFalse = exp(6);
						}
						break;
					case 7:
						{
						_localctx = new UndefExpContext(new ExpContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(196);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(197);
						((UndefExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__29 || _la==T__30) ) {
							((UndefExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(198);
						match(T__31);
						}
						break;
					}
					} 
				}
				setState(203);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,19,_ctx);
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
		public Token name;
		public Token hidden;
		public Token type;
		public List<TerminalNode> ID() { return getTokens(BiLangParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(BiLangParser.ID, i);
		}
		public VarDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varDec; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterVarDec(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitVarDec(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitVarDec(this);
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
			setState(204);
			((VarDecContext)_localctx).name = match(ID);
			setState(205);
			match(T__21);
			setState(207);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__43) {
				{
				setState(206);
				((VarDecContext)_localctx).hidden = match(T__43);
				}
			}

			setState(209);
			((VarDecContext)_localctx).type = match(ID);
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
		"\u0004\u00013\u00d4\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0001\u0000\u0005\u0000\u0014\b\u0000\n\u0000\f\u0000\u0017"+
		"\t\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0005\u0002%\b\u0002\n\u0002\f\u0002(\t\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003"+
		"\u00021\b\u0002\u0001\u0003\u0001\u0003\u0004\u00035\b\u0003\u000b\u0003"+
		"\f\u00036\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0003\u0003F\b\u0003\u0004\u0003H\b\u0003\u000b"+
		"\u0003\f\u0003I\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0003\u0003R\b\u0003\u0001\u0004\u0001\u0004\u0001"+
		"\u0004\u0001\u0004\u0001\u0004\u0005\u0004Y\b\u0004\n\u0004\f\u0004\\"+
		"\t\u0004\u0003\u0004^\b\u0004\u0001\u0004\u0003\u0004a\b\u0004\u0001\u0004"+
		"\u0001\u0004\u0003\u0004e\b\u0004\u0001\u0004\u0001\u0004\u0003\u0004"+
		"i\b\u0004\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0004\u0005~\b\u0005\u000b\u0005\f\u0005\u007f"+
		"\u0001\u0005\u0001\u0005\u0003\u0005\u0084\b\u0005\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0003\u0006\u008a\b\u0006\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0005\u0007"+
		"\u0099\b\u0007\n\u0007\f\u0007\u009c\t\u0007\u0003\u0007\u009e\b\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0003\u0007\u00ae\b\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0005\u0007\u00c8\b\u0007"+
		"\n\u0007\f\u0007\u00cb\t\u0007\u0001\b\u0001\b\u0001\b\u0003\b\u00d0\b"+
		"\b\u0001\b\u0001\b\u0001\b\u0000\u0001\u000e\t\u0000\u0002\u0004\u0006"+
		"\b\n\f\u000e\u0010\u0000\t\u0001\u0000\u0007\u000b\u0001\u0000\u0019\u001a"+
		"\u0001\u0000)*\u0001\u0000\u001b\u001c\u0002\u0000\u0019\u0019\u001d\u001d"+
		"\u0001\u0000!$\u0002\u0000\u001e\u001f%&\u0001\u0000\'(\u0001\u0000\u001e"+
		"\u001f\u00ef\u0000\u0015\u0001\u0000\u0000\u0000\u0002\u001b\u0001\u0000"+
		"\u0000\u0000\u00040\u0001\u0000\u0000\u0000\u0006Q\u0001\u0000\u0000\u0000"+
		"\bS\u0001\u0000\u0000\u0000\n\u0083\u0001\u0000\u0000\u0000\f\u0085\u0001"+
		"\u0000\u0000\u0000\u000e\u00ad\u0001\u0000\u0000\u0000\u0010\u00cc\u0001"+
		"\u0000\u0000\u0000\u0012\u0014\u0003\u0002\u0001\u0000\u0013\u0012\u0001"+
		"\u0000\u0000\u0000\u0014\u0017\u0001\u0000\u0000\u0000\u0015\u0013\u0001"+
		"\u0000\u0000\u0000\u0015\u0016\u0001\u0000\u0000\u0000\u0016\u0018\u0001"+
		"\u0000\u0000\u0000\u0017\u0015\u0001\u0000\u0000\u0000\u0018\u0019\u0003"+
		"\u0006\u0003\u0000\u0019\u001a\u0005\u0000\u0000\u0001\u001a\u0001\u0001"+
		"\u0000\u0000\u0000\u001b\u001c\u0005\u0001\u0000\u0000\u001c\u001d\u0005"+
		"-\u0000\u0000\u001d\u001e\u0005\u0002\u0000\u0000\u001e\u001f\u0003\u0004"+
		"\u0002\u0000\u001f\u0003\u0001\u0000\u0000\u0000 !\u0005\u0003\u0000\u0000"+
		"!&\u0005.\u0000\u0000\"#\u0005\u0004\u0000\u0000#%\u0005.\u0000\u0000"+
		"$\"\u0001\u0000\u0000\u0000%(\u0001\u0000\u0000\u0000&$\u0001\u0000\u0000"+
		"\u0000&\'\u0001\u0000\u0000\u0000\')\u0001\u0000\u0000\u0000(&\u0001\u0000"+
		"\u0000\u0000)1\u0005\u0005\u0000\u0000*+\u0005\u0003\u0000\u0000+,\u0005"+
		".\u0000\u0000,-\u0005\u0006\u0000\u0000-.\u0005.\u0000\u0000.1\u0005\u0005"+
		"\u0000\u0000/1\u0005-\u0000\u00000 \u0001\u0000\u0000\u00000*\u0001\u0000"+
		"\u0000\u00000/\u0001\u0000\u0000\u00001\u0005\u0001\u0000\u0000\u0000"+
		"24\u0007\u0000\u0000\u000035\u0003\b\u0004\u000043\u0001\u0000\u0000\u0000"+
		"56\u0001\u0000\u0000\u000064\u0001\u0000\u0000\u000067\u0001\u0000\u0000"+
		"\u000078\u0001\u0000\u0000\u000089\u0005\f\u0000\u00009:\u0003\u0006\u0003"+
		"\u0000:R\u0001\u0000\u0000\u0000;<\u0005\r\u0000\u0000<=\u0003\u0010\b"+
		"\u0000=>\u0005\u0002\u0000\u0000>?\u0005\u000e\u0000\u0000?@\u0005-\u0000"+
		"\u0000@G\u0005\u0003\u0000\u0000AB\u0003\b\u0004\u0000BC\u0005\u000f\u0000"+
		"\u0000CE\u0003\u000e\u0007\u0000DF\u0005\f\u0000\u0000ED\u0001\u0000\u0000"+
		"\u0000EF\u0001\u0000\u0000\u0000FH\u0001\u0000\u0000\u0000GA\u0001\u0000"+
		"\u0000\u0000HI\u0001\u0000\u0000\u0000IG\u0001\u0000\u0000\u0000IJ\u0001"+
		"\u0000\u0000\u0000JK\u0001\u0000\u0000\u0000KL\u0005\u0005\u0000\u0000"+
		"LM\u0005\f\u0000\u0000MN\u0003\u0006\u0003\u0000NR\u0001\u0000\u0000\u0000"+
		"OP\u0005\u0010\u0000\u0000PR\u0003\n\u0005\u0000Q2\u0001\u0000\u0000\u0000"+
		"Q;\u0001\u0000\u0000\u0000QO\u0001\u0000\u0000\u0000R\u0007\u0001\u0000"+
		"\u0000\u0000S`\u0005-\u0000\u0000T]\u0005\u0011\u0000\u0000UZ\u0003\u0010"+
		"\b\u0000VW\u0005\u0004\u0000\u0000WY\u0003\u0010\b\u0000XV\u0001\u0000"+
		"\u0000\u0000Y\\\u0001\u0000\u0000\u0000ZX\u0001\u0000\u0000\u0000Z[\u0001"+
		"\u0000\u0000\u0000[^\u0001\u0000\u0000\u0000\\Z\u0001\u0000\u0000\u0000"+
		"]U\u0001\u0000\u0000\u0000]^\u0001\u0000\u0000\u0000^_\u0001\u0000\u0000"+
		"\u0000_a\u0005\u0012\u0000\u0000`T\u0001\u0000\u0000\u0000`a\u0001\u0000"+
		"\u0000\u0000ad\u0001\u0000\u0000\u0000bc\u0005\u0013\u0000\u0000ce\u0005"+
		".\u0000\u0000db\u0001\u0000\u0000\u0000de\u0001\u0000\u0000\u0000eh\u0001"+
		"\u0000\u0000\u0000fg\u0005\u0014\u0000\u0000gi\u0003\u000e\u0007\u0000"+
		"hf\u0001\u0000\u0000\u0000hi\u0001\u0000\u0000\u0000i\t\u0001\u0000\u0000"+
		"\u0000jk\u0003\u000e\u0007\u0000kl\u0005\u0015\u0000\u0000lm\u0003\n\u0005"+
		"\u0000mn\u0005\u0016\u0000\u0000no\u0003\n\u0005\u0000o\u0084\u0001\u0000"+
		"\u0000\u0000pq\u0005\r\u0000\u0000qr\u0003\u0010\b\u0000rs\u0005\u0002"+
		"\u0000\u0000st\u0003\u000e\u0007\u0000tu\u0005\u0017\u0000\u0000uv\u0003"+
		"\n\u0005\u0000v\u0084\u0001\u0000\u0000\u0000wx\u0005\u0011\u0000\u0000"+
		"xy\u0003\n\u0005\u0000yz\u0005\u0012\u0000\u0000z\u0084\u0001\u0000\u0000"+
		"\u0000{}\u0005\u0003\u0000\u0000|~\u0003\f\u0006\u0000}|\u0001\u0000\u0000"+
		"\u0000~\u007f\u0001\u0000\u0000\u0000\u007f}\u0001\u0000\u0000\u0000\u007f"+
		"\u0080\u0001\u0000\u0000\u0000\u0080\u0081\u0001\u0000\u0000\u0000\u0081"+
		"\u0082\u0005\u0005\u0000\u0000\u0082\u0084\u0001\u0000\u0000\u0000\u0083"+
		"j\u0001\u0000\u0000\u0000\u0083p\u0001\u0000\u0000\u0000\u0083w\u0001"+
		"\u0000\u0000\u0000\u0083{\u0001\u0000\u0000\u0000\u0084\u000b\u0001\u0000"+
		"\u0000\u0000\u0085\u0086\u0005-\u0000\u0000\u0086\u0087\u0005\u000f\u0000"+
		"\u0000\u0087\u0089\u0003\u000e\u0007\u0000\u0088\u008a\u0005\f\u0000\u0000"+
		"\u0089\u0088\u0001\u0000\u0000\u0000\u0089\u008a\u0001\u0000\u0000\u0000"+
		"\u008a\r\u0001\u0000\u0000\u0000\u008b\u008c\u0006\u0007\uffff\uffff\u0000"+
		"\u008c\u008d\u0005\u0011\u0000\u0000\u008d\u008e\u0003\u000e\u0007\u0000"+
		"\u008e\u008f\u0005\u0012\u0000\u0000\u008f\u00ae\u0001\u0000\u0000\u0000"+
		"\u0090\u0091\u0005-\u0000\u0000\u0091\u0092\u0005\u0018\u0000\u0000\u0092"+
		"\u00ae\u0005-\u0000\u0000\u0093\u0094\u0005-\u0000\u0000\u0094\u009d\u0005"+
		"\u0011\u0000\u0000\u0095\u009a\u0003\u000e\u0007\u0000\u0096\u0097\u0005"+
		"\u0004\u0000\u0000\u0097\u0099\u0003\u000e\u0007\u0000\u0098\u0096\u0001"+
		"\u0000\u0000\u0000\u0099\u009c\u0001\u0000\u0000\u0000\u009a\u0098\u0001"+
		"\u0000\u0000\u0000\u009a\u009b\u0001\u0000\u0000\u0000\u009b\u009e\u0001"+
		"\u0000\u0000\u0000\u009c\u009a\u0001\u0000\u0000\u0000\u009d\u0095\u0001"+
		"\u0000\u0000\u0000\u009d\u009e\u0001\u0000\u0000\u0000\u009e\u009f\u0001"+
		"\u0000\u0000\u0000\u009f\u00ae\u0005\u0012\u0000\u0000\u00a0\u00a1\u0007"+
		"\u0001\u0000\u0000\u00a1\u00ae\u0003\u000e\u0007\r\u00a2\u00ae\u0007\u0002"+
		"\u0000\u0000\u00a3\u00ae\u0005-\u0000\u0000\u00a4\u00ae\u0005.\u0000\u0000"+
		"\u00a5\u00ae\u0005/\u0000\u0000\u00a6\u00a7\u0005+\u0000\u0000\u00a7\u00a8"+
		"\u0003\u0010\b\u0000\u00a8\u00a9\u0005\u0002\u0000\u0000\u00a9\u00aa\u0003"+
		"\u000e\u0007\u0000\u00aa\u00ab\u0005\u0017\u0000\u0000\u00ab\u00ac\u0003"+
		"\u000e\u0007\u0001\u00ac\u00ae\u0001\u0000\u0000\u0000\u00ad\u008b\u0001"+
		"\u0000\u0000\u0000\u00ad\u0090\u0001\u0000\u0000\u0000\u00ad\u0093\u0001"+
		"\u0000\u0000\u0000\u00ad\u00a0\u0001\u0000\u0000\u0000\u00ad\u00a2\u0001"+
		"\u0000\u0000\u0000\u00ad\u00a3\u0001\u0000\u0000\u0000\u00ad\u00a4\u0001"+
		"\u0000\u0000\u0000\u00ad\u00a5\u0001\u0000\u0000\u0000\u00ad\u00a6\u0001"+
		"\u0000\u0000\u0000\u00ae\u00c9\u0001\u0000\u0000\u0000\u00af\u00b0\n\f"+
		"\u0000\u0000\u00b0\u00b1\u0007\u0003\u0000\u0000\u00b1\u00c8\u0003\u000e"+
		"\u0007\r\u00b2\u00b3\n\u000b\u0000\u0000\u00b3\u00b4\u0007\u0004\u0000"+
		"\u0000\u00b4\u00c8\u0003\u000e\u0007\f\u00b5\u00b6\n\t\u0000\u0000\u00b6"+
		"\u00b7\u0007\u0005\u0000\u0000\u00b7\u00c8\u0003\u000e\u0007\n\u00b8\u00b9"+
		"\n\b\u0000\u0000\u00b9\u00ba\u0007\u0006\u0000\u0000\u00ba\u00c8\u0003"+
		"\u000e\u0007\t\u00bb\u00bc\n\u0007\u0000\u0000\u00bc\u00bd\u0007\u0007"+
		"\u0000\u0000\u00bd\u00c8\u0003\u000e\u0007\b\u00be\u00bf\n\u0006\u0000"+
		"\u0000\u00bf\u00c0\u0005\u0015\u0000\u0000\u00c0\u00c1\u0003\u000e\u0007"+
		"\u0000\u00c1\u00c2\u0005\u0016\u0000\u0000\u00c2\u00c3\u0003\u000e\u0007"+
		"\u0006\u00c3\u00c8\u0001\u0000\u0000\u0000\u00c4\u00c5\n\n\u0000\u0000"+
		"\u00c5\u00c6\u0007\b\u0000\u0000\u00c6\u00c8\u0005 \u0000\u0000\u00c7"+
		"\u00af\u0001\u0000\u0000\u0000\u00c7\u00b2\u0001\u0000\u0000\u0000\u00c7"+
		"\u00b5\u0001\u0000\u0000\u0000\u00c7\u00b8\u0001\u0000\u0000\u0000\u00c7"+
		"\u00bb\u0001\u0000\u0000\u0000\u00c7\u00be\u0001\u0000\u0000\u0000\u00c7"+
		"\u00c4\u0001\u0000\u0000\u0000\u00c8\u00cb\u0001\u0000\u0000\u0000\u00c9"+
		"\u00c7\u0001\u0000\u0000\u0000\u00c9\u00ca\u0001\u0000\u0000\u0000\u00ca"+
		"\u000f\u0001\u0000\u0000\u0000\u00cb\u00c9\u0001\u0000\u0000\u0000\u00cc"+
		"\u00cd\u0005-\u0000\u0000\u00cd\u00cf\u0005\u0016\u0000\u0000\u00ce\u00d0"+
		"\u0005,\u0000\u0000\u00cf\u00ce\u0001\u0000\u0000\u0000\u00cf\u00d0\u0001"+
		"\u0000\u0000\u0000\u00d0\u00d1\u0001\u0000\u0000\u0000\u00d1\u00d2\u0005"+
		"-\u0000\u0000\u00d2\u0011\u0001\u0000\u0000\u0000\u0015\u0015&06EIQZ]"+
		"`dh\u007f\u0083\u0089\u009a\u009d\u00ad\u00c7\u00c9\u00cf";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}