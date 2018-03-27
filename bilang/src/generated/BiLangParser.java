// Generated from /Users/elazarg/workspace/research/bilang/BiLang.g4 by ANTLR 4.7
package generated;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class BiLangParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.7", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		T__31=32, T__32=33, T__33=34, T__34=35, T__35=36, T__36=37, T__37=38, 
		T__38=39, T__39=40, ID=41, INT=42, ADDRESS=43, STRING=44, BlockComment=45, 
		LineComment=46, WS=47;
	public static final int
		RULE_program = 0, RULE_typeDec = 1, RULE_typeExp = 2, RULE_exp = 3, RULE_stmt = 4, 
		RULE_packet = 5, RULE_whereClause = 6, RULE_varDec = 7;
	public static final String[] ruleNames = {
		"program", "typeDec", "typeExp", "exp", "stmt", "packet", "whereClause", 
		"varDec"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'type'", "'='", "'{'", "','", "'}'", "'..'", "'('", "')'", "'-'", 
		"'!'", "'*'", "'/'", "'+'", "'<'", "'<='", "'>='", "'>'", "'=='", "'!='", 
		"'&&'", "'||'", "'.'", "'?'", "':'", "'undefined'", "'var'", "';'", "'yield'", 
		"'hidden'", "'join'", "'many'", "':='", "'reveal'", "'if'", "'else'", 
		"'for'", "'from'", "'transfer'", "'to'", "'where'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, "ID", "INT", "ADDRESS", "STRING", "BlockComment", 
		"LineComment", "WS"
	};
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
	public static class ProgramContext extends ParserRuleContext {
		public TerminalNode EOF() { return getToken(BiLangParser.EOF, 0); }
		public List<TypeDecContext> typeDec() {
			return getRuleContexts(TypeDecContext.class);
		}
		public TypeDecContext typeDec(int i) {
			return getRuleContext(TypeDecContext.class,i);
		}
		public List<StmtContext> stmt() {
			return getRuleContexts(StmtContext.class);
		}
		public StmtContext stmt(int i) {
			return getRuleContext(StmtContext.class,i);
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
			setState(19);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__0) {
				{
				{
				setState(16);
				typeDec();
				}
				}
				setState(21);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(23); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(22);
				stmt();
				}
				}
				setState(25); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__2) | (1L << T__25) | (1L << T__27) | (1L << T__29) | (1L << T__32) | (1L << T__33) | (1L << T__35) | (1L << T__37) | (1L << ID))) != 0) );
			setState(27);
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
			setState(29);
			match(T__0);
			setState(30);
			((TypeDecContext)_localctx).name = match(ID);
			setState(31);
			match(T__1);
			setState(32);
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
			setState(50);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				_localctx = new SubsetTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(34);
				match(T__2);
				setState(35);
				((SubsetTypeExpContext)_localctx).INT = match(INT);
				((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
				setState(40);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__3) {
					{
					{
					setState(36);
					match(T__3);
					setState(37);
					((SubsetTypeExpContext)_localctx).INT = match(INT);
					((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
					}
					}
					setState(42);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(43);
				match(T__4);
				}
				break;
			case 2:
				_localctx = new RangeTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(44);
				match(T__2);
				setState(45);
				((RangeTypeExpContext)_localctx).start = match(INT);
				setState(46);
				match(T__5);
				setState(47);
				((RangeTypeExpContext)_localctx).end = match(INT);
				setState(48);
				match(T__4);
				}
				break;
			case 3:
				_localctx = new TypeIdContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(49);
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
	public static class UndefExpContext extends ExpContext {
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
		int _startState = 6;
		enterRecursionRule(_localctx, 6, RULE_exp, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(79);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				{
				_localctx = new ParenExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(53);
				match(T__6);
				setState(54);
				exp(0);
				setState(55);
				match(T__7);
				}
				break;
			case 2:
				{
				_localctx = new CallExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(57);
				((CallExpContext)_localctx).callee = match(ID);
				setState(58);
				match(T__6);
				setState(67);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__6) | (1L << T__8) | (1L << T__9) | (1L << T__24) | (1L << ID) | (1L << INT) | (1L << ADDRESS))) != 0)) {
					{
					setState(59);
					((CallExpContext)_localctx).exp = exp(0);
					((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
					setState(64);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__3) {
						{
						{
						setState(60);
						match(T__3);
						setState(61);
						((CallExpContext)_localctx).exp = exp(0);
						((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
						}
						}
						setState(66);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(69);
				match(T__7);
				}
				break;
			case 3:
				{
				_localctx = new UnOpExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(70);
				((UnOpExpContext)_localctx).op = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__8 || _la==T__9) ) {
					((UnOpExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(71);
				exp(12);
				}
				break;
			case 4:
				{
				_localctx = new MemberExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(72);
				((MemberExpContext)_localctx).role = match(ID);
				setState(73);
				match(T__21);
				setState(74);
				((MemberExpContext)_localctx).field = match(ID);
				}
				break;
			case 5:
				{
				_localctx = new IdExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(75);
				((IdExpContext)_localctx).name = match(ID);
				}
				break;
			case 6:
				{
				_localctx = new NumLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(76);
				match(INT);
				}
				break;
			case 7:
				{
				_localctx = new AddressLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(77);
				match(ADDRESS);
				}
				break;
			case 8:
				{
				_localctx = new UndefExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(78);
				match(T__24);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(104);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(102);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,7,_ctx) ) {
					case 1:
						{
						_localctx = new BinOpMultExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpMultExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(81);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(82);
						((BinOpMultExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__10 || _la==T__11) ) {
							((BinOpMultExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(83);
						((BinOpMultExpContext)_localctx).right = exp(12);
						}
						break;
					case 2:
						{
						_localctx = new BinOpAddExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpAddExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(84);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(85);
						((BinOpAddExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__8 || _la==T__12) ) {
							((BinOpAddExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(86);
						((BinOpAddExpContext)_localctx).right = exp(11);
						}
						break;
					case 3:
						{
						_localctx = new BinOpCompExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpCompExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(87);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(88);
						((BinOpCompExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__13) | (1L << T__14) | (1L << T__15) | (1L << T__16))) != 0)) ) {
							((BinOpCompExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(89);
						((BinOpCompExpContext)_localctx).right = exp(10);
						}
						break;
					case 4:
						{
						_localctx = new BinOpEqExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpEqExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(90);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(91);
						((BinOpEqExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__17 || _la==T__18) ) {
							((BinOpEqExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(92);
						((BinOpEqExpContext)_localctx).right = exp(9);
						}
						break;
					case 5:
						{
						_localctx = new BinOpBoolExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpBoolExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(93);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(94);
						((BinOpBoolExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__19 || _la==T__20) ) {
							((BinOpBoolExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(95);
						((BinOpBoolExpContext)_localctx).right = exp(8);
						}
						break;
					case 6:
						{
						_localctx = new IfExpContext(new ExpContext(_parentctx, _parentState));
						((IfExpContext)_localctx).cond = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(96);
						if (!(precpred(_ctx, 5))) throw new FailedPredicateException(this, "precpred(_ctx, 5)");
						setState(97);
						match(T__22);
						setState(98);
						((IfExpContext)_localctx).ifTrue = exp(0);
						setState(99);
						match(T__23);
						setState(100);
						((IfExpContext)_localctx).ifFalse = exp(6);
						}
						break;
					}
					} 
				}
				setState(106);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
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

	public static class StmtContext extends ParserRuleContext {
		public StmtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_stmt; }
	 
		public StmtContext() { }
		public void copyFrom(StmtContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class RevealStmtContext extends StmtContext {
		public Token target;
		public WhereClauseContext where;
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public WhereClauseContext whereClause() {
			return getRuleContext(WhereClauseContext.class,0);
		}
		public RevealStmtContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterRevealStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitRevealStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitRevealStmt(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class VarDefContext extends StmtContext {
		public VarDecContext dec;
		public ExpContext init;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public VarDefContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterVarDef(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitVarDef(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitVarDef(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class IfStmtContext extends StmtContext {
		public StmtContext ifTrue;
		public StmtContext ifFalse;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<StmtContext> stmt() {
			return getRuleContexts(StmtContext.class);
		}
		public StmtContext stmt(int i) {
			return getRuleContext(StmtContext.class,i);
		}
		public IfStmtContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterIfStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitIfStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitIfStmt(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class TransferStmtContext extends StmtContext {
		public ExpContext amount;
		public Token from;
		public Token to;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<TerminalNode> ID() { return getTokens(BiLangParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(BiLangParser.ID, i);
		}
		public TransferStmtContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterTransferStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitTransferStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitTransferStmt(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssignStmtContext extends StmtContext {
		public Token target;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public AssignStmtContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterAssignStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitAssignStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitAssignStmt(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class BlockStmtContext extends StmtContext {
		public List<StmtContext> stmt() {
			return getRuleContexts(StmtContext.class);
		}
		public StmtContext stmt(int i) {
			return getRuleContext(StmtContext.class,i);
		}
		public BlockStmtContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterBlockStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitBlockStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitBlockStmt(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class YieldDefContext extends StmtContext {
		public Token hidden;
		public List<PacketContext> packet() {
			return getRuleContexts(PacketContext.class);
		}
		public PacketContext packet(int i) {
			return getRuleContext(PacketContext.class,i);
		}
		public YieldDefContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterYieldDef(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitYieldDef(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitYieldDef(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class JoinDefContext extends StmtContext {
		public List<PacketContext> packet() {
			return getRuleContexts(PacketContext.class);
		}
		public PacketContext packet(int i) {
			return getRuleContext(PacketContext.class,i);
		}
		public JoinDefContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterJoinDef(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitJoinDef(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitJoinDef(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ForYieldStmtContext extends StmtContext {
		public Token from;
		public PacketContext packet() {
			return getRuleContext(PacketContext.class,0);
		}
		public StmtContext stmt() {
			return getRuleContext(StmtContext.class,0);
		}
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public ForYieldStmtContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterForYieldStmt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitForYieldStmt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitForYieldStmt(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class JoinManyDefContext extends StmtContext {
		public Token role;
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public JoinManyDefContext(StmtContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterJoinManyDef(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitJoinManyDef(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitJoinManyDef(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StmtContext stmt() throws RecognitionException {
		StmtContext _localctx = new StmtContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_stmt);
		int _la;
		try {
			setState(180);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				_localctx = new VarDefContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(107);
				match(T__25);
				setState(108);
				((VarDefContext)_localctx).dec = varDec();
				setState(111);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__1) {
					{
					setState(109);
					match(T__1);
					setState(110);
					((VarDefContext)_localctx).init = exp(0);
					}
				}

				setState(113);
				match(T__26);
				}
				break;
			case 2:
				_localctx = new YieldDefContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(115);
				match(T__27);
				setState(117);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__28) {
					{
					setState(116);
					((YieldDefContext)_localctx).hidden = match(T__28);
					}
				}

				setState(120); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(119);
					packet();
					}
					}
					setState(122); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID );
				setState(124);
				match(T__26);
				}
				break;
			case 3:
				_localctx = new JoinDefContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(126);
				match(T__29);
				setState(128); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(127);
					packet();
					}
					}
					setState(130); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID );
				setState(132);
				match(T__26);
				}
				break;
			case 4:
				_localctx = new JoinManyDefContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(134);
				match(T__29);
				setState(135);
				match(T__30);
				setState(136);
				((JoinManyDefContext)_localctx).role = match(ID);
				setState(137);
				match(T__26);
				}
				break;
			case 5:
				_localctx = new BlockStmtContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(138);
				match(T__2);
				setState(140); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(139);
					stmt();
					}
					}
					setState(142); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__2) | (1L << T__25) | (1L << T__27) | (1L << T__29) | (1L << T__32) | (1L << T__33) | (1L << T__35) | (1L << T__37) | (1L << ID))) != 0) );
				setState(144);
				match(T__4);
				}
				break;
			case 6:
				_localctx = new AssignStmtContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(146);
				((AssignStmtContext)_localctx).target = match(ID);
				setState(147);
				match(T__31);
				setState(148);
				exp(0);
				setState(149);
				match(T__26);
				}
				break;
			case 7:
				_localctx = new RevealStmtContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(151);
				match(T__32);
				setState(152);
				((RevealStmtContext)_localctx).target = match(ID);
				setState(153);
				((RevealStmtContext)_localctx).where = whereClause();
				setState(154);
				match(T__26);
				}
				break;
			case 8:
				_localctx = new IfStmtContext(_localctx);
				enterOuterAlt(_localctx, 8);
				{
				setState(156);
				match(T__33);
				setState(157);
				match(T__6);
				setState(158);
				exp(0);
				setState(159);
				match(T__7);
				setState(160);
				((IfStmtContext)_localctx).ifTrue = stmt();
				setState(163);
				_errHandler.sync(this);
				switch ( getInterpreter().adaptivePredict(_input,14,_ctx) ) {
				case 1:
					{
					setState(161);
					match(T__34);
					setState(162);
					((IfStmtContext)_localctx).ifFalse = stmt();
					}
					break;
				}
				}
				break;
			case 9:
				_localctx = new ForYieldStmtContext(_localctx);
				enterOuterAlt(_localctx, 9);
				{
				setState(165);
				match(T__35);
				setState(166);
				match(T__27);
				setState(167);
				packet();
				setState(168);
				match(T__36);
				setState(169);
				((ForYieldStmtContext)_localctx).from = match(ID);
				setState(170);
				stmt();
				}
				break;
			case 10:
				_localctx = new TransferStmtContext(_localctx);
				enterOuterAlt(_localctx, 10);
				{
				setState(172);
				match(T__37);
				setState(173);
				((TransferStmtContext)_localctx).amount = exp(0);
				setState(174);
				match(T__36);
				setState(175);
				((TransferStmtContext)_localctx).from = match(ID);
				setState(176);
				match(T__38);
				setState(177);
				((TransferStmtContext)_localctx).to = match(ID);
				setState(178);
				match(T__26);
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

	public static class PacketContext extends ParserRuleContext {
		public Token role;
		public VarDecContext varDec;
		public List<VarDecContext> decls = new ArrayList<VarDecContext>();
		public WhereClauseContext whereClause() {
			return getRuleContext(WhereClauseContext.class,0);
		}
		public TerminalNode ID() { return getToken(BiLangParser.ID, 0); }
		public List<VarDecContext> varDec() {
			return getRuleContexts(VarDecContext.class);
		}
		public VarDecContext varDec(int i) {
			return getRuleContext(VarDecContext.class,i);
		}
		public PacketContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_packet; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterPacket(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitPacket(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitPacket(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PacketContext packet() throws RecognitionException {
		PacketContext _localctx = new PacketContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_packet);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(182);
			((PacketContext)_localctx).role = match(ID);
			setState(195);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__6) {
				{
				setState(183);
				match(T__6);
				setState(192);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==ID) {
					{
					setState(184);
					((PacketContext)_localctx).varDec = varDec();
					((PacketContext)_localctx).decls.add(((PacketContext)_localctx).varDec);
					setState(189);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__3) {
						{
						{
						setState(185);
						match(T__3);
						setState(186);
						((PacketContext)_localctx).varDec = varDec();
						((PacketContext)_localctx).decls.add(((PacketContext)_localctx).varDec);
						}
						}
						setState(191);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(194);
				match(T__7);
				}
			}

			}
			setState(197);
			whereClause();
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

	public static class WhereClauseContext extends ParserRuleContext {
		public ExpContext cond;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public WhereClauseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_whereClause; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).enterWhereClause(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof BiLangListener ) ((BiLangListener)listener).exitWhereClause(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof BiLangVisitor ) return ((BiLangVisitor<? extends T>)visitor).visitWhereClause(this);
			else return visitor.visitChildren(this);
		}
	}

	public final WhereClauseContext whereClause() throws RecognitionException {
		WhereClauseContext _localctx = new WhereClauseContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_whereClause);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(201);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__39) {
				{
				setState(199);
				match(T__39);
				setState(200);
				((WhereClauseContext)_localctx).cond = exp(0);
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

	public static class VarDecContext extends ParserRuleContext {
		public Token name;
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
		enterRule(_localctx, 14, RULE_varDec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(203);
			((VarDecContext)_localctx).name = match(ID);
			setState(204);
			match(T__23);
			setState(205);
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
		case 3:
			return exp_sempred((ExpContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean exp_sempred(ExpContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 11);
		case 1:
			return precpred(_ctx, 10);
		case 2:
			return precpred(_ctx, 9);
		case 3:
			return precpred(_ctx, 8);
		case 4:
			return precpred(_ctx, 7);
		case 5:
			return precpred(_ctx, 5);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\61\u00d2\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\3\2\7\2\24\n"+
		"\2\f\2\16\2\27\13\2\3\2\6\2\32\n\2\r\2\16\2\33\3\2\3\2\3\3\3\3\3\3\3\3"+
		"\3\3\3\4\3\4\3\4\3\4\7\4)\n\4\f\4\16\4,\13\4\3\4\3\4\3\4\3\4\3\4\3\4\3"+
		"\4\5\4\65\n\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\7\5A\n\5\f\5\16"+
		"\5D\13\5\5\5F\n\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\5\5R\n\5\3\5"+
		"\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3"+
		"\5\3\5\3\5\7\5i\n\5\f\5\16\5l\13\5\3\6\3\6\3\6\3\6\5\6r\n\6\3\6\3\6\3"+
		"\6\3\6\5\6x\n\6\3\6\6\6{\n\6\r\6\16\6|\3\6\3\6\3\6\3\6\6\6\u0083\n\6\r"+
		"\6\16\6\u0084\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\6\6\u008f\n\6\r\6\16\6\u0090"+
		"\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3"+
		"\6\3\6\5\6\u00a6\n\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3"+
		"\6\3\6\3\6\5\6\u00b7\n\6\3\7\3\7\3\7\3\7\3\7\7\7\u00be\n\7\f\7\16\7\u00c1"+
		"\13\7\5\7\u00c3\n\7\3\7\5\7\u00c6\n\7\3\7\3\7\3\b\3\b\5\b\u00cc\n\b\3"+
		"\t\3\t\3\t\3\t\3\t\2\3\b\n\2\4\6\b\n\f\16\20\2\b\3\2\13\f\3\2\r\16\4\2"+
		"\13\13\17\17\3\2\20\23\3\2\24\25\3\2\26\27\2\u00f0\2\25\3\2\2\2\4\37\3"+
		"\2\2\2\6\64\3\2\2\2\bQ\3\2\2\2\n\u00b6\3\2\2\2\f\u00b8\3\2\2\2\16\u00cb"+
		"\3\2\2\2\20\u00cd\3\2\2\2\22\24\5\4\3\2\23\22\3\2\2\2\24\27\3\2\2\2\25"+
		"\23\3\2\2\2\25\26\3\2\2\2\26\31\3\2\2\2\27\25\3\2\2\2\30\32\5\n\6\2\31"+
		"\30\3\2\2\2\32\33\3\2\2\2\33\31\3\2\2\2\33\34\3\2\2\2\34\35\3\2\2\2\35"+
		"\36\7\2\2\3\36\3\3\2\2\2\37 \7\3\2\2 !\7+\2\2!\"\7\4\2\2\"#\5\6\4\2#\5"+
		"\3\2\2\2$%\7\5\2\2%*\7,\2\2&\'\7\6\2\2\')\7,\2\2(&\3\2\2\2),\3\2\2\2*"+
		"(\3\2\2\2*+\3\2\2\2+-\3\2\2\2,*\3\2\2\2-\65\7\7\2\2./\7\5\2\2/\60\7,\2"+
		"\2\60\61\7\b\2\2\61\62\7,\2\2\62\65\7\7\2\2\63\65\7+\2\2\64$\3\2\2\2\64"+
		".\3\2\2\2\64\63\3\2\2\2\65\7\3\2\2\2\66\67\b\5\1\2\678\7\t\2\289\5\b\5"+
		"\29:\7\n\2\2:R\3\2\2\2;<\7+\2\2<E\7\t\2\2=B\5\b\5\2>?\7\6\2\2?A\5\b\5"+
		"\2@>\3\2\2\2AD\3\2\2\2B@\3\2\2\2BC\3\2\2\2CF\3\2\2\2DB\3\2\2\2E=\3\2\2"+
		"\2EF\3\2\2\2FG\3\2\2\2GR\7\n\2\2HI\t\2\2\2IR\5\b\5\16JK\7+\2\2KL\7\30"+
		"\2\2LR\7+\2\2MR\7+\2\2NR\7,\2\2OR\7-\2\2PR\7\33\2\2Q\66\3\2\2\2Q;\3\2"+
		"\2\2QH\3\2\2\2QJ\3\2\2\2QM\3\2\2\2QN\3\2\2\2QO\3\2\2\2QP\3\2\2\2Rj\3\2"+
		"\2\2ST\f\r\2\2TU\t\3\2\2Ui\5\b\5\16VW\f\f\2\2WX\t\4\2\2Xi\5\b\5\rYZ\f"+
		"\13\2\2Z[\t\5\2\2[i\5\b\5\f\\]\f\n\2\2]^\t\6\2\2^i\5\b\5\13_`\f\t\2\2"+
		"`a\t\7\2\2ai\5\b\5\nbc\f\7\2\2cd\7\31\2\2de\5\b\5\2ef\7\32\2\2fg\5\b\5"+
		"\bgi\3\2\2\2hS\3\2\2\2hV\3\2\2\2hY\3\2\2\2h\\\3\2\2\2h_\3\2\2\2hb\3\2"+
		"\2\2il\3\2\2\2jh\3\2\2\2jk\3\2\2\2k\t\3\2\2\2lj\3\2\2\2mn\7\34\2\2nq\5"+
		"\20\t\2op\7\4\2\2pr\5\b\5\2qo\3\2\2\2qr\3\2\2\2rs\3\2\2\2st\7\35\2\2t"+
		"\u00b7\3\2\2\2uw\7\36\2\2vx\7\37\2\2wv\3\2\2\2wx\3\2\2\2xz\3\2\2\2y{\5"+
		"\f\7\2zy\3\2\2\2{|\3\2\2\2|z\3\2\2\2|}\3\2\2\2}~\3\2\2\2~\177\7\35\2\2"+
		"\177\u00b7\3\2\2\2\u0080\u0082\7 \2\2\u0081\u0083\5\f\7\2\u0082\u0081"+
		"\3\2\2\2\u0083\u0084\3\2\2\2\u0084\u0082\3\2\2\2\u0084\u0085\3\2\2\2\u0085"+
		"\u0086\3\2\2\2\u0086\u0087\7\35\2\2\u0087\u00b7\3\2\2\2\u0088\u0089\7"+
		" \2\2\u0089\u008a\7!\2\2\u008a\u008b\7+\2\2\u008b\u00b7\7\35\2\2\u008c"+
		"\u008e\7\5\2\2\u008d\u008f\5\n\6\2\u008e\u008d\3\2\2\2\u008f\u0090\3\2"+
		"\2\2\u0090\u008e\3\2\2\2\u0090\u0091\3\2\2\2\u0091\u0092\3\2\2\2\u0092"+
		"\u0093\7\7\2\2\u0093\u00b7\3\2\2\2\u0094\u0095\7+\2\2\u0095\u0096\7\""+
		"\2\2\u0096\u0097\5\b\5\2\u0097\u0098\7\35\2\2\u0098\u00b7\3\2\2\2\u0099"+
		"\u009a\7#\2\2\u009a\u009b\7+\2\2\u009b\u009c\5\16\b\2\u009c\u009d\7\35"+
		"\2\2\u009d\u00b7\3\2\2\2\u009e\u009f\7$\2\2\u009f\u00a0\7\t\2\2\u00a0"+
		"\u00a1\5\b\5\2\u00a1\u00a2\7\n\2\2\u00a2\u00a5\5\n\6\2\u00a3\u00a4\7%"+
		"\2\2\u00a4\u00a6\5\n\6\2\u00a5\u00a3\3\2\2\2\u00a5\u00a6\3\2\2\2\u00a6"+
		"\u00b7\3\2\2\2\u00a7\u00a8\7&\2\2\u00a8\u00a9\7\36\2\2\u00a9\u00aa\5\f"+
		"\7\2\u00aa\u00ab\7\'\2\2\u00ab\u00ac\7+\2\2\u00ac\u00ad\5\n\6\2\u00ad"+
		"\u00b7\3\2\2\2\u00ae\u00af\7(\2\2\u00af\u00b0\5\b\5\2\u00b0\u00b1\7\'"+
		"\2\2\u00b1\u00b2\7+\2\2\u00b2\u00b3\7)\2\2\u00b3\u00b4\7+\2\2\u00b4\u00b5"+
		"\7\35\2\2\u00b5\u00b7\3\2\2\2\u00b6m\3\2\2\2\u00b6u\3\2\2\2\u00b6\u0080"+
		"\3\2\2\2\u00b6\u0088\3\2\2\2\u00b6\u008c\3\2\2\2\u00b6\u0094\3\2\2\2\u00b6"+
		"\u0099\3\2\2\2\u00b6\u009e\3\2\2\2\u00b6\u00a7\3\2\2\2\u00b6\u00ae\3\2"+
		"\2\2\u00b7\13\3\2\2\2\u00b8\u00c5\7+\2\2\u00b9\u00c2\7\t\2\2\u00ba\u00bf"+
		"\5\20\t\2\u00bb\u00bc\7\6\2\2\u00bc\u00be\5\20\t\2\u00bd\u00bb\3\2\2\2"+
		"\u00be\u00c1\3\2\2\2\u00bf\u00bd\3\2\2\2\u00bf\u00c0\3\2\2\2\u00c0\u00c3"+
		"\3\2\2\2\u00c1\u00bf\3\2\2\2\u00c2\u00ba\3\2\2\2\u00c2\u00c3\3\2\2\2\u00c3"+
		"\u00c4\3\2\2\2\u00c4\u00c6\7\n\2\2\u00c5\u00b9\3\2\2\2\u00c5\u00c6\3\2"+
		"\2\2\u00c6\u00c7\3\2\2\2\u00c7\u00c8\5\16\b\2\u00c8\r\3\2\2\2\u00c9\u00ca"+
		"\7*\2\2\u00ca\u00cc\5\b\5\2\u00cb\u00c9\3\2\2\2\u00cb\u00cc\3\2\2\2\u00cc"+
		"\17\3\2\2\2\u00cd\u00ce\7+\2\2\u00ce\u00cf\7\32\2\2\u00cf\u00d0\7+\2\2"+
		"\u00d0\21\3\2\2\2\26\25\33*\64BEQhjqw|\u0084\u0090\u00a5\u00b6\u00bf\u00c2"+
		"\u00c5\u00cb";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}