package vegas.generated;// Generated from C:/Users/elazar/workspace/bilang/Vegas.g4 by ANTLR 4.13.2
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link VegasParser}.
 */
public interface VegasListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link VegasParser#program}.
	 * @param ctx the parse tree
	 */
	void enterProgram(VegasParser.ProgramContext ctx);
	/**
	 * Exit a parse tree produced by {@link VegasParser#program}.
	 * @param ctx the parse tree
	 */
	void exitProgram(VegasParser.ProgramContext ctx);
	/**
	 * Enter a parse tree produced by {@link VegasParser#typeDec}.
	 * @param ctx the parse tree
	 */
	void enterTypeDec(VegasParser.TypeDecContext ctx);
	/**
	 * Exit a parse tree produced by {@link VegasParser#typeDec}.
	 * @param ctx the parse tree
	 */
	void exitTypeDec(VegasParser.TypeDecContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SubsetTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void enterSubsetTypeExp(VegasParser.SubsetTypeExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SubsetTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void exitSubsetTypeExp(VegasParser.SubsetTypeExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code RangeTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void enterRangeTypeExp(VegasParser.RangeTypeExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code RangeTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void exitRangeTypeExp(VegasParser.RangeTypeExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code TypeId}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void enterTypeId(VegasParser.TypeIdContext ctx);
	/**
	 * Exit a parse tree produced by the {@code TypeId}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void exitTypeId(VegasParser.TypeIdContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ReceiveExt}
	 * labeled alternative in {@link VegasParser#ext}.
	 * @param ctx the parse tree
	 */
	void enterReceiveExt(VegasParser.ReceiveExtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ReceiveExt}
	 * labeled alternative in {@link VegasParser#ext}.
	 * @param ctx the parse tree
	 */
	void exitReceiveExt(VegasParser.ReceiveExtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code WithdrawExt}
	 * labeled alternative in {@link VegasParser#ext}.
	 * @param ctx the parse tree
	 */
	void enterWithdrawExt(VegasParser.WithdrawExtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code WithdrawExt}
	 * labeled alternative in {@link VegasParser#ext}.
	 * @param ctx the parse tree
	 */
	void exitWithdrawExt(VegasParser.WithdrawExtContext ctx);
	/**
	 * Enter a parse tree produced by {@link VegasParser#query}.
	 * @param ctx the parse tree
	 */
	void enterQuery(VegasParser.QueryContext ctx);
	/**
	 * Exit a parse tree produced by {@link VegasParser#query}.
	 * @param ctx the parse tree
	 */
	void exitQuery(VegasParser.QueryContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IfOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterIfOutcome(VegasParser.IfOutcomeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IfOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitIfOutcome(VegasParser.IfOutcomeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code LetOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterLetOutcome(VegasParser.LetOutcomeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code LetOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitLetOutcome(VegasParser.LetOutcomeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ParenOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterParenOutcome(VegasParser.ParenOutcomeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ParenOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitParenOutcome(VegasParser.ParenOutcomeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code OutcomeExp}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterOutcomeExp(VegasParser.OutcomeExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code OutcomeExp}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitOutcomeExp(VegasParser.OutcomeExpContext ctx);
	/**
	 * Enter a parse tree produced by {@link VegasParser#item}.
	 * @param ctx the parse tree
	 */
	void enterItem(VegasParser.ItemContext ctx);
	/**
	 * Exit a parse tree produced by {@link VegasParser#item}.
	 * @param ctx the parse tree
	 */
	void exitItem(VegasParser.ItemContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpEqExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpEqExp(VegasParser.BinOpEqExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpEqExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpEqExp(VegasParser.BinOpEqExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code UndefExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterUndefExp(VegasParser.UndefExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code UndefExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitUndefExp(VegasParser.UndefExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpAddExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpAddExp(VegasParser.BinOpAddExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpAddExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpAddExp(VegasParser.BinOpAddExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpCompExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpCompExp(VegasParser.BinOpCompExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpCompExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpCompExp(VegasParser.BinOpCompExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code UnOpExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterUnOpExp(VegasParser.UnOpExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code UnOpExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitUnOpExp(VegasParser.UnOpExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code MemberExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterMemberExp(VegasParser.MemberExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code MemberExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitMemberExp(VegasParser.MemberExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IdExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterIdExp(VegasParser.IdExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IdExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitIdExp(VegasParser.IdExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code CallExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterCallExp(VegasParser.CallExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code CallExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitCallExp(VegasParser.CallExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IfExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterIfExp(VegasParser.IfExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IfExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitIfExp(VegasParser.IfExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpBoolExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpBoolExp(VegasParser.BinOpBoolExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpBoolExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpBoolExp(VegasParser.BinOpBoolExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ParenExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterParenExp(VegasParser.ParenExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ParenExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitParenExp(VegasParser.ParenExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BoolLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBoolLiteralExp(VegasParser.BoolLiteralExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BoolLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBoolLiteralExp(VegasParser.BoolLiteralExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code LetExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterLetExp(VegasParser.LetExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code LetExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitLetExp(VegasParser.LetExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code AddressLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterAddressLiteralExp(VegasParser.AddressLiteralExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code AddressLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitAddressLiteralExp(VegasParser.AddressLiteralExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpMultExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpMultExp(VegasParser.BinOpMultExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpMultExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpMultExp(VegasParser.BinOpMultExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code NumLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterNumLiteralExp(VegasParser.NumLiteralExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code NumLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitNumLiteralExp(VegasParser.NumLiteralExpContext ctx);
	/**
	 * Enter a parse tree produced by {@link VegasParser#varDec}.
	 * @param ctx the parse tree
	 */
	void enterVarDec(VegasParser.VarDecContext ctx);
	/**
	 * Exit a parse tree produced by {@link VegasParser#varDec}.
	 * @param ctx the parse tree
	 */
	void exitVarDec(VegasParser.VarDecContext ctx);
}