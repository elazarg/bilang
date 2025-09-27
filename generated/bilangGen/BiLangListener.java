// Generated from D:/workspace/bilang/BiLang.g4 by ANTLR 4.13.2
package bilangGen;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link BiLangParser}.
 */
public interface BiLangListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link BiLangParser#program}.
	 * @param ctx the parse tree
	 */
	void enterProgram(BiLangParser.ProgramContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#program}.
	 * @param ctx the parse tree
	 */
	void exitProgram(BiLangParser.ProgramContext ctx);
	/**
	 * Enter a parse tree produced by {@link BiLangParser#typeDec}.
	 * @param ctx the parse tree
	 */
	void enterTypeDec(BiLangParser.TypeDecContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#typeDec}.
	 * @param ctx the parse tree
	 */
	void exitTypeDec(BiLangParser.TypeDecContext ctx);
	/**
	 * Enter a parse tree produced by the {@code SubsetTypeExp}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void enterSubsetTypeExp(BiLangParser.SubsetTypeExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code SubsetTypeExp}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void exitSubsetTypeExp(BiLangParser.SubsetTypeExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code RangeTypeExp}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void enterRangeTypeExp(BiLangParser.RangeTypeExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code RangeTypeExp}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void exitRangeTypeExp(BiLangParser.RangeTypeExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code TypeId}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void enterTypeId(BiLangParser.TypeIdContext ctx);
	/**
	 * Exit a parse tree produced by the {@code TypeId}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 */
	void exitTypeId(BiLangParser.TypeIdContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ReceiveExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 */
	void enterReceiveExt(BiLangParser.ReceiveExtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ReceiveExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 */
	void exitReceiveExt(BiLangParser.ReceiveExtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code FoldExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 */
	void enterFoldExt(BiLangParser.FoldExtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code FoldExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 */
	void exitFoldExt(BiLangParser.FoldExtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code WithdrawExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 */
	void enterWithdrawExt(BiLangParser.WithdrawExtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code WithdrawExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 */
	void exitWithdrawExt(BiLangParser.WithdrawExtContext ctx);
	/**
	 * Enter a parse tree produced by {@link BiLangParser#query}.
	 * @param ctx the parse tree
	 */
	void enterQuery(BiLangParser.QueryContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#query}.
	 * @param ctx the parse tree
	 */
	void exitQuery(BiLangParser.QueryContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IfOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterIfOutcome(BiLangParser.IfOutcomeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IfOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitIfOutcome(BiLangParser.IfOutcomeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code LetOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterLetOutcome(BiLangParser.LetOutcomeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code LetOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitLetOutcome(BiLangParser.LetOutcomeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ParenOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterParenOutcome(BiLangParser.ParenOutcomeContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ParenOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitParenOutcome(BiLangParser.ParenOutcomeContext ctx);
	/**
	 * Enter a parse tree produced by the {@code OutcomeExp}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void enterOutcomeExp(BiLangParser.OutcomeExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code OutcomeExp}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 */
	void exitOutcomeExp(BiLangParser.OutcomeExpContext ctx);
	/**
	 * Enter a parse tree produced by {@link BiLangParser#item}.
	 * @param ctx the parse tree
	 */
	void enterItem(BiLangParser.ItemContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#item}.
	 * @param ctx the parse tree
	 */
	void exitItem(BiLangParser.ItemContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpEqExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpEqExp(BiLangParser.BinOpEqExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpEqExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpEqExp(BiLangParser.BinOpEqExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code UndefExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterUndefExp(BiLangParser.UndefExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code UndefExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitUndefExp(BiLangParser.UndefExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpAddExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpAddExp(BiLangParser.BinOpAddExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpAddExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpAddExp(BiLangParser.BinOpAddExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpCompExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpCompExp(BiLangParser.BinOpCompExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpCompExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpCompExp(BiLangParser.BinOpCompExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code UnOpExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterUnOpExp(BiLangParser.UnOpExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code UnOpExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitUnOpExp(BiLangParser.UnOpExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code MemberExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterMemberExp(BiLangParser.MemberExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code MemberExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitMemberExp(BiLangParser.MemberExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IdExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterIdExp(BiLangParser.IdExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IdExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitIdExp(BiLangParser.IdExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code CallExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterCallExp(BiLangParser.CallExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code CallExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitCallExp(BiLangParser.CallExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IfExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterIfExp(BiLangParser.IfExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IfExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitIfExp(BiLangParser.IfExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpBoolExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpBoolExp(BiLangParser.BinOpBoolExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpBoolExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpBoolExp(BiLangParser.BinOpBoolExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ParenExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterParenExp(BiLangParser.ParenExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ParenExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitParenExp(BiLangParser.ParenExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BoolLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBoolLiteralExp(BiLangParser.BoolLiteralExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BoolLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBoolLiteralExp(BiLangParser.BoolLiteralExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code LetExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterLetExp(BiLangParser.LetExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code LetExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitLetExp(BiLangParser.LetExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code AddressLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterAddressLiteralExp(BiLangParser.AddressLiteralExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code AddressLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitAddressLiteralExp(BiLangParser.AddressLiteralExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BinOpMultExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterBinOpMultExp(BiLangParser.BinOpMultExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BinOpMultExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitBinOpMultExp(BiLangParser.BinOpMultExpContext ctx);
	/**
	 * Enter a parse tree produced by the {@code NumLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void enterNumLiteralExp(BiLangParser.NumLiteralExpContext ctx);
	/**
	 * Exit a parse tree produced by the {@code NumLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 */
	void exitNumLiteralExp(BiLangParser.NumLiteralExpContext ctx);
	/**
	 * Enter a parse tree produced by {@link BiLangParser#varDec}.
	 * @param ctx the parse tree
	 */
	void enterVarDec(BiLangParser.VarDecContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#varDec}.
	 * @param ctx the parse tree
	 */
	void exitVarDec(BiLangParser.VarDecContext ctx);
}