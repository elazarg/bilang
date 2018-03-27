// Generated from /Users/elazarg/workspace/research/bilang/BiLang.g4 by ANTLR 4.7
package generated;
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
	 * Enter a parse tree produced by the {@code VarDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterVarDef(BiLangParser.VarDefContext ctx);
	/**
	 * Exit a parse tree produced by the {@code VarDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitVarDef(BiLangParser.VarDefContext ctx);
	/**
	 * Enter a parse tree produced by the {@code YieldDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterYieldDef(BiLangParser.YieldDefContext ctx);
	/**
	 * Exit a parse tree produced by the {@code YieldDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitYieldDef(BiLangParser.YieldDefContext ctx);
	/**
	 * Enter a parse tree produced by the {@code JoinDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterJoinDef(BiLangParser.JoinDefContext ctx);
	/**
	 * Exit a parse tree produced by the {@code JoinDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitJoinDef(BiLangParser.JoinDefContext ctx);
	/**
	 * Enter a parse tree produced by the {@code JoinManyDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterJoinManyDef(BiLangParser.JoinManyDefContext ctx);
	/**
	 * Exit a parse tree produced by the {@code JoinManyDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitJoinManyDef(BiLangParser.JoinManyDefContext ctx);
	/**
	 * Enter a parse tree produced by the {@code BlockStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterBlockStmt(BiLangParser.BlockStmtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code BlockStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitBlockStmt(BiLangParser.BlockStmtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code AssignStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterAssignStmt(BiLangParser.AssignStmtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code AssignStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitAssignStmt(BiLangParser.AssignStmtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code RevealStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterRevealStmt(BiLangParser.RevealStmtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code RevealStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitRevealStmt(BiLangParser.RevealStmtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code IfStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterIfStmt(BiLangParser.IfStmtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code IfStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitIfStmt(BiLangParser.IfStmtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ForYieldStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterForYieldStmt(BiLangParser.ForYieldStmtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ForYieldStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitForYieldStmt(BiLangParser.ForYieldStmtContext ctx);
	/**
	 * Enter a parse tree produced by the {@code TransferStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterTransferStmt(BiLangParser.TransferStmtContext ctx);
	/**
	 * Exit a parse tree produced by the {@code TransferStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitTransferStmt(BiLangParser.TransferStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link BiLangParser#packet}.
	 * @param ctx the parse tree
	 */
	void enterPacket(BiLangParser.PacketContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#packet}.
	 * @param ctx the parse tree
	 */
	void exitPacket(BiLangParser.PacketContext ctx);
	/**
	 * Enter a parse tree produced by {@link BiLangParser#whereClause}.
	 * @param ctx the parse tree
	 */
	void enterWhereClause(BiLangParser.WhereClauseContext ctx);
	/**
	 * Exit a parse tree produced by {@link BiLangParser#whereClause}.
	 * @param ctx the parse tree
	 */
	void exitWhereClause(BiLangParser.WhereClauseContext ctx);
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