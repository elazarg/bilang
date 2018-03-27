// Generated from /Users/elazarg/workspace/research/bilang/BiLang.g4 by ANTLR 4.7
package generated;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link BiLangParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface BiLangVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link BiLangParser#program}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProgram(BiLangParser.ProgramContext ctx);
	/**
	 * Visit a parse tree produced by {@link BiLangParser#typeDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeDec(BiLangParser.TypeDecContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SubsetTypeExp}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSubsetTypeExp(BiLangParser.SubsetTypeExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code RangeTypeExp}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRangeTypeExp(BiLangParser.RangeTypeExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code TypeId}
	 * labeled alternative in {@link BiLangParser#typeExp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeId(BiLangParser.TypeIdContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpEqExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpEqExp(BiLangParser.BinOpEqExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code UndefExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUndefExp(BiLangParser.UndefExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpAddExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpAddExp(BiLangParser.BinOpAddExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpCompExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpCompExp(BiLangParser.BinOpCompExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code UnOpExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnOpExp(BiLangParser.UnOpExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code MemberExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMemberExp(BiLangParser.MemberExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IdExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExp(BiLangParser.IdExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code CallExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCallExp(BiLangParser.CallExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfExp(BiLangParser.IfExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpBoolExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpBoolExp(BiLangParser.BinOpBoolExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ParenExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExp(BiLangParser.ParenExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code AddressLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAddressLiteralExp(BiLangParser.AddressLiteralExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpMultExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpMultExp(BiLangParser.BinOpMultExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code NumLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNumLiteralExp(BiLangParser.NumLiteralExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code VarDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDef(BiLangParser.VarDefContext ctx);
	/**
	 * Visit a parse tree produced by the {@code YieldDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitYieldDef(BiLangParser.YieldDefContext ctx);
	/**
	 * Visit a parse tree produced by the {@code JoinDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitJoinDef(BiLangParser.JoinDefContext ctx);
	/**
	 * Visit a parse tree produced by the {@code JoinManyDef}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitJoinManyDef(BiLangParser.JoinManyDefContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BlockStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBlockStmt(BiLangParser.BlockStmtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code AssignStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignStmt(BiLangParser.AssignStmtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code RevealStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRevealStmt(BiLangParser.RevealStmtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfStmt(BiLangParser.IfStmtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ForYieldStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForYieldStmt(BiLangParser.ForYieldStmtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code TransferStmt}
	 * labeled alternative in {@link BiLangParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTransferStmt(BiLangParser.TransferStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link BiLangParser#packet}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPacket(BiLangParser.PacketContext ctx);
	/**
	 * Visit a parse tree produced by {@link BiLangParser#whereClause}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitWhereClause(BiLangParser.WhereClauseContext ctx);
	/**
	 * Visit a parse tree produced by {@link BiLangParser#varDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDec(BiLangParser.VarDecContext ctx);
}