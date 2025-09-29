// Generated from BiLang.g4 by ANTLR 4.13.2
package bilang.generated;
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
	 * Visit a parse tree produced by the {@code ReceiveExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReceiveExt(BiLangParser.ReceiveExtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code WithdrawExt}
	 * labeled alternative in {@link BiLangParser#ext}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitWithdrawExt(BiLangParser.WithdrawExtContext ctx);
	/**
	 * Visit a parse tree produced by {@link BiLangParser#query}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuery(BiLangParser.QueryContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfOutcome(BiLangParser.IfOutcomeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code LetOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLetOutcome(BiLangParser.LetOutcomeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ParenOutcome}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenOutcome(BiLangParser.ParenOutcomeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code OutcomeExp}
	 * labeled alternative in {@link BiLangParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOutcomeExp(BiLangParser.OutcomeExpContext ctx);
	/**
	 * Visit a parse tree produced by {@link BiLangParser#item}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitItem(BiLangParser.ItemContext ctx);
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
	 * Visit a parse tree produced by the {@code BoolLiteralExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolLiteralExp(BiLangParser.BoolLiteralExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code LetExp}
	 * labeled alternative in {@link BiLangParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLetExp(BiLangParser.LetExpContext ctx);
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
	 * Visit a parse tree produced by {@link BiLangParser#varDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDec(BiLangParser.VarDecContext ctx);
}