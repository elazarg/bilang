import org.scalatest.FunSuite

import Syntax.transpose

class SyntaxTest extends FunSuite {
  test("Transposing rows to columns") {
    rowsToCols(MontyHall)
    rowsToCols(SNPG)
  }

  test("Transposing columns to rows") {
    colsToRows(MontyHall)
    colsToRows(SNPG)
  }

  private def rowsToCols(game: Game) = {
    assert(transpose(game.rows) === game.cols)
  }

  private def colsToRows(game: Game) = {
    assert(transpose(game.cols) === game.rows)
  }

}
