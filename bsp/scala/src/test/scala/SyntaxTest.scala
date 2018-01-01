import Examples.{oddsEvensCols, oddsEvensRows}
import Syntax.transpose
import org.scalatest.FunSuite

class SyntaxTest extends FunSuite {
  test("Transposing rows to columns") {
    assert(transpose(oddsEvensRows) === oddsEvensCols)
  }
  test("Transposing columns to rows") {
    assert(transpose(oddsEvensCols) === oddsEvensRows)
  }
}
