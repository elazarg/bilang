import org.scalatest.FunSuite

import Syntax.transpose
import OddsEvens.{cols, rows}

class SyntaxTest extends FunSuite {
  test("Transposing rows to columns") {
    assert(transpose(rows) === cols)
  }
  test("Transposing columns to rows") {
    assert(transpose(cols) === rows)
  }
}
