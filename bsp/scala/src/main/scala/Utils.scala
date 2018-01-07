import Syntax.{Num, Value}

object Utils {
  def hash(value: Value): Num = Num(value.hashCode)
}