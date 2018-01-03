
trait Example {
  def rows: Syntax.ProgramRows = Syntax.transpose(cols)

  def cols: Syntax.ProgramCols = Syntax.transpose(rows)

  val packets: Seq[Packet]
}
