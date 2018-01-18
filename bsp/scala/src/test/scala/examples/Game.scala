
trait Game {
  def rows: Syntax.ProgramRows = Syntax.transpose(cols)

  def cols: Syntax.ProgramCols = Syntax.transpose(rows)
}

abstract sealed class Action
case class Send(client: Int) extends Action
case class Deliver(client: Int) extends Action
case class Progress(client: Int) extends Action


trait GameRun {
  val game: Game
  val players: List[Strategy]
  val schedule: List[Action]
  val expectedEvents: List[StepState]
}
