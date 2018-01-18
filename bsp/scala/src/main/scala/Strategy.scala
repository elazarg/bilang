
trait Strategy {
  def act(events: List[Model.Event]) : Option[Packet]
}

trait SimpleStrategy extends Strategy {
  val role: Syntax.RoleName

  def actSimple(events: List[Model.Event]) : Option[Syntax.Value]

  final override def act(events: List[Model.Event]) : Option[Packet] = {
    if (events.isEmpty) Some(JoinPacket(this, -1, role))
    else actSimple(events).map(SmallStepPacket(this, events.size - 1, role, _))
  }
}
