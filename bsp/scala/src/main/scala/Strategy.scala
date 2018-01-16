
trait Strategy {
  def act(events: List[Model.Event]) : Option[Packet]
}
