import scala.collection.mutable

class Network(contract: Model, players: List[Strategy]) {
  private val packets = players.map(_=> mutable.Queue[Packet]())
  var time = 0
  def events: List[Model.Event] = contract.state

  def clientStep(i: Int): Unit = {
    for (packet <- players(i).act(events)) {
      packets(i).enqueue(packet)
    }
  }

  def perform(i: Int): Unit = {
    val packet = packets(i).dequeue()
    contract.receive(packet, time)
  }

  def AddProgress(i: Int): Unit = {
    packets(i).enqueue(ProgressPacket(contract.pc))
  }

  def step(): Unit = {
    time += 1
  }
}
