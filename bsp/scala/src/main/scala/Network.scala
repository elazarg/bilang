import scala.collection.mutable

class Network(contract: Model, players: List[Strategy]) {
  private val packets = players.map(_=> mutable.Queue[Packet]())
  private var events = List[Model.Event]()

  def clientStep(i: Int): Unit = {
    packets(i).enqueue(players(i).act(events))
  }

  def perform(i: Int): Unit = {
    val packet = packets(i).dequeue()
    for (event <- contract.receive(packet))
      events +:= event
  }

  def AddProgress(i: Int): Unit = {
    packets(i).enqueue(ProgressPacket(contract.pc))
  }

  def step(): Unit = {
    contract.time += 1
  }
}
