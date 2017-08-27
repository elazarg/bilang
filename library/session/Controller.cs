using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks.Dataflow;

struct Session {
    readonly Action<PublicLink> server;
    readonly Action<ServerLink>[] clients;

    internal Session(Action<PublicLink> server, params Action<ServerLink>[] clients) {
        this.server = server;
        this.clients = clients;
    }

    internal IEnumerable<Actor> CreateActors(BC bc) {
        Action<PublicLink> _server = server;
        yield return new Actor(0, () => _server(new PublicLink(bc, 0)));
        for (uint i = 0; i < clients.Length; i++) {
            uint address = i + 1;
            var client = clients[i];
            yield return new Actor(address, () => client(new ServerLink(bc, address)));
        }
    }
}

class Actor {
    internal readonly uint address;
    internal readonly Thread thread;
    internal readonly BufferBlock<bool> run = new BufferBlock<bool>();
    internal readonly BroadcastBlock<string> state = new BroadcastBlock<string>(x=>x);

    internal void Yield(object details) {
        state.Post($"Waiting: {details}");
        run.Receive();
        state.Post($"Running");
    }

    internal void Wake() {
        run.Post(true);
    }

    public Actor(uint address, Action action) {
        this.address = address;
        this.thread = new Thread(() => { action(); state.Post("Done"); });
        state.Post("Ready to start");
    }
}


class Controller {
    List<Actor> actors = new List<Actor>();
    static Random rnd = new Random();

    private static void Prompt(string s) {
        Console.Write($"\r{s}\n>>> ");
        Console.Out.Flush();
    }

    internal void Yield(uint address, object details) {
        actors[(int)address].Yield(details);
    }

    public void Start(Session game) {
        BC bc = new BC(this);
        actors = game.CreateActors(bc).ToList();
        var threads = new List<Thread>();
        foreach (var actor in actors) {
            bc.requests.Register(actor.address);
            threads.Add(actor.thread);
            actor.thread.Start();
        }
        StartRepl();
    }

    private void StartRepl() {
        Prompt("Start game");
        while (true) {
            var s = Console.ReadLine();
            if (s == "exit" || s == "q" || s == "quit") {
                Console.WriteLine("Killing threads");
                foreach (var actor in actors)
                    actor.thread.Abort();
                Console.WriteLine("Exiting");
                return;
            } else if (int.TryParse(s, out int address)) {
                if (address < actors.Count) {
                    Prompt($"Wake {address}");
                    actors[address].Wake();
                } else {
                    Prompt($"Bad address {address}");
                }
            } else if (s.Contains(" ") && s.Split(' ')[0] == "run" && uint.TryParse(s.Split(' ')[1], out uint count)) {
                for (int i = 0; i < count; i++) {
                    int id = rnd.Next(actors.Count);
                    Prompt($"Wake {id}");
                    actors[id].Wake();
                    Thread.Sleep(100);
                }
            } else if (s != "") {
                Prompt($"Unkown command {s}");
            } else {
                int id = rnd.Next(actors.Count);
                Prompt($"Wake {id}");
                actors[id].Wake();
            }
            {
                foreach (var actor in actors) {
                    var v = actor.state.Receive();
                    Prompt($"{actor.address}: {v}");
                }
            }
        }
    }
}
