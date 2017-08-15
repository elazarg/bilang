using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;
using System.Threading.Tasks.Dataflow;

struct ServerMsg { }
struct ClientMsg { }

static class VM {
    static Thread server = new Thread(MontyHall.Server);
    static Thread clientHost = new Thread(() => MontyHall.ClientHost(MontyHall.Door.a));
    static Thread clientGuest = new Thread(MontyHall.ClientGuest);

    static BufferBlock<ServerMsg> msgsFromServer;
    static BufferBlock<ClientMsg> msgsToServer;
    static BufferBlock<uint> connectionsToServer;

    static BufferBlock<uint> connectionsFromHost;
    static BufferBlock<ClientMsg> msgsFromHost;

    static BufferBlock<uint> connectionsFromGuest;
    static BufferBlock<ClientMsg> msgsFromGuest;

    public static void Main() {
        server.Start();
        clientGuest.Start();
        clientHost.Start();
        RunScheduler();
    }

    private static void RunScheduler() {
        throw new NotImplementedException();
    }

    public static uint WaitForClientConnection(string tag = "") {
        // should block
        return connectionsToServer.Receive();
    }
    public static ClientMsg WaitForClientMessage(string tag = "") {
        // should block
        return msgsToServer.Receive();
    }
    public static void ConnectToServer(string tag = "") {
        if (Thread.CurrentThread == clientHost)
            connectionsFromHost.Post<uint>(0x1324);
        if (Thread.CurrentThread == clientGuest)
            connectionsFromGuest.Post<uint>(0x1324);
        // How to block here?
    }


}
