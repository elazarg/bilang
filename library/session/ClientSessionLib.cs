using System;
using System.Collections.Generic;
using System.Text;
using System.Threading.Tasks;
using static Utils;

static class ClientSessionLib
{

#pragma warning disable CS1998 // Async method lacks 'await' operators and will run synchronously
    public class UpwardConnection {
        public uint id;
        public void Send<T>(T t) { }
        public Task SendAsync<T>(T t) { return Task.Run(() => Send(t)); }
        public async Task<string> ReceiveNotification() { return ""; }
        public async Task ReceiveNotification(string tag) { }
        public async Task<T> ReceiveNotification<T>(string tag = "") { return default; }

        public async Task<Hiding<T>> Hide<T>(T value) where T : struct {
            var res = new Hiding<T>(value, new System.Random(0x2346).Next());
            await SendAsync(res.Hidden(id));
            return res;
        }

        public async Task Hide<T>(T value, string until) where T : struct {
            var hiddenChoice = await Hide(value);
            await ReceiveNotification(until);
            await OpenAsync(hiddenChoice);
        }

        public void Open<T>(Hiding<T> hv) where T : struct {
            Send(hv);
        }
        public Task OpenAsync<T>(Hiding<T> hv) where T : struct {
            return Task.Run(() => Open(hv));
        }
    }

    public class Contract {
        public async Task<UpwardConnection> Connect(uint id) { return new UpwardConnection(); }
        public async Task<UpwardConnection> Connect(string tag, int id = 0) { return new UpwardConnection(); }
        public async Task<UpwardConnection> Connect<T>(string tag, T init) { return new UpwardConnection(); }

        public int Read<T>(string v) where T: struct {
            throw new NotImplementedException();
        }
    }
}
