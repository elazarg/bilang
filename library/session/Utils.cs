using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Linq;

/***
 * Helper library - has nothing special to do with the blockchain
 */
public static class Utils {

    public struct Nothing { }
    
    public struct DPair<T1, T2> : IDisposable
        where T1 : IDisposable
        where T2 : IDisposable {
        public T1 Item1;
        public T2 Item2;

        public DPair(T1 item1, T2 item2) : this() {
            this.Item1 = item1;
            this.Item2 = item2;
        }

        public void Dispose() {
            Item1.Dispose();
            Item2.Dispose();
        }
    }

    public static void Atomically(Action f) {
        // non-async function f
        f();
    }
    
    public static bool NoReq<T>(T x) => true;


    public struct Hidden<T> where T : struct {
        public readonly int hash;

        public Hidden(int hash) : this() {
            this.hash = hash;
        }
        
        public bool CheckOpen(T value, int salt, uint owner) {
            return (value, salt, owner).GetHashCode() == hash;
        }
    }

    public struct Hiding<T> where T : struct {
        public readonly int salt;
        public readonly T value;

        public Hiding(T value, int salt) : this() {
            this.value = value;
            this.salt = salt;
        }

        public int Hidden(uint owner) {
            return (value, salt, owner).GetHashCode();
        }
    }
}
