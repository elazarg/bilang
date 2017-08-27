using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Linq;

/***
 * Helper library - has nothing special to do with the blockchain
 */
public static class Utils {
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
