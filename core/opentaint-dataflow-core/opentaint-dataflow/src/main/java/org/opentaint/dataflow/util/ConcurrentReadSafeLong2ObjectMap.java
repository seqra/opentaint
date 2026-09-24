package org.opentaint.dataflow.util;

import it.unimi.dsi.fastutil.HashCommon;
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap;
import org.jetbrains.annotations.Nullable;

public final class ConcurrentReadSafeLong2ObjectMap<V> extends Long2ObjectOpenHashMap<V> {
    @Override
    public @Nullable V get(long k) {
        if (k == 0) {
            if (!containsNullKey) return defRetValue;

            do {
                int n = this.n;
                V[] value = this.value;
                if (value.length == n + 1) return value[n];
            } while (true);
        }

        while (true) {
            long[] key = this.key;
            V[] value = this.value;
            int n = this.n;


            if (key.length != n + 1 || value.length != n + 1) continue;

            int mask = n - 1;
            int pos = (int) HashCommon.mix(k) & mask;
            long curr = key[pos];
            if (curr == 0) return defRetValue;

            if (k == curr) return value[pos];


            while (true) {
                pos = (pos + 1) & mask;
                curr = key[pos];
                if (curr == 0) return defRetValue;

                if (k == curr) return value[pos];
            }
        }
    }

    @Override
    public V remove(long k) {
        throw new UnsupportedOperationException("Removals are not allowed");
    }

    public long[] getKeys() {
        return this.key;
    }

    public V[] getValues() {
        return this.value;
    }

    public int getN() {
        return this.n;
    }

    public boolean getContainsNullKey() {
        return this.containsNullKey;
    }

    private static final long serialVersionUID = 0L;
}
