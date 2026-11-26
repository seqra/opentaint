package org.opentaint.dataflow.util;

import it.unimi.dsi.fastutil.HashCommon;
import it.unimi.dsi.fastutil.longs.LongOpenHashSet;

public final class ConcurrentReadSafeLongSet extends LongOpenHashSet {
    @Override
    public boolean contains(long k) {
        if (k == 0) return containsNull;

        while (true) {
            long[] key = this.key;
            int n = this.n;


            if (key.length != n + 1) continue;

            int mask = n - 1;
            int pos = (int) HashCommon.mix(k) & mask;
            long curr = key[pos];
            if (curr == 0) return false;

            if (k == curr) return true;


            while (true) {
                pos = (pos + 1) & mask;
                curr = key[pos];
                if (curr == 0) return false;

                if (k == curr) return true;
            }
        }
    }

    @Override
    public boolean remove(long k) {
        throw new UnsupportedOperationException("Removals are not allowed");
    }

    public long[] getKeys() {
        return this.key;
    }

    public int getN() {
        return this.n;
    }

    public boolean getContainsNull() {
        return this.containsNull;
    }

    private static final long serialVersionUID = 0L;
}
