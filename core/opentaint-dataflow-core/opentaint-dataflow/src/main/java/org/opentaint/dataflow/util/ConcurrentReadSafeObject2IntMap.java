package org.opentaint.dataflow.util;

import it.unimi.dsi.fastutil.HashCommon;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import org.jetbrains.annotations.Nullable;

/**
 * A flat object-to-int map supporting one writer and multiple concurrent point readers.
 *
 * <p>Writes are published through a sequence counter. Readers retry if a write overlaps their
 * lookup, which prevents observing a key before its primitive value or a partially published
 * rehash. Removals are not supported.</p>
 */
public final class ConcurrentReadSafeObject2IntMap<K> extends Object2IntOpenHashMap<K> {
    public static final int NO_VALUE = -1;

    private volatile long writeSequence;

    public ConcurrentReadSafeObject2IntMap() {
        super();
        defaultReturnValue(NO_VALUE);
    }

    @Override
    public int getInt(@Nullable Object k) {
        while (true) {
            long sequenceBefore = writeSequence;
            if ((sequenceBefore & 1) != 0) continue;

            K[] key = this.key;
            int[] value = this.value;
            int result = findValue(k, key, value);

            if (sequenceBefore == writeSequence) return result;
        }
    }

    private int findValue(@Nullable Object k, K[] key, int[] value) {
        if (k == null) return containsNullKey ? value[value.length - 1] : defRetValue;

        int mask = key.length - 2;
        int pos = HashCommon.mix(k.hashCode()) & mask;
        K curr = key[pos];
        if (curr == null) return defRetValue;
        if (k.equals(curr)) return value[pos];

        while (true) {
            pos = (pos + 1) & mask;
            curr = key[pos];
            if (curr == null) return defRetValue;
            if (k.equals(curr)) return value[pos];
        }
    }

    @Override
    public int put(K key, int value) {
        beginWrite();
        try {
            return super.put(key, value);
        } finally {
            endWrite();
        }
    }

    @Override
    public int putIfAbsent(K key, int value) {
        beginWrite();
        try {
            return super.putIfAbsent(key, value);
        } finally {
            endWrite();
        }
    }

    private void beginWrite() {
        writeSequence++;
    }

    private void endWrite() {
        writeSequence++;
    }

    @Override
    public int removeInt(Object k) {
        throw new UnsupportedOperationException("Removals are not allowed");
    }

    private static final long serialVersionUID = 0L;
}
