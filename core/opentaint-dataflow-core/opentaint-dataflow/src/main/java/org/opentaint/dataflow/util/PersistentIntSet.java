package org.opentaint.dataflow.util;

import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;

public class PersistentIntSet extends IntOpenHashSet {
    PersistentIntSet(int initialCapacity) {
        super(initialCapacity);
    }

    public PersistentIntSet persistentAdd(int element) {
        if (contains(element)) return this;
        PersistentIntSet copy = clone();
        copy.add(element);
        return copy;
    }

    public PersistentIntSet persistentRemove(int element) {
        if (!contains(element)) return this;
        PersistentIntSet copy = clone();
        copy.remove(element);
        return copy;
    }

    public PersistentIntSet persistentAddAll(PersistentIntSet other) {
        PersistentIntSet copy = clone();
        copy.addAll(other);
        if (copy.size == this.size) return this;
        if (copy.size == other.size) return other;
        return copy;
    }

    public PersistentIntSet persistentRetainAll(PersistentIntSet other) {
        PersistentIntSet copy = clone();
        copy.retainAll(other);
        if (copy.size == this.size) return this;
        return copy;
    }

    public static PersistentIntSet create(IntList elements) {
        PersistentIntSet set = new PersistentIntSet(elements.size());
        set.addAll(elements);
        return set;
    }

    public static PersistentIntSet singleton(int element) {
        PersistentIntSet set = new PersistentIntSet(2);
        set.add(element);
        return set;
    }

    @Override
    public PersistentIntSet clone() {
        return (PersistentIntSet) super.clone();
    }

    private static final long serialVersionUID = 0L;
}
