package org.opentaint.dataflow.bidi;

import org.opentaint.dataflow.bidi.interp.UnresolvedCallObserver;

/** Compilation control: the optional capability must not add an abstract SAM member. */
public final class UnresolvedObserverSam {
    private UnresolvedObserverSam() {}

    public static UnresolvedCallObserver observer() {
        return (call, position, plan) -> {};
    }
}
