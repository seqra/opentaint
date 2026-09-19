package org.opentaint.dataflow.util

import java.util.concurrent.atomic.AtomicLong

/**
 * The memory-driven fact-depth ladder: spend spare heap on PROGRESS, and stop when it runs out.
 *
 * ## Why this knob, and why it is free of any recall argument
 *
 * The engine delays an edge whose fact is deeper than `factDepthLimit`, and raises that limit by
 * `FACT_DEPTH_STEP` whenever a unit runs out of work. **Delaying is not dropping.**
 * `NormalMethodAnalyzer.updateFactDepthLimit` re-adds every delayed edge at the new limit, and the
 * analysis is only reported complete when no unit holds a delayed edge. So the step size decides
 * WHEN an edge is processed and never WHETHER -- it cannot cause a false negative, and it needs no
 * soundness proof beyond that replay.
 *
 * That makes it the only lever in this work that trades performance against nothing at all.
 *
 * ## What the constant step costs, measured
 *
 * Conductor, 8 GB, on the sound arm (decoupled depth budget, `descendStatic`, the `[any]`
 * absorptions). Every arm keeps all four reference findings.
 *
 * | `factDepthStep` | events | `analyzedAdd` | outcome |
 * |---|---|---|---|
 * | 1 (shipped) | 926,442 | 78,242 | **stalls** at `+0`, and the heap sits at **72%** |
 * | 4 | 1,462,437 | 207,982 | OOM |
 * | 16 | 2,217,639 | 201,054 | OOM |
 * | 64 | 1,932,746 | 222,973 | OOM |
 * | 20,000 | 2,200,988 | 174,345 | OOM |
 *
 * A constant is either too small -- the run stalls with 28% of the heap unused -- or too large --
 * the released edges triple the demand and the heap fills. There is no constant in between, which is
 * the standing shape of this problem: `no_pressure_no_loss` says a bound must cost nothing until it
 * is needed, and a constant cannot.
 *
 * ## The controller
 *
 * The signal is the engine's own post-GC heap, taken from the GC notification `MemoryManager`
 * already handles -- the only accurate reading of what the analysis retains, since
 * `Runtime.freeMemory` counts garbage the next collection takes back.
 *
 * Below [softPercent] of the engine's own out-of-memory threshold there is room, so the ladder takes
 * [bigStep] rungs and releases the delayed work. At or above it the ladder drops to [smallStep] and
 * the delaying goes back to shedding load. The controller is therefore SYMMETRIC, unlike every
 * budget in this project: it may rise again when memory is released, because nothing it does is a
 * widening and there is no monotonicity to preserve.
 */
object FactDepthLadder {
    val enabled: Boolean =
        System.getProperty("opentaint.dynamicFactDepth")?.toBooleanStrictOrNull() ?: false

    /** The fraction of the engine's OOM threshold below which spare heap is spent on progress. */
    val softPercent: Int =
        System.getProperty("opentaint.dynamicFactDepthSoft")?.toIntOrNull() ?: 70

    /** Rungs taken per resume while there is room. */
    val bigStep: Int =
        System.getProperty("opentaint.dynamicFactDepthBig")?.toIntOrNull() ?: 1000

    /** Rungs taken per resume while there is not. Never 0: the ladder must still terminate. */
    val smallStep: Int =
        System.getProperty("opentaint.dynamicFactDepthSmall")?.toIntOrNull() ?: 1

    @Volatile
    private var underPressure: Boolean = false

    private val bigSteps = AtomicLong()
    private val smallSteps = AtomicLong()
    private val readings = AtomicLong()

    /** One post-GC reading, from the same notification the memory guard uses. */
    fun observe(usedAfterGc: Long, oomThreshold: Long) {
        if (!enabled || oomThreshold <= 0L) return
        readings.incrementAndGet()
        underPressure = usedAfterGc * 100L >= oomThreshold * softPercent
    }

    /**
     * The rungs to take on this resume.
     *
     * Returns the shipped constant when the controller is off, so the flag is the identity.
     */
    fun step(shipped: Int): Int {
        if (!enabled) return shipped
        return if (underPressure) {
            smallSteps.incrementAndGet()
            smallStep
        } else {
            bigSteps.incrementAndGet()
            bigStep
        }
    }

    fun report(): String =
        "fdLadder=" + (if (!enabled) "off" else if (underPressure) "hold" else "open") +
            " fdBig=" + bigSteps.get() + " fdSmall=" + smallSteps.get() +
            " fdReads=" + readings.get()

    /** Test seam: the controller is process-global, so a test that moves it must put it back. */
    fun resetForTest() {
        underPressure = false
        bigSteps.set(0)
        smallSteps.set(0)
        readings.set(0)
    }
}
