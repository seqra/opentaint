package org.opentaint.dataflow.ap.ifds.access

/**
 * THE switch between LITERAL and DENOTATIONAL `[any]` matching, and the single place it is read.
 *
 * `[any]` is read two different ways depending on the question asked of a fact:
 *
 *  - **denotation** -- `readAccessor`, `startsWithAccessor`, `contains`/`equalTo`; the rule
 *    preconditions, alias analysis, trace resolution. `[any]` is zero-or-more covered steps, and
 *    this object does not touch them.
 *  - **matching** -- which premise a fact activates: `delta`, `filterStartsWith`, the premise
 *    lookup, the initial-fact abstraction's descent, and the exact cleaner's `[any]` branch.
 *
 * [literal] decides the second. `true` (the default) means a premise link matches only a LITERAL
 * child, or a child directly under the node's `[any]` edge with the `[any]` taken zero times.
 * `false` restores the pre-2026-08-27 engine, which additionally SYNTHESISES the demanded accessor
 * out of the `[any]` and reinstalls the `[any]` below it.
 *
 * ## Why this object exists
 *
 * The two readings are ONE decision, and it used to be parsed independently in two places -- here
 * and privately inside `Cleaner.kt`, which has no `ApManager` in scope at its use site. A manager
 * constructed with `literalAnyMatch = false` therefore still got literal-era CLEANING, in the same
 * JVM, silently. One object, parsed once, is the fix: everything global reads these fields, and a
 * per-instance override lives on the manager that owns it.
 *
 * ## What follows from the choice, and why it is not a free A/B
 *
 * The mode is not a local behaviour of one operator. It decides whether a fact's premises are
 * exactly its literal prefixes -- which is what bounds the summary-application round trip
 * (`AnyDeltaConcatRoundTripTest`) and what stops `TreeInitialFactAbstraction`'s R3c/R4 ladder from
 * walking `sum n!/(n-k)!` premises. It also decides whether a rewrite that DELETES a literal edge
 * (`compressAbsorbCoveredSiblings`) is sound: under the denotational reader such a fold is a
 * widening in both channels, and under the literal reader it narrows the fact's matchable set. See
 * `docs/superpowers/specs/2026-08-27-sibling-absorption-and-pot-cost.md`.
 */
object AnyMatchMode {
    const val LITERAL_ANY_MATCH_PROPERTY = "opentaint.literalAnyMatch"

    /**
     * `-Dopentaint.literalAnyMatch=true|false`, default `true`.
     *
     * Read once, at class initialisation -- setting the property after this class loads has no
     * effect, which is why every test that needs the other mode either forwards the property
     * (`FORWARDED_TEST_PROPERTIES`) or constructs its manager with an explicit argument.
     */
    @JvmField
    val literal: Boolean = boolProperty(LITERAL_ANY_MATCH_PROPERTY) ?: true

    /**
     * Whether an EXACT cleaner leaves a mark sitting under an `[any]` alone.
     *
     * Follows [literal], because the two are one decision: clearing is only sound while the premise
     * ladder exists to represent the surviving `>=1`-step readings, and the literal mode is exactly
     * what removes that ladder. `-Dopentaint.exactCleanerKeepsAny` overrides it for ablation.
     */
    @JvmField
    val exactCleanerKeepsAny: Boolean =
        boolProperty("opentaint.exactCleanerKeepsAny") ?: literal

    /**
     * `-Dopentaint.literalAnyMatch.<part>` -- an ABLATION rung, not a setting to ship.
     *
     * Null when unset. The caller decides what it falls back to, and -- this is the part that was
     * wrong before -- a caller that was handed an explicit per-instance value different from
     * [literal] must NOT consult this at all: a global bisect knob silently overriding a deliberate
     * per-instance choice made `literalAnyMatch = false` in a test mean "false unless some `-D` I
     * did not set says otherwise".
     */
    fun part(name: String): Boolean? = boolProperty("$LITERAL_ANY_MATCH_PROPERTY.$name")

    fun boolProperty(name: String): Boolean? =
        System.getProperty(name)?.trim()?.lowercase()
            ?.let { it != "false" && it != "0" && it != "off" }
}
