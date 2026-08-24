package org.opentaint.ir.test.python.tier3

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test

/**
 * @Disabled: the angle-bracket class name `<closure_…>` is not a valid Python identifier and
 * [PIRReconstructor] cannot emit parseable Python for it. [RoundTripLocalFunctionTest] still
 * passes because it goes through the sanitised function-only path; this test targets the raw
 * synthetic shape and is the placeholder for that follow-up.
 */
@Tag("tier3")
class RoundTripCallableShimTest {

    @Disabled("PIRReconstructor follow-up — synthesised <closure_*> class names are not valid Python identifiers")
    @Test
    fun `synthetic adapter class round-trips with raw angle-bracket name`() {
        // TODO: implement when PIRReconstructor learns the new closure shape.
        // The plan-of-record:
        //   1. Reconstructor recognises `<closure_X>` in module.classes.
        //   2. Adapter class emits as Python with sanitised name.
        //   3. PIRCall to the adapter constructor reconstructs as instantiation.
        //   4. Verify executing original Python and reconstructed Python yields
        //      identical results for a fixture exercising captures, *args,
        //      **kwargs, default values, and keyword-only arguments.
    }
}
