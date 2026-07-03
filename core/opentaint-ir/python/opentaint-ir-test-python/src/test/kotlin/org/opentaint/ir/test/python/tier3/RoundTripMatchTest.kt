package org.opentaint.ir.test.python.tier3

import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test

/**
 * Round-trip tests for `match` statements. Executes the original `match` and the
 * reconstructed desugaring (if/elif chain) and asserts identical results —
 * verifies the desugaring in [StatementLowering.visitMatch] preserves semantics.
 * v1 covers capture / wildcard / `as` / value patterns and guards.
 */
@Tag("tier3")
class RoundTripMatchTest : RoundTripTestBase() {

    override val allSources = """
def rtm_capture(x: int) -> int:
    match x:
        case y:
            return y + 1
    return -1

def rtm_value(x: int) -> str:
    match x:
        case 1:
            return "one"
        case 2:
            return "two"
        case _:
            return "many"

def rtm_value_no_wildcard(x: int) -> str:
    match x:
        case 1:
            return "one"
        case 2:
            return "two"
    return "fallthrough"

def rtm_as(x: int) -> int:
    match x:
        case 5 as y:
            return y * 10
        case other:
            return other

def rtm_guard(x: int) -> str:
    match x:
        case y if y > 10:
            return "big"
        case y if y > 0:
            return "small"
        case _:
            return "nonpos"

def rtm_str_value(s: str) -> str:
    match s:
        case "hello":
            return "greeting"
        case "bye":
            return "farewell"
        case other:
            return other

def rtm_nested_in_if(x: int) -> int:
    if x > 0:
        match x:
            case 1:
                return 100
            case _:
                return 200
    return 0
    """.trimIndent()

    @Test fun `match - capture`() = roundTrip("rtm_capture",
        posArgs(listOf(5), listOf(0), listOf(-3)))

    @Test fun `match - value with wildcard`() = roundTrip("rtm_value",
        posArgs(listOf(1), listOf(2), listOf(3), listOf(0)))

    @Test fun `match - value no wildcard fallthrough`() = roundTrip("rtm_value_no_wildcard",
        posArgs(listOf(1), listOf(2), listOf(9)))

    @Test fun `match - as binding`() = roundTrip("rtm_as",
        posArgs(listOf(5), listOf(7)))

    @Test fun `match - guarded cases`() = roundTrip("rtm_guard",
        posArgs(listOf(20), listOf(5), listOf(0), listOf(-1)))

    @Test fun `match - string value`() = roundTrip("rtm_str_value",
        posArgs(listOf("hello"), listOf("bye"), listOf("other")))

    @Test fun `match - nested in if`() = roundTrip("rtm_nested_in_if",
        posArgs(listOf(1), listOf(2), listOf(-1)))
}
