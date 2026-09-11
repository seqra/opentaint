package org.opentaint.ir.test.python.tier3

import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test

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

def rtm_or(x: int) -> str:
    match x:
        case 1 | 2 | 3:
            return "small"
        case 10 | 20:
            return "round"
        case _:
            return "other"

def rtm_singleton(v: object) -> str:
    match v:
        case None:
            return "none"
        case True:
            return "true"
        case False:
            return "false"
        case _:
            return "other"

def rtm_singleton_in_or(v: object) -> str:
    match v:
        case None | False:
            return "falsy"
        case True:
            return "true"
        case _:
            return "other"

def rtm_class_noargs(v: object) -> str:
    match v:
        case bool():
            return "bool"
        case int():
            return "int"
        case str():
            return "str"
        case _:
            return "other"

def rtm_class_as_binding(v: object) -> str:
    match v:
        case str() as s:
            return "str:" + s
        case int() as n:
            return "int:" + str(n)
        case _:
            return "other"
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

    @Test fun `match - or pattern`() = roundTrip("rtm_or",
        posArgs(listOf(1), listOf(3), listOf(10), listOf(20), listOf(7)))

    @Test fun `match - singleton pattern`() = roundTrip("rtm_singleton",
        posArgs(listOf(null), listOf(true), listOf(false), listOf(0), listOf(1), listOf("x")))

    @Test fun `match - singleton inside or`() = roundTrip("rtm_singleton_in_or",
        posArgs(listOf(null), listOf(false), listOf(true), listOf(0), listOf("x")))

    @Test fun `match - class pattern without args`() = roundTrip("rtm_class_noargs",
        posArgs(listOf(true), listOf(5), listOf("x"), listOf(1.5), listOf(null)))

    @Test fun `match - class pattern with as binding`() = roundTrip("rtm_class_as_binding",
        posArgs(listOf("hi"), listOf(7), listOf(1.5)))
}
