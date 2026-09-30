package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary.Edge
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRValue
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class JIRStatementSummaryTest : BasicTestUtils() {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private val ap = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val cls = "sample.sequent.StatementSummarySample"
    private val field = FieldAccessor(cls, "f", "java.lang.Object")
    private val next = FieldAccessor(cls, "next", cls)
    private val staticField = FieldAccessor(cls, "sField", "java.lang.Object")
    private val classStatic = ClassStaticAccessor(cls)

    private fun insts(method: String): List<JIRInst> = findMethod(cls, method).instList.instructions
    private fun assigns(method: String) = insts(method).filterIsInstance<JIRAssignInst>()
    private fun base(v: JIRValue) = accessPathBase(v)!!

    private fun p(base: AccessPathBase, vararg path: Accessor): InitialFactAp =
        path.foldRight(ap.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }

    private fun summary(inst: JIRInst) = JIRStatementSummary.build(ap, inst, aliasAnalysis = null)
    private fun edges(inst: JIRInst) = summary(inst).transfers.flatMap { it.edges.asList() }.toSet()

    private val g = FieldAccessor(cls, "g", "java.lang.Object")

    private fun preconditions(inst: JIRInst, fact: InitialFactAp): Set<InitialFactAp>? {
        val reversed = JIRStatementSummary.buildReversed(ap, inst, aliasAnalysis = null)
        if (reversed.find(fact.base) == null) return null
        return (reversed.preconditionFacts(fact) ?: listOf(fact)).toSet()
    }

    @Test
    fun `field read splits the instance and kills the target`() {
        val inst = assigns("fieldRead").first { it.rhv is JIRFieldRef }
        val x = base(inst.lhv)
        val y = base((inst.rhv as JIRFieldRef).instance!!)
        assertEquals(setOf(
            Edge(p(y).exclude(field), p(y)),
            Edge(p(y, field), p(y, field)),
            Edge(p(y, field), p(x)),
        ), edges(inst))
        assertEquals(emptyList(), summary(inst).find(x)?.edges?.asList())
    }

    @Test
    fun `field write is a strong update of the field`() {
        val inst = assigns("fieldWrite").first { it.lhv is JIRFieldRef }
        val y = base((inst.lhv as JIRFieldRef).instance!!)
        val x = base(inst.rhv as JIRValue)
        assertEquals(setOf(
            Edge(p(y).exclude(field), p(y)),
            Edge(p(x), p(x)),
            Edge(p(x), p(y, field)),
        ), edges(inst))
    }

    @Test
    fun `static read splits the class static base`() {
        val inst = assigns("staticRead").first { it.rhv is JIRFieldRef }
        val x = base(inst.lhv)
        val s = AccessPathBase.ClassStatic
        assertEquals(setOf(
            Edge(p(s).exclude(classStatic), p(s)),
            Edge(p(s, classStatic).exclude(staticField), p(s, classStatic)),
            Edge(p(s, classStatic, staticField), p(s, classStatic, staticField)),
            Edge(p(s, classStatic, staticField), p(x)),
        ), edges(inst))
    }

    @Test
    fun `static write is a strong update of the static field`() {
        val inst = assigns("staticWrite").first { it.lhv is JIRFieldRef }
        val x = base(inst.rhv as JIRValue)
        val s = AccessPathBase.ClassStatic
        assertEquals(setOf(
            Edge(p(s).exclude(classStatic), p(s)),
            Edge(p(s, classStatic).exclude(staticField), p(s, classStatic)),
            Edge(p(x), p(x)),
            Edge(p(x), p(s, classStatic, staticField)),
        ), edges(inst))
    }

    @Test
    fun `array read is split like a field read`() {
        val inst = assigns("arrayRead").first { it.rhv is JIRArrayAccess }
        val x = base(inst.lhv)
        val y = base((inst.rhv as JIRArrayAccess).array)
        assertEquals(setOf(
            Edge(p(y).exclude(ElementAccessor), p(y)),
            Edge(p(y, ElementAccessor), p(y, ElementAccessor)),
            Edge(p(y, ElementAccessor), p(x)),
        ), edges(inst))
    }

    @Test
    fun `array write is weak`() {
        val inst = assigns("arrayWrite").first { it.lhv is JIRArrayAccess }
        val y = base((inst.lhv as JIRArrayAccess).array)
        val x = base(inst.rhv as JIRValue)
        assertEquals(setOf(
            Edge(p(y), p(y)),
            Edge(p(x), p(x)),
            Edge(p(x), p(y, ElementAccessor)),
        ), edges(inst))
    }

    @Test
    fun `self write moves the old value into the field`() {
        val inst = assigns("selfWrite").first { it.lhv is JIRFieldRef }
        val a = base(inst.rhv as JIRValue)
        assertEquals(setOf(
            Edge(p(a).exclude(field), p(a)),
            Edge(p(a), p(a, field)),
        ), edges(inst))
    }

    @Test
    fun `self read keeps only the read field and refines the overwritten instance`() {
        val fieldRead = assigns("selfRead").first { (it.rhv as? JIRFieldRef)?.field?.name == "next" }
        val rhv = fieldRead.rhv as JIRFieldRef
        val instance = rhv.instance!!
        val inst = JIRAssignInst(fieldRead.location, instance, rhv)
        val x = base(instance)
        assertEquals(setOf(
            Edge(p(x).exclude(next), null),
            Edge(p(x, next), p(x)),
        ), edges(inst))
    }

    @Test
    fun `cast moves the operand and filters it by the cast type`() {
        val inst = assigns("cast").first { it.rhv is JIRCastExpr }
        val x = base(inst.lhv)
        val cast = inst.rhv as JIRCastExpr
        val y = base(cast.operand)
        assertEquals(setOf(Edge(p(y), p(y)), Edge(p(y), p(x))), edges(inst))
        assertTrue(cast.type in summary(inst).find(y)?.typeFilters.orEmpty())
    }

    @Test
    fun `binary expression moves both operands`() {
        val inst = assigns("binary").first { it.rhv is JIRBinaryExpr }
        val z = base(inst.lhv)
        val bin = inst.rhv as JIRBinaryExpr
        val a = base(bin.lhv)
        val b = base(bin.rhv)
        assertEquals(setOf(
            Edge(p(a), p(a)), Edge(p(a), p(z)),
            Edge(p(b), p(b)), Edge(p(b), p(z)),
        ), edges(inst))
    }

    @Test
    fun `return moves the value to the result and kills the old result`() {
        val inst = insts("cast").filterIsInstance<JIRReturnInst>().single()
        val x = base(inst.returnValue!!)
        assertEquals(setOf(Edge(p(x), p(x)), Edge(p(x), p(AccessPathBase.Return))), edges(inst))
        assertEquals(emptyList(), summary(inst).find(AccessPathBase.Return)?.edges?.asList())
    }

    @Test
    fun `reversed field read maps the target back into the field`() {
        val inst = assigns("fieldRead").first { it.rhv is JIRFieldRef }
        val x = base(inst.lhv)
        val y = base((inst.rhv as JIRFieldRef).instance!!)
        assertEquals(setOf(p(y, field, g)), preconditions(inst, p(x, g)))
        assertEquals(setOf(p(y, g)), preconditions(inst, p(y, g)))
        assertEquals(setOf(p(y, field, g)), preconditions(inst, p(y, field, g)))
    }

    @Test
    fun `reversed field write maps the field back to the value and keeps the rest`() {
        val inst = assigns("fieldWrite").first { it.lhv is JIRFieldRef }
        val y = base((inst.lhv as JIRFieldRef).instance!!)
        val x = base(inst.rhv as JIRValue)
        assertEquals(setOf(p(x, g)), preconditions(inst, p(y, field, g)))
        assertEquals(setOf(p(y, g)), preconditions(inst, p(y, g)))
        assertEquals(setOf(p(x, g)), preconditions(inst, p(x, g)))
    }

    @Test
    fun `reversed return maps the result back to the value`() {
        val inst = insts("cast").filterIsInstance<JIRReturnInst>().single()
        val x = base(inst.returnValue!!)
        assertEquals(setOf(p(x, g)), preconditions(inst, p(AccessPathBase.Return, g)))
        assertEquals(null, preconditions(inst, p(AccessPathBase.This, g)))
    }

    @Test
    fun `reversed kill has no preconditions`() {
        val inst = insts("staticWrite").filterIsInstance<JIRReturnInst>().single()
        assertEquals(emptySet(), preconditions(inst, p(AccessPathBase.Return, g)))
    }
}
