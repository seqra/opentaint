package org.opentaint.dataflow.bidi.engine

import mu.KLogging
import org.opentaint.dataflow.bidi.ap.*
import java.util.IdentityHashMap
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicLong

/** Bounded diagnostic text only. The normal campaign leaves these properties unset. */
internal object LoopPipelineTrace {
    private val logger = object : KLogging() {}.logger
    private val recorder by lazy {
        val method = System.getProperty("org.opentaint.bidi.loopTraceMethod")
        val run = System.getProperty("org.opentaint.bidi.loopTraceRun")?.toIntOrNull()
        val limit = System.getProperty("org.opentaint.bidi.loopTraceLimit", "128").toIntOrNull()
        val settings = if (!method.isNullOrEmpty() && run != null && run > 0 && limit != null && limit > 0)
            Settings(method, run, minOf(limit, 4096)) else null
        Recorder(settings) { logger.info { it } }
    }

    fun enabled(run: Int, method: MethodKey): Boolean = recorder.enabled(run) && recorder.matches(method.toString())

    fun record(run: Int, method: MethodKey, stage: String, write: Fields.() -> Unit) =
        recorder.record(run, method.toString(), stage, write)

    fun finishRun(run: Int) = recorder.finishRun(run)

    internal data class Settings(val method: String, val run: Int, val limit: Int,
                                 val maxChars: Int = 65536, val maxNodes: Int = 4096) {
        init { require(run > 0 && limit in 1..4096 && maxChars >= 128 && maxNodes > 0) }
    }

    internal data class Counts(val attempted: Long, val emitted: Long, val oversized: Long,
                               val limitDropped: Long, val errors: Long, val sinkErrors: Long)

    internal class Recorder(private val settings: Settings?, private val sink: (String) -> Unit) {
        private val attempted = AtomicLong()
        private val emitted = AtomicLong()
        private val oversized = AtomicLong()
        private val limitDropped = AtomicLong()
        private val errors = AtomicLong()
        private val sinkErrors = AtomicLong()
        private val finished = AtomicBoolean()

        fun enabled(run: Int): Boolean = settings?.run == run
        fun matches(method: String): Boolean = settings?.method == method
        fun snapshot(): Counts = Counts(attempted.get(), emitted.get(), oversized.get(), limitDropped.get(),
            errors.get(), sinkErrors.get())

        fun record(run: Int, method: String, stage: String, write: Fields.() -> Unit) {
            val config = settings ?: return
            if (run != config.run || method != config.method) return
            val sequence = attempted.incrementAndGet()
            if (sequence > config.limit) { limitDropped.incrementAndGet(); return }
            try {
                val fields = Fields(config.maxChars, config.maxNodes)
                fields.number("run", run)
                fields.text("method", method)
                fields.text("stage", stage)
                fields.number("sequence", sequence)
                fields.number("nanoTime", System.nanoTime())
                fields.write()
                val line = fields.finish()
                if (emit("BIDI_LOOP_PIPELINE_TRACE $line")) emitted.incrementAndGet()
            } catch (_: Oversized) {
                oversized.incrementAndGet()
                emit("BIDI_LOOP_PIPELINE_TRACE_DROP run=$run sequence=$sequence reason=OVERSIZED counts=${snapshot()}")
            } catch (error: RuntimeException) {
                errors.incrementAndGet()
                emit("BIDI_LOOP_PIPELINE_TRACE_DROP run=$run sequence=$sequence reason=${error.javaClass.name} counts=${snapshot()}")
            }
        }

        fun finishRun(run: Int) {
            if (enabled(run) && finished.compareAndSet(false, true))
                emit("BIDI_LOOP_PIPELINE_TRACE_STATS run=$run method=${settings!!.method} limit=${settings.limit} " +
                    "maxChars=${settings.maxChars} maxNodes=${settings.maxNodes} counts=${snapshot()}")
        }

        private fun emit(line: String): Boolean {
            return try { sink(line); true } catch (_: RuntimeException) { sinkErrors.incrementAndGet(); false }
        }
    }

    private class Oversized : RuntimeException(null, null, false, false)

    /** Immediate serialization; never retains an AP, premise, node or manager after record returns. */
    internal class Fields internal constructor(private val maxChars: Int, private val maxNodes: Int) {
        private val out = StringBuilder().append('{')
        private val names = HashSet<String>()
        private val nodeIds = IdentityHashMap<TrieNode<*>, Int>()
        private val nodes = ArrayList<TrieNode<*>>()
        private val fieldIds = LinkedHashSet<Int>()
        private val markIds = LinkedHashSet<Int>()
        private var manager: ApManager? = null
        private var first = true

        fun catalog(ap: ApManager) {
            require(manager == null || manager === ap) { "Mixed trace catalogs" }
            manager = ap
        }
        fun text(name: String, value: String) { key(name); string(value) }
        fun number(name: String, value: Number) { key(name); append(value.toString()) }
        fun flag(name: String, value: Boolean) { key(name); append(value.toString()) }
        fun pattern(name: String, value: Pattern) { key(name); patternValue(value) }

        fun premise(name: String, value: PremiseKey) {
            key(name); append("{\"kind\":"); string(if (value.isZero) "ZERO" else if (value is PremiseSet) "ND" else "INITIAL")
            append(",\"members\":[")
            for (index in 0 until value.size) {
                if (index != 0) append(",")
                val member = value.member(index)
                catalog(member.manager)
                append("{\"id\":"); append(member.id.toString()); append(",\"baseType\":"); string(member.base.javaClass.name)
                append(",\"base\":"); string(member.base.toString()); append(",\"path\":"); fields(member.pathData)
                append(",\"tail\":"); string(member.tail.name); append(",\"E\":"); exclusion(member.exclusion)
                append(",\"mark\":"); mark(member.mark); append("}")
            }
            append("]}")
        }

        fun facts(name: String, value: Facts) {
            key(name); append("{\"kind\":"); string(when (value) { is Reach -> "REACH"; is FlowTree -> "FLOW"; is TaintTree -> "TAINT" })
            append(",\"baseType\":"); string(value.base.javaClass.name); append(",\"base\":"); string(value.base.toString())
            append(",\"layer\":"); string(value.layer.name)
            when (value) {
                is Reach -> append(",\"tail\":\"EXACT\",\"root\":null,\"protection\":null")
                is FlowTree -> {
                    append(",\"tail\":"); string(value.tail.name); append(",\"E\":"); exclusion(value.exclusion)
                    append(",\"mx\":"); marks(value.markExclusion.data)
                    append(",\"root\":"); append(node(value.root).toString()); append(",\"protection\":null")
                }
                is TaintTree -> {
                    append(",\"tail\":"); string(value.anyTail.name); append(",\"E\":"); exclusion(value.exclusion)
                    append(",\"root\":"); append(node(value.root).toString()); append(",\"protection\":")
                    append(value.nonSubsumable?.let { node(it).toString() } ?: "null")
                }
            }
            append("}")
        }

        private fun patternValue(value: Pattern) {
            append("{\"baseType\":"); string(value.fact.base.javaClass.name)
            append(",\"base\":"); string(value.fact.base.toString()); append(",\"path\":[")
            for ((index, accessor) in value.fact.path.withIndex()) {
                if (index != 0) append(","); append(accessor.toString()); fieldIds += accessor
            }
            append("],\"tail\":"); string(value.fact.tail.name); append(",\"E\":"); exclusion(value.exclusion)
            append(",\"mark\":"); mark(value.fact.mark); append("}")
        }

        private fun mark(value: MarkSlot) {
            when (value) {
                is MarkSlot.Concrete -> { append("{\"kind\":\"CONCRETE\",\"id\":"); append(value.mark.id.toString()); markIds += value.mark.id; append("}") }
                is MarkSlot.Star -> { append("{\"kind\":\"FLOW\",\"mx\":"); marks(value.excluded.data); append("}") }
            }
        }
        private fun exclusion(value: ExclusionSet) = fields((value as? ExclusionSet.Concrete)?.data ?: EMPTY_PATH)
        private fun fields(values: IntArray) = ints(values, fieldIds)
        private fun marks(values: IntArray) = ints(values, markIds)
        private fun ints(values: IntArray, dictionary: MutableSet<Int>) {
            append("[")
            for (index in values.indices) {
                if (index != 0) append(","); append(values[index].toString()); dictionary += values[index]
            }
            append("]")
        }

        private fun node(value: TrieNode<*>): Int {
            nodeIds[value]?.let { return it }
            if (nodes.size == maxNodes) throw Oversized()
            val id = nodes.size; nodeIds[value] = id; nodes += value; return id
        }

        internal fun finish(): String {
            key("nodes"); append("[")
            var index = 0
            while (index < nodes.size) {
                if (index != 0) append(",")
                val value = nodes[index]
                append("{\"id\":"); append(index.toString())
                when (val leaf = value.leaf) {
                    is FlowLeaf -> { append(",\"flowLeaf\":"); append((leaf == FlowLeaf.LEAF).toString()) }
                    is TaintLeaves -> { append(",\"exact\":"); marks(leaf.exact.data); append(",\"any\":"); marks(leaf.any.data) }
                }
                append(",\"children\":[")
                val accessors = value.accessorData
                if (accessors != null) for (child in accessors.indices) {
                    if (child != 0) append(",")
                    append("{\"field\":"); append(accessors[child].toString()); fieldIds += accessors[child]
                    append(",\"node\":"); append(node(value.childData!![child]).toString()); append("}")
                }
                append("]}"); index++
            }
            append("]")
            val ap = manager
            key("catalogIncluded"); append((ap != null).toString())
            if (ap != null) {
                key("fields"); append("[")
                for ((ordinal, id) in fieldIds.withIndex()) {
                    if (ordinal != 0) append(",")
                    append("{\"id\":"); append(id.toString()); append(",\"name\":"); string(ap.accessors.accessor(id).toString()); append("}")
                }
                append("]"); key("marks"); append("[")
                for ((ordinal, id) in markIds.withIndex()) {
                    if (ordinal != 0) append(",")
                    val mark = TaintMark(id)
                    append("{\"id\":"); append(id.toString()); append(",\"name\":"); string(ap.marks.name(mark))
                    append(",\"key\":"); string(ap.marks.key(mark).toString()); append("}")
                }
                append("]")
            }
            append("}"); return out.toString()
        }

        private fun key(name: String) {
            require(names.add(name)) { "Duplicate trace field" }
            if (!first) append(",") else first = false
            string(name); append(":")
        }
        private fun string(value: String) {
            append("\"")
            for (character in value) when (character) {
                '"' -> append("\\\"")
                '\\' -> append("\\\\")
                '\n' -> append("\\n")
                '\r' -> append("\\r")
                '\t' -> append("\\t")
                else -> if (character.code < 32) append("\\u" + character.code.toString(16).padStart(4, '0')) else append(character.toString())
            }
            append("\"")
        }
        private fun append(value: String) {
            if (out.length + value.length > maxChars) throw Oversized()
            out.append(value)
        }
    }
}
