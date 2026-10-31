package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.MethodKey
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst

data class SinkKey(val method: CommonMethod, val statement: CommonInst, val ruleId: String)
data class ReportDescriptor(val key: SinkKey, val rule: CommonTaintConfigurationSink,
                            val representativeMethodKey: MethodKey)

/** Stable physical sink identities. Does not retain forms or witness trees. */
class ReportCatalog {
    private val byKey = HashMap<SinkKey, ReportId>()
    private val descriptors = ArrayList<ReportDescriptor>()

    @Synchronized fun intern(key: SinkKey, rule: CommonTaintConfigurationSink, context: MethodKey): ReportId {
        check(context.method == key.method && rule.id == key.ruleId)
        return byKey.getOrPut(key) {
            ReportId(descriptors.size).also { descriptors += ReportDescriptor(key, rule, context) }
        }
    }

    @Synchronized fun descriptor(id: ReportId): ReportDescriptor = descriptors[id.value]
}
