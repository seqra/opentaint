package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.cfg.CommonInst

/**
 * The mark-set scan's output (spec §10): the rules and actions still needed at
 * each recorded statement. Sinks map to the empty set (kept whole, never
 * restricted); sources map to their needed [CommonTaintAction] subset.
 */
typealias ActionableRules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>
