package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.cfg.CommonInst

typealias ActionableRules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>
