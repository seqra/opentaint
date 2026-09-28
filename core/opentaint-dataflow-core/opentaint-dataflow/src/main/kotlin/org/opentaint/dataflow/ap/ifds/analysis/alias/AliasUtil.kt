package org.opentaint.dataflow.ap.ifds.analysis.alias

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.alias.LocalAliasAnalysis.CommonAliasApInfo
import org.opentaint.ir.api.common.cfg.CommonInst

inline fun <AliasInfo, AliasAccessor> LocalAliasAnalysis<AliasInfo, AliasAccessor>.forEachAliasAtStatement(
    statement: CommonInst,
    fact: FinalFactAp,
    relevantAlias: AliasInfo.() -> CommonAliasApInfo<AliasAccessor>?,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (FinalFactAp) -> Unit
) = forEachAliasAtStatement(statement, fact) { fact, alias ->
    alias.relevantAlias()?.let {
        applyAlias(fact, it, apAccessor, body)
    }
}

inline fun <AliasInfo, AliasAccessor> LocalAliasAnalysis<AliasInfo, AliasAccessor>.forEachAliasAtStatement(
    statement: CommonInst,
    fact: InitialFactAp,
    relevantAlias: AliasInfo.() -> CommonAliasApInfo<AliasAccessor>?,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (InitialFactAp) -> Unit
) = forEachAliasAtStatement(statement, fact) { fact, alias ->
    alias.relevantAlias()?.let {
        applyAlias(fact, it, apAccessor, body)
    }
}

fun <AliasInfo, AliasAccessor> LocalAliasAnalysis<AliasInfo, AliasAccessor>.forEachHeapAliasBeforeStatement(
    statement: CommonInst,
    fact: FinalFactAp,
    aliasAccessor: Accessor.() -> AliasAccessor?,
    relevantAlias: AliasInfo.() -> CommonAliasApInfo<AliasAccessor>?,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (FinalFactAp) -> Unit
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    forEachHeapAlias(base, statement, fact, { f ->
        val next = mutableListOf<Pair<AliasAccessor, FinalFactAp>>()
        val accessors = f.getStartAccessors()
        for (accessor in accessors) {
            val aa = accessor.aliasAccessor() ?: continue
            val nexFact = f.readAccessor(accessor) ?: continue
            next.add(aa to nexFact)
        }
        next
    }) { alias, f ->
        alias.relevantAlias()?.let {
            applyAlias(f, it, apAccessor, body)
        }
    }
}

inline fun <F : FactAp, AliasInfo, AliasAccessor> LocalAliasAnalysis<AliasInfo, AliasAccessor>.forEachAliasAtStatement(
    statement: CommonInst,
    fact: F,
    applyAlias: (F, AliasInfo) -> Unit
) {
    val base = fact.base as? AccessPathBase.LocalVar ?: return
    val aliases = findAlias(base, statement) ?: return
    aliases.forEach { applyAlias(fact, it) }
}

inline fun <AliasInfo, AliasAccessor> LocalAliasAnalysis<AliasInfo, AliasAccessor>.forEachAliasAtStatementAmongBases(
    statement: CommonInst,
    fact: InitialFactAp,
    bases: List<AccessPathBase.LocalVar>,
    relevantAlias: AliasInfo.() -> CommonAliasApInfo<AliasAccessor>?,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (InitialFactAp) -> Unit
) {
    bases.forEach { base ->
        val aliases = findAlias(base, statement) ?: return@forEach
        aliases.forEach { alias ->
            alias.relevantAlias()?.let {
                unapplyAlias(fact, base, it, apAccessor, body)
            }
        }
    }
}

inline fun <AliasAccessor> applyAlias(
    fact: FinalFactAp,
    alias: CommonAliasApInfo<AliasAccessor>,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (FinalFactAp) -> Unit
) {
    val result = alias.accessors.foldRight(fact.rebase(alias.base)) { accessor, f ->
        val apAccessor = accessor.apAccessor()
        f.prependAccessor(apAccessor)
    }

    body(result)
}

inline fun <AliasAccessor> applyAlias(
    fact: InitialFactAp,
    alias: CommonAliasApInfo<AliasAccessor>,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (InitialFactAp) -> Unit
) {
    val result = alias.accessors.foldRight(fact.rebase(alias.base)) { accessor, f ->
        val apAccessor = accessor.apAccessor()
        f.prependAccessor(apAccessor)
    }

    body(result)
}

inline fun <AliasAccessor> unapplyAlias(
    fact: InitialFactAp,
    newBase: AccessPathBase.LocalVar,
    alias: CommonAliasApInfo<AliasAccessor>,
    apAccessor: AliasAccessor.() -> Accessor,
    body: (InitialFactAp) -> Unit
) {
    if (alias.base != fact.base) {
        return
    }

    val result = alias.accessors.fold(fact.rebase(newBase)) { f, accessor ->
        val apAccessor = accessor.apAccessor()
        f.readAccessor(apAccessor) ?: return
    }

    body(result)
}
