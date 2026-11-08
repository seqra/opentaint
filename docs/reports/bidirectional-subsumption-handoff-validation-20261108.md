# Restricted FLOW demand handoff validation

8 November 2026. The first real-project attempt at e1838296f exposed an
old ANY-only handoff assertion. Conductor reached and engine-completed
**run-3**, but committed only **run-2**; its accepted report remained
**run-1**. The run-3 barrier failed with:

    IllegalStateException:
    A restricted FLOW demand result must be ANY with empty field exclusions

OWASP completed and accepted **run-5**, with 4,112 reported entries.
Its initial run-1 engine time was 84.796 seconds. Exact final quality and
performance comparisons use the repaired runtime. Thingsboard was stopped
by the owner when the Conductor error was found. Stirling-PDF did not start.
This initial attempt is not a completed four-project campaign.

## Cause and correction

The selected C5 table preserves a correlated STAR on DEMAND. It can also
select EXACT/FLOW from ANY/FLOW on DEMAND; summary normalization then
produces STAR/FLOW on DEMAND. The old validators still assumed that only
ANY/FLOW could leave a restricted run.

The repair aligns four validators with the selected contract. It keeps the
candidate, its support layer, both demand endpoints and physical block ports.
It reuses guidance normalization. It adds no transfer, admission, widening,
source permission or stopping rule.

The new native regression traces:

    raw candidate:            P/FLOW -> ret.ANY/FLOW, DEMAND
    paired exact selector:   P/FLOW -> ret.EXACT/FLOW, DEMAND
    normalized publication:  P/FLOW -> ret.STAR/FLOW, DEMAND
    next demand:             ret.STAR/FLOW -> P/FLOW

A second path checks an already correlated STAR with field exclusions.
Both method and block handoff are checked in both direction transitions.
The C2 rule that rejects deeper inputs under a later precise STAR demand
stays unchanged.

## Evidence

The full checks pass **2,510 common-core tests and 461 JVM tests**, with no
failures, errors or skips. The 1,245 pinned constructive declarations pass.
Sixteen additional bridge proofs check format and paired-row preservation.
They do not prove the complete native analyzer or universal convergence.

The initial attempt metadata and error are retained under the campaign
directory. All owned initial-attempt processes were verified stopped.
The repaired runtime was committed, packaged and measured on all four fixed
FULL/16 GiB configurations. Latest reached / committed / accepted: OWASP
run-5 / run-5 / run-5; Conductor run-14 / run-13 / run-13; Thingsboard
run-2 / run-1 / run-1; Stirling run-52 / run-51 / run-51. See the
[final report](bidirectional-subsumption-initial-demand-performance-20261108.md).
