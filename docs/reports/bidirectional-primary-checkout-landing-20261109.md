# Primary checkout landing

9 November 2026. State: **LANDED / NATIVE SUITES PASS**.

The complete implementation, tests, proofs, reports and next proposal are
integrated in the primary checkout:

    /drive-testcomp/opentaint-go-rules/opentaint-w3
    branch: saloed/bidirectional

The incoming branch ends at 5b2cae1cb8fab0e0fe8dbac94eb7fce6edac1305.
Its measured runtime is 334234c24e9008f4a2614b8213b8b2e73b6ba9e1.
The primary checkout has the exact same core tree:

    8b38a03586138acbbf5aaadd94b5fb301d6c9cad

Core conflicts are resolved with that complete tested tree. The earlier
committed experimental implementation is superseded. Current specifications,
historical reports and formal evidence from the primary branch are retained.
No runtime behavior is changed as part of this landing. Existing project
timeouts and strict finding differences remain documented in the
[performance report](bidirectional-subsumption-initial-demand-performance-20261108.md).

## Preserved local work

Before integration, the primary checkout had 45 modified tracked files and
694 untracked files. The tracked patch and source copies were backed up.
All untracked file hashes were recorded. The four withdrawn prototype tests
and the two generated debug directories were moved out of the checkout.
The backup was verified before the prototype was removed from the active tree.

Backup location:

    /drive-testcomp/opentaint-go-rules/subsumption-initial-demand-20261108/main-checkout-backup-20261109T084552Z

The backup contains backup.json, tracked.patch, index.patch, status-before.txt
and the saved files. The original committed state is also retained as branch
backup/pre-main-land-20261109t084552z, at
2e29a55c3cce8d54516a09f9976752e4c561087e.

Existing formal-analysis sources, memory-diagnostic scripts and the local
dated issue note are retained in commit 5f4dd1d79. They are source artifacts,
not new runtime changes. Python syntax and all four XML templates were checked.
Generated debug binaries and ignored formal build outputs are not committed.

## Validation

Run both native suites directly from the primary checkout:

    cd core
    ./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
      :opentaint-dataflow-core:opentaint-jvm-dataflow:test \
      --offline --no-daemon --max-workers=2 --console=plain

The primary-checkout run passes **2,510 common-core and 461 JVM tests**, with
zero failures, errors or skips. The full command finishes successfully in
3 minutes 50 seconds. The [verification receipt](data/bidirectional-primary-checkout-landing-20261109.json)
records the XML hashes, backup manifest hash and exact source-tree check.

At landing, the project campaign was not repeated: its measured core and the
landed core have identical Git trees. The later
[post-merge validation](bidirectional-post-merge-project-validation-20261109.md)
reruns Stirling-PDF, Conductor and Thingsboard with the saved settings. All
three preserve the exact accepted findings and locations. This landing does
not implement any of the next-iteration optimizations.
