# External report data

Report-data directories larger than 10 MB in total are kept outside the repository.
The complete `docs/reports/data/` directory was archived on 12 November 2026.
Reports, figures and design documents remain in the repository.

The archive is a sibling of this checkout:

```text
../report-data-archive/opentaint-w3/
    archive-manifest.json
    inventory.jsonl
    docs/reports/data/...
```

The [archive record](external-data.json) gives the absolute local path, file
count, byte total and inventory hash. The external inventory records the
original path, size and SHA-256 of every file. The archive also preserves
the original Git index entries and staged diff.

Evidence links in existing reports keep their original `data/...` paths.
Restore a local copy when those links or campaign tools are needed. From the
repository root, with `docs/reports/data` absent:

```sh
cp -a ../report-data-archive/opentaint-w3/docs/reports/data docs/reports/data
```

The restored directory remains ignored by Git. Transfer the external archive
separately when another checkout needs the evidence. The archive move does
not rewrite existing Git history.

## Termination experiment sources

The sibling archive's `docs/reports/data/bidirectional-experiment-sources-20261118/`
preserves the exploratory sources and their original paths. Its
`inventory.json` records file sizes and SHA-256 hashes. The Gradle
test source set contains the maintained native regressions.

To restore the archived source links locally:

```sh
mkdir -p docs/reports/data
cp -a ../report-data-archive/opentaint-w3/docs/reports/data/bidirectional-experiment-sources-20261118 docs/reports/data/
```

For a historical command that uses `scripts/demand_campaign/` or
`scripts/demand_experiments/`, recover the relevant source group at
its original path in a scratch checkout of the report's recorded
revision. Reuse the report's recorded inputs and build settings.
