{% include "shared/engine/facts.md" %}

- One `<name>` folder per unit — never write into another unit's test project, so concurrent agents don't race
- A dataflow test project is incomplete unless every sample is classified under all four plain/starred source/sink harness rules
