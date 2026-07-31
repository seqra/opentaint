This skill writes only the test-project stage back:

- a rule side → `stages.test_project: done` in the source or sink unit
- a dataflow approximation → one `build.test_project` entry per method in the batch file, `status: done` for a method whose sample made it into the project, `status: failed` for one no sample could be written for (excluded)

{% include "shared/tracking/source-unit.md" %}

{% include "shared/tracking/sink-unit.md" %}

{% include "shared/tracking/approximations-batch.md" %}
