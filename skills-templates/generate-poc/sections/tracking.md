This skill writes only the finding's `poc` (`confirmed` / `failed`) and the outcome appended to `notes`; it never changes `verdict` or the other finding fields. When it starts an app instance it appends one entry to the server registry, and stops there — teardown isn't its job.

{% include "shared/tracking/findings.md" %}

{% include "shared/tracking/poc-servers.md" %}
