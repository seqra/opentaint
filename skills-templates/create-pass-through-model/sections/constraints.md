{% include "shared/engine/facts.md" %}

- Model one function per rule — never a regex/wildcard matcher or an all-arguments position to cover many at once; over-modeling copies taint through methods you never vetted and manufactures false positives
- Keep produced configs comment-free
