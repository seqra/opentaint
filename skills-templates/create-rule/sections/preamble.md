# Skill: Create Rule

{% include "shared/engine/facts.md" %}

A unit names the source or sink members to detect. Identify an existing built-in or project library rule when it already implements the boundary, otherwise author a custom rule, then verify the unit against its test project. Every selected or created source rule must carry the unit's `untrusted-data-source` tag, and every selected or created sink rule must carry its unit group's `*-sink` tag. Production joins use those tags and are assembled later only when a new sink tag needs one.
