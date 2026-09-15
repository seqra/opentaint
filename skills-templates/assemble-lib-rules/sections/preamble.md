# Skill: Assemble Lib Rules

Reusable source rules share the single `untrusted-data-source` tag. Write only the security joins that connect it to sink tags reported as uncovered by `get_status.py`. An existing join automatically includes every new library rule carrying either tag. The main scan verifies the joins.
