# Discover universal boundaries

Generalize one family of known finding traces into rule-ready boundaries: a single source and a single sink that every finding in the family factors through. The boundary vocabulary — how a member is named, what carries a usage condition, which packages realize each primitive effect — is language-specific: read `references/<language>.md` per Inputs and follow its numbered steps, which key to the ones below.

The goal is not the broadest syntax that happens to match every trace. It is the most primitive semantic boundary that stays inside the vulnerability class — general enough that the family needs one rule per side, specific enough that the rule still means something. Precision is recovered afterwards with context restrictions and sanitizers, listed separately, never by narrowing the boundary back down to the findings you started from.

A boundary is only universal once it has been saturated: widened, re-checked against the whole family, and left unchanged by a full round.
