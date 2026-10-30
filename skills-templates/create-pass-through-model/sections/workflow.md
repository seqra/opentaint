### 1. Understand the propagation

Take the batch's `passthrough` methods not yet in `build.done` (or the specific `methods` you were handed) and study each from its real code: read the source (per the language reference). Model each method purely from what its own code does, **independent** of how the project uses it — the config describes the method's intrinsic propagation. Answer: where does the input data go? Data that arrives on the receiver or an argument — does it come back out, through the return value, an argument the method writes into, the receiver, or an object or field it stores into? Note too whether the object holds the data between calls (a setter stashes it and a getter hands it back later, or a builder accumulates it) — that needs a virtual field. That shape is what the config expresses.

### 2. Write the config

Write one passThrough config per package under `.opentaint/pass-through` (the format and patterns are in the language reference). A method already in `build.done` and not explicitly handed in `methods` is built and trusted — leave it and its config as-is. Repair an explicitly handed method in its existing config; add a new method to its existing package config rather than rewriting the file. Two ideas drive the copy:

- Cover every position — `this` and each argument: copy each to where its data flows, or to itself when it flows nowhere
- When the data lives in the object between calls, route the writer and the reader through a shared virtual field — a nominal storage location both name identically. What the writer stashes there is what the reader pulls back, if the two name it differently, the taint is lost.

### 3. Re-check your configs

Before returning, confirm you wrote a passThrough for every method you were to model, and that each config's copies actually match how the method moves data in its source — every position covered, and a writer and its reader sharing the identical virtual field. Append each written method not already present to `build.done` (per Tracking); a repaired method remains recorded there.
