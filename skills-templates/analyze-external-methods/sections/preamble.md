# Skill: Analyze External Methods

OpenTaint is a dataflow taint analyzer: it starts from the data a source introduces and follows it call by call until the flow stops. A flow stops for one of two reasons — the data reached a method that carries it nowhere (call `size()` on a tainted collection and its whole contents collapse into one number, so the taint is gone), or it reached a method whose body the analyzer can't see, typically an external dependency. That opaque method may itself be taint-killing (e.g. the same `size()`), or it may in fact carry the data onward — and then it needs an approximation telling the engine exactly how the data moves through the call, or every trace through it is silently cut.

You are handed the list of those dropped methods. Decide which ones actually carry data and which don't, and for each carrier determine the kind of approximation it needs, so the build stage can restore the flow.

On a deep run these same methods carry a second, independent question — whether the call is itself a dangerous operation (a sink); that pass is step 2.
