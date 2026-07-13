# Skill: Create Dataflow Approximation

A dataflow approximation is code that expresses how data moves through a method the analyzer can't trace through — an opaque call where the engine loses taint because it can't see the body. You write a small stand-in that reproduces the method's real propagation from its inputs to its outputs, so the analyzer can follow taint through it. Run it against the prepared test project and refine until the sample passes.
