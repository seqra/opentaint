# Local work-reduction laws

These are unselected next-iteration candidates. No runtime change is made.

Run `lean C2Descendants.lean` from this directory with Lean 4.35.0. The model
checks nine local laws and four examples. It covers an empty-output branch,
ordered stream filtering and a constructive negative witness. It does not
prove the whole native C2, trie layout, loop observer or analyzer. Some list
equality laws use Lean propext. No Classical.choice or excluded middle is used.

[source-proof.md](source-proof.md) audits the native branch and its scope.
[receipt.json](receipt.json) pins the source and tested model. The examples
come from active Conductor run-8; last completed/accepted run is run-7.
