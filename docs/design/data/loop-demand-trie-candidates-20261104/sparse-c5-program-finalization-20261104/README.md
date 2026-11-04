# Sparse C5 finalization conditional delta

UNSELECTED EXTERNAL CANDIDATE. No Kotlin implementation or native test receipt.

The model uses exact ordered protected/plain bucket streams and annotated output
identities. It proves sparse sorted-key finalization equal to dense finalization
under an explicit exact sparse-key permutation invariant and the unchanged native
emitter. An executable certificate detects omitted/duplicate program ordinals;
that dense reference certificate is for testing, not proposed hot-path work.

The model does not prove the native hash table, bucket collector, AP packer,
header interpretation, actual allocation bytes or performance. These remain
explicit adapter and native RED/GREEN obligations in the candidate note.

Run `python3 check.py`. The standalone compiler uses Lean 4.33.1, one worker and a
768 MiB budget. Every explicit declaration is audited; only propext and Quot.sound
are permitted. No Classical.choice, sorry or native-decide axiom is accepted.
