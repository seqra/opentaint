
### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.passthrough.PassthroughValueFlowSamples#stringBuilderAppendUnsafe
end run=9 COMPLETE/NO_DEMAND_EDGE elapsed=0.071578565 final confirmed=1 provisional=0 totalEngine=0.06s lastGain=run-1
  Q2: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
  Q1p: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
  REPEAT: never fires
  REPEAT_loose: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.01 | 1 | 1 | 1 | 1 | 1 | 0 | 0 |  |
| 2 | B | 1 | COMPLETE | 0.01 | 1 | 2 | 1 | 1 | 2 | 0 | 0 | 2 |
| 3 | F | 2 | COMPLETE | 0.01 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 1 |
| 4 | B | 3 | COMPLETE | 0.01 | 1 | 2 | 1 | 1 | 2 | 0 | 0 | 2 |
| 5 | F | 4 | COMPLETE | 0.01 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 1 |
| 6 | B | 5 | COMPLETE | 0.00 | 1 | 2 | 1 | 1 | 2 | 0 | 0 | 2 |
| 7 | F | 6 | COMPLETE | 0.01 | 1 | 1 | 1 | 1 | 1 | 0 | 0 | 1 |
| 8 | B | 7 | COMPLETE | 0.00 | 1 | 2 | 1 | 1 | 2 | 0 | 0 | 2 |
| 9 | F | 8 | COMPLETE | 0.01 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.passthrough.PassthroughValueFlowSamples#facesSelectItemGroupUnsafe
end run=5 COMPLETE/NO_DEMAND_EDGE elapsed=0.016675998 final confirmed=1 provisional=0 totalEngine=0.01s lastGain=run-5
  Q2: never fires
  Q1p: never fires
  REPEAT: never fires
  REPEAT_loose: never fires
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.01 | 0 | 1 | 1 | 1 | 1 | 0 | 0 |  |
| 2 | B | 1 | COMPLETE | 0.00 | 0 | 2 | 1 | 1 | 2 | 0 | 0 | 2 |
| 3 | F | 2 | COMPLETE | 0.00 | 0 | 1 | 1 | 1 | 1 | 0 | 0 | 1 |
| 4 | B | 3 | COMPLETE | 0.00 | 0 | 2 | 1 | 1 | 2 | 0 | 0 | 2 |
| 5 | F | 4 | COMPLETE | 0.00 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.passthrough.PassthroughContainerSamples#listIterateUnsafe
end run=5 COMPLETE/NO_DEMAND_EDGE elapsed=0.08545913100000001 final confirmed=1 provisional=0 totalEngine=0.08s lastGain=run-3
  Q2: never fires
  Q1p: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s (=natural end)
  REPEAT: never fires
  REPEAT_loose: never fires
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.03 | 0 | 9 | 1 | 3 | 1 | 0 | 0 |  |
| 2 | B | 1 | COMPLETE | 0.01 | 0 | 14 | 1 | 1 | 0 | 0 | 0 | 14 |
| 3 | F | 2 | COMPLETE | 0.01 | 1 | 3 | 1 | 3 | 1 | 0 | 0 | 3 |
| 4 | B | 3 | COMPLETE | 0.01 | 1 | 6 | 1 | 1 | 0 | 0 | 0 | 6 |
| 5 | F | 4 | COMPLETE | 0.01 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.passthrough.PassthroughContainerSamples#mapEntryUnsafe
end run=7 COMPLETE/NO_DEMAND_EDGE elapsed=0.119229193 final confirmed=1 provisional=0 totalEngine=0.11s lastGain=run-5
  Q2: never fires
  Q1p: run-7 count=1 loss=0 savedEngine=0.0s savedWall=0.0s (=natural end)
  REPEAT: never fires
  REPEAT_loose: never fires
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.02 | 0 | 14 | 1 | 3 | 1 | 0 | 0 |  |
| 2 | B | 1 | COMPLETE | 0.02 | 0 | 24 | 1 | 2 | 2 | 0 | 0 | 24 |
| 3 | F | 2 | COMPLETE | 0.05 | 0 | 3 | 1 | 3 | 1 | 0 | 0 | 3 |
| 4 | B | 3 | COMPLETE | 0.01 | 0 | 14 | 1 | 1 | 0 | 0 | 0 | 14 |
| 5 | F | 4 | COMPLETE | 0.01 | 1 | 3 | 1 | 3 | 1 | 0 | 0 | 3 |
| 6 | B | 5 | COMPLETE | 0.01 | 1 | 6 | 1 | 1 | 0 | 0 | 0 | 6 |
| 7 | F | 6 | COMPLETE | 0.01 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.externalconfigurationcontrol.BeanInjectionSamples#doPost
end run=7 COMPLETE/NO_DEMAND_EDGE elapsed=0.077336864 final confirmed=1 provisional=0 totalEngine=0.07s lastGain=run-5
  Q2: never fires
  Q1p: run-7 count=1 loss=0 savedEngine=0.0s savedWall=0.0s (=natural end)
  REPEAT: never fires
  REPEAT_loose: never fires
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.02 | 0 | 18 | 1 | 2 | 1 | 0 | 0 |  |
| 2 | B | 1 | COMPLETE | 0.01 | 0 | 41 | 1 | 1 | 0 | 0 | 0 | 41 |
| 3 | F | 2 | COMPLETE | 0.02 | 0 | 3 | 1 | 3 | 1 | 0 | 0 | 3 |
| 4 | B | 3 | COMPLETE | 0.00 | 0 | 6 | 1 | 1 | 0 | 0 | 0 | 6 |
| 5 | F | 4 | COMPLETE | 0.00 | 1 | 2 | 1 | 2 | 1 | 0 | 0 | 2 |
| 6 | B | 5 | COMPLETE | 0.00 | 1 | 4 | 1 | 1 | 0 | 0 | 0 | 4 |
| 7 | F | 6 | COMPLETE | 0.00 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.pathtraversal.PathTraversalServletSamples$UnsafeCookieDownloadServlet#doGet
end run=5 COMPLETE/NO_DEMAND_EDGE elapsed=0.07415938300000001 final confirmed=3 provisional=0 totalEngine=0.07s lastGain=run-3
  Q2: never fires
  Q1p: run-5 count=3 loss=0 savedEngine=0.0s savedWall=0.0s (=natural end)
  REPEAT: never fires
  REPEAT_loose: never fires
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.03 | 0 | 11 | 2 | 4 | 5 | 0 | 1 |  |
| 2 | B | 1 | COMPLETE | 0.01 | 0 | 18 | 2 | 1 | 0 | 0 | 0 | 18 |
| 3 | F | 2 | COMPLETE | 0.02 | 3 | 6 | 2 | 6 | 3 | 5 | 1 | 6 |
| 4 | B | 3 | COMPLETE | 0.01 | 3 | 8 | 2 | 1 | 0 | 0 | 0 | 8 |
| 5 | F | 4 | COMPLETE | 0.01 | 3 | 0 | 0 | 0 | 0 | 9 | 1 | 0 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.pathtraversal.PathTraversalServletSamples$UnsafeFileUploadServlet#doPost
end run=11 COMPLETE/RUN_LIMIT elapsed=0.344661931 final confirmed=1 provisional=0 totalEngine=0.33s lastGain=run-3
  Q2: run-7 count=1 loss=0 savedEngine=0.1s savedWall=0.1s
  Q1p: run-5 count=1 loss=0 savedEngine=0.2s savedWall=0.2s
  REPEAT: run-9 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
  REPEAT_loose: run-9 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.03 | 0 | 17 | 2 | 5 | 3 | 0 | 1 |  |
| 2 | B | 1 | COMPLETE | 0.02 | 0 | 64 | 2 | 1 | 0 | 8 | 0 | 64 |
| 3 | F | 2 | COMPLETE | 0.06 | 1 | 28 | 2 | 25 | 3 | 57 | 1 | 28 |
| 4 | B | 3 | COMPLETE | 0.02 | 1 | 28 | 2 | 1 | 0 | 1 | 0 | 28 |
| 5 | F | 4 | COMPLETE | 0.05 | 1 | 26 | 2 | 27 | 3 | 48 | 1 | 26 |
| 6 | B | 5 | COMPLETE | 0.03 | 1 | 26 | 2 | 1 | 0 | 0 | 0 | 26 |
| 7 | F | 6 | COMPLETE | 0.06 | 1 | 26 | 2 | 27 | 3 | 40 | 1 | 26 |
| 8 | B | 7 | COMPLETE | 0.01 | 1 | 26 | 2 | 1 | 0 | 0 | 0 | 26 |
| 9 | F | 8 | COMPLETE | 0.02 | 1 | 26 | 2 | 27 | 3 | 40 | 1 | 26 |
| 10 | B | 9 | COMPLETE | 0.01 | 1 | 26 | 2 | 1 | 0 | 0 | 0 | 26 |
| 11 | F | 10 | COMPLETE | 0.02 | 1 | 26 | 2 | 27 | 3 | 40 | 1 | 26 |

### [NATIVE-Nov12-472288cf] work-reduction-20261112/rules security.passthrough.PassthroughFileModelSamples#fileToStringUnsafe
end run=11 COMPLETE/RUN_LIMIT elapsed=0.037259867 final confirmed=1 provisional=0 totalEngine=0.03s lastGain=run-1
  Q2: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
  Q1p: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
  REPEAT: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
  REPEAT_loose: run-5 count=1 loss=0 savedEngine=0.0s savedWall=0.0s
| run | dir | K | status | engine s | reports | demand rows | keys | target demand | seeds | crossings | analysed | compaction rows |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F | 1 | COMPLETE | 0.01 | 1 | 1 | 1 | 1 | 3 | 0 | 0 |  |
| 2 | B | 1 | COMPLETE | 0.01 | 1 | 2 | 1 | 1 | 18 | 0 | 0 | 2 |
| 3 | F | 2 | COMPLETE | 0.00 | 1 | 1 | 1 | 1 | 3 | 0 | 0 | 1 |
| 4 | B | 3 | COMPLETE | 0.00 | 1 | 2 | 1 | 1 | 18 | 0 | 0 | 2 |
| 5 | F | 4 | COMPLETE | 0.00 | 1 | 1 | 1 | 1 | 3 | 0 | 0 | 1 |
| 6 | B | 5 | COMPLETE | 0.00 | 1 | 2 | 1 | 1 | 18 | 0 | 0 | 2 |
| 7 | F | 6 | COMPLETE | 0.00 | 1 | 1 | 1 | 1 | 3 | 0 | 0 | 1 |
| 8 | B | 7 | COMPLETE | 0.00 | 1 | 2 | 1 | 1 | 18 | 0 | 0 | 2 |
| 9 | F | 8 | COMPLETE | 0.00 | 1 | 1 | 1 | 1 | 3 | 0 | 0 | 1 |
| 10 | B | 9 | COMPLETE | 0.00 | 1 | 2 | 1 | 1 | 18 | 0 | 0 | 2 |
| 11 | F | 10 | COMPLETE | 0.00 | 1 | 1 | 1 | 1 | 3 | 0 | 0 | 1 |
