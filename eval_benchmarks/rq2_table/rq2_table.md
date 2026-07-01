# RQ2: acyclic-κ elimination — zap vs grind vs aesop

Headline metric: `elim_hb` = heartbeats spent in the acyclic-κ elimination step only (residual VC left as `all_goals sorry`). Parenthesised `×` is slowdown relative to `zap` (fusion).

| VC | suite | zap | grind | aesop |
|---|---|--:|--:|--:|
| `AnfBin_proof` | flux-med | 80 | 2854 (36×) | 717 (9×) |
| `AnfImpl__0__IsAnf_proof` | flux-med | 250 | FAIL | FAIL |
| `AnfImpl__0__ToAnf_proof` | flux-med | 2259 | FAIL | FAIL |
| `AnfImpl__0__ToImm_proof` | flux-med | 2009 | FAIL | FAIL |
| `AnfLet_proof` | flux-med | 98 | 1113 (11×) | 804 (8×) |
| `ArraysAdd2N_proof` | flux-med | 36 | 702 (20×) | 453 (13×) |
| `ArraysAddNK_proof` | flux-med | 72 | 6927 (96×) | 12742 (177×) |
| `ArraysAverageColor_proof` | flux-med | 192 | 38122 (199×) | 308524 (1607×) |
| `ArraysDotK_proof` | flux-med | 66 | 6181 (94×) | 11109 (168×) |
| `BasicsBurpi_proof` | flux-med | 23 | 476 (21×) | 563 (24×) |
| `BasicsLet2_proof` | flux-med | 39 | 528 (14×) | 756 (19×) |
| `BasicsTestAbs_proof` | flux-med | 35 | 886 (25×) | 405 (12×) |
| `BorrowsCheckVal_proof` | flux-med | 41 | 328 (8×) | 3328 (81×) |
| `BsearchBinarySearch_proof` | flux-med | 170 | 20841 (123×) | 46691 (275×) |
| `CsvCsvOpt_proof` | flux-med | 207 | 34368 (166×) | 1258723 (6081×) |
| `CsvCsv_proof` | flux-med | 116 | 15778 (136×) | 141970 (1224×) |
| `CsvImpl__0__Push_proof` | flux-med | 38 | 1074 (28×) | 441 (12×) |
| `DemoImpl__0__Forward_proof` | flux-med | 91 | 6394 (70×) | 1682 (18×) |
| `DemoImpl__0__New_proof` | flux-med | 326 | FAIL | 360584 (1106×) |
| `DemoInit_proof` | flux-med | 708 | FAIL | FAIL |
| `DotproductDot1_proof` | flux-med | 25 | 1047 (42×) | 305 (12×) |
| `DotproductDot2_proof` | flux-med | 25 | 1047 (42×) | 305 (12×) |
| `DotproductDot3_proof` | flux-med | 25 | 1047 (42×) | 305 (12×) |
| `DotproductDot4_proof` | flux-med | 25 | 1047 (42×) | 305 (12×) |
| `DotproductRepeat1_proof` | flux-med | 558 | FAIL | FAIL |
| `DotproductRepeat2_proof` | flux-med | 1020 | FAIL | FAIL |
| `FftFftTest_proof` | flux-med | 242 | FAIL | 460315 (1902×) |
| `FftLoopC_proof` | flux-med | 106 | 22651 (214×) | 48812 (460×) |
| `HeapsortShiftDown_proof` | flux-med | 220 | FAIL | 830477 (3775×) |
| `KmeansInitCenters_proof` | flux-med | 92 | 7533 (82×) | 146449 (1592×) |
| `KmeansKmeansStep_proof` | flux-med | 195 | 31598 (162×) | 833148 (4273×) |
| `KmeansKmeans_proof` | flux-med | 155 | 19478 (126×) | 221248 (1427×) |
| `KmeansMinIndex_proof` | flux-med | 121 | FAIL | 130424 (1078×) |
| `KmeansNearest_proof` | flux-med | 123 | FAIL | 54262 (441×) |
| `KmeansNormalizeCenters_proof` | flux-med | 67 | 1755 (26×) | 9984 (149×) |
| `KmpKmpSearch_proof` | flux-med | 406 | FAIL | 140127 (345×) |
| `KmpKmpTable_proof` | flux-med | 712 | 1089159 (1530×) | 1840562 (2585×) |
| `ListsAppend_proof` | flux-med | 104 | FAIL | 8285 (80×) |
| `ListsClone_proof` | flux-med | 33 | 783 (24×) | 457 (14×) |
| `ListsMappend_proof` | flux-med | 54 | FAIL | 4597 (85×) |
| `NeuralDotProduct2_proof` | flux-med | 30 | 1157 (39×) | 336 (11×) |
| `NeuralImpl__0__Backward_proof` | flux-med | 325 | FAIL | FAIL |
| `NeuralImpl__0__Forward_proof` | flux-med | 91 | 6393 (70×) | 1682 (18×) |
| `NeuralImpl__0__New_proof` | flux-med | 362 | FAIL | 474514 (1311×) |
| `NeuralImpl__1__Backward_proof` | flux-med | 84 | FAIL | 755 (9×) |
| `NeuralImpl__1__New_proof` | flux-med | 57 | 774 (14×) | 996 (17×) |
| `NeuralInit0_proof` | flux-med | 739 | FAIL | FAIL |
| `NeuralInit2_proof` | flux-med | 207 | FAIL | FAIL |
| `NeuralInit_proof` | flux-med | 1294 | FAIL | FAIL |
| `NeuralMeanSquaredError_proof` | flux-med | 30 | 1157 (39×) | 336 (11×) |
| `NeuralMkWeights_proof` | flux-med | 272 | FAIL | 136992 (504×) |
| `RangeImpl__3__Next_proof` | flux-med | 40 | 677 (17×) | 1130 (28×) |
| `RangeImpl__4__Next_proof` | flux-med | 36 | 443 (12×) | 463 (13×) |
| `RmatImpl__0__GetMut_proof` | flux-med | 68 | 1545 (23×) | 406 (6×) |
| `RmatImpl__0__Get_proof` | flux-med | 48 | 920 (19×) | 333 (7×) |
| `RmatImpl__0__New_proof` | flux-med | 102 | 7886 (77×) | 340544 (3339×) |
| `SimplexDepartVar_proof` | flux-med | 343 | FAIL | 349154 (1018×) |
| `SimplexEnterVar_proof` | flux-med | 99 | FAIL | 34539 (349×) |
| `SimplexSimplex_proof` | flux-med | 76 | 10313 (136×) | 6590 (87×) |
| `SimplexUnb1_proof` | flux-med | 135 | FAIL | 236715 (1753×) |
| `SparseExample1_proof` | flux-med | 297 | 10735 (36×) | 26319 (89×) |
| `SparseExample2_proof` | flux-med | 617 | 36897 (60×) | 88427 (143×) |
| `SparseImpl__0__Get_proof` | flux-med | 274 | 207489 (757×) | 96548 (352×) |
| `SparseImpl__0__Multiply_proof` | flux-med | 363 | FAIL | 1487901 (4099×) |
| `SparseImpl__0__New_proof` | flux-med | 4907 | FAIL | FAIL |
| `UninitFillFromAndVec_proof` | flux-med | 175 | 35222 (201×) | 3389293 (19367×) |
| `UninitFillFromSlice_proof` | flux-med | 176 | 35225 (200×) | 3460553 (19662×) |
| `VecDequeImpl__1__HandleCapacityIncrease_proof` | flux-med | 307 | 108467 (353×) | 68458 (223×) |
| `VecDequeImpl__3__Grow_proof` | flux-med | 69 | FAIL | 7084 (103×) |
| `VectorsCopyWithIter_proof` | flux-med | 157 | 32856 (209×) | FAIL |
| `VectorsCountGood_proof` | flux-med | 146 | 23033 (158×) | 2748135 (18823×) |
| `VectorsCountSlice_proof` | flux-med | 147 | 23037 (157×) | 2809907 (19115×) |
| `VectorsInit_proof` | flux-med | 708 | FAIL | FAIL |
| `VectorsMinIndex_proof` | flux-med | 121 | FAIL | 130424 (1078×) |
| `VectorsRangeR_proof` | flux-med | 66 | FAIL | 7328 (111×) |
| `VectorsTestRangeWhile_proof` | flux-med | 134 | 21146 (158×) | 843843 (6297×) |
| `VectorsTestRvec0_proof` | flux-med | 92 | 2272 (25×) | 4994 (54×) |
| `VectorsTestRvec_proof` | flux-med | 59 | 1054 (18×) | 1760 (30×) |
| `arbitrary-kvar-arg` | lf | 139 | FAIL | 12215 (88×) |
| `comment` | lf | 433 | FAIL | 89855 (208×) |
| `exists_oddity` | lf | 27 | 385 (14×) | 336 (12×) |
| `icfp17-ex1` | lf | 23 | 565 (25×) | 218 (9×) |
| `icfp17-ex2` | lf | 88 | 8670 (99×) | 2316 (26×) |
| `icfp17-ex3` | lf | 80 | FAIL | 2713 (34×) |
| `kut00` | lf | 26 | 502 (19×) | 290 (11×) |
| `mod00` | lf | 26 | 605 (23×) | 471 (18×) |
| `scrape02` | lf | 234 | FAIL | FAIL |
| `scrape03` | lf | 16 | 195 (12×) | 915 (57×) |
| `test02` | lf | 31 | 1181 (38×) | 842 (27×) |
| `AlistImpl__0__ReplaceIfPresent_proof` | hash | 1226 | FAIL | FAIL |
| `BucketMapImpl__0__GetInList_proof` | hash | 104 | 3419 (33×) | 10983 (106×) |
| `BucketMapImpl__0__InsertInList_proof` | hash | 186 | 14932 (80×) | 27014 (145×) |
| `BucketMapImpl__0__RemoveFromList_proof` | hash | 924 | FAIL | FAIL |
| `SortInsertRec_proof` | sort | 280 | 1943388 (6941×) | 28547 (102×) |
| `SortInsert_proof` | sort | 244 | 773688 (3171×) | 50407 (207×) |
| `SortMergeSort_proof` | sort | 100 | 12958 (130×) | 60989 (610×) |
| `SortMerge_proof` | sort | 1875 | FAIL | FAIL |
| `SortMergesortRange_proof` | sort | 282 | 369965 (1312×) | 30647 (109×) |
| `SortPartition_proof` | sort | 272 | 321408 (1182×) | 581775 (2139×) |
| `SortQuicksortRange_proof` | sort | 199 | 328450 (1651×) | 93658 (471×) |
| `SortTest1_proof` | sort | 690 | 343336 (498×) | 41413 (60×) |
| `SortTestSorted_proof` | sort | 36 | 2227 (62×) | 1139 (32×) |
| `VectorsTest1_proof` | sort | 690 | 344234 (499×) | 42305 (61×) |

**Coverage:** zap 103/103  grind 66/103  aesop 86/103

**Geomean slowdown vs zap** (solved-by-both): grind 78.5×  aesop 147.2×

## Per-suite aggregate

| suite | VCs | zap ok | grind ok | aesop ok | gm grind/zap | gm aesop/zap |
|---|--:|--:|--:|--:|--:|--:|
| flux-medium | 78 | 78 | 48 | 65 | 61.1× | 184.4× |
| liquid-fixpoint | 11 | 11 | 7 | 10 | 25.6× | 30.1× |
| hashtable | 4 | 4 | 2 | 2 | 51.4× | 123.8× |
| sorting | 10 | 10 | 9 | 9 | 784.1× | 176.2× |
