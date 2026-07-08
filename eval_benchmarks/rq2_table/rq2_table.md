# RQ2: acyclic-κ elimination — zap vs grind vs aesop

Headline metric: `elim_hb` = heartbeats spent in the acyclic-κ elimination step only (residual VC left as `all_goals sorry`). Parenthesised `×` is slowdown relative to `zap` (fusion).

| VC | suite | zap | grind | aesop |
|---|---|--:|--:|--:|
| `AnfBin_proof` | flux-med | 80 | 2855 (36×) | 717 (9×) |
| `AnfImpl__0__IsAnf_proof` | flux-med | 250 | FAIL | FAIL |
| `AnfImpl__0__ToAnf_proof` | flux-med | 2259 | FAIL | FAIL |
| `AnfImpl__0__ToImm_proof` | flux-med | 2009 | FAIL | FAIL |
| `AnfLet_proof` | flux-med | 98 | 1114 (11×) | 804 (8×) |
| `ArraysAdd2N_proof` | flux-med | 36 | 702 (20×) | 453 (13×) |
| `ArraysAddNK_proof` | flux-med | 72 | 6927 (96×) | 12742 (177×) |
| `ArraysAverageColor_proof` | flux-med | 192 | 38122 (199×) | 308525 (1607×) |
| `ArraysDotK_proof` | flux-med | 66 | 6181 (94×) | 11109 (168×) |
| `BasicsBurpi_proof` | flux-med | 23 | 476 (21×) | 563 (24×) |
| `BasicsLet2_proof` | flux-med | 39 | 528 (14×) | 756 (19×) |
| `BasicsTestAbs_proof` | flux-med | 35 | 886 (25×) | 405 (12×) |
| `BorrowsCheckVal_proof` | flux-med | 41 | 328 (8×) | 3328 (81×) |
| `BsearchBinarySearch_proof` | flux-med | 170 | 20841 (123×) | 46691 (275×) |
| `CsvCsvOpt_proof` | flux-med | 207 | 34369 (166×) | 1258723 (6081×) |
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
| `KmpKmpTable_proof` | flux-med | 712 | 1089161 (1530×) | 1840562 (2585×) |
| `ListsAppend_proof` | flux-med | 104 | FAIL | 8285 (80×) |
| `ListsClone_proof` | flux-med | 33 | 783 (24×) | 457 (14×) |
| `ListsMappend_proof` | flux-med | 54 | FAIL | 4597 (85×) |
| `NeuralDotProduct2_proof` | flux-med | 30 | 1157 (39×) | 336 (11×) |
| `NeuralImpl__0__Backward_proof` | flux-med | 325 | FAIL | FAIL |
| `NeuralImpl__0__Forward_proof` | flux-med | 91 | 6394 (70×) | 1682 (18×) |
| `NeuralImpl__0__New_proof` | flux-med | 362 | FAIL | 474514 (1311×) |
| `NeuralImpl__1__Backward_proof` | flux-med | 84 | FAIL | 754 (9×) |
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
| `SparseExample2_proof` | flux-med | 617 | 36897 (60×) | 88426 (143×) |
| `SparseImpl__0__Get_proof` | flux-med | 274 | 207489 (757×) | 96548 (352×) |
| `SparseImpl__0__Multiply_proof` | flux-med | 363 | FAIL | 1487901 (4099×) |
| `SparseImpl__0__New_proof` | flux-med | 4907 | FAIL | FAIL |
| `UninitFillFromAndVec_proof` | flux-med | 175 | 35222 (201×) | 3389293 (19367×) |
| `UninitFillFromSlice_proof` | flux-med | 176 | 35225 (200×) | 3460553 (19662×) |
| `VecDequeImpl__1__HandleCapacityIncrease_proof` | flux-med | 307 | 108467 (353×) | 68458 (223×) |
| `VecDequeImpl__3__Grow_proof` | flux-med | 69 | FAIL | 7084 (103×) |
| `VectorsCopyWithIter_proof` | flux-med | 157 | 32856 (209×) | FAIL |
| `VectorsCountGood_proof` | flux-med | 146 | 23034 (158×) | 2748135 (18823×) |
| `VectorsCountSlice_proof` | flux-med | 147 | 23038 (157×) | 2809907 (19115×) |
| `VectorsInit_proof` | flux-med | 708 | FAIL | FAIL |
| `VectorsMinIndex_proof` | flux-med | 121 | FAIL | 130424 (1078×) |
| `VectorsRangeR_proof` | flux-med | 66 | FAIL | 7328 (111×) |
| `VectorsTestRangeWhile_proof` | flux-med | 134 | 21146 (158×) | 843843 (6297×) |
| `VectorsTestRvec0_proof` | flux-med | 92 | 2273 (25×) | 4994 (54×) |
| `VectorsTestRvec_proof` | flux-med | 59 | 1054 (18×) | 1760 (30×) |
| `FdmapImpl__0__CreateSock_proof` | wave | 42 | 567 (14×) | 291 (7×) |
| `FdmapImpl__0__Create_proof` | wave | 40 | 420 (10×) | 282 (7×) |
| `FdmapImpl__0__Delete_proof` | wave | 299 | FAIL | 31040 (104×) |
| `FdmapImpl__0__FdToNative_proof` | wave | 47 | 2005 (43×) | 522 (11×) |
| `FdmapImpl__0__PopFd_proof` | wave | 92 | 5415 (59×) | 1561 (17×) |
| `FdmapImpl__0__Shift_proof` | wave | 143 | 7331 (51×) | 2188 (15×) |
| `PathResolutionExpandPath_proof` | wave | 749 | FAIL | 1711853 (2286×) |
| `PathResolutionExpandSymlink_proof` | wave | 65 | 3983 (61×) | 5028 (77×) |
| `PathResolutionResolvePath_proof` | wave | 364 | 60447 (166×) | FAIL |
| `PollWritebackFds_proof` | wave | 850 | FAIL | FAIL |
| `PollWritebackTimeouts_proof` | wave | 797 | FAIL | FAIL |
| `RuntimeFreshCtx_proof` | wave | 35 | 261 (7×) | 2171 (62×) |
| `RuntimeImpl__0__FitsInLinMemUsize_proof` | wave | 320 | 14071 (44×) | 45386 (142×) |
| `RuntimeImpl__0__FitsInLinMem_proof` | wave | 320 | 14071 (44×) | 45386 (142×) |
| `RuntimeImpl__0__ReadU16_proof` | wave | 86 | 3918 (46×) | 5137 (60×) |
| `RuntimeImpl__0__ReadU32_proof` | wave | 213 | 41020 (193×) | 27350 (128×) |
| `RuntimeImpl__0__ReadU64_proof` | wave | 652 | 392536 (602×) | 146012 (224×) |
| `RuntimeImpl__0__TranslateIovs_proof` | wave | 191 | 40839 (214×) | 95130 (498×) |
| `TypesImpl__5__FromSyscallRet_proof` | wave | 18 | 147 (8×) | 124 (7×) |
| `TypesPlatformImpl__3__Parse_proof` | wave | 1017 | FAIL | 214273 (211×) |
| `WrappersWasiArgsGet_proof` | wave | 3021 | FAIL | FAIL |
| `WrappersWasiEnvironGet_proof` | wave | 3049 | FAIL | FAIL |
| `WrappersWasiFdAdvise_proof` | wave | 470 | FAIL | 122645 (261×) |
| `WrappersWasiFdClose_proof` | wave | 199 | 13407 (67×) | 2600 (13×) |
| `WrappersWasiFdFilestatSetTimes_proof` | wave | 150 | 4189 (28×) | 1568 (10×) |
| `WrappersWasiFdReaddir_proof` | wave | 126 | 1436 (11×) | 851 (7×) |
| `WrappersWasiFdSeek_proof` | wave | 413 | FAIL | 103947 (252×) |
| `WrappersWasiPathFilestatGet_proof` | wave | 174 | 3979 (23×) | 13452 (77×) |
| `WrappersWasiPathFilestatSetTimes_proof` | wave | 626 | FAIL | 185436 (296×) |
| `WrappersWasiPathLink_proof` | wave | 2628 | FAIL | FAIL |
| `WrappersWasiPathRename_proof` | wave | 943 | FAIL | 208038 (221×) |
| `WrappersWasiSockConnect_proof` | wave | 294 | FAIL | 23642 (80×) |
| `WrappersWasiSockRecv_proof` | wave | 599 | FAIL | 379117 (633×) |
| `WrappersWasiSockSend_proof` | wave | 493 | FAIL | 286328 (581×) |
| `WrappersWasiSocket_proof` | wave | 276 | 4493 (16×) | 19495 (71×) |
| `AddColorcode_proof` | Flux l | 188 | FAIL | 13155 (70×) |
| `Add_proof` | Flux l | 48 | 2967 (62×) | 734 (15×) |
| `Append_proof` | Flux l | 104 | FAIL | 8285 (80×) |
| `Array00_proof` | Flux l | 14 | 203 (14×) | 283 (20×) |
| `Bad_proof` | Flux l | 83 | 978 (12×) | 744 (9×) |
| `Bar1_proof` | Flux l | 18 | 77 (4×) | 102 (6×) |
| `Bar_proof` | Flux l | 33 | 1261 (38×) | 1025 (31×) |
| `BazCall_proof` | Flux l | 27 | 459 (17×) | 262 (10×) |
| `Baz_proof` | Flux l | 18 | 77 (4×) | 102 (6×) |
| `Baz_proof` | Flux l | 9 | 24 (3×) | 70 (8×) |
| `BinarySearch_proof` | Flux l | 206 | 37165 (180×) | 73945 (359×) |
| `BinarySearch_proof` | Flux l | 327 | 79322 (243×) | 467365 (1429×) |
| `Blah2_proof` | Flux l | 59 | 2308 (39×) | 1926 (33×) |
| `Blah3_proof` | Flux l | 92 | 4980 (54×) | 3894 (42×) |
| `BobARR_proof` | Flux l | 17 | 369 (22×) | 481 (28×) |
| `Bob_proof` | Flux l | 23 | 484 (21×) | 250 (11×) |
| `Burpi_proof` | Flux l | 23 | 476 (21×) | 563 (24×) |
| `Choose_proof` | Flux l | 47 | FAIL | 36041 (767×) |
| `Client0_proof` | Flux l | 37 | 614 (17×) | 354 (10×) |
| `Clone_proof` | Flux l | 33 | 783 (24×) | 457 (14×) |
| `CloseAtJoin_proof` | Flux l | 57 | FAIL | 2553 (45×) |
| `CloseAtReturn_proof` | Flux l | 9 | 28 (3×) | 73 (8×) |
| `CloseOnMove_proof` | Flux l | 20 | 340 (17×) | 329 (16×) |
| `Cons_proof` | Flux l | 22 | 298 (14×) | 146 (7×) |
| `DepartVar_proof` | Flux l | 343 | FAIL | 349156 (1018×) |
| `Direct_proof` | Flux l | 20 | 377 (19×) | 519 (26×) |
| `Donald_proof` | Flux l | 130 | 18058 (139×) | 2054 (16×) |
| `Dot2_proof` | Flux l | 47 | 2957 (63×) | 720 (15×) |
| `Dot2_proof` | Flux l | 47 | 2958 (63×) | 720 (15×) |
| `Dot_proof` | Flux l | 41 | 1865 (45×) | 495 (12×) |
| `EnterVar_proof` | Flux l | 106 | FAIL | 49690 (469×) |
| `FROG_proof` | Flux l | 17 | 164 (10×) | 175 (10×) |
| `FftTest_proof` | Flux l | 279 | FAIL | 746750 (2677×) |
| `FillVecIndexLoop_proof` | Flux l | 1294 | FAIL | FAIL |
| `FillVecIndex_proof` | Flux l | 207 | FAIL | FAIL |
| `FillVecLoop_proof` | Flux l | 730 | FAIL | FAIL |
| `FillVecMap_proof` | Flux l | 207 | FAIL | FAIL |
| `FirstHalf_proof` | Flux l | 40 | 516 (13×) | 1235 (31×) |
| `First_proof` | Flux l | 22 | 336 (15×) | 414 (19×) |
| `Foo_proof` | Flux l | 194 | FAIL | 69355 (358×) |
| `Foo_proof` | Flux l | 302 | 186035 (616×) | 880362 (2915×) |
| `GooberIDXS_proof` | Flux l | 17 | 368 (22×) | 481 (28×) |
| `Goofy_proof` | Flux l | 53 | 5191 (98×) | 9208 (174×) |
| `Gt_proof` | Flux l | 17 | 149 (9×) | 118 (7×) |
| `HOG_proof` | Flux l | 17 | 311 (18×) | 189 (11×) |
| `Impl__0__Append_proof` | Flux l | 33 | 1025 (31×) | 31878 (966×) |
| `Impl__0__Foreach_proof` | Flux l | 49 | FAIL | 3865 (79×) |
| `Impl__0__GetMut_proof` | Flux l | 71 | 1670 (24×) | 440 (6×) |
| `Impl__0__Get_proof` | Flux l | 55 | 1019 (19×) | 384 (7×) |
| `Impl__0__IntoNnf_proof` | Flux l | 6442 | FAIL | FAIL |
| `Impl__0__New_proof` | Flux l | 96 | 13555 (141×) | 330433 (3442×) |
| `Impl__0__Simplify_proof` | Flux l | 4603 | FAIL | FAIL |
| `Impl__0__Succ_proof` | Flux l | 18 | 181 (10×) | 124 (7×) |
| `Impl__0__Succ_proof` | Flux l | 18 | 181 (10×) | 124 (7×) |
| `Impl__0__TryFrom_proof` | Flux l | 14 | 61 (4×) | 81 (6×) |
| `Impl__0__TryInto_proof` | Flux l | 14 | 33 (2×) | 81 (6×) |
| `Impl__1__Foreach_proof` | Flux l | 634 | FAIL | FAIL |
| `Impl__1__Next_proof` | Flux l | 33 | 788 (24×) | 616 (19×) |
| `Impl__1__Pop_proof` | Flux l | 78 | FAIL | 11533 (148×) |
| `Impl__1__Push_proof` | Flux l | 25 | 530 (21×) | 337 (13×) |
| `Impl__1__Succ_proof` | Flux l | 18 | 181 (10×) | 124 (7×) |
| `Impl__2__From_proof` | Flux l | 38 | FAIL | 2202 (58×) |
| `Impl__2__From_proof` | Flux l | 38 | FAIL | 2202 (58×) |
| `IncBox_proof` | Flux l | 14 | 46 (3×) | 92 (7×) |
| `IncTest_proof` | Flux l | 14 | 117 (8×) | 86 (6×) |
| `InitCenters_proof` | Flux l | 100 | 15257 (153×) | 274699 (2747×) |
| `IsMonth30_proof` | Flux l | 49 | 913 (19×) | 1636 (33×) |
| `IsSomeFlip_proof` | Flux l | 30 | FAIL | 20000 (667×) |
| `IsSome_proof` | Flux l | 30 | FAIL | 20000 (667×) |
| `JoinArr_proof` | Flux l | 151 | FAIL | 16885 (112×) |
| `KmeansStep_proof` | Flux l | 777 | FAIL | FAIL |
| `Kmeans_proof` | Flux l | 156 | 18134 (116×) | 227698 (1460×) |
| `KmpSearch_proof` | Flux l | 643 | FAIL | 434214 (675×) |
| `KmpSearch_proof` | Flux l | 764 | FAIL | 1439611 (1884×) |
| `KmpTable_proof` | Flux l | 836 | 1682446 (2012×) | 3828719 (4580×) |
| `KmpTable_proof` | Flux l | 977 | FAIL | FAIL |
| `Let2_proof` | Flux l | 25 | 278 (11×) | 444 (18×) |
| `Let3_proof` | Flux l | 32 | 367 (11×) | 698 (22×) |
| `Lib_proof` | Flux l | 35 | 345 (10×) | 307 (9×) |
| `LoopC_proof` | Flux l | 105 | 13104 (125×) | 52852 (503×) |
| `Lt_proof` | Flux l | 16 | 147 (9×) | 103 (6×) |
| `MakeNatRes_proof` | Flux l | 9 | 91 (10×) | 89 (10×) |
| `Mappend_proof` | Flux l | 54 | FAIL | 4597 (85×) |
| `Maximum_proof` | Flux l | 324 | FAIL | 2549063 (7867×) |
| `MinIndexFold_proof` | Flux l | 140 | FAIL | 3762417 (26874×) |
| `MinIndex_proof` | Flux l | 127 | 13147 (104×) | 75209 (592×) |
| `MkDate_proof` | Flux l | 144 | 11926 (83×) | 25205 (175×) |
| `MkPairsWithBound_proof` | Flux l | 76 | 6633 (87×) | 20424 (269×) |
| `MkPairsWithBound_proof` | Flux l | 76 | 8380 (110×) | 21474 (283×) |
| `MkPairsWithBound_proof` | Flux l | 76 | 8380 (110×) | 21474 (283×) |
| `MoveOutOfBox_proof` | Flux l | 81 | 1822 (22×) | 1342 (17×) |
| `Nearest_proof` | Flux l | 136 | FAIL | 75175 (553×) |
| `NoCloseJoin_proof` | Flux l | 57 | FAIL | 2625 (46×) |
| `NormalizeCenters_proof` | Flux l | 96 | 4396 (46×) | 24707 (257×) |
| `OpaqueStruct01_proof` | Flux l | 42 | FAIL | 1835 (44×) |
| `Or_proof` | Flux l | 23 | 62 (3×) | 120 (5×) |
| `Pop2_proof` | Flux l | 132 | 19027 (144×) | 18325 (139×) |
| `RangeImpl__2__Next_proof` | Flux l | 33 | 789 (24×) | 616 (19×) |
| `RealExample_proof` | Flux l | 47 | 1059 (23×) | 2289 (49×) |
| `RefJoin_proof` | Flux l | 27 | FAIL | 1292 (48×) |
| `SafeDiv_proof` | Flux l | 33 | 399 (12×) | 245 (7×) |
| `ShiftDown_proof` | Flux l | 411 | 962558 (2342×) | 1979371 (4816×) |
| `Simplex_proof` | Flux l | 78 | 11110 (142×) | 6622 (85×) |
| `Succ_proof` | Flux l | 18 | 181 (10×) | 124 (7×) |
| `Test001Client_proof` | Flux l | 40 | FAIL | 705 (18×) |
| `Test001Client_proof` | Flux l | 40 | FAIL | 976 (24×) |
| `Test001_proof` | Flux l | 184 | FAIL | 5899 (32×) |
| `Test001_proof` | Flux l | 234 | FAIL | 9152 (39×) |
| `Test002Client_proof` | Flux l | 40 | FAIL | 705 (18×) |
| `Test002Client_proof` | Flux l | 62 | FAIL | 2302 (37×) |
| `Test002_proof` | Flux l | 184 | FAIL | 5899 (32×) |
| `Test002_proof` | Flux l | 299 | FAIL | 12495 (42×) |
| `Test00_proof` | Flux l | 16 | 314 (20×) | 678 (42×) |
| `Test00_proof` | Flux l | 20 | 377 (19×) | 519 (26×) |
| `Test00_proof` | Flux l | 14 | 102 (7×) | 120 (9×) |
| `Test00_proof` | Flux l | 15 | 196 (13×) | 221 (15×) |
| `Test00_proof` | Flux l | 19 | 241 (13×) | 197 (10×) |
| `Test00_proof` | Flux l | 9 | 103 (11×) | 78 (9×) |
| `Test00_proof` | Flux l | 30 | 310 (10×) | 906 (30×) |
| `Test00_proof` | Flux l | 27 | FAIL | 1346 (50×) |
| `Test00_proof` | Flux l | 40 | FAIL | 2528 (63×) |
| `Test01_proof` | Flux l | 16 | 292 (18×) | 633 (40×) |
| `Test01_proof` | Flux l | 35 | 1047 (30×) | 803 (23×) |
| `Test01_proof` | Flux l | 50 | 936 (19×) | 538 (11×) |
| `Test01_proof` | Flux l | 14 | 104 (7×) | 142 (10×) |
| `Test01_proof` | Flux l | 36 | 355 (10×) | 280 (8×) |
| `Test01_proof` | Flux l | 24 | 651 (27×) | 232 (10×) |
| `Test01_proof` | Flux l | 9 | 103 (11×) | 78 (9×) |
| `Test02_proof` | Flux l | 27 | FAIL | 1129 (42×) |
| `Test02_proof` | Flux l | 14 | 185 (13×) | 138 (10×) |
| `Test02_proof` | Flux l | 9 | FAIL | 88 (10×) |
| `Test02_proof` | Flux l | 162 | 4305 (27×) | 2708 (17×) |
| `Test02_proof` | Flux l | 14 | 104 (7×) | 142 (10×) |
| `Test02_proof` | Flux l | 9 | 103 (11×) | 78 (9×) |
| `Test03_proof` | Flux l | 415 | 16931 (41×) | 10658 (26×) |
| `Test03_proof` | Flux l | 115 | 2097 (18×) | 3793 (33×) |
| `Test04_proof` | Flux l | 27 | 783 (29×) | 1272 (47×) |
| `Test0_proof` | Flux l | 175 | FAIL | 2956 (17×) |
| `Test0_proof` | Flux l | 175 | FAIL | 2956 (17×) |
| `Test0_proof` | Flux l | 175 | FAIL | 2956 (17×) |
| `Test0_proof` | Flux l | 175 | FAIL | 2956 (17×) |
| `Test0_proof` | Flux l | 450 | FAIL | 181524 (403×) |
| `Test1Old_proof` | Flux l | 188 | FAIL | 8965 (48×) |
| `Test1_proof` | Flux l | 28 | 256 (9×) | 244 (9×) |
| `Test1_proof` | Flux l | 28 | 494 (18×) | 769 (27×) |
| `Test1_proof` | Flux l | 9 | 95 (11×) | 84 (9×) |
| `Test1_proof` | Flux l | 48 | FAIL | 4934 (103×) |
| `Test1_proof` | Flux l | 27 | FAIL | FAIL |
| `Test2Old_proof` | Flux l | 116 | FAIL | 4605 (40×) |
| `Test2_proof` | Flux l | 27 | 312 (12×) | 255 (9×) |
| `Test2_proof` | Flux l | 27 | 314 (12×) | 255 (9×) |
| `Test2_proof` | Flux l | 58 | 2231 (38×) | 2727 (47×) |
| `Test2_proof` | Flux l | 39 | FAIL | 3493 (90×) |
| `Test2_proof` | Flux l | 95 | FAIL | FAIL |
| `Test2_proof` | Flux l | 57 | 2356 (41×) | 2308 (40×) |
| `Test2_proof` | Flux l | 302 | FAIL | 121491 (402×) |
| `Test3_proof` | Flux l | 28 | 256 (9×) | 244 (9×) |
| `Test3_proof` | Flux l | 43 | FAIL | 3860 (90×) |
| `Test3_proof` | Flux l | 59 | 713 (12×) | 1196 (20×) |
| `Test3_proof` | Flux l | 859 | FAIL | FAIL |
| `Test7_proof` | Flux l | 30 | FAIL | 1900 (63×) |
| `TestAlsoOk_proof` | Flux l | 68 | 1245 (18×) | 1007 (15×) |
| `TestArrayUnwrap_proof` | Flux l | 148 | 37987 (257×) | 3985 (27×) |
| `TestBarEq_proof` | Flux l | 83 | 963 (12×) | 740 (9×) |
| `TestBothBoundedConcrete_proof` | Flux l | 117 | 4016 (34×) | 2883 (25×) |
| `TestCheckedDivI32_proof` | Flux l | 45 | 763 (17×) | 631 (14×) |
| `TestCheckedDivIsize_proof` | Flux l | 113 | 4016 (36×) | 2395 (21×) |
| `TestCheckedDivU32_proof` | Flux l | 17 | 188 (11×) | 169 (10×) |
| `TestCheckedDivUsize_proof` | Flux l | 17 | 188 (11×) | 169 (10×) |
| `TestCheckedI32_proof` | Flux l | 51 | 737 (14×) | 1157 (23×) |
| `TestCheckedIsize_proof` | Flux l | 51 | 737 (14×) | 1157 (23×) |
| `TestCheckedMulI32_proof` | Flux l | 22 | 216 (10×) | 311 (14×) |
| `TestCheckedMulIsize_proof` | Flux l | 22 | 216 (10×) | 311 (14×) |
| `TestCheckedMulU32_proof` | Flux l | 22 | 210 (10×) | 268 (12×) |
| `TestCheckedMulUsize_proof` | Flux l | 22 | 210 (10×) | 268 (12×) |
| `TestCheckedNegI32_proof` | Flux l | 45 | 777 (17×) | 496 (11×) |
| `TestCheckedNegIsize_proof` | Flux l | 45 | 777 (17×) | 496 (11×) |
| `TestCheckedU32_proof` | Flux l | 49 | 930 (19×) | 809 (17×) |
| `TestCheckedUsize_proof` | Flux l | 49 | 930 (19×) | 809 (17×) |
| `TestEnumerate1_proof` | Flux l | 507 | FAIL | FAIL |
| `TestExiR_proof` | Flux l | 45 | 1002 (22×) | 2330 (52×) |
| `TestFooEq_proof` | Flux l | 83 | 963 (12×) | 740 (9×) |
| `TestFor_proof` | Flux l | 45 | FAIL | 665 (15×) |
| `TestForeach_proof` | Flux l | 18 | FAIL | 211 (12×) |
| `TestFromValidUnwrap_proof` | Flux l | 192 | 23708 (123×) | 5925 (31×) |
| `TestIntoBothBoundedConcrete_proof` | Flux l | 69 | 1703 (25×) | 2103 (30×) |
| `TestIter2_proof` | Flux l | 158 | 25398 (161×) | 2940137 (18608×) |
| `TestIterForLoopSlice_proof` | Flux l | 157 | 26818 (171×) | 2939756 (18725×) |
| `TestIterForLoopVec2_proof` | Flux l | 165 | 35759 (217×) | 3191298 (19341×) |
| `TestIterForLoopVec_proof` | Flux l | 158 | 26055 (165×) | 2874129 (18191×) |
| `TestIter_proof` | Flux l | 69 | 3055 (44×) | 31649 (459×) |
| `TestLib_proof` | Flux l | 27 | 312 (12×) | 255 (9×) |
| `TestLoop_proof` | Flux l | 73 | 2458 (34×) | 6731 (92×) |
| `TestLowerBoundedConcrete_proof` | Flux l | 17 | 176 (10×) | 134 (8×) |
| `TestMap_proof` | Flux l | 17 | FAIL | 200 (12×) |
| `TestNeg_proof` | Flux l | 83 | 990 (12×) | 745 (9×) |
| `TestNext_proof` | Flux l | 45 | FAIL | 665 (15×) |
| `TestOk_proof` | Flux l | 36 | 661 (18×) | 399 (11×) |
| `TestOk_proof` | Flux l | 68 | 1245 (18×) | 1007 (15×) |
| `TestOptSpecs_proof` | Flux l | 28 | 256 (9×) | 244 (9×) |
| `TestPush_proof` | Flux l | 125 | 3538 (28×) | 7261 (58×) |
| `TestRc_proof` | Flux l | 26 | 131 (5×) | 223 (9×) |
| `TestRepeatArrayIndexRead_proof` | Flux l | 9 | 24 (3×) | 70 (8×) |
| `TestRepeatReturnGeqZero_proof` | Flux l | 9 | 91 (10×) | 89 (10×) |
| `TestRepeatReturnPos_proof` | Flux l | 9 | 103 (11×) | 78 (9×) |
| `TestRepeatWriteThenRead_proof` | Flux l | 16 | 238 (15×) | 442 (28×) |
| `TestSafeDiv_proof` | Flux l | 17 | 188 (11×) | 169 (10×) |
| `TestSplitFirstTailLen_proof` | Flux l | 19 | 272 (14×) | 178 (9×) |
| `TestSplitLastInitLen_proof` | Flux l | 19 | 272 (14×) | 178 (9×) |
| `TestTryFromConcrete_proof` | Flux l | 15 | 162 (11×) | 120 (8×) |
| `TestUpperBoundedUConcrete_proof` | Flux l | 25 | 202 (8×) | 234 (9×) |
| `TestVecOfNat_proof` | Flux l | 116 | FAIL | 5638 (49×) |
| `Test_proof` | Flux l | 29 | 527 (18×) | 285 (10×) |
| `Test_proof` | Flux l | 134 | 3773 (28×) | 169037 (1261×) |
| `Test_proof` | Flux l | 32 | 975 (30×) | 1170 (37×) |
| `Test_proof` | Flux l | 134 | 6487 (48×) | 72500 (541×) |
| `Test_proof` | Flux l | 15 | 171 (11×) | 109 (7×) |
| `Test_proof` | Flux l | 16 | 226 (14×) | 176 (11×) |
| `Test_proof` | Flux l | 33 | 526 (16×) | 321 (10×) |
| `Test_proof` | Flux l | 107 | FAIL | 30727 (287×) |
| `Test_proof` | Flux l | 91 | 2852 (31×) | 8093 (89×) |
| `Test_proof` | Flux l | 144 | 15307 (106×) | 210265 (1460×) |
| `Test_proof` | Flux l | 71 | FAIL | 102317 (1441×) |
| `Test_proof` | Flux l | 37 | 314 (8×) | 2975 (80×) |
| `Test_proof` | Flux l | 23 | 153 (7×) | 185 (8×) |
| `Test_proof` | Flux l | 9 | 25 (3×) | 72 (8×) |
| `Unb1_proof` | Flux l | 140 | FAIL | 268781 (1920×) |
| `UpdateCenters_proof` | Flux l | 641 | FAIL | FAIL |
| `Update_proof` | Flux l | 9 | 28 (3×) | 73 (8×) |
| `VecPush_proof` | Flux l | 59 | 1014 (17×) | 2090 (35×) |
| `Write_proof` | Flux l | 20 | 314 (16×) | 525 (26×) |
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
| `test02` | lf | 31 | 1180 (38×) | 842 (27×) |
| `AlistImpl__0__ReplaceIfPresent_proof` | hash | 1226 | FAIL | FAIL |
| `BucketMapImpl__0__GetInList_proof` | hash | 104 | 3424 (33×) | 10987 (106×) |
| `BucketMapImpl__0__InsertInList_proof` | hash | 186 | 14999 (81×) | 26954 (145×) |
| `BucketMapImpl__0__RemoveFromList_proof` | hash | 924 | FAIL | FAIL |
| `SortInsertRec_proof` | sort | 280 | 1943389 (6941×) | 28547 (102×) |
| `SortInsert_proof` | sort | 244 | 773688 (3171×) | 50407 (207×) |
| `SortMergeSort_proof` | sort | 100 | 12958 (130×) | 60989 (610×) |
| `SortMerge_proof` | sort | 1875 | FAIL | FAIL |
| `SortMergesortRange_proof` | sort | 282 | 369965 (1312×) | 30647 (109×) |
| `SortPartition_proof` | sort | 272 | 321408 (1182×) | 581775 (2139×) |
| `SortQuicksortRange_proof` | sort | 199 | 328452 (1651×) | 93658 (471×) |
| `SortTest1_proof` | sort | 690 | 343333 (498×) | 41413 (60×) |
| `SortTestSorted_proof` | sort | 36 | 2227 (62×) | 1139 (32×) |
| `VectorsTest1_proof` | sort | 690 | 344239 (499×) | 42305 (61×) |

**Coverage:** zap 369/369  grind 247/369  aesop 332/369

**Geomean slowdown vs zap** (solved-by-both): grind 31.9×  aesop 60.1×

## Per-suite aggregate

| suite | VCs | zap ok | grind ok | aesop ok | gm grind/zap | gm aesop/zap |
|---|--:|--:|--:|--:|--:|--:|
| flux-medium | 78 | 78 | 48 | 65 | 61.1× | 184.4× |
| wave | 35 | 35 | 20 | 29 | 41.2× | 75.2× |
| Flux lean-bench | 231 | 231 | 161 | 217 | 21.4× | 40.8× |
| liquid-fixpoint | 11 | 11 | 7 | 10 | 25.6× | 30.1× |
| hashtable | 4 | 4 | 2 | 2 | 51.5× | 123.7× |
| sorting | 10 | 10 | 9 | 9 | 784.1× | 176.2× |
