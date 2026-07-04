# Table 1: Non-trivial VCs and Proof Failures

| Benchmark | Non-trivial VCs | Failures | Success % | Success % (cyclic) | fixpoint-hs time | Lean Time |
|-----------|----------------:|---------:|----------:|-------------------:|----------:|----------:|
| flux-medium | 148 | 16 | 89.2% | 78.3% | — | 9.2m |
| wave | 77 | 3 | 96.1% | 70.0% | — | 4.0m |
| Flux lean-bench | 620 | 21 | 96.6% | 83.8% | — | 7.4m |
| Liquid-fixpoint | 47 | 2 | 95.7% | 100.0% | — | 1.3m |
| **Total** | **892** | **42** | **95.3%** | **82.3%** | **—** | **21.9m** |

# Table 2: Kvar Classification of Non-trivial VCs

| Benchmark | none | acyclic | cyclic | both | Total |
|-----------|-----:|--------:|-------:|-----:|------:|
| flux-medium | 52 | 36 | 16 | 44 | 148 |
| wave | 41 | 26 | 1 | 9 | 77 |
| Flux lean-bench | 355 | 185 | 30 | 50 | 620 |
| Liquid-fixpoint | 22 | 11 | 12 | 2 | 47 |
| **Total** | **470** | **258** | **59** | **105** | **892** |
