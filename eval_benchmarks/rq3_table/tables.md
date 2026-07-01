# Table 1: Non-trivial VCs and Proof Failures

| Benchmark | Non-trivial VCs | Failures | Success % | Success % (cyclic) | fixpoint-hs time | Lean Time |
|-----------|----------------:|---------:|----------:|-------------------:|----------:|----------:|
| flux-medium | 148 | 27 | 81.8% | 60.0% | — | 10.8m |
| wave | 77 | 12 | 84.4% | 20.0% | — | 10.0m |
| Flux lean-bench | 620 | 31 | 95.0% | 77.5% | — | 17.3m |
| Liquid-fixpoint | 47 | 2 | 95.7% | 100.0% | — | 1.4m |
| **Total** | **892** | **72** | **91.9%** | **69.5%** | **—** | **39.5m** |

# Table 2: Kvar Classification of Non-trivial VCs

| Benchmark | none | acyclic | cyclic | both | Total |
|-----------|-----:|--------:|-------:|-----:|------:|
| flux-medium | 52 | 36 | 16 | 44 | 148 |
| wave | 41 | 26 | 1 | 9 | 77 |
| Flux lean-bench | 355 | 185 | 30 | 50 | 620 |
| Liquid-fixpoint | 22 | 11 | 12 | 2 | 47 |
| **Total** | **470** | **258** | **59** | **105** | **892** |
