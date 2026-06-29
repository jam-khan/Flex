import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure SparseCSRMatrix  where
  mkSparseCSRMatrix₀ ::
    rows : Int 
    cols : Int 
    nnz : Int 
  deriving Inhabited
attribute [grind .] SparseCSRMatrix.ext


end F
