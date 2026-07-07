import Lean
import Flex.Core.KVar

open Lean

instance : ToString KVar where
  toString k :=
    if k.params.isEmpty then toString k.name
    else
      let ps := ", ".intercalate (k.params.map toString)
      s!"{k.name}({ps})"
