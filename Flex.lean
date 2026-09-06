
-- Core utils, monads and infra
import Flex.Core

-- Fusion algorithm
import Flex.Fusion

--  Elaboration helpers for peeling existentials and building witness expressions.
import Flex.Elab

-- Proof producing local refinement type inference
import Flex.Zap

-- Tactic related code
import Flex.Tactic

-- Predicate Abstraction
import Flex.PA

-- Certifying `#spec` frontend over ordinary Lean definitions
import Flex.Front

-- Sound Verification Condition Generation for Imp
import Flex.VCG.While.Types
import Flex.VCG.While.Semantics

--  Sound verified gen for λᵣ
import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Substitution
import Flex.VCG.STLC.Entailment
import Flex.VCG.STLC.Typing
import Flex.VCG.STLC.VCGen
import Flex.VCG.STLC.Declarative
import Flex.VCG.STLC.Semantics
import Flex.VCG.STLC.Safety
import Flex.VCG.STLC.Examples
