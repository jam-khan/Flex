import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AnfExp
open Classical
set_option linter.unusedVariables false


namespace F



def AnfBin := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> Prop, 
 ∀ (e1₀ : AnfExp),
  ∀ (e2₀ : AnfExp),
   ((AnfExp.imm e1₀) -> (AnfExp.anf e1₀)) ->
    ((AnfExp.imm e2₀) -> (AnfExp.anf e2₀)) ->
     (((k0 (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀)))) ∧
     (∀ (a'₀ : AnfExp),
      ((k0 (AnfExp.imm a'₀) (AnfExp.anf a'₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀))) ->
       ((AnfExp.imm a'₀) -> (AnfExp.anf a'₀)) ->
        (((k1 (AnfExp.imm e2₀) (AnfExp.anf e2₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) (AnfExp.imm a'₀) (AnfExp.anf a'₀)))) ∧
        (∀ (a'₁ : AnfExp),
         ((k1 (AnfExp.imm a'₁) (AnfExp.anf a'₁) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) (AnfExp.imm a'₀) (AnfExp.anf a'₀))) ->
          ((AnfExp.imm a'₁) -> (AnfExp.anf a'₁)) ->
           (((AnfExp.imm a'₀) ∧ (AnfExp.imm a'₁)) = ((AnfExp.imm e1₀) ∧ (AnfExp.imm e2₀))))
        )
     
end F
