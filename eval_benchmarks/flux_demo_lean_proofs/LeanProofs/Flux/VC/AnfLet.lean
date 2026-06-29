import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AnfExp
open Classical
set_option linter.unusedVariables false


namespace F



def AnfLet := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : String) -> (a7 : String) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : String) -> (a7 : String) -> (a8 : Prop) -> (a9 : Prop) -> Prop, 
 ∀ (e1₀ : AnfExp),
  ∀ (e2₀ : AnfExp),
   ∀ (a'₀ : String),
    ((AnfExp.imm e1₀) -> (AnfExp.anf e1₀)) ->
     ((AnfExp.imm e2₀) -> (AnfExp.anf e2₀)) ->
      ∀ (a'₁ : String),
       (((k0 (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) a'₀ a'₁))) ∧
       (∀ (a'₂ : AnfExp),
        ((k0 (AnfExp.imm a'₂) (AnfExp.anf a'₂) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) a'₀ a'₁)) ->
         ((AnfExp.imm a'₂) -> (AnfExp.anf a'₂)) ->
          (((k1 (AnfExp.imm e2₀) (AnfExp.anf e2₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) a'₀ a'₁ (AnfExp.imm a'₂) (AnfExp.anf a'₂)))) ∧
          (∀ (a'₃ : AnfExp),
           ((k1 (AnfExp.imm a'₃) (AnfExp.anf a'₃) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) a'₀ a'₁ (AnfExp.imm a'₂) (AnfExp.anf a'₂))) ->
            ((AnfExp.imm a'₃) -> (AnfExp.anf a'₃)) ->
             (((AnfExp.anf a'₂) ∧ (AnfExp.anf a'₃)) = ((AnfExp.anf e1₀) ∧ (AnfExp.anf e2₀))))
          )
       
end F
