import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AnfExp
open Classical
set_option linter.unusedVariables false


namespace F



def AnfImpl__0__IsImm := 
 ∀ (e₀ : AnfExp),
  ((AnfExp.imm e₀) -> (AnfExp.anf e₀)) ->
   ((e₀ = (AnfExp.mkAnfExp₀ True True)) ->
    ∀ (a'₀ : String),
     (True = (AnfExp.imm e₀))) ∧
   ((e₀ = (AnfExp.mkAnfExp₀ True True)) ->
    ∀ (a'₁ : Int),
     (True = (AnfExp.imm e₀))) ∧
   (∀ (e1₀ : AnfExp),
    ∀ (e2₀ : AnfExp),
     (e₀ = (AnfExp.mkAnfExp₀ False ((AnfExp.imm e1₀) ∧ (AnfExp.imm e2₀)))) ->
      ((AnfExp.imm e1₀) -> (AnfExp.anf e1₀)) ->
       ((AnfExp.imm e2₀) -> (AnfExp.anf e2₀)) ->
        (False = (AnfExp.imm e₀))) ∧
   (∀ (e1₁ : AnfExp),
    ∀ (e2₁ : AnfExp),
     (e₀ = (AnfExp.mkAnfExp₀ False ((AnfExp.anf e1₁) ∧ (AnfExp.anf e2₁)))) ->
      ∀ (a'₆ : String),
       ((AnfExp.imm e1₁) -> (AnfExp.anf e1₁)) ->
        ((AnfExp.imm e2₁) -> (AnfExp.anf e2₁)) ->
         (False = (AnfExp.imm e₀)))
   
end F
