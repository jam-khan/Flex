import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AnfExp
open Classical
set_option linter.unusedVariables false


namespace F



def AnfImpl__0__IsAnf := ∃ k0 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : String) -> Prop, 
 ∀ (e₀ : AnfExp),
  ((AnfExp.imm e₀) -> (AnfExp.anf e₀)) ->
   ((e₀ = (AnfExp.mkAnfExp₀ True True)) ->
    ∀ (a'₀ : String),
     (True = (AnfExp.anf e₀))) ∧
   ((e₀ = (AnfExp.mkAnfExp₀ True True)) ->
    ∀ (a'₁ : Int),
     (True = (AnfExp.anf e₀))) ∧
   (∀ (e1₀ : AnfExp),
    ∀ (e2₀ : AnfExp),
     (e₀ = (AnfExp.mkAnfExp₀ False ((AnfExp.imm e1₀) ∧ (AnfExp.imm e2₀)))) ->
      ((AnfExp.imm e1₀) -> (AnfExp.anf e1₀)) ->
       ((AnfExp.imm e2₀) -> (AnfExp.anf e2₀)) ->
        ((¬(AnfExp.imm e1₀)) ->
         ((k0 False (AnfExp.imm e₀) (AnfExp.anf e₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀)))) ∧
        ((AnfExp.imm e1₀) ->
         ((k0 (AnfExp.imm e2₀) (AnfExp.imm e₀) (AnfExp.anf e₀) True (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀)))) ∧
        (∀ (a'₄ : Prop),
         ((k0 a'₄ (AnfExp.imm e₀) (AnfExp.anf e₀) (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀))) ->
          (a'₄ = (AnfExp.anf e₀)))
        ) ∧
   (∀ (e1₁ : AnfExp),
    ∀ (e2₁ : AnfExp),
     (e₀ = (AnfExp.mkAnfExp₀ False ((AnfExp.anf e1₁) ∧ (AnfExp.anf e2₁)))) ->
      ∀ (a'₇ : String),
       ((AnfExp.imm e1₁) -> (AnfExp.anf e1₁)) ->
        ((AnfExp.imm e2₁) -> (AnfExp.anf e2₁)) ->
         ((¬(AnfExp.anf e1₁)) ->
          ((k1 False (AnfExp.imm e₀) (AnfExp.anf e₀) (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₇))) ∧
         ((AnfExp.anf e1₁) ->
          ((k1 (AnfExp.anf e2₁) (AnfExp.imm e₀) (AnfExp.anf e₀) (AnfExp.imm e1₁) True (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₇))) ∧
         (∀ (a'₈ : Prop),
          ((k1 a'₈ (AnfExp.imm e₀) (AnfExp.anf e₀) (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₇)) ->
           (a'₈ = (AnfExp.anf e₀)))
         )
   
end F
