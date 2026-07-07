import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AnfExp
open Classical
set_option linter.unusedVariables false


namespace F



def AnfImpl__0__ToAnf := ∃ k0 : (a0 : Int) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Int) -> (a13 : Int) -> (a14 : Prop) -> (a15 : Prop) -> (a16 : Int) -> (a17 : Int) -> Prop, ∃ k1 : (a0 : String) -> (a1 : Int) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Int) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Int) -> (a14 : Int) -> (a15 : Prop) -> (a16 : Prop) -> (a17 : Int) -> (a18 : Int) -> Prop, ∃ k2 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Int) -> (a3 : Prop) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Int) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Prop) -> (a14 : Int) -> (a15 : Int) -> (a16 : Prop) -> (a17 : Prop) -> (a18 : Int) -> (a19 : Int) -> Prop, ∃ k3 : (a0 : String) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Prop) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Int) -> (a11 : Int) -> (a12 : Prop) -> (a13 : Prop) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Prop) -> (a18 : Prop) -> Prop, ∃ k4 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Prop) -> (a14 : Prop) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Prop) -> (a19 : Prop) -> Prop, 
 ∀ (a'₀ : AnfExp),
  ((AnfExp.imm a'₀) -> (AnfExp.anf a'₀)) ->
   ∀ (count₀ : Int),
    (count₀ ≥ 0) ->
     ((a'₀ = (AnfExp.mkAnfExp₀ True True)) ->
      ∀ (a'₂ : String),
       ∀ (a'₃ : String),
        ∀ (e₀ : AnfExp),
         (AnfExp.imm e₀) ->
          (True -> (AnfExp.anf e₀)) ->
           (AnfExp.anf e₀)) ∧
     ((a'₀ = (AnfExp.mkAnfExp₀ True True)) ->
      ∀ (a'₅ : Int),
       ∀ (e₁ : AnfExp),
        (AnfExp.imm e₁) ->
         (True -> (AnfExp.anf e₁)) ->
          (AnfExp.anf e₁)) ∧
     (∀ (e1₀ : AnfExp),
      ∀ (e2₀ : AnfExp),
       (a'₀ = (AnfExp.mkAnfExp₀ False ((AnfExp.imm e1₀) ∧ (AnfExp.imm e2₀)))) ->
        ((AnfExp.imm e1₀) -> (AnfExp.anf e1₀)) ->
         ((AnfExp.imm e2₀) -> (AnfExp.anf e2₀)) ->
          ∀ (v1₀ : AnfExp),
           (AnfExp.imm v1₀) ->
            (True -> (AnfExp.anf v1₀)) ->
             ∀ (count₁ : Int),
              (count₁ ≥ 0) ->
               ∀ (binds₀ : Int),
                (0 ≤ binds₀) ->
                 ∀ (v2₀ : AnfExp),
                  (AnfExp.imm v2₀) ->
                   (True -> (AnfExp.anf v2₀)) ->
                    ∀ (count₂ : Int),
                     (count₂ ≥ 0) ->
                      ∀ (binds₁ : Int),
                       (0 ≤ binds₁) ->
                        (((k0 binds₁ False True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁))) ∧
                        (∀ (a'₁₅ : String),
                         ∀ (e₂ : AnfExp),
                          (AnfExp.anf e₂) ->
                           (((k1 a'₁₅ binds₁ False True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁))) ∧
                           (((k2 (AnfExp.imm e₂) True binds₁ False True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁)))
                           ) ∧
                        (∀ (binds₂ : Int),
                         ∀ (res₀ : Prop),
                          ∀ (res₁ : Prop),
                           ((k0 binds₂ res₀ res₁ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁)) ->
                            ((binds₂ ≠ 0) ->
                             ((binds₂ > 0)) ∧
                             (∀ (a'₂₀ : String),
                              ((k1 a'₂₀ binds₂ res₀ res₁ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁)) ->
                               ∀ (a'₂₁ : AnfExp),
                                ((k2 (AnfExp.imm a'₂₁) (AnfExp.anf a'₂₁) binds₂ res₀ res₁ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁)) ->
                                 (((k3 a'₂₀ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁ binds₂ res₀ res₁))) ∧
                                 (((k4 (AnfExp.imm a'₂₁) (AnfExp.anf a'₂₁) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁ binds₂ res₀ res₁)))
                                 ) ∧
                             ((0 ≤ (binds₂ - 1)) ->
                              ∀ (a'₂₂ : String),
                               ((k3 a'₂₂ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁ binds₂ res₀ res₁)) ->
                                ∀ (a'₂₃ : AnfExp),
                                 ((k4 (AnfExp.imm a'₂₃) (AnfExp.anf a'₂₃) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁ binds₂ res₀ res₁)) ->
                                  ((AnfExp.imm a'₂₃) -> (AnfExp.anf a'₂₃)) ->
                                   ∀ (a'₂₄ : String),
                                    (False -> ((AnfExp.anf a'₂₃) ∧ res₁)) ->
                                     (((k0 (binds₂ - 1) False ((AnfExp.anf a'₂₃) ∧ res₁) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁))) ∧
                                     (∀ (a'₂₅ : String),
                                      ((k3 a'₂₅ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁ binds₂ res₀ res₁)) ->
                                       ∀ (a'₂₆ : AnfExp),
                                        ((k4 (AnfExp.imm a'₂₆) (AnfExp.anf a'₂₆) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁ binds₂ res₀ res₁)) ->
                                         (((k1 a'₂₅ (binds₂ - 1) False ((AnfExp.anf a'₂₃) ∧ res₁) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁))) ∧
                                         (((k2 (AnfExp.imm a'₂₆) (AnfExp.anf a'₂₆) (binds₂ - 1) False ((AnfExp.anf a'₂₃) ∧ res₁) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₀ True (AnfExp.anf v2₀) count₂ binds₁)))
                                         )
                                     )
                             ) ∧
                            ((¬(binds₂ ≠ 0)) ->
                             res₁)
                            )
                        )
     
end F
