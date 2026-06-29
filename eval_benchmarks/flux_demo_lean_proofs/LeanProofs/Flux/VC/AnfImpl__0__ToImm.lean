import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.AnfExp
open Classical
set_option linter.unusedVariables false


namespace F



def AnfImpl__0__ToImm := ∃ k0 : (a0 : String) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Int) -> (a12 : Int) -> (a13 : Prop) -> (a14 : Prop) -> (a15 : Int) -> (a16 : Int) -> (a17 : String) -> (a18 : Int) -> Prop, ∃ k1 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Int) -> (a13 : Int) -> (a14 : Prop) -> (a15 : Prop) -> (a16 : Int) -> (a17 : Int) -> (a18 : String) -> (a19 : Int) -> Prop, ∃ k2 : (a0 : String) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Int) -> (a4 : Int) -> (a5 : Prop) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : String) -> (a10 : Prop) -> (a11 : Prop) -> (a12 : Int) -> (a13 : String) -> (a14 : Int) -> Prop, ∃ k3 : (a0 : Prop) -> (a1 : Prop) -> (a2 : Prop) -> (a3 : Prop) -> (a4 : Int) -> (a5 : Int) -> (a6 : Prop) -> (a7 : Prop) -> (a8 : Prop) -> (a9 : Prop) -> (a10 : String) -> (a11 : Prop) -> (a12 : Prop) -> (a13 : Int) -> (a14 : String) -> (a15 : Int) -> Prop, 
 ∀ (a'₀ : AnfExp),
  ((AnfExp.imm a'₀) -> (AnfExp.anf a'₀)) ->
   ∀ (count₀ : Int),
    (count₀ ≥ 0) ->
     ∀ (binds₀ : Int),
      (0 ≤ binds₀) ->
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
                 ∀ (binds₁ : Int),
                  (0 ≤ binds₁) ->
                   ∀ (v2₀ : AnfExp),
                    (AnfExp.imm v2₀) ->
                     (True -> (AnfExp.anf v2₀)) ->
                      ∀ (count₂ : Int),
                       (count₂ ≥ 0) ->
                        ∀ (binds₂ : Int),
                         (0 ≤ binds₂) ->
                          ∀ (tmp₀ : String),
                           ∀ (count₃ : Int),
                            (count₃ ≥ 0) ->
                             (∀ (a'₁₃ : String),
                              ∀ (e₀ : AnfExp),
                               (AnfExp.anf e₀) ->
                                (((k0 a'₁₃ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₁ True (AnfExp.anf v2₀) count₂ binds₂ tmp₀ count₃))) ∧
                                (((k1 (AnfExp.imm e₀) True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₁ True (AnfExp.anf v2₀) count₂ binds₂ tmp₀ count₃)))
                                ) ∧
                             (((k0 tmp₀ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₁ True (AnfExp.anf v2₀) count₂ binds₂ tmp₀ count₃))) ∧
                             (((k1 False True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₁ True (AnfExp.anf v2₀) count₂ binds₂ tmp₀ count₃))) ∧
                             ((0 ≤ (binds₂ + 1)) ->
                              ∀ (a'₁₅ : String),
                               ((k0 a'₁₅ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₁ True (AnfExp.anf v2₀) count₂ binds₂ tmp₀ count₃)) ->
                                ∀ (a'₁₆ : AnfExp),
                                 ((k1 (AnfExp.imm a'₁₆) (AnfExp.anf a'₁₆) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₀) (AnfExp.anf e1₀) (AnfExp.imm e2₀) (AnfExp.anf e2₀) True (AnfExp.anf v1₀) count₁ binds₁ True (AnfExp.anf v2₀) count₂ binds₂ tmp₀ count₃)) ->
                                  (AnfExp.anf a'₁₆))
                             ) ∧
       (∀ (e1₁ : AnfExp),
        ∀ (e2₁ : AnfExp),
         (a'₀ = (AnfExp.mkAnfExp₀ False ((AnfExp.anf e1₁) ∧ (AnfExp.anf e2₁)))) ->
          ∀ (a'₁₉ : String),
           ((AnfExp.imm e1₁) -> (AnfExp.anf e1₁)) ->
            ((AnfExp.imm e2₁) -> (AnfExp.anf e2₁)) ->
             ∀ (a₀ : AnfExp),
              (AnfExp.anf a₀) ->
               ((AnfExp.imm a₀) -> True) ->
                ∀ (count₄ : Int),
                 (count₄ ≥ 0) ->
                  ∀ (tmp₁ : String),
                   ∀ (count₅ : Int),
                    (count₅ ≥ 0) ->
                     (∀ (a'₂₄ : String),
                      ∀ (e₁ : AnfExp),
                       (AnfExp.anf e₁) ->
                        (((k2 a'₂₄ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₁₉ (AnfExp.imm a₀) True count₄ tmp₁ count₅))) ∧
                        (((k3 (AnfExp.imm e₁) True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₁₉ (AnfExp.imm a₀) True count₄ tmp₁ count₅)))
                        ) ∧
                     (((k2 tmp₁ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₁₉ (AnfExp.imm a₀) True count₄ tmp₁ count₅))) ∧
                     (((k3 (AnfExp.imm a₀) True (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₁₉ (AnfExp.imm a₀) True count₄ tmp₁ count₅))) ∧
                     ((0 ≤ (binds₀ + 1)) ->
                      ∀ (a'₂₆ : String),
                       ((k2 a'₂₆ (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₁₉ (AnfExp.imm a₀) True count₄ tmp₁ count₅)) ->
                        ∀ (a'₂₇ : AnfExp),
                         ((k3 (AnfExp.imm a'₂₇) (AnfExp.anf a'₂₇) (AnfExp.imm a'₀) (AnfExp.anf a'₀) count₀ binds₀ (AnfExp.imm e1₁) (AnfExp.anf e1₁) (AnfExp.imm e2₁) (AnfExp.anf e2₁) a'₁₉ (AnfExp.imm a₀) True count₄ tmp₁ count₅)) ->
                          (AnfExp.anf a'₂₇))
                     )
       
end F
