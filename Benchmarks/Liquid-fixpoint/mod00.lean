import LeanFixpoint
/-
; this is a comment too.

(var $k0 (int))


; this is a comment
(constraint
  (and ; this is a random comment
    (and
      (forall ((a0 int) ((= a0 4)))
        ($k0 a0)
      )
      (forall ((a1 int) ((= a1 10)))
        ; and yet another comment
        ($k0 a1)
      )
    )
    (forall ((a2 int) (true))
    ; sprinkle sprinkle
      (forall ((_ int) ($k0 a2))
        (tag ((= ((mod a2 2)) 0)) "0")  ; lets stick a comment here too!
      )
    )
  )
)
-/

def mod00Prop : Prop :=
  ∃ κ0 : Int → Prop,
    (∀ a0 : Int, a0 = 4 → κ0 a0)
    ∧ (∀ a1 : Int, a1 = 10 → κ0 a1)
    ∧ (∀ a2 : Int, True → ∀ _ : Int, κ0 a2 → a2 % 2 = 0)

theorem mod00Proof : mod00Prop := by
  solve_fusion
  
