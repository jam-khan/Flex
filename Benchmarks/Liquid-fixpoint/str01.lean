import LeanFixpoint
/-

Below requires addition of native_decide

(constraint
  (and
    (forall ((x Str) ((= x "cat")))
      (forall ((y Str) ((= y "dogeral")))
        (and
          ((= (strLen x) 3))
          ((= (strLen y) 7)))))

    (forall ((x Str) ((= x "cat")))
      (forall ((y Str) ((= y "caterpillar")))
        ((strPrefixOf x y))))

    (forall ((x Str) ((= x "pillar")))
      (forall ((y Str) ((= y "caterpillar")))
        ((strSuffixOf x y))))

    (forall ((x Str) ((= x "pill")))
      (forall ((y Str) ((= y "caterpillar")))
        ((strContains y x))))

    (forall ((x Str) ((= x "hot")))
      (forall ((y Str) ((= y "dog")))
        (forall ((z Str) ((= z "hotdog")))
          (and
            ((= (strConcat x y) z))))))
  )
)
-/



def str01Prop : Prop :=
  -- strLen
  (∀ x : String, x = "cat" → ∀ y : String, y = "dogeral" →
    x.length = 3 ∧ y.length = 7)
  -- strPrefixOf x y  (y starts with x)
  ∧ (∀ x : String, x = "cat" → ∀ y : String, y = "caterpillar" →
    (y.startsWith x))
  -- strSuffixOf x y  (y ends with x)
  ∧ (∀ x : String, x = "pillar" → ∀ y : String, y = "caterpillar" →
    (y.endsWith x))
  -- strContains y x  (y contains x as substring)
  ∧ (∀ x : String, x = "pill" → ∀ y : String, y = "caterpillar" →
    (y.splitOn x).length > 1)
  -- strConcat
  ∧ (∀ x : String, x = "hot" → ∀ y : String, y = "dog" →
    ∀ z : String, z = "hotdog" → x ++ y = z)

theorem str01Proof : str01Prop := by
  solve_fusion
  -- sorry
  -- solve_fusion
