import LeanFixpoint

open Classical

-- Inlined definitions (standalone, no imports needed)
abbrev Arr (t0 : Type) [Inhabited t0] : Type := Int -> t0

@[ext]
structure VectorsAVec (t0 : Type) [Inhabited t0] where
  mkVectorsAVec₀ ::
    elems : (Arr t0)
    len : Int

@[simp, reducible]
def sort_is_sorted_between (a: Arr Int) (lo hi: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi) -> (a i <= a j)

@[simp]
noncomputable def sort_is_bigger (arr: Arr Int) (lo hi p: Int) : Prop :=
  forall ix, (lo <= ix /\ ix < hi) -> (arr ix <= arr p)

@[simp]
noncomputable def sort_is_smaller (arr: Arr Int) (lo hi p: Int) : Prop :=
  forall ix, (lo <= ix /\ ix < hi) -> (arr p <= arr ix)

@[simp]
noncomputable def sort_is_partitioned_by (arr: Arr Int) (lo mid hi pivot: Int) : Prop :=
  sort_is_bigger arr lo mid pivot /\ sort_is_smaller arr mid hi pivot

@[simp]
noncomputable def is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, (lo <= i && i <= hi) -> (∃ j, lo <= j /\ j <= hi /\ new i = old j))

@[simp]
noncomputable def is_frame (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, i < lo -> new i = old i) /\ (∀ i, (hi < i) -> new i = old i)

@[simp]
noncomputable def sort_is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  is_perm old new lo hi /\ is_frame old new lo hi

def SortQuicksortRange := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : (VectorsAVec Int)) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (VectorsAVec Int)) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : (Arr Int)) -> (a14 : Int) -> (a15 : (Arr Int)) -> (a16 : Int) -> Prop,
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     (hi₀ < (VectorsAVec.len old₀)) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         ((¬(lo₀ < hi₀)) ->
          (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
          ((sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (hi₀ + 1))) ∧
          ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems old₀) lo₀ hi₀))
          ) ∧
         ((lo₀ < hi₀) ->
          ∀ (p₀ : Int),
           ∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_partitioned_by (VectorsAVec.elems v₀) lo₀ p₀ (hi₀ + 1) p₀) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) lo₀ hi₀) ∧ (lo₀ ≤ p₀) ∧ (p₀ ≤ hi₀)) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              (p₀ ≥ 0) ->
               ((¬(lo₀ < p₀)) ->
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
               ((lo₀ < p₀) ->
                (((p₀ - 1) ≥ 0)) ∧
                ((lo₀ < (VectorsAVec.len v₀))) ∧
                (((p₀ - 1) < (VectorsAVec.len v₀))) ∧
                (∀ (v₁ : (VectorsAVec Int)),
                 (((VectorsAVec.len v₁) = (VectorsAVec.len v₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₁) lo₀ ((p₀ - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₀) (VectorsAVec.elems v₁) lo₀ (p₀ - 1))) ->
                  ((VectorsAVec.len v₁) ≥ 0) ->
                   ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₁) (VectorsAVec.len v₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))))
                ) ∧
               (∀ (a'₃ : (VectorsAVec Int)),
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                 ((¬(p₀ < hi₀)) ->
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                 ((p₀ < hi₀) ->
                  (((p₀ + 1) < (VectorsAVec.len a'₃))) ∧
                  ((hi₀ < (VectorsAVec.len a'₃))) ∧
                  (∀ (v₂ : (VectorsAVec Int)),
                   (((VectorsAVec.len v₂) = (VectorsAVec.len a'₃)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₂) (p₀ + 1) (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems a'₃) (VectorsAVec.elems v₂) (p₀ + 1) hi₀)) ->
                    ((VectorsAVec.len v₂) ≥ 0) ->
                     ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems v₂) (VectorsAVec.len v₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                  ) ∧
                 (∀ (a'₅ : (VectorsAVec Int)),
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₅) (VectorsAVec.len a'₅) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                   (((VectorsAVec.len a'₅) = (VectorsAVec.len old₀))) ∧
                   ((sort_is_sorted_between (VectorsAVec.elems a'₅) lo₀ (hi₀ + 1))) ∧
                   ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems a'₅) lo₀ hi₀))
                   )
                 )
               )

theorem bigger_perm :
  sort_is_bigger a lo p p -> sort_is_perm a a' lo (p-1) -> sort_is_bigger a' lo p p
  := by
  intros; simp_all [sort_is_bigger, sort_is_perm, is_perm, is_frame]; grind

theorem sort_is_perm_trans :
  sort_is_perm old new lo hi -> sort_is_perm new new' lo hi -> sort_is_perm old new' lo hi
  := by
  intros; simp_all [sort_is_perm, is_perm, is_frame]; grind

theorem sort_is_perm_id : sort_is_perm arr arr lo hi := by
  intros; simp_all [sort_is_perm, is_perm, is_frame]; intros i _ _; exists i

theorem is_perm_trans :
  is_perm old new lo hi -> is_perm new new' lo hi -> is_perm old new' lo hi
  := by
  intros; simp_all [is_perm]; grind

theorem is_perm_id : is_perm arr arr lo hi := by
  intros; simp_all [is_perm]; intros i _ _; exists i

theorem is_smaller_perm' :
  sort_is_smaller a p hi p -> sort_is_perm a a' lo (p - 1) -> sort_is_smaller a' p hi p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_smaller_perm :
  sort_is_smaller a1 p (hi + 1) p -> sort_is_perm a1 a2 (p + 1) hi -> sort_is_smaller a2 p (hi + 1) p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

@[simp]
theorem is_sorted_using_pivot :
  sort_is_sorted_between a lo p ->
  sort_is_sorted_between a (p + 1) (hi + 1) ->
  sort_is_bigger a lo p p ->
  sort_is_smaller a p (hi + 1) p ->
  sort_is_sorted_between a lo (hi + 1)
  := by
  simp_all [sort_is_smaller, sort_is_bigger, sort_is_sorted_between]; grind

set_option maxHeartbeats 1600000 in
theorem SortQuicksortRange_proof : SortQuicksortRange := by
  unfold SortQuicksortRange
  zapK
  all_goals (
    split_hyps
    -- Collapse False branches that just got exposed by β-reducing
    -- the κ-witness lambdas into the new hypothesis types.
    all_goals (try simp only
      [or_false, false_or, and_false] at *)
    all_goals (try grind)
    -- all_goals (try aesop)
  )
  case _ => refine ⟨fun i _ => ⟨i, ?_, ?_, rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩
            <;> simp_all
  -- Residual 2 + 3 — the actual quicksort math.
  --
  -- Both require taking the κ-hypotheses (named hyp1 and hyp2 below) and
  -- destructuring them through their outer ∃-binders (p₀_1, v₀_1, a'₃_1
  -- and the re-intro'd old₀, lo₀, hi₀, p₀, v₀) before reaching the
  -- (no-rec ∨ rec) disjunction that carries the recursive-call witness.
  -- The old proof against a hand-defined k0/k1 used `rw [k0] at hyp1;
  -- split_hyp_ors`, which exposed the Or at the surface; the current
  -- zapK-generated k0/k1 have the outer ∀-binders of the SortQuicksortRange
  -- definition baked into ∃-binders, so the Or is nested ~6 binders deep.
  --
  -- Once destructured (use `obtain ⟨_, _, _, _, _, _, p_w, v_w, ⟨_, _, _,
  -- _, _⟩, _, _, a3_w, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
  -- ⟨...⟩⟩, hor⟩ := hyp1`), the proof chain is:
  --
  --   * Residual 2: apply `is_sorted_using_pivot` after extracting
  --     a'₃ sorted on [lo, p] and a'₅ sorted on [p+1, hi+1] from the
  --     two κ-hypotheses, plus `bigger_perm` / `is_smaller_perm` /
  --     `is_smaller_perm'` to lift the partition's pivot bounds through
  --     the perm chain v₀ → a'₃ → a'₅.
  --
  --   * Residual 3: chain three `is_perm_trans` applications:
  --     old₀ → v₀ (from outer hyp0)
  --     v₀  → a'₃ (from κ0's left-rec)
  --     a'₃ → a'₅ (from κ1's right-rec)
  --     plus the frame conjuncts from `sort_is_perm`'s `is_frame`.
  case _ => sorry
  case _ => sorry
