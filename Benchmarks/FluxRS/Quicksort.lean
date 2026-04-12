import LeanFixpoint

open Classical

-- Inlined definitions (standalone, no imports needed)
abbrev Arr (t0 : Type) [Inhabited t0] : Type := Int -> t0

@[ext]
structure VectorsAVec (t0 : Type) [Inhabited t0] where
  mkVectorsAVec₀ ::
    elems : (Arr t0)
    len : Int

@[simp]
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

noncomputable def is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, (lo <= i && i <= hi) -> (∃ j, lo <= j /\ j <= hi /\ new i = old j))

noncomputable def is_frame (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, i < lo -> new i = old i) /\ (∀ i, (hi < i) -> new i = old i)

noncomputable def sort_is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  is_perm old new lo hi /\ is_frame old new lo hi

-- acyclic (non-cut) kvars
-- def k0 (lo₀ : Int) (p₀ : Int) (v₀ : (VectorsAVec Int)) (hi₀ : Int) (old₀ : (VectorsAVec Int)) (a'₆ : (Arr Int)) (a'₇ : Int) (a'₈ : (Arr Int)) (a'₉ : Int) (a'₁₀ : Int) (a'₁₁ : Int) (a'₁₂ : Int) (a'₁₃ : (Arr Int)) (a'₁₄ : Int) : Prop :=
--   (((∃ (a'₁₅ : (VectorsAVec Int)), ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₁₅))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((p₀ - 1) + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₁₅))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (p₀ - 1)) ∧ (a'₆ = (VectorsAVec.elems a'₁₅)) ∧ (a'₇ = (VectorsAVec.len a'₁₅)) ∧ ((VectorsAVec.len a'₁₅) = (VectorsAVec.len v₀)) ∧ ((VectorsAVec.len a'₁₅) ≥ 0))) ∧ (((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (a'₈ = (VectorsAVec.elems old₀)) ∧ (a'₉ = (VectorsAVec.len old₀)) ∧ (a'₁₀ = lo₀) ∧ (a'₁₁ = hi₀) ∧ (a'₁₂ = p₀) ∧ (a'₁₃ = (VectorsAVec.elems v₀)) ∧ (a'₁₄ = (VectorsAVec.len v₀)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < p₀) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)) ∨ ((((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (¬(lo₀ < p₀)) ∧ (a'₆ = (VectorsAVec.elems v₀)) ∧ (a'₇ = (VectorsAVec.len v₀)) ∧ (a'₈ = (VectorsAVec.elems old₀)) ∧ (a'₉ = (VectorsAVec.len old₀)) ∧ (a'₁₀ = lo₀) ∧ (a'₁₁ = hi₀) ∧ (a'₁₂ = p₀) ∧ (a'₁₃ = (VectorsAVec.elems v₀)) ∧ (a'₁₄ = (VectorsAVec.len v₀)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)))
-- def k1 (p₀ : Int) (hi₀ : Int) (a'₃ : (VectorsAVec Int)) (v₀ : (VectorsAVec Int)) (lo₀ : Int) (old₀ : (VectorsAVec Int)) (a'₁₆ : (Arr Int)) (a'₁₇ : Int) (a'₁₈ : (Arr Int)) (a'₁₉ : Int) (a'₂₀ : Int) (a'₂₁ : Int) (a'₂₂ : Int) (a'₂₃ : (Arr Int)) (a'₂₄ : Int) (a'₂₅ : (Arr Int)) (a'₂₆ : Int) : Prop :=
--   (((∃ (a'₂₇ : (VectorsAVec Int)), ((((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₇))) : ((Int -> (Int -> Prop)))) (p₀ + 1))) : ((Int -> Prop))) (hi₀ + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems a'₃))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₇))) : ((Int -> (Int -> Prop)))) (p₀ + 1))) : ((Int -> Prop))) hi₀) ∧ (a'₁₆ = (VectorsAVec.elems a'₂₇)) ∧ (a'₁₇ = (VectorsAVec.len a'₂₇)) ∧ ((VectorsAVec.len a'₂₇) = (VectorsAVec.len a'₃)) ∧ ((VectorsAVec.len a'₂₇) ≥ 0))) ∧ (((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (((∃ (a'₂₈ : (VectorsAVec Int)), (((VectorsAVec.len a'₂₈) = (VectorsAVec.len v₀)) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₈))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((p₀ - 1) + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₈))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (p₀ - 1)) ∧ ((VectorsAVec.len a'₂₈) ≥ 0) ∧ ((VectorsAVec.len a'₂₈) ≥ 0) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems a'₂₈)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len a'₂₈)))) ∧ (lo₀ < p₀)) ∨ ((¬(lo₀ < p₀)) ∧ (¬(lo₀ < p₀)) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems v₀)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len v₀)))) ∧ (a'₂₆ = (VectorsAVec.len a'₃)) ∧ (a'₁₈ = (VectorsAVec.elems old₀)) ∧ (a'₁₉ = (VectorsAVec.len old₀)) ∧ (a'₂₀ = lo₀) ∧ (a'₂₁ = hi₀) ∧ (a'₂₂ = p₀) ∧ (a'₂₃ = (VectorsAVec.elems v₀)) ∧ (a'₂₄ = (VectorsAVec.len v₀)) ∧ (a'₂₅ = (VectorsAVec.elems a'₃)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (p₀ < hi₀) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)) ∨ ((((((((((((((((sort_is_partitioned_by) : (((Arr Int) -> (Int -> (Int -> (Int -> (Int -> Prop))))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> (Int -> (Int -> Prop)))))) lo₀)) : ((Int -> (Int -> (Int -> Prop))))) p₀)) : ((Int -> (Int -> Prop)))) (hi₀ + 1))) : ((Int -> Prop))) p₀) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems old₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems v₀))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) hi₀) ∧ (((∃ (a'₂₉ : (VectorsAVec Int)), (((VectorsAVec.len a'₂₉) = (VectorsAVec.len v₀)) ∧ (((((((((sort_is_sorted_between) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₉))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) ((p₀ - 1) + 1)) ∧ ((((((((((((sort_is_perm) : (((Arr Int) -> ((Arr Int) -> (Int -> (Int -> Prop)))))) (VectorsAVec.elems v₀))) : (((Arr Int) -> (Int -> (Int -> Prop))))) (VectorsAVec.elems a'₂₉))) : ((Int -> (Int -> Prop)))) lo₀)) : ((Int -> Prop))) (p₀ - 1)) ∧ ((VectorsAVec.len a'₂₉) ≥ 0) ∧ ((VectorsAVec.len a'₂₉) ≥ 0) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems a'₂₉)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len a'₂₉)))) ∧ (lo₀ < p₀)) ∨ ((¬(lo₀ < p₀)) ∧ (¬(lo₀ < p₀)) ∧ ((VectorsAVec.elems a'₃) = (VectorsAVec.elems v₀)) ∧ ((VectorsAVec.len a'₃) = (VectorsAVec.len v₀)))) ∧ (¬(p₀ < hi₀)) ∧ (a'₁₆ = (VectorsAVec.elems a'₃)) ∧ (a'₁₇ = (VectorsAVec.len a'₃)) ∧ (a'₂₆ = (VectorsAVec.len a'₃)) ∧ (a'₁₈ = (VectorsAVec.elems old₀)) ∧ (a'₁₉ = (VectorsAVec.len old₀)) ∧ (a'₂₀ = lo₀) ∧ (a'₂₁ = hi₀) ∧ (a'₂₂ = p₀) ∧ (a'₂₃ = (VectorsAVec.elems v₀)) ∧ (a'₂₄ = (VectorsAVec.len v₀)) ∧ (a'₂₅ = (VectorsAVec.elems a'₃)) ∧ ((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (p₀ ≥ 0) ∧ (hi₀ ≥ 0) ∧ (lo₀ ≥ 0) ∧ ((VectorsAVec.len v₀) ≥ 0) ∧ ((VectorsAVec.len old₀) ≥ 0) ∧ (hi₀ < (VectorsAVec.len old₀)) ∧ (lo₀ < hi₀) ∧ (lo₀ < (VectorsAVec.len old₀)) ∧ (p₀ ≤ hi₀) ∧ (lo₀ ≤ p₀)))

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

-- theorem is_smaller_perm :
--   sort_is_smaller a lo p p -> sort_is_perm a a' lo (p-1) -> sort_is_smaller a' lo p p
--   := by
--   intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_smaller_perm' :
  sort_is_smaller a p hi p -> sort_is_perm a a' lo (p - 1) -> sort_is_smaller a' p hi p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_smaller_perm :
  sort_is_smaller a1 p (hi + 1) p -> sort_is_perm a1 a2 (p + 1) hi -> sort_is_smaller a2 p (hi + 1) p
  := by
  intros; simp_all [sort_is_smaller, sort_is_perm, is_perm, is_frame]; grind

theorem is_sorted_using_pivot :
  sort_is_sorted_between a lo p ->
  sort_is_sorted_between a (p + 1) (hi + 1) ->
  sort_is_bigger a lo p p ->
  sort_is_smaller a p (hi + 1) p ->
  sort_is_sorted_between a lo (hi + 1)
  := by
  simp_all [sort_is_smaller, sort_is_bigger, sort_is_sorted_between]; grind

def qs_k1 (p : Int) (_hi : Int) (a1 a0 : VectorsAVec Int) (lo : Int) (old : VectorsAVec Int) (_a2_elems : Arr Int) (a2_len : Int) (_ : Arr Int) (_ : Int) (_ _ _ : Int) (_ : Arr Int) (_ : Int) (_ : Arr Int) (_ : Int) : Prop :=
  a0.len = old.len /\ a1.len = old.len /\ a2_len = old.len /\
  sort_is_sorted_between a1.elems lo p /\
  is_perm a0.elems a1.elems lo p /\
  a1.elems p = a0.elems p /\
  sort_is_smaller a1.elems lo p (a1.elems p)

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

def SortQuicksortRange_proof : SortQuicksortRange := by
  solve_fusion
  dsimp only
  

  all_goals sorry
