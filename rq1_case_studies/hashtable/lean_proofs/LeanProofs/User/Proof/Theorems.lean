import LeanProofs.User.Struct.OVec
import LeanProofs.User.Struct.ASeq
import LeanProofs.User.Fun.SvecSet
import LeanProofs.User.Fun.SvecGet
import LeanProofs.User.Fun.SvecLen
import LeanProofs.User.Fun.AlistAseqSet
import LeanProofs.User.Fun.AlistAseqLen
import LeanProofs.User.Fun.AlistAseqContainsKey
import LeanProofs.User.Fun.AlistAseqKeyMatches
import LeanProofs.User.Fun.AlistAseqRemoveKey
import LeanProofs.User.Fun.AlistAseqUniqueKeys
import LeanProofs.User.Fun.AlistAseqCons
import LeanProofs.User.Fun.BucketMapTotalLen
import LeanProofs.User.Fun.BucketMapEmpties
import LeanProofs.User.Fun.BucketMapAbsorbBucket
import LeanProofs.User.Fun.BucketMapAbsorbBuckets
import LeanProofs.User.Fun.BucketMapUniqueKeys
import LeanProofs.User.Fun.BucketMapKeysDistributedByHash
import LeanProofs.User.Fun.BucketMapDisjointWithList
import LeanProofs.User.Fun.BucketMapDisjoint
open Classical

namespace F

theorem svec_set_set (v : OVec (ASeq Int Int))
  : svec_set (svec_set v k l1) k l2 = svec_set v k l2 := by
    simp

theorem svec_get_set_ne (v : OVec (ASeq Int Int)) (h : k ≠ k') (h1 : k ≥ 0) (h2 : k' ≥ 0)
  : svec_get (svec_set v k l) k' = svec_get v k' := by
    simp
    rw [List.getElem?_set_ne]
    omega

theorem svec_get_set_eq (v : OVec (ASeq Int Int)) (h : k = k') (h' : 0 ≤ k ∧ k < svec_len v)
  : svec_get (svec_set v k l) k' = l := by
    simp ; rw [List.getElem?_set] ; grind

theorem svec_len_set1 (l : ASeq Int Int)
  : svec_len (alist_aseq_set l k v) = svec_len l := by
    induction l
    case nil => simp
    case cons h t ih =>
      grind

theorem svec_len_set2 (l : OVec (ASeq Int Int))
  : svec_len (svec_set l k v) = svec_len l := by
    simp

theorem list_eq_take_drop (l : List α) : l = l.take i ++ l.drop i := by
  simp

theorem drop_sum (l : List Nat) (h : n < l.length)
  : (l.drop (n + 1)).sum = (l.drop n).sum - l[n] := by
    revert n
    induction l
    case nil => simp
    case cons hd tl ih =>
      simp ; intros n h
      cases n
      case zero =>
        simp
      case succ n =>
        rw [ih]
        grind
        grind

theorem elem_le_sum (l : List Nat) : e ∈ l → e ≤ l.sum := by
  revert e ; induction l
  case nil => simp
  case cons hd tl ih =>
    grind

theorem total_length_set (v : OVec (ASeq Int Int)) (h : 0 ≤ k ∧ k < svec_len v)
  : bucket_map_total_len (svec_set v k l) = bucket_map_total_len v + svec_len l - svec_len (svec_get v k) := by
    simp_all
    have : k.toNat < List.length v := by omega
    rw [List.set_eq_take_append_cons_drop]
    simp [this]
    conv => rhs ; rw [@list_eq_take_drop _ k.toNat (List.map List.length v)]
    rw [List.sum_append_nat, drop_sum, Int.ofNat_sub]
    · grind
    · apply elem_le_sum
      rw [List.mem_iff_getElem]
      exists 0 ; exists (by grind)
      grind
    · grind

theorem alist_set_ident_keys (l : ASeq Int Int)
  : ∀ i : Nat, (h : i < List.length l) → (h' : i < List.length (alist_aseq_set l k v)) → l[i].fst = (alist_aseq_set l k v)[i].fst := by
    induction l
    case nil => simp
    case cons hd tl ih =>
      grind

theorem alist_set_contains_contains (l : ASeq Int Int)
  : (k, x) ∈ alist_aseq_set l k' v → alist_aseq_contains_key l k := by
    fun_induction alist_aseq_set
    · simp
    · intro ; simp
      by_cases k = k' <;> grind
    · grind

theorem alist_remove_contains_contains (l : ASeq Int Int)
  : (k, x) ∈ alist_aseq_remove_key l k' → alist_aseq_contains_key l k := by
    fun_induction alist_aseq_remove_key <;> grind

theorem unique_nc_cons_nc (l : ASeq Int Int) (h : alist_aseq_unique_keys l) (h' : ¬alist_aseq_contains_key l k)
  : alist_aseq_unique_keys (alist_aseq_cons k v l) := by
    simp_all
    intros a b abelem keq
    apply h'
    rw [←keq] at abelem
    assumption

theorem unique_set_uniqe (l : ASeq Int Int) (h : alist_aseq_unique_keys l)
  : alist_aseq_unique_keys (alist_aseq_set l k v) := by
    simp at *
    rw [List.pairwise_iff_getElem] at *
    intros i j ib jb ij
    rw [←alist_set_ident_keys, ←alist_set_ident_keys]
    apply_assumption
    assumption
    grind [svec_len_set1]
    grind [svec_len_set1]

theorem unique_cons_nc (l : ASeq Int Int) (h : alist_aseq_unique_keys (alist_aseq_cons k v l))
  : ¬ alist_aseq_contains_key l k := by
    simp at * ; grind

theorem unique_remove_unique (l : ASeq Int Int) (h : alist_aseq_unique_keys l)
  : alist_aseq_unique_keys (alist_aseq_remove_key l k) := by
    fun_induction alist_aseq_remove_key
    · simp
    · grind
    · apply unique_nc_cons_nc
      apply_assumption ; grind
      intro cont
      simp at cont ; rcases cont with ⟨x, cont⟩
      have := alist_remove_contains_contains _ cont
      simp at this ; rcases this
      simp at h
      grind

theorem unique_remove_nc (l : ASeq Int Int) (h : alist_aseq_unique_keys l)
  : ¬ alist_aseq_contains_key (alist_aseq_remove_key l k) k := by
  fun_induction alist_aseq_remove_key <;> simp_all
  grind


theorem int_of_nat_le {a b : Nat} {h : a ≤ b}
  : Int.ofNat a ≤ ↑b := by
    simp ; assumption

theorem aseq_len_svec_len (l : ASeq Int Int) : alist_aseq_len l = svec_len l := by grind

theorem contains_remove_len (l : ASeq Int Int) (h : alist_aseq_contains_key l k) (h' : alist_aseq_unique_keys l)
  : svec_len (alist_aseq_remove_key l k) = svec_len l - 1 := by
    fun_induction alist_aseq_remove_key <;> grind

theorem set_get_eq (v : OVec (ASeq Int Int)) (h : 0 ≤ k ∧ k < svec_len v)
  : svec_set v k (svec_get v k) = v := by
    simp_all

theorem total_len_empties : bucket_map_total_len (bucket_map_empties n : OVec (ASeq Int Int)) = 0 := by
  induction n <;> simp

theorem alist_set_matches (l : ASeq Int Int) : alist_aseq_contains_key l k → alist_aseq_key_matches (alist_aseq_set l k v) k v := by
  intro hc
  induction l generalizing k v <;> grind

theorem key_matches_set_ne (l : ASeq Int Int) (hne : k' ≠ k)
  : alist_aseq_key_matches l k' v' ↔ alist_aseq_key_matches (alist_aseq_set l k v) k' v' := by
  induction l generalizing k k' v v' <;> simp_all ; grind

theorem mem_alist_aseq_set_or_eq (l : ASeq Int Int) (k v : Int) (e : Int × Int)
  (h : e ∈ alist_aseq_set l k v) : e ∈ l ∨ e = (k, v) := by
    induction l <;> grind

theorem mem_absorb (v : OVec (ASeq Int Int)) (h : b' ∈ bucket_map_absorb_bucket v b) (h' : e ∈ b')
  : (∃ s, s ∈ v ∧ e ∈ s) ∨ e ∈ b := by
    induction b generalizing v b' e with
    | nil =>
      simp [bucket_map_absorb_bucket] at h ⊢
      exact ⟨b', h, h'⟩
    | cons hd tl ih =>
      rcases hd with ⟨k, val⟩
      simp [bucket_map_absorb_bucket] at h ⊢
      have hrec := ih (v := insert v k val) (b' := b') (e := e) h h'
      rcases hrec with hrec | hrec
      · rcases hrec with ⟨s, hs, he⟩
        unfold insert at hs
        change
          s ∈
            svec_set v (k % svec_len v)
              (if alist_aseq_contains_key (svec_get v (k % svec_len v)) k then
                alist_aseq_set (svec_get v (k % svec_len v)) k val
              else
                alist_aseq_cons k val (svec_get v (k % svec_len v))) at hs
        rcases List.mem_or_eq_of_mem_set hs with hs | hs
        · exact Or.inl ⟨s, hs, he⟩
        · subst hs
          by_cases hck : (∃ x, (k, x) ∈ v[(k % ↑(List.length v)).toNat]?.getD [])
          · simp [Inhabited.default, hck] at he
            rcases
                mem_alist_aseq_set_or_eq (v[(k % ↑(List.length v)).toNat]?.getD []) k val e he with
              he' | he'
            · grind
            · right ; left ; simp [he']
          · grind
      · exact Or.inr (Or.inr hrec)

theorem total_len_set_cons_get (v : OVec (ASeq Int Int)) (i : Nat) (e : Int × Int) (h : i < v.length)
  : bucket_map_total_len (v.set i (e :: v[i])) = bucket_map_total_len v + 1 := by
    induction v generalizing i with
    | nil =>
      cases h
    | cons hd tl ih =>
      cases i <;> grind

theorem total_len_set_cons_getD (v : OVec (ASeq Int Int)) (i : Nat) (e : Int × Int) (h : i < v.length)
  : bucket_map_total_len (v.set i (e :: (v[i]?.getD []))) = bucket_map_total_len v + 1 := by
    have hsome : v[i]? = some v[i] := List.getElem?_eq_getElem h
    simpa [hsome] using total_len_set_cons_get v i e h

theorem insert_total_len_add_one (v : OVec (ASeq Int Int)) (key val : Int)
  (hpos : svec_len v > 0)
  (hno : ∀ b e, b ∈ v → e ∈ b → e.fst ≠ key)
  : bucket_map_total_len (insert v key val) = bucket_map_total_len v + 1 := by
    have hmod_lt : key % ↑(v.length) < ↑(v.length) := by
      simpa [svec_len] using (Int.emod_lt_of_pos key hpos)
    have hlen_pos : (0 : Int) < ↑(v.length) := by
      simpa [svec_len] using hpos
    have hlen_ne : (↑(v.length) : Int) ≠ 0 := by
      omega
    have hmod_nn : 0 ≤ key % ↑(v.length) := by
      exact Int.emod_nonneg key hlen_ne
    have hidx : (key % ↑(v.length)).toNat < v.length := by
      exact (Int.toNat_lt hmod_nn).2 hmod_lt
    have hbmem_getD : v[(key % ↑(v.length)).toNat]?.getD [] ∈ v := by
      simp [List.getElem?_eq_getElem hidx, List.getElem_mem hidx]
    have hnot_getD : ¬ ∃ x, (key, x) ∈ v[(key % ↑(v.length)).toNat]?.getD [] := by
      intro hx
      rcases hx with ⟨x, hx⟩
      exact (hno _ _ hbmem_getD hx) rfl
    unfold insert
    simp [svec_get, svec_len, svec_set, hnot_getD, Inhabited.default]
    simpa [bucket_map_total_len] using
      total_len_set_cons_getD v (key % ↑(v.length)).toNat (key, val) hidx

theorem key_matches_mem (l : ASeq Int Int) (h : alist_aseq_key_matches l k v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [alist_aseq_key_matches] at h
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp [alist_aseq_key_matches, List.lookup] at h
    by_cases hk : k = k' <;> grind

theorem mem_unique_key_matches (l : ASeq Int Int) (h : alist_aseq_unique_keys l) (hmem : (k, v) ∈ l)
  : alist_aseq_key_matches l k v := by
  induction l generalizing k v with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [alist_aseq_unique_keys, List.pairwise_cons] at h
    simp only [alist_aseq_key_matches, List.lookup_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with heq | hmem <;> grind

theorem absorb_bucket_len' (v : OVec (ASeq Int Int)) (b : ASeq Int Int)
  : svec_len (bucket_map_absorb_bucket v b) = svec_len v := by
    induction b generalizing v with
    | nil => simp [bucket_map_absorb_bucket]
    | cons p ps ih =>
      simp [bucket_map_absorb_bucket, insert, svec_set, svec_len]
      grind

theorem mem_distributed_key_matches (v : OVec (ASeq Int Int))
  (h1 : bucket_map_unique_keys v) (h2 : bucket_map_keys_distributed_by_hash v) (_h3 : svec_len v > 0)
  (s : ASeq Int Int) (hs : s ∈ v) (hmem : (k, val) ∈ s)
  : alist_aseq_key_matches (svec_get v (k % svec_len v)) k val := by
    obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hs
    have hcontains : alist_aseq_contains_key s k := by
      simp [alist_aseq_contains_key]
      exact ⟨val, hmem⟩
    have hiInt0 : (0:Int) ≤ (i : Int) := Int.natCast_nonneg i
    have hiIntLt : (i : Int) < svec_len v := by
      simpa [svec_len] using (Int.ofNat_lt.mpr hi)
    have hgetEq : svec_get v (i : Int) = s := by
      simp [svec_get]
      grind
    grind [mem_unique_key_matches]

theorem mem_absorb_key_matches (v : OVec (ASeq Int Int)) (l : ASeq Int Int)
  (h1 : bucket_map_unique_keys v) (h2 : bucket_map_keys_distributed_by_hash v) (h3 : svec_len v > 0)
  (h4 : alist_aseq_unique_keys l)
  (hmatch : alist_aseq_key_matches (svec_get (bucket_map_absorb_bucket v l) (k % svec_len (bucket_map_absorb_bucket v l))) k val)
  : alist_aseq_key_matches (svec_get v (k % svec_len v)) k val ∨ alist_aseq_key_matches l k val := by
    have hlen : svec_len (bucket_map_absorb_bucket v l) = svec_len v := absorb_bucket_len' v l
    rw [hlen] at hmatch
    have hgetmem : svec_get (bucket_map_absorb_bucket v l) (k % svec_len v) ∈ bucket_map_absorb_bucket v l := by
      have hidx : (k % svec_len v).toNat < (bucket_map_absorb_bucket v l).length := by
        have := Int.emod_lt_of_pos k h3
        have hnn := Int.emod_nonneg k (by omega : svec_len v ≠ 0)
        have : (k % svec_len v).toNat < v.length := by
          simp [svec_len] at *
          omega
        grind
      grind
    have hmem : (k, val) ∈ svec_get (bucket_map_absorb_bucket v l) (k % svec_len v) :=
      key_matches_mem _ hmatch
    have habs := mem_absorb v hgetmem hmem
    rcases habs with ⟨s, hs, he⟩ | hl
    · left
      exact mem_distributed_key_matches v h1 h2 h3 s hs he
    · right
      exact mem_unique_key_matches l h4 hl

theorem insert_len_eq (v : OVec (ASeq Int Int)) (key val : Int)
  : svec_len (insert v key val) = svec_len v := by
    unfold insert svec_set svec_len
    simp [List.length_set]

theorem bucket_mem_of_pos (v : OVec (ASeq Int Int)) (key : Int) (hpos : svec_len v > 0)
  : svec_get v (key % svec_len v) ∈ v := by
    simp_all
    rw [List.getElem?_eq_getElem]
    grind
    simp_all ; apply Int.emod_lt_of_pos
    grind

theorem insert_preserves_key_matches (v : OVec (ASeq Int Int)) (key val key' val' : Int)
  (hpos : svec_len v > 0) (hne : key' ≠ key)
  (h : alist_aseq_key_matches (svec_get v (key % svec_len v)) key val)
  : alist_aseq_key_matches (svec_get (insert v key' val') (key % svec_len v)) key val := by
    have hkb : 0 ≤ key % svec_len v ∧ key % svec_len v < svec_len v :=
      ⟨Int.emod_nonneg key (by omega), Int.emod_lt_of_pos key hpos⟩
    have hkb' : 0 ≤ key' % svec_len v ∧ key' % svec_len v < svec_len v :=
      ⟨Int.emod_nonneg key' (by omega), Int.emod_lt_of_pos key' hpos⟩
    unfold insert
    by_cases hidx : key' % svec_len v = key % svec_len v
    · rw [hidx, svec_get_set_eq _ (by rfl) hkb]
      by_cases hcontains : alist_aseq_contains_key (svec_get v (key % svec_len v)) key'
      · rw [←hidx] at hcontains
        simp_all [-alist_aseq_key_matches]
        grind [key_matches_set_ne]
      · rw [←hidx] at hcontains
        grind
    · grind

theorem insert_produces_key_matches (v : OVec (ASeq Int Int)) (key val : Int) (hpos : svec_len v > 0)
  : alist_aseq_key_matches (svec_get (insert v key val) (key % svec_len v)) key val := by
    have hkb : 0 ≤ key % svec_len v ∧ key % svec_len v < svec_len v :=
      ⟨Int.emod_nonneg key (by omega), Int.emod_lt_of_pos key hpos⟩
    unfold insert
    rw [svec_get_set_eq _ (by rfl) hkb]
    by_cases hc : alist_aseq_contains_key (svec_get v (key % svec_len v)) key
      <;> grind [alist_set_matches]

theorem absorb_preserves_key_matches (v : OVec (ASeq Int Int)) (l : ASeq Int Int) (key val : Int)
  (hpos : svec_len v > 0) (hnotin : ∀ e ∈ l, e.fst ≠ key)
  (h : alist_aseq_key_matches (svec_get v (key % svec_len v)) key val)
  : alist_aseq_key_matches (svec_get (bucket_map_absorb_bucket v l) (key % svec_len (bucket_map_absorb_bucket v l))) key val := by
    induction l generalizing v with
    | nil => simpa [bucket_map_absorb_bucket] using h
    | cons hd tl ih =>
      rcases hd with ⟨k', v'⟩
      have hne : k' ≠ key := hnotin (k', v') (by simp)
      have hpos' : svec_len (insert v k' v') > 0 := by
        rw [insert_len_eq]; exact hpos
      have hmatch' : alist_aseq_key_matches (svec_get (insert v k' v') (key % svec_len v)) key val :=
        insert_preserves_key_matches v key val k' v' hpos hne h
      have hmatch'' : alist_aseq_key_matches (svec_get (insert v k' v') (key % svec_len (insert v k' v'))) key val := by
        rwa [insert_len_eq]
      grind

theorem mem_absorb_key_matches_preserved (v : OVec (ASeq Int Int)) (l : ASeq Int Int) (key val : Int)
  (hdisj : bucket_map_disjoint_with_list v l) (hpos : svec_len v > 0)
  (h : alist_aseq_key_matches (svec_get v (key % svec_len v)) key val)
  : alist_aseq_key_matches (svec_get (bucket_map_absorb_bucket v l) (key % svec_len (bucket_map_absorb_bucket v l))) key val := by
    have hmemv : (key, val) ∈ svec_get v (key % svec_len v) := key_matches_mem _ h
    have hbmem : svec_get v (key % svec_len v) ∈ v := bucket_mem_of_pos v key hpos
    have hnotin : ∀ e ∈ l, e.fst ≠ key := by grind
    exact absorb_preserves_key_matches v l key val hpos hnotin h

theorem absorb_key_matches_of_mem (v : OVec (ASeq Int Int)) (l : ASeq Int Int) (key val : Int)
  (hpos : svec_len v > 0) (huniq : alist_aseq_unique_keys l) (hmem : (key, val) ∈ l)
  : alist_aseq_key_matches (svec_get (bucket_map_absorb_bucket v l) (key % svec_len (bucket_map_absorb_bucket v l))) key val := by
    induction l generalizing v with
    | nil => simp at hmem
    | cons hd tl ih =>
      rcases hd with ⟨k', v'⟩
      have huniq' : (∀ (a b : Int), (a, b) ∈ tl → ¬k' = a) ∧ alist_aseq_unique_keys tl := by
        simpa [alist_aseq_unique_keys] using huniq
      have hnotk' : ∀ (a b : Int), (a, b) ∈ tl → ¬k' = a := huniq'.1
      have huniqtl : alist_aseq_unique_keys tl := huniq'.2
      have hpos' : svec_len (insert v k' v') > 0 := by
        rw [insert_len_eq]; exact hpos
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨hk, hv⟩ := heq
        subst hk; subst hv
        have hnotin : ∀ e ∈ tl, e.fst ≠ key := by
          intro e he
          rcases e with ⟨ek, ev⟩
          exact fun hk => (hnotk' ek ev he) hk.symm
        have hmatch0 : alist_aseq_key_matches (svec_get (insert v key val) (key % svec_len v)) key val :=
          insert_produces_key_matches v key val hpos
        have hmatch1 : alist_aseq_key_matches (svec_get (insert v key val) (key % svec_len (insert v key val))) key val := by
          rwa [insert_len_eq]
        have := absorb_preserves_key_matches (insert v key val) tl key val hpos' hnotin hmatch1
        simpa [bucket_map_absorb_bucket] using this
      · have hnek : k' ≠ key := by
          grind
        have := ih (v := insert v k' v') hpos' huniqtl hmem
        simpa [bucket_map_absorb_bucket] using this

theorem no_overlap_num_entries_preserved1 (v1 : OVec (ASeq Int Int))
  (h1 : ∀ b1 e1 e2, b1 ∈ v1 → e1 ∈ b1 → e2 ∈ b2 → e1.fst ≠ e2.fst)
  (h2 : svec_len v1 > 0)
  (h3 : alist_aseq_unique_keys b2)
  : bucket_map_total_len (bucket_map_absorb_bucket v1 b2) = bucket_map_total_len v1 + b2.length := by
    induction b2 generalizing v1 with
    | nil =>
      simp [bucket_map_absorb_bucket]
    | cons hd tl ih =>
      rcases hd with ⟨k, v⟩
      have h3' : (∀ (a b : Int), (a, b) ∈ tl → ¬k = a) ∧ alist_aseq_unique_keys tl := by
        simpa [alist_aseq_unique_keys] using h3
      have h3k : ∀ (a b : Int), (a, b) ∈ tl → ¬k = a := h3'.1
      have h3tl : alist_aseq_unique_keys tl := h3'.2
      simp [bucket_map_absorb_bucket] at ⊢
      have hno : ∀ b e, b ∈ v1 → e ∈ b → e.fst ≠ k := by grind
      have hins : bucket_map_total_len (insert v1 k v) = bucket_map_total_len v1 + 1 := by
        exact insert_total_len_add_one v1 k v h2 hno
      have h2' : svec_len (insert v1 k v) > 0 := by
        unfold insert svec_set svec_len
        simpa [List.length_set] using h2
      have h1' : ∀ b e1 e2, b ∈ insert v1 k v → e1 ∈ b → e2 ∈ tl → e1.fst ≠ e2.fst := by
        intro b e1 e2 hb he1 he2
        have hb' : b ∈ bucket_map_absorb_bucket v1 [(k, v)] := by
          simpa [bucket_map_absorb_bucket, insert] using hb
        have hmem := mem_absorb v1 hb' he1
        grind
      have htail : bucket_map_total_len (bucket_map_absorb_bucket (insert v1 k v) tl) =
          bucket_map_total_len (insert v1 k v) + tl.length := by
        exact ih (v1 := insert v1 k v) h1' h2' h3tl
      grind


theorem no_overlap_num_entries_preserved (v1 v2 : OVec (ASeq Int Int))
  (h1: ∀ b1 b2 e1 e2, b1 ∈ v1 → b2 ∈ v2 → e1 ∈ b1 → e2 ∈ b2 → e1.fst ≠ e2.fst)
  (h0 : svec_len v1 > 0)
  (h2 : bucket_map_keys_distributed_by_hash v2)
  (h3 : bucket_map_unique_keys v2)
  : bucket_map_total_len (bucket_map_absorb_buckets v1 v2) = bucket_map_total_len v1 + bucket_map_total_len v2 := by
    have hidxdisj_v2 :
        ∀ (i j : Nat) (hi : i < v2.length) (hj : j < v2.length),
          ∀ (e1 e2 : Int × Int),
            i ≠ j →
            e1 ∈ v2[i]'hi →
            e2 ∈ v2[j]'hj →
            e1.fst ≠ e2.fst := by
      intro i j hi hj e1 e2 hij he1 he2
      intro heq
      have hk1 : alist_aseq_contains_key (svec_get v2 (i : Int)) e1.fst := by
        have hm : e1.fst ∈ (v2[i]).map Prod.fst := by
          exact List.mem_map.mpr ⟨e1, he1, rfl⟩
        simpa [svec_get, alist_aseq_contains_key, hi] using hm
      have hk2 : alist_aseq_contains_key (svec_get v2 (j : Int)) e2.fst := by
        have hm : e2.fst ∈ (v2[j]).map Prod.fst := by
          exact List.mem_map.mpr ⟨e2, he2, rfl⟩
        simpa [svec_get, alist_aseq_contains_key, hj] using hm
      have hiInt : (i : Int) < svec_len v2 := by
        have : (i : Int) < (v2.length : Int) := Int.ofNat_lt.mpr hi
        simpa [svec_len] using this
      have hjInt : (j : Int) < svec_len v2 := by
        have : (j : Int) < (v2.length : Int) := Int.ofNat_lt.mpr hj
        simpa [svec_len] using this
      have hmod1 : e1.fst % svec_len v2 = (i : Int) := by
        exact h2 i e1.fst ⟨Int.natCast_nonneg i, hiInt⟩ hk1
      have hmod2 : e2.fst % svec_len v2 = (j : Int) := by
        exact h2 j e2.fst ⟨Int.natCast_nonneg j, hjInt⟩ hk2
      have hijeq : (i : Int) = (j : Int) := by
        calc
          (i : Int) = e1.fst % svec_len v2 := by simpa using hmod1.symm
          _ = e2.fst % svec_len v2 := by simp [heq]
          _ = (j : Int) := hmod2
      exact hij (Int.ofNat.inj hijeq)
    have haux :
        ∀ (w1 w2 : OVec (ASeq Int Int)),
          (∀ b1 b2 e1 e2, b1 ∈ w1 → b2 ∈ w2 → e1 ∈ b1 → e2 ∈ b2 → e1.fst ≠ e2.fst) →
          (∀ (i j : Nat) (hi : i < w2.length) (hj : j < w2.length),
            ∀ (e1 e2 : Int × Int),
              i ≠ j →
              e1 ∈ w2[i]'hi →
              e2 ∈ w2[j]'hj →
              e1.fst ≠ e2.fst) →
          svec_len w1 > 0 →
          bucket_map_unique_keys w2 →
          bucket_map_total_len (bucket_map_absorb_buckets w1 w2) = bucket_map_total_len w1 + bucket_map_total_len w2 := by
      intro w1 w2
      induction w2 generalizing w1 with
      | nil =>
        intro _ _ _ _
        simp [bucket_map_absorb_buckets]
      | cons hd tl ih =>
        intro hcross hidxdisj hpos huniq
        have hhduniq : alist_aseq_unique_keys hd := by
          exact huniq hd (by simp)
        have hhd :
            bucket_map_total_len (bucket_map_absorb_bucket w1 hd) = bucket_map_total_len w1 + hd.length := by
          apply no_overlap_num_entries_preserved1 (v1 := w1)
          · intro b e1 e2 hb he1 he2
            exact hcross b hd e1 e2 hb (by simp) he1 he2
          · exact hpos
          · exact hhduniq
        have hcross' :
            ∀ b1 b2 e1 e2,
              b1 ∈ bucket_map_absorb_bucket w1 hd →
              b2 ∈ tl →
              e1 ∈ b1 →
              e2 ∈ b2 →
              e1.fst ≠ e2.fst := by
          intro b1 b2 e1 e2 hb1 hb2 he1 he2
          have hmem := mem_absorb w1 hb1 he1
          rcases hmem with hmem | hmem
          · rcases hmem with ⟨s, hs, he⟩
            exact hcross s b2 e1 e2 hs (by simp [hb2]) he he2
          · rcases List.mem_iff_get.mp hb2 with ⟨j, hj, rfl⟩
            exact hidxdisj 0 (j + 1) (by simp) (by grind) e1 e2 (by omega) (by simpa using hmem) (by simpa using he2)
        have hidxdisj' :
            ∀ (i j : Nat) (hi : i < tl.length) (hj : j < tl.length),
              ∀ (e1 e2 : Int × Int),
                i ≠ j →
                e1 ∈ tl[i]'hi →
                e2 ∈ tl[j]'hj →
                e1.fst ≠ e2.fst := by
          intro i j hi hj e1 e2 hij he1 he2
          exact hidxdisj (i + 1) (j + 1) (by simpa using Nat.succ_lt_succ hi) (by simpa using Nat.succ_lt_succ hj) e1 e2 (by omega) (by simpa [hi] using he1) (by simpa [hj] using he2)
        have hpos' : svec_len (bucket_map_absorb_bucket w1 hd) > 0 := by
          grind [absorb_bucket_len']
        have huniq_tl : bucket_map_unique_keys tl := by
          intro b hb
          exact huniq b (by simp [hb])
        have htl :
            bucket_map_total_len (bucket_map_absorb_buckets (bucket_map_absorb_bucket w1 hd) tl) =
            bucket_map_total_len (bucket_map_absorb_bucket w1 hd) + bucket_map_total_len tl := by
          exact ih (w1 := bucket_map_absorb_bucket w1 hd) hcross' hidxdisj' hpos' huniq_tl
        calc
          bucket_map_total_len (bucket_map_absorb_buckets w1 (hd :: tl))
              = bucket_map_total_len (bucket_map_absorb_buckets (bucket_map_absorb_bucket w1 hd) tl) := by
                  simp [bucket_map_absorb_buckets]
          _ = bucket_map_total_len (bucket_map_absorb_bucket w1 hd) + bucket_map_total_len tl := htl
          _ = (bucket_map_total_len w1 + hd.length) + bucket_map_total_len tl := by rw [hhd]
          _ = bucket_map_total_len w1 + (hd.length + bucket_map_total_len tl) := by omega
          _ = bucket_map_total_len w1 + bucket_map_total_len (hd :: tl) := by rfl
    exact haux v1 v2 h1 hidxdisj_v2 h0 h3

theorem absorb_bucket_append (v : OVec (ASeq Int Int)) (l1 l2 : ASeq Int Int)
  : bucket_map_absorb_bucket v (l1 ++ l2) = bucket_map_absorb_bucket (bucket_map_absorb_bucket v l1) l2 := by
    induction l1 generalizing v with
    | nil => simp [bucket_map_absorb_bucket]
    | cons hd tl ih =>
      rcases hd with ⟨k, val⟩
      simp [bucket_map_absorb_bucket]
      exact ih (v := insert v k val)

theorem absorb_buckets_eq_absorb_flatten (v bs : OVec (ASeq Int Int))
  : bucket_map_absorb_buckets v bs = bucket_map_absorb_bucket v bs.flatten := by
    induction bs generalizing v with
    | nil => simp [bucket_map_absorb_buckets, bucket_map_absorb_bucket]
    | cons hd tl ih =>
      simp only [bucket_map_absorb_buckets, List.flatten_cons]
      rw [ih, absorb_bucket_append]

theorem cross_index_disjoint_of_distributed (v2 : OVec (ASeq Int Int)) (h2 : bucket_map_keys_distributed_by_hash v2)
  (i j : Nat) (hi : i < v2.length) (hj : j < v2.length) (hij : i ≠ j)
  (e1 e2 : Int × Int) (he1 : e1 ∈ v2[i]'hi) (he2 : e2 ∈ v2[j]'hj)
  : e1.fst ≠ e2.fst := by
    intro heq
    have hk1 : alist_aseq_contains_key (svec_get v2 (i : Int)) e1.fst := by
      have hm : e1.fst ∈ (v2[i]).map Prod.fst := by
        exact List.mem_map.mpr ⟨e1, he1, rfl⟩
      simpa [svec_get, alist_aseq_contains_key, hi] using hm
    have hk2 : alist_aseq_contains_key (svec_get v2 (j : Int)) e2.fst := by
      have hm : e2.fst ∈ (v2[j]).map Prod.fst := by
        exact List.mem_map.mpr ⟨e2, he2, rfl⟩
      simpa [svec_get, alist_aseq_contains_key, hj] using hm
    have hiInt : (i : Int) < svec_len v2 := by
      have : (i : Int) < (v2.length : Int) := Int.ofNat_lt.mpr hi
      simpa [svec_len] using this
    have hjInt : (j : Int) < svec_len v2 := by
      have : (j : Int) < (v2.length : Int) := Int.ofNat_lt.mpr hj
      simpa [svec_len] using this
    have hmod1 : e1.fst % svec_len v2 = (i : Int) := by
      exact h2 i e1.fst ⟨Int.natCast_nonneg i, hiInt⟩ hk1
    have hmod2 : e2.fst % svec_len v2 = (j : Int) := by
      exact h2 j e2.fst ⟨Int.natCast_nonneg j, hjInt⟩ hk2
    have hijeq : (i : Int) = (j : Int) := by
      calc
        (i : Int) = e1.fst % svec_len v2 := by simpa using hmod1.symm
        _ = e2.fst % svec_len v2 := by simp [heq]
        _ = (j : Int) := hmod2
    exact hij (Int.ofNat.inj hijeq)

theorem unique_keys_flatten_of_distributed (v2 : OVec (ASeq Int Int))
  (h2 : bucket_map_keys_distributed_by_hash v2) (h3 : bucket_map_unique_keys v2)
  : alist_aseq_unique_keys v2.flatten := by
    simp only [alist_aseq_unique_keys]
    rw [List.pairwise_flatten]
    constructor
    · intro l hl
      exact h3 l hl
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij x hx y hy
      exact cross_index_disjoint_of_distributed v2 h2 i j hi hj (by omega) x y hx hy

theorem disjoint_with_list_flatten_of_disjoint (v bs : OVec (ASeq Int Int)) (h : bucket_map_disjoint v bs)
  : bucket_map_disjoint_with_list v bs.flatten := by
    intro b1 e1 e2 hb1 he1 he2
    rw [List.mem_flatten] at he2
    obtain ⟨b2, hb2, he2'⟩ := he2
    exact h b1 b2 e1 e2 hb1 hb2 he1 he2'

theorem mem_absorb_buckets_key_matches (v bs : OVec (ASeq Int Int))
  (h1 : bucket_map_unique_keys v) (h2 : bucket_map_keys_distributed_by_hash v) (h3 : svec_len v > 0)
  (h4 : bucket_map_unique_keys bs) (h5 : bucket_map_keys_distributed_by_hash bs)
  (hmatch : alist_aseq_key_matches (svec_get (bucket_map_absorb_buckets v bs) (k % svec_len (bucket_map_absorb_buckets v bs))) k val)
  : alist_aseq_key_matches (svec_get v (k % svec_len v)) k val ∨ alist_aseq_key_matches (svec_get bs (k % svec_len bs)) k val := by
    rw [absorb_buckets_eq_absorb_flatten] at hmatch
    have huniq_flat : alist_aseq_unique_keys bs.flatten := unique_keys_flatten_of_distributed bs h5 h4
    have hres := mem_absorb_key_matches v bs.flatten h1 h2 h3 huniq_flat hmatch
    rcases hres with hl | hr
    · exact Or.inl hl
    · have hmem : (k, val) ∈ bs.flatten := key_matches_mem _ hr
      rw [List.mem_flatten] at hmem
      obtain ⟨b, hb, hmemb⟩ := hmem
      have hpos_bs : svec_len bs > 0 := by
        have := List.length_pos_of_mem hb
        simpa [svec_len] using this
      exact Or.inr (mem_distributed_key_matches bs h4 h5 hpos_bs b hb hmemb)

theorem mem_absorb_buckets_key_matches_preserved (v bs : OVec (ASeq Int Int)) (key val : Int)
  (hdisj : bucket_map_disjoint v bs) (hpos : svec_len v > 0)
  (h : alist_aseq_key_matches (svec_get v (key % svec_len v)) key val)
  : alist_aseq_key_matches (svec_get (bucket_map_absorb_buckets v bs) (key % svec_len (bucket_map_absorb_buckets v bs))) key val := by
    rw [absorb_buckets_eq_absorb_flatten]
    have hdisjflat := disjoint_with_list_flatten_of_disjoint v bs hdisj
    exact mem_absorb_key_matches_preserved v bs.flatten key val hdisjflat hpos h

theorem absorb_buckets_key_matches_of_mem (v bs : OVec (ASeq Int Int)) (key val : Int)
  (hpos : svec_len v > 0) (huniq : bucket_map_unique_keys bs) (hdist : bucket_map_keys_distributed_by_hash bs)
  (hmem : (key, val) ∈ bs.flatten)
  : alist_aseq_key_matches (svec_get (bucket_map_absorb_buckets v bs) (key % svec_len (bucket_map_absorb_buckets v bs))) key val := by
    rw [absorb_buckets_eq_absorb_flatten]
    have huniqflat := unique_keys_flatten_of_distributed bs hdist huniq
    exact absorb_key_matches_of_mem v bs.flatten key val hpos huniqflat hmem

theorem mem_absorb_buckets_key_matches_preserved_from_bs (v bs : OVec (ASeq Int Int)) (key val : Int)
  (h4 : bucket_map_unique_keys bs) (h5 : bucket_map_keys_distributed_by_hash bs)
  (hposbs : svec_len bs > 0) (hposv : svec_len v > 0)
  (h : alist_aseq_key_matches (svec_get bs (key % svec_len bs)) key val)
  : alist_aseq_key_matches (svec_get (bucket_map_absorb_buckets v bs) (key % svec_len (bucket_map_absorb_buckets v bs))) key val := by
    have hmem : (key, val) ∈ svec_get bs (key % svec_len bs) := key_matches_mem _ h
    have hbmem : svec_get bs (key % svec_len bs) ∈ bs := bucket_mem_of_pos bs key hposbs
    have hflat : (key, val) ∈ bs.flatten := List.mem_flatten.mpr ⟨_, hbmem, hmem⟩
    exact absorb_buckets_key_matches_of_mem v bs key val hposv h4 h5 hflat

theorem insert_preserves_distributed (v : OVec (ASeq Int Int)) (key val : Int) (hpos : svec_len v > 0)
  (hdist : bucket_map_keys_distributed_by_hash v)
  : bucket_map_keys_distributed_by_hash (insert v key val) := by
    unfold insert
    unfold bucket_map_keys_distributed_by_hash
    rw [svec_len_set2]
    intro i k hik hcontains
    obtain ⟨ilb, iub⟩ := hik
    by_cases ieq : i = key % svec_len v
    · subst ieq
      rw [svec_get_set_eq v rfl ⟨Int.emod_nonneg key (by omega), Int.emod_lt_of_pos key hpos⟩] at hcontains
      by_cases hins : alist_aseq_contains_key (svec_get v (key % svec_len v)) key
      · simp only [hins, if_true] at hcontains
        by_cases keq : k = key
        · rw [keq]
        · simp only [alist_aseq_contains_key, List.mem_map] at hcontains
          rcases hcontains with ⟨⟨k', x⟩, hx, hkx⟩
          simp only at hkx
          rw [hkx] at hx
          have := alist_set_contains_contains _ hx
          exact hdist _ k ⟨ilb, iub⟩ this
      · simp only [hins, if_false] at hcontains
        simp only [alist_aseq_contains_key, alist_aseq_cons, List.map_cons, List.mem_cons] at hcontains
        rcases hcontains with hk | hk
        · rw [hk]
        · exact hdist _ k ⟨ilb, iub⟩ hk
    · rw [svec_get_set_ne v (Ne.symm ieq) (Int.emod_nonneg key (by omega)) ilb] at hcontains
      exact hdist i k ⟨ilb, iub⟩ hcontains

theorem insert_preserves_unique (v : OVec (ASeq Int Int)) (key val : Int) (hpos : svec_len v > 0)
  (huniq : bucket_map_unique_keys v)
  : bucket_map_unique_keys (insert v key val) := by
    unfold insert
    unfold bucket_map_unique_keys
    intro bucket hbucketmem
    have hbase : alist_aseq_unique_keys (svec_get v (key % svec_len v)) := by
      have hmem : svec_get v (key % svec_len v) ∈ v := bucket_mem_of_pos v key hpos
      exact huniq _ hmem
    have hres : alist_aseq_unique_keys
        (if alist_aseq_contains_key (svec_get v (key % svec_len v)) key
         then alist_aseq_set (svec_get v (key % svec_len v)) key val
         else alist_aseq_cons key val (svec_get v (key % svec_len v))) := by
      by_cases hins : alist_aseq_contains_key (svec_get v (key % svec_len v)) key
      · simp only [hins, if_true]
        exact unique_set_uniqe _ hbase
      · simp only [hins, if_false]
        exact unique_nc_cons_nc _ hbase hins
    rw [List.mem_iff_getElem] at hbucketmem
    obtain ⟨i, hi, hbucket⟩ := hbucketmem
    by_cases ieq2 : i = (key % svec_len v).toNat
    · subst ieq2
      rw [← hbucket]
      simp only [svec_set]
      rw [List.getElem_set_self]
      exact hres
    · rw [← hbucket]
      simp only [svec_set]
      rw [List.getElem_set_ne (Ne.symm ieq2)]
      apply huniq
      unfold svec_get svec_len at *
      grind

theorem insert_key_matches_iff (v : OVec (ASeq Int Int)) (key val key' val' : Int)
  (hpos : svec_len v > 0) (hne : key' ≠ key)
  : alist_aseq_key_matches (svec_get v (key % svec_len v)) key val ↔
    alist_aseq_key_matches (svec_get (insert v key' val') (key % svec_len (insert v key' val'))) key val := by
    rw [insert_len_eq]
    have hkb : 0 ≤ key % svec_len v ∧ key % svec_len v < svec_len v :=
      ⟨Int.emod_nonneg key (by omega), Int.emod_lt_of_pos key hpos⟩
    have hkb' : 0 ≤ key' % svec_len v ∧ key' % svec_len v < svec_len v :=
      ⟨Int.emod_nonneg key' (by omega), Int.emod_lt_of_pos key' hpos⟩
    unfold insert
    by_cases hidx : key' % svec_len v = key % svec_len v
    · rw [hidx, svec_get_set_eq v rfl hkb]
      by_cases hcontains : alist_aseq_contains_key (svec_get v (key % svec_len v)) key'
      · simp only [hcontains, if_true]
        exact key_matches_set_ne (svec_get v (key % svec_len v)) hne.symm
      · simp only [hcontains, if_false]
        constructor <;> grind
    · rw [svec_get_set_ne v hidx hkb'.1 hkb.1]

theorem svec_len_empties (n : Int) (hn : n ≥ 0)
  : svec_len (bucket_map_empties n : OVec (ASeq Int Int)) = n := by
    simp [bucket_map_empties, svec_len]
    omega

theorem empties_unique (n : Int) : bucket_map_unique_keys (bucket_map_empties n : OVec (ASeq Int Int)) := by
  intro b hb
  simp only [bucket_map_empties] at hb
  rw [List.eq_of_mem_replicate hb]
  simp [alist_aseq_unique_keys]

theorem empties_distributed (n : Int) : bucket_map_keys_distributed_by_hash (bucket_map_empties n : OVec (ASeq Int Int)) := by
  intro i k hik hcontains
  exfalso
  simp only [svec_get, bucket_map_empties] at hcontains
  by_cases hib : i.toNat < n.toNat <;> grind

theorem no_match_in_empties (n i k val : Int)
  : ¬ alist_aseq_key_matches (svec_get (bucket_map_empties n : OVec (ASeq Int Int)) i) k val := by
    simp only [alist_aseq_key_matches, svec_get, bucket_map_empties]
    by_cases hib : i.toNat < n.toNat <;> grind

theorem empties_pos (n : Int) (hn : n > 0)
  : svec_len (bucket_map_empties n : OVec (ASeq Int Int)) > 0 := by
    rw [svec_len_empties n (by omega)]
    omega

end F
