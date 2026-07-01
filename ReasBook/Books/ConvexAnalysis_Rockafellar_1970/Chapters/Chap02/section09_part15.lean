/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section03_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part14

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology

section Chap02
section Section09

/-- Theorem 9.8. Let `C1, ..., Cm` be nonempty closed convex sets in `ℝ^n` such that whenever
`z1, ..., zm` satisfy `zi ∈ 0^+ Ci` and `z1 + ... + zm = 0`, each `zi` lies in the lineality
space of `Ci`. Let `C = conv (C1 ∪ ... ∪ Cm)`. Then
`cl C = ⋃ {lam1 C1 + ... + lamm Cm | lam_i ≥ 0^+, lam1 + ... + lamm = 1}`, where
`lam_i ≥ 0^+` means `lam_i Ci` is interpreted as `0^+ Ci` when `lam_i = 0`. Moreover,
`0^+ (cl C) = 0^+ C1 + ... + 0^+ Cm`. -/
theorem closure_convexHull_iUnion_eq_iUnion_weighted_sum_and_recessionCone
    {n m : Nat} (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCclosed : ∀ i, IsClosed (C i))
    (hCconv : ∀ i, Convex Real (C i))
    (hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (C i)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (C i))
    (hm : 0 < m) :
    let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
    closure C0 =
      ⋃ (lam : Fin m → ℝ)
        (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
        (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) ∧
      Set.recessionCone (closure C0) = ∑ i, Set.recessionCone (C i) := by
  classical
  -- Unfold the `let`-binding for `C0` to keep the proof structured.
  dsimp
  rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm) with ⟨m', rfl⟩
  -- Set up the lifted cone data in `ℝ^(n+1)`; the main argument remains to be filled in.
  let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
  let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
        (fun i => coords v (Fin.natAdd 1 i))
  let S : Fin (Nat.succ m') → Set (EuclideanSpace Real (Fin (1 + n))) :=
    fun i => {v | first v = 1 ∧ tail v ∈ C i}
  let K : Fin (Nat.succ m') → Set (EuclideanSpace Real (Fin (1 + n))) :=
    fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
  let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
  let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
    (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
  have hfirst_nonneg :
      ∀ i, ∀ v, v ∈ closure (K i) → 0 ≤ first v := by
    intro i v hv
    simpa [coords, first, tail, S, K] using
      (first_nonneg_of_mem_closure_lifted_cone (n := n) (C := C i) (hCne i) (hCclosed i)
        (hCconv i) v hv)
  have hclosure_sum :
      closure (∑ i, K i) = ∑ i, closure (K i) := by
    simpa [coords, first, tail, S, K] using
      (closure_sum_cones_eq_sum_closure_cones (n := n) (m := Nat.succ m') (C := C) hCne hCclosed
        hCconv
        hlineal)
  have hC0conv : Convex Real C0 := by
    simpa [C0] using (convex_convexHull (𝕜 := Real) (s := ⋃ i, C i))
  have hC0ne : Set.Nonempty C0 := by
    rcases hCne (0 : Fin (Nat.succ m')) with ⟨x, hx⟩
    have hne_union : (⋃ i, C i).Nonempty := by
      refine ⟨x, ?_⟩
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
    simpa [C0] using (hne_union.convexHull (𝕜 := Real))
  have hclosure_cone :
      closure K0 = closure (∑ i, K i) := by
    simpa [C0, coords, first, tail, S0, K0, S, K] using
      (closure_cone_over_convexHull_eq_closure_sum_cones_succ (n := n) (m := m') (C := C)
        hCne hCconv)
  have hclosureK0 : closure K0 = ∑ i, closure (K i) := hclosure_cone.trans hclosure_sum
  have hslice :
      closure C0 =
        {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
    simpa [C0, coords, first, tail, S0, K0] using
      (closure_C0_eq_first_one_slice_closure_lifted_cone (n := n) (C0 := C0) hC0conv)
  have hslice_sum :
      ∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m') → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) := by
    intro v hv1
    simpa [coords, first, tail, S, K] using
      (mem_sum_closure_cones_first_eq_one_iff (n := n) (m := Nat.succ m') (C := C)
        hCne hCclosed hCconv v hv1)
  have hslice_sum0 :
      ∀ v, first v = 0 →
        (v ∈ ∑ i, closure (K i) ↔ tail v ∈ ∑ i, Set.recessionCone (C i)) := by
    intro v hv0
    simpa [coords, first, tail, S, K] using
      (mem_sum_closure_cones_first_eq_zero_iff (n := n) (m := Nat.succ m') (C := C)
        hCne hCclosed hCconv v hv0)
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hx' := hx
      rw [hslice] at hx'
      rcases hx' with ⟨v, hvcl, hv1, hvx⟩
      have hvsum : v ∈ ∑ i, closure (K i) := by
        simpa [hclosureK0] using hvcl
      rcases (hslice_sum v hv1).1 hvsum with ⟨lam, hlam, hsum_lam, htail_mem⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨lam, ?_⟩
      refine Set.mem_iUnion.2 ?_
      refine ⟨⟨hlam, hsum_lam⟩, ?_⟩
      simpa [hvx] using htail_mem
    · intro hx
      rcases (Set.mem_iUnion.1 hx) with ⟨lam, hx⟩
      rcases (Set.mem_iUnion.1 hx) with ⟨hlam, htail_mem⟩
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (1 : ℝ))
      let append :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
            EuclideanSpace Real (Fin (1 + n)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
            ((Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
      let v : EuclideanSpace Real (Fin (1 + n)) := append y0 x
      have hv1 : first v = 1 ∧ tail v = x := by
        have h := first_tail_append (n := n) (y := y0) (z := x)
        simpa [coords, first, tail, append, v, y0] using h
      have hvsum : v ∈ ∑ i, closure (K i) := by
        exact (hslice_sum v hv1.1).2 ⟨lam, hlam.1, hlam.2, by simpa [hv1.2] using htail_mem⟩
      have hvcl : v ∈ closure K0 := by
        simpa [hclosureK0] using hvsum
      have hx' : x ∈ {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
        exact ⟨v, hvcl, hv1.1, hv1.2⟩
      have : x ∈ closure C0 := by
        rw [hslice]
        exact hx'
      exact this
  · ext x
    constructor
    · intro hx
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))
      let append :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
            EuclideanSpace Real (Fin (1 + n)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
            ((Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
      let v : EuclideanSpace Real (Fin (1 + n)) := append y0 x
      have hv0 : first v = 0 ∧ tail v = x := by
        have h := first_tail_append (n := n) (y := y0) (z := x)
        simpa [coords, first, tail, append, v, y0] using h
      let S0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
        {v | first v = 1 ∧ tail v ∈ closure C0}
      let K0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
        (ConvexCone.hull Real S0bar : Set (EuclideanSpace Real (Fin (1 + n))))
      have hclosureKbar : closure K0 = closure K0bar := by
        simpa [coords, first, tail, S0, K0, S0bar, K0bar] using
          (closure_lifted_cone_eq_closure_lifted_cone_closure (n := n) (C0 := C0))
      have hC0bar_ne : Set.Nonempty (closure C0) := hC0ne.closure
      have hclosure :
          closure K0bar =
            K0bar ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (closure C0)} := by
        simpa [coords, first, tail, S0bar, K0bar] using
          (closure_cone_eq_union_recession (n := n) (C := closure C0) hC0bar_ne isClosed_closure
            (Convex.closure hC0conv))
      have hvclbar : v ∈ closure K0bar := by
        have hvrec :
            v ∈ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (closure C0)} := by
          refine ⟨hv0.1, ?_⟩
          simpa [hv0.2] using hx
        have : v ∈ K0bar ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (closure C0)} :=
          Or.inr hvrec
        simpa [hclosure] using this
      have hvcl : v ∈ closure K0 := by
        simpa [hclosureKbar] using hvclbar
      have hvsum : v ∈ ∑ i, closure (K i) := by
        simpa [hclosureK0] using hvcl
      have htail_mem : tail v ∈ ∑ i, Set.recessionCone (C i) :=
        (hslice_sum0 v hv0.1).1 hvsum
      simpa [hv0.2] using htail_mem
    · intro hx
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))
      let append :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
            EuclideanSpace Real (Fin (1 + n)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
            ((Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
      let v : EuclideanSpace Real (Fin (1 + n)) := append y0 x
      have hv0 : first v = 0 ∧ tail v = x := by
        have h := first_tail_append (n := n) (y := y0) (z := x)
        simpa [coords, first, tail, append, v, y0] using h
      have hvsum : v ∈ ∑ i, closure (K i) := by
        exact (hslice_sum0 v hv0.1).2 (by simpa [hv0.2] using hx)
      have hvcl : v ∈ closure K0 := by
        simpa [hclosureK0] using hvsum
      let S0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
        {v | first v = 1 ∧ tail v ∈ closure C0}
      let K0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
        (ConvexCone.hull Real S0bar : Set (EuclideanSpace Real (Fin (1 + n))))
      have hclosureKbar : closure K0 = closure K0bar := by
        simpa [coords, first, tail, S0, K0, S0bar, K0bar] using
          (closure_lifted_cone_eq_closure_lifted_cone_closure (n := n) (C0 := C0))
      have hvclbar : v ∈ closure K0bar := by
        simpa [hclosureKbar] using hvcl
      have htail_rec : tail v ∈ Set.recessionCone (closure C0) := by
        simpa [coords, first, tail, S0bar, K0bar, hv0.1] using
          (tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n) (C := closure C0)
            (hCclosed := isClosed_closure) (hCconv := (Convex.closure hC0conv))
            (v := v) hvclbar hv0.1)
      simpa [hv0.2] using htail_rec

/-- Finite sums of recession cone elements stay in the recession cone. -/
lemma recessionCone_sum_mem_finset {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCconv : Convex Real C) {s : Finset (Fin m)}
    (z : Fin m → EuclideanSpace Real (Fin n))
    (hz : ∀ i ∈ s, z i ∈ Set.recessionCone C) :
    (Finset.sum s (fun i => z i)) ∈ Set.recessionCone C := by
  classical
  revert hz
  refine Finset.induction_on s ?h0 ?hstep
  · intro _
    have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
      intro x hx t ht
      simpa using hx
    simpa [Finset.sum_empty] using hzero
  · intro a s ha hs hz'
    have hz'' : ∀ i ∈ s, z i ∈ Set.recessionCone C := by
      intro i hi
      exact hz' i (by simp [hi])
    have hsum_mem : (Finset.sum s (fun i => z i)) ∈ Set.recessionCone C := hs hz''
    have hza : z a ∈ Set.recessionCone C := hz' a (by simp [ha])
    have hsum :
        z a + Finset.sum s (fun i => z i) ∈ Set.recessionCone C :=
      recessionCone_add_mem (C := C) hCconv hza hsum_mem
    simpa [Finset.sum_insert, ha] using hsum

/-- Zero-sum vectors in a common recession cone give lineality directions. -/
lemma linealitySpace_of_sum_zero_same_recession {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (K : Set (EuclideanSpace Real (Fin n)))
    (hCconv : ∀ i, Convex Real (C i)) (hK : ∀ i, Set.recessionCone (C i) = K) :
    ∀ z : Fin m → EuclideanSpace Real (Fin n),
      (∀ i, z i ∈ K) → (∑ i, z i) = 0 → ∀ i, z i ∈ Set.linealitySpace (C i) := by
  classical
  intro z hzK hsum i
  have hzrec : z i ∈ Set.recessionCone (C i) := by
    simpa [hK i] using hzK i
  have hzrec' :
      ∀ j ∈ (Finset.univ.erase i), z j ∈ Set.recessionCone (C i) := by
    intro j hj
    have hzKj : z j ∈ K := hzK j
    simpa [hK i] using hzKj
  have hsum_eq :
      (∑ j, z j) = z i + (Finset.univ.erase i).sum (fun j => z j) := by
    symm
    exact
      (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin m))) (f := fun j => z j)
        (a := i) (by simp))
  have hsum' : z i + (Finset.univ.erase i).sum (fun j => z j) = 0 := by
    calc
      z i + (Finset.univ.erase i).sum (fun j => z j) = ∑ j, z j := by
        exact hsum_eq.symm
      _ = 0 := hsum
  have hneg_sum : -z i = (Finset.univ.erase i).sum (fun j => z j) := by
    have h := eq_neg_of_add_eq_zero_left hsum'
    have h' := congrArg Neg.neg h
    simpa using h'
  have hsum_mem :
      (Finset.univ.erase i).sum (fun j => z j) ∈ Set.recessionCone (C i) :=
    recessionCone_sum_mem_finset (C := C i) (hCconv i) (s := Finset.univ.erase i) (z := z)
      hzrec'
  have hzneg : -z i ∈ Set.recessionCone (C i) := by
    simpa [hneg_sum] using hsum_mem
  have hzneg' : z i ∈ -Set.recessionCone (C i) := by
    simpa [Set.mem_neg] using hzneg
  simpa [Set.linealitySpace] using And.intro hzneg' hzrec

/-- A positive weight absorbs the recession cone. -/
lemma absorb_recessionCone_into_positive_weight {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} {K : Set (EuclideanSpace Real (Fin n))}
    (hK : Set.recessionCone C = K) {t : ℝ} (ht : 0 < t) :
    K + t • C = t • C := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_add.1 hx with ⟨k, hkK, y, hy, rfl⟩
    rcases Set.mem_smul_set.1 hy with ⟨c, hc, rfl⟩
    have hkrec : k ∈ Set.recessionCone C := by
      simpa [hK] using hkK
    have hpos : 0 ≤ (1 / t) := by
      exact one_div_nonneg.mpr (le_of_lt ht)
    have hc' : c + (1 / t) • k ∈ C := hkrec hc hpos
    refine Set.mem_smul_set.2 ?_
    refine ⟨c + (1 / t) • k, hc', ?_⟩
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hxcalc : t • (c + (1 / t) • k) = t • c + k := by
      calc
        t • (c + (1 / t) • k) = t • c + t • ((1 / t) • k) := by
          simp [smul_add]
        _ = t • c + (t * (1 / t)) • k := by
          simp [smul_smul]
        _ = t • c + k := by
          simp [one_div, ht0]
    calc
      t • (c + (1 / t) • k) = t • c + k := hxcalc
      _ = k + t • c := by ac_rfl
  · intro x hx
    have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ K := by
      have hzero' : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone C := by
        intro x hx t ht
        simpa using hx
      simpa [hK] using hzero'
    refine Set.mem_add.2 ?_
    exact ⟨0, hzero, x, hx, by simp⟩

/-- Weighted Minkowski sums lie in the convex hull of the union. -/
lemma weighted_sum_subset_convexHull {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) {lam : Fin m → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1) :
    (∑ i, lam i • C i) ⊆ convexHull Real (⋃ i, C i) := by
  classical
  intro x hx
  rcases
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
        (f := fun i => lam i • C i) (a := x)).1 hx with
    ⟨y, hy, hsumy⟩
  have hy' : ∀ i, ∃ z, z ∈ C i ∧ y i = lam i • z := by
    intro i
    have hyi : y i ∈ lam i • C i := by
      simpa using (hy (i := i) (by simp))
    rcases Set.mem_smul_set.1 hyi with ⟨z, hzC, hzy⟩
    exact ⟨z, hzC, hzy.symm⟩
  classical
  choose z hzC hzy using hy'
  have hzU : ∀ i, z i ∈ ⋃ i, C i := by
    intro i
    exact Set.mem_iUnion.2 ⟨i, hzC i⟩
  have hxsum : ∑ i, lam i • z i = x := by
    calc
      ∑ i, lam i • z i = ∑ i, y i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hzy i).symm
      _ = x := hsumy
  have hconv : Convex Real (convexHull Real (⋃ i, C i)) := by
    simpa using (convex_convexHull (𝕜 := Real) (s := ⋃ i, C i))
  have hzHull : ∀ i, z i ∈ convexHull Real (⋃ i, C i) := by
    intro i
    exact
      (subset_convexHull (𝕜 := Real) (s := ⋃ i, C i)) (Set.mem_iUnion.2 ⟨i, hzC i⟩)
  have hlam' : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ lam i := by
    intro i hi
    exact hlam i
  have hsum' : ∑ i ∈ (Finset.univ : Finset (Fin m)), lam i = 1 := by
    simpa using hsum
  have hzHull' :
      ∀ i ∈ (Finset.univ : Finset (Fin m)), z i ∈ convexHull Real (⋃ i, C i) := by
    intro i hi
    exact hzHull i
  have hxmem :
      (∑ i, lam i • z i) ∈ convexHull Real (⋃ i, C i) :=
    Convex.sum_mem (s := convexHull Real (⋃ i, C i)) (t := (Finset.univ : Finset (Fin m)))
      (w := lam) (z := z) hconv hlam' hsum' hzHull'
  simpa [hxsum] using hxmem

/-- A weighted recession-cone sum can be reduced to the usual weighted sum. -/
lemma mem_sum_if_recessionCone {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (K : Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCconv : ∀ i, Convex Real (C i))
    (hK : ∀ i, Set.recessionCone (C i) = K) {lam : Fin m → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    {x : EuclideanSpace Real (Fin n)}
    (hx : x ∈ ∑ i, (if lam i = 0 then K else lam i • C i)) :
    x ∈ ∑ i, lam i • C i := by
  classical
  rcases
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
        (f := fun i => (if lam i = 0 then K else lam i • C i)) (a := x)).1 hx with
    ⟨y, hy, hsumy⟩
  have hsum_ne : (∑ i, lam i) ≠ 0 := by
    simp [hsum]
  obtain ⟨i0, _, hne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hpos : 0 < lam i0 := lt_of_le_of_ne (hlam i0) (Ne.symm hne0)
  let sK : Finset (Fin m) := Finset.univ.filter fun i => lam i = 0
  let sPos : Finset (Fin m) := Finset.univ.filter fun i => lam i ≠ 0
  let k : EuclideanSpace Real (Fin n) := Finset.sum sK (fun i => y i)
  let ypos : Fin m → EuclideanSpace Real (Fin n) := fun i => if lam i = 0 then 0 else y i
  have hyK : ∀ i ∈ sK, y i ∈ Set.recessionCone (C i0) := by
    intro i hi
    have hzero : lam i = 0 := (Finset.mem_filter.mp hi).2
    have hyi : y i ∈ K := by
      have hyi' := hy (i := i) (by simp)
      simpa [hzero] using hyi'
    simpa [hK i0] using hyi
  have hkrec : k ∈ Set.recessionCone (C i0) := by
    have hkrec' :
        (Finset.sum sK (fun i => y i)) ∈ Set.recessionCone (C i0) :=
      recessionCone_sum_mem_finset (C := C i0) (hCconv i0) (s := sK) (z := y) hyK
    simpa [k] using hkrec'
  have hkK : k ∈ K := by
    simpa [hK i0] using hkrec
  have hypos_mem :
      ∀ i ∈ (Finset.univ : Finset (Fin m)), ypos i ∈ lam i • C i := by
    intro i hi
    by_cases hzero : lam i = 0
    · rcases hCne i with ⟨c, hc⟩
      have hmem : (0 : EuclideanSpace Real (Fin n)) ∈ lam i • C i := by
        refine Set.mem_smul_set.2 ?_
        refine ⟨c, hc, ?_⟩
        simp [hzero]
      simpa [ypos, hzero] using hmem
    · have hyi : y i ∈ lam i • C i := by
        have hyi' := hy (i := i) (by simp)
        simpa [hzero] using hyi'
      simpa [ypos, hzero] using hyi
  have hypos_sum_mem :
      (∑ i, ypos i) ∈ ∑ i, lam i • C i := by
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => lam i • C i) (a := ∑ i, ypos i)).2 ?_
    refine ⟨ypos, ?_, rfl⟩
    intro i hi
    exact hypos_mem i hi
  have hsum_split :
      (∑ i, y i) = k + Finset.sum sPos (fun i => y i) := by
    have h :=
      (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
        (p := fun i => lam i = 0) (f := fun i => y i))
    have h' :
        (∑ i, y i) =
          Finset.sum sK (fun i => y i) + Finset.sum sPos (fun i => y i) := by
      simpa [sK, sPos] using h.symm
    simpa [k] using h'
  have hsum_ypos : Finset.sum sPos (fun i => y i) = ∑ i, ypos i := by
    have h :=
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i => lam i ≠ 0) (f := fun i => y i))
    have h' : (∑ i, if lam i ≠ 0 then y i else 0) = ∑ i, ypos i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hzero : lam i = 0
      · simp [ypos, hzero]
      · simp [ypos, hzero]
    have h'' : Finset.sum sPos (fun i => y i) = ∑ i, if lam i ≠ 0 then y i else 0 := by
      simpa [sPos] using h
    exact h''.trans h'
  have hx_eq : x = k + ∑ i, ypos i := by
    calc
      x = ∑ i, y i := by simpa using hsumy.symm
      _ = k + Finset.sum sPos (fun i => y i) := hsum_split
      _ = k + ∑ i, ypos i := by simp [hsum_ypos]
  have hxmemKsum : x ∈ K + ∑ i, lam i • C i := by
    refine Set.mem_add.2 ?_
    refine ⟨k, hkK, ∑ i, ypos i, hypos_sum_mem, ?_⟩
    simp [hx_eq]
  have hsum_sets :
      K + ∑ i, lam i • C i = ∑ i, lam i • C i := by
    have hsplit :
        ∑ i, lam i • C i =
          lam i0 • C i0 + Finset.sum (Finset.univ.erase i0) (fun i => lam i • C i) := by
      symm
      exact
        (Finset.add_sum_erase (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => lam i • C i) (a := i0) (by simp))
    calc
      K + ∑ i, lam i • C i =
          K + (lam i0 • C i0 +
            Finset.sum (Finset.univ.erase i0) (fun i => lam i • C i)) := by
        simp [hsplit]
      _ = (K + lam i0 • C i0) +
            Finset.sum (Finset.univ.erase i0) (fun i => lam i • C i) := by
        ac_rfl
      _ = lam i0 • C i0 +
            Finset.sum (Finset.univ.erase i0) (fun i => lam i • C i) := by
        simp [absorb_recessionCone_into_positive_weight (C := C i0) (K := K) (hK i0) hpos]
      _ = ∑ i, lam i • C i := by
        simp [hsplit]
  simpa [hsum_sets] using hxmemKsum

/-- The sum of a nonempty family of equal recession cones is the cone. -/
lemma sum_recessionCone_eq_K {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (K : Set (EuclideanSpace Real (Fin n)))
    (hCconv : ∀ i, Convex Real (C i)) (hK : ∀ i, Set.recessionCone (C i) = K) (hm : 0 < m) :
    (∑ i, Set.recessionCone (C i)) = K := by
  classical
  let i0 : Fin m := ⟨0, hm⟩
  apply Set.Subset.antisymm
  · intro x hx
    rcases
        (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
          (f := fun i => Set.recessionCone (C i)) (a := x)).1 hx with
      ⟨z, hz, hsum⟩
    have hzK : ∀ i ∈ (Finset.univ : Finset (Fin m)), z i ∈ Set.recessionCone (C i0) := by
      intro i hi
      have hz' : z i ∈ Set.recessionCone (C i) := by
        simpa using (hz (i := i) (by simp))
      have hzK' : z i ∈ K := by
        simpa [hK i] using hz'
      simpa [hK i0] using hzK'
    have hsumK :
        (Finset.sum (Finset.univ : Finset (Fin m)) (fun i => z i)) ∈
          Set.recessionCone (C i0) :=
      recessionCone_sum_mem_finset (C := C i0) (hCconv i0) (s := (Finset.univ : Finset (Fin m)))
        (z := z) hzK
    have hxrec : x ∈ Set.recessionCone (C i0) := by
      simpa [hsum] using hsumK
    simpa [hK i0] using hxrec
  · intro x hxK
    have hxrec0 : x ∈ Set.recessionCone (C i0) := by
      simpa [hK i0] using hxK
    have hzero : ∀ i, (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone (C i) := by
      intro i x hx t ht
      simpa using hx
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => Set.recessionCone (C i)) (a := x)).2 ?_
    refine ⟨fun i => if i = i0 then x else 0, ?_, ?_⟩
    · intro i hi
      by_cases h : i = i0
      · subst h
        simpa using hxrec0
      · have h0 : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone (C i) := hzero i
        simpa [h] using h0
    · classical
      simp [i0]

/-- Corollary 9.8.1. If `C1, ..., Cm` are nonempty closed convex sets in `ℝ^n` all having the
same recession cone `K`, then `C = conv (C1 ∪ ... ∪ Cm)` is closed and has `K` as its recession
cone. -/
theorem convexHull_iUnion_closed_and_recessionCone_eq {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (K : Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCclosed : ∀ i, IsClosed (C i))
    (hCconv : ∀ i, Convex Real (C i))
    (hK : ∀ i, Set.recessionCone (C i) = K) (hm : 0 < m) :
    let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
    IsClosed C0 ∧ Set.recessionCone C0 = K := by
  classical
  dsimp
  let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
  have hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (C i)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (C i) := by
    intro z hz hsum
    have hzK : ∀ i, z i ∈ K := by
      intro i
      simpa [hK i] using hz i
    exact
      linealitySpace_of_sum_zero_same_recession (C := C) (K := K) hCconv hK z hzK hsum
  have hmain :
      closure C0 =
          ⋃ (lam : Fin m → ℝ)
            (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
            ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) ∧
        Set.recessionCone (closure C0) = ∑ i, Set.recessionCone (C i) := by
    simpa [C0] using
      (closure_convexHull_iUnion_eq_iUnion_weighted_sum_and_recessionCone (C := C) hCne hCclosed
        hCconv hlineal hm)
  rcases hmain with ⟨hclosure, hrec⟩
  have hsubset : closure C0 ⊆ C0 := by
    intro x hx
    have hx' :
        x ∈
          ⋃ (lam : Fin m → ℝ)
            (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
            ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
      simpa [hclosure] using hx
    rcases Set.mem_iUnion.1 hx' with ⟨lam, hx'⟩
    rcases Set.mem_iUnion.1 hx' with ⟨hlam, hxsum⟩
    rcases hlam with ⟨hlam_nonneg, hsum_lam⟩
    have hxsumK :
        x ∈ ∑ i, (if lam i = 0 then K else lam i • C i) := by
      simpa [hK] using hxsum
    have hxsum' :
        x ∈ ∑ i, lam i • C i := by
      exact
        mem_sum_if_recessionCone (C := C) (K := K) hCne hCconv hK hlam_nonneg hsum_lam hxsumK
    have hxconv :
        x ∈ convexHull Real (⋃ i, C i) :=
      (weighted_sum_subset_convexHull (C := C) (lam := lam) hlam_nonneg hsum_lam) hxsum'
    simpa [C0] using hxconv
  have hclosure_eq : closure C0 = C0 := by
    exact Set.Subset.antisymm hsubset subset_closure
  have hclosed : IsClosed C0 := (closure_eq_iff_isClosed).1 hclosure_eq
  have hsumK : (∑ i, Set.recessionCone (C i)) = K :=
    sum_recessionCone_eq_K (C := C) (K := K) hCconv hK hm
  have hrec' : Set.recessionCone C0 = K := by
    have hrec0 : Set.recessionCone (closure C0) = K := by
      simpa [hsumK] using hrec
    simpa [hclosed.closure_eq] using hrec0
  exact ⟨hclosed, hrec'⟩

/-- Replace empty members of a finite family by a fixed set without changing the union. -/
lemma iUnion_replace_empty_eq {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (i0 : Fin m)
    [DecidablePred fun i => (C i).Nonempty] :
    (⋃ i, (if (C i).Nonempty then C i else C i0)) = ⋃ i, C i := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    by_cases hCi : (C i).Nonempty
    · have hx' : x ∈ C i := by
        simpa [hCi] using hx
      exact Set.mem_iUnion.2 ⟨i, hx'⟩
    · have hx' : x ∈ C i0 := by
        simpa [hCi] using hx
      exact Set.mem_iUnion.2 ⟨i0, hx'⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    have hCi : (C i).Nonempty := ⟨x, hx⟩
    exact Set.mem_iUnion.2 ⟨i, by simpa [hCi] using hx⟩

/-- Bounded closed convex sets have recession cone `{0}`. -/
lemma recessionCone_eq_singleton_zero_of_bounded {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) (hCbdd : Bornology.IsBounded C) :
    Set.recessionCone C = {0} := by
  exact
    (bounded_iff_recessionCone_eq_singleton_zero (C := C) hCne hCclosed hCconv).1 hCbdd

/-- If some member of a finite family is nonempty, the convex hull of the union is nonempty. -/
lemma convexHull_iUnion_nonempty {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n))) (hne : ∃ i, (C i).Nonempty) :
    (convexHull Real (⋃ i, C i)).Nonempty := by
  rcases hne with ⟨i, hi⟩
  rcases hi with ⟨x, hx⟩
  have hne_union : (⋃ i, C i).Nonempty := by
    exact ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩⟩
  simpa [convexHull_nonempty_iff] using hne_union

/-- Corollary 9.8.2 9.8.2.1. If `C1, ..., Cm` are closed bounded convex sets in `ℝ^n`,
then `conv (C1 ∪ ... ∪ Cm)` is closed and bounded. -/
theorem convexHull_iUnion_closed_and_bounded {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCclosed : ∀ i, IsClosed (C i)) (hCbdd : ∀ i, Bornology.IsBounded (C i))
    (hCconv : ∀ i, Convex Real (C i)) :
    IsClosed (convexHull Real (⋃ i, C i)) ∧
      Bornology.IsBounded (convexHull Real (⋃ i, C i)) := by
  classical
  by_cases hne : ∃ i, (C i).Nonempty
  · rcases hne with ⟨i0, hi0⟩
    let C' : Fin m → Set (EuclideanSpace Real (Fin n)) :=
      fun i => if (C i).Nonempty then C i else C i0
    have hC'ne : ∀ i, Set.Nonempty (C' i) := by
      intro i
      by_cases hCi : (C i).Nonempty
      · simp [C', hCi]
      · simpa [C', hCi] using hi0
    have hC'closed : ∀ i, IsClosed (C' i) := by
      intro i
      by_cases hCi : (C i).Nonempty
      · simpa [C', hCi] using hCclosed i
      · simpa [C', hCi] using hCclosed i0
    have hC'conv : ∀ i, Convex Real (C' i) := by
      intro i
      by_cases hCi : (C i).Nonempty
      · simpa [C', hCi] using hCconv i
      · simpa [C', hCi] using hCconv i0
    have hC'bdd : ∀ i, Bornology.IsBounded (C' i) := by
      intro i
      by_cases hCi : (C i).Nonempty
      · simpa [C', hCi] using hCbdd i
      · simpa [C', hCi] using hCbdd i0
    have hC'rec :
        ∀ i, Set.recessionCone (C' i) = ({0} : Set (EuclideanSpace Real (Fin n))) := by
      intro i
      exact
        recessionCone_eq_singleton_zero_of_bounded (hCne := hC'ne i) (hCclosed := hC'closed i)
          (hCconv := hC'conv i) (hCbdd := hC'bdd i)
    have hUnion : (⋃ i, C' i) = ⋃ i, C i := by
      simpa [C'] using (iUnion_replace_empty_eq (C := C) i0)
    have hm : 0 < m := by
      exact Nat.lt_of_le_of_lt (Nat.zero_le i0.1) i0.is_lt
    have hclosed_rec :
        IsClosed (convexHull Real (⋃ i, C' i)) ∧
          Set.recessionCone (convexHull Real (⋃ i, C' i)) =
            ({0} : Set (EuclideanSpace Real (Fin n))) := by
      simpa using
        (convexHull_iUnion_closed_and_recessionCone_eq (C := C')
          (K := ({0} : Set (EuclideanSpace Real (Fin n)))) hC'ne hC'closed hC'conv hC'rec
          hm)
    have hclosed : IsClosed (convexHull Real (⋃ i, C i)) := by
      simpa [hUnion] using hclosed_rec.1
    have hrec :
        Set.recessionCone (convexHull Real (⋃ i, C i)) =
          ({0} : Set (EuclideanSpace Real (Fin n))) := by
      simpa [hUnion] using hclosed_rec.2
    have hne_hull : (convexHull Real (⋃ i, C i)).Nonempty :=
      convexHull_iUnion_nonempty (C := C) ⟨i0, hi0⟩
    have hconv_hull : Convex Real (convexHull Real (⋃ i, C i)) := by
      simpa using (convex_convexHull (𝕜 := Real) (s := ⋃ i, C i))
    have hbdd :
        Bornology.IsBounded (convexHull Real (⋃ i, C i)) := by
      exact
        (bounded_iff_recessionCone_eq_singleton_zero (C := convexHull Real (⋃ i, C i)) hne_hull
          hclosed hconv_hull).2 hrec
    exact ⟨hclosed, hbdd⟩
  · have hUnion : (⋃ i, C i) = (∅ : Set (EuclideanSpace Real (Fin n))) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
        exact (hne ⟨i, ⟨x, hx⟩⟩).elim
      · intro hx
        cases hx
    simp [hUnion]

/-- Closed proper convex functions have closed, convex, nonempty epigraphs. -/
lemma epigraph_family_closed_convex_nonempty {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    ∀ i,
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
        IsClosed (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
        Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
  intro i
  have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
    (hproper i).2.1
  have hconv : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
    simpa [ConvexFunctionOn] using (hproper i).1
  have hls : LowerSemicontinuous (f i) := (hclosed i).2
  have hsub :
      ∀ α : Real, IsClosed {x | f i x ≤ (α : EReal)} := by
    exact (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f i)).1.1 hls
  have hclosed_epi :
      IsClosed (epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f i)).2.1 hsub
  exact ⟨hne, hclosed_epi, hconv⟩

/-- The convex hull of a union of epigraphs lies in the epigraph of any convex minorant. -/
lemma convexHull_union_epigraph_subset_epigraph_of_minorant {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {h : (Fin n → Real) → EReal}
    (hh : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) h)
    (hle : ∀ i, h ≤ f i) :
    convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)) ⊆
      epigraph (Set.univ : Set (Fin n → Real)) h := by
  simpa using (convexHull_union_subset_epigraph_of_le (f := f) (h := h) hh hle)

/-- Recession cones of the epigraph family agree with the common recession function. -/
lemma recessionCone_epigraph_eq_epigraph_k {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {k : (Fin n → Real) → EReal}
    (hconv : ∀ i, Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hk :
      ∀ (i : Fin m) (y : Fin n → Real),
        k y = sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x }) :
    ∀ i,
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
        epigraph (Set.univ : Set (Fin n → Real)) k := by
  classical
  intro i
  apply Set.Subset.antisymm
  · intro p hp
    rcases p with ⟨y, a⟩
    have hle : ∀ x : Fin n → Real, f i (x + y) - f i x ≤ (a : EReal) := by
      intro x
      by_cases htop : f i x = ⊤
      · have hsub : f i (x + y) - f i x = (⊥ : EReal) := by
          simp [htop]
        simp [hsub]
      · have hbot : f i x ≠ (⊥ : EReal) :=
          (hproper i).2.2 x (by simp)
        have hleμ :
            f i x ≤ ((f i x).toReal : EReal) := EReal.le_coe_toReal htop
        have hmem :
            (x, (f i x).toReal) ∈
              epigraph (Set.univ : Set (Fin n → Real)) (f i) :=
          (mem_epigraph_univ_iff (f := f i)).2 hleμ
        have hrec :
            (x + y, (f i x).toReal + a) ∈
              epigraph (Set.univ : Set (Fin n → Real)) (f i) := by
          have hrec' := hp hmem (t := (1 : Real)) (by exact zero_le_one)
          simpa using hrec'
        have hle' :
            f i (x + y) ≤ ((f i x).toReal : EReal) + (a : EReal) :=
          (mem_epigraph_univ_iff (f := f i)).1 hrec
        have hEq : ((f i x).toReal : EReal) = f i x := EReal.coe_toReal htop hbot
        have hle'' :
            f i (x + y) ≤ (a : EReal) + f i x := by
          simpa [hEq, add_comm, add_left_comm, add_assoc] using hle'
        exact
          (EReal.sub_le_iff_le_add (a := f i (x + y)) (b := f i x) (c := (a : EReal))
              (h₁ := Or.inl hbot) (h₂ := Or.inl htop)).2 hle''
    have hsup_le :
        sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x } ≤
          (a : EReal) := by
      refine sSup_le ?_
      intro r hr
      rcases hr with ⟨x, rfl⟩
      exact hle x
    have hky : k y ≤ (a : EReal) := by
      simpa [hk i y] using hsup_le
    exact (mem_epigraph_univ_iff (f := k)).2 hky
  · intro p hp
    rcases p with ⟨y, a⟩
    have hky : k y ≤ (a : EReal) :=
      (mem_epigraph_univ_iff (f := k)).1 hp
    have hbound :
        ∀ x : Fin n → Real, f i (x + y) - f i x ≤ k y := by
      intro x
      have hmem :
          f i (x + y) - f i x ∈
            { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x } := ⟨x, rfl⟩
      have hle := le_sSup hmem
      simpa [hk i y] using hle
    have hconv' : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := hconv i
    have hadd :
        ∀ p ∈ epigraph (Set.univ : Set (Fin n → Real)) (f i),
          p + (1 : Real) • (y, a) ∈
            epigraph (Set.univ : Set (Fin n → Real)) (f i) := by
      intro p hp
      rcases p with ⟨x, μ⟩
      have hxle : f i x ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := f i)).1 hp
      have hdiff : f i (x + y) - f i x ≤ (a : EReal) :=
        le_trans (hbound x) hky
      have hle' : f i (x + y) ≤ (a : EReal) + f i x :=
        (EReal.sub_le_iff_le_add
          (a := f i (x + y)) (b := f i x) (c := (a : EReal))
          (h₁ := Or.inr (EReal.coe_ne_top a)) (h₂ := Or.inr (EReal.coe_ne_bot a))).1 hdiff
      have hle'' : f i (x + y) ≤ (a : EReal) + (μ : EReal) :=
        by
          have hle'' :
              (a : EReal) + f i x ≤ (a : EReal) + (μ : EReal) :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_left hxle (a : EReal))
          exact le_trans hle' hle''
      have hmem :
          (x + y, μ + a) ∈ epigraph (Set.univ : Set (Fin n → Real)) (f i) :=
        (mem_epigraph_univ_iff (f := f i)).2 (by
          simpa [add_comm, add_left_comm, add_assoc] using hle'')
      simpa [one_smul, add_comm, add_left_comm, add_assoc] using hmem
    have hrec :
        (y, a) ∈ Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
      exact
        mem_recessionCone_of_add_mem_fixed_t
          (C := epigraph (Set.univ : Set (Fin n → Real)) (f i)) hconv' (v := (y, a))
          (t := (1 : Real)) (by exact zero_lt_one) hadd
    simpa using hrec

/-- Closedness and recession cone of the convex hull of a finite epigraph family in product space. -/
lemma convexHull_union_epigraph_closed_recession_prod {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {k : (Fin n → Real) → EReal}
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hk :
      ∀ (i : Fin m) (y : Fin n → Real),
        k y = sSup { r : EReal | ∃ x : Fin n → Real, r = f i (x + y) - f i x })
    (hm : 0 < m) :
    let C0 : Set ((Fin n → Real) × Real) :=
      convexHull ℝ (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))
    IsClosed C0 ∧
      Set.recessionCone C0 = epigraph (Set.univ : Set (Fin n → Real)) k := by
  classical
  intro C0
  let e := prodLinearEquiv_append (n := n)
  let C' : Fin m → Set (EuclideanSpace Real (Fin (n + 1))) :=
    fun i => e '' epigraph (Set.univ : Set (Fin n → Real)) (f i)
  have hC : ∀ i,
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
        IsClosed (epigraph (Set.univ : Set (Fin n → Real)) (f i)) ∧
        Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
    epigraph_family_closed_convex_nonempty (hclosed := hclosed) (hproper := hproper)
  have hCne : ∀ i, Set.Nonempty (C' i) := by
    intro i
    rcases (hC i).1 with ⟨p, hp⟩
    exact ⟨e p, ⟨p, hp, rfl⟩⟩
  have hCclosed : ∀ i, IsClosed (C' i) := by
    intro i
    have hclosed_epi :
        IsClosed (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := (hC i).2.1
    let hhome := (e.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosed' :
        IsClosed ((hhome : _ → _) '' epigraph (Set.univ : Set (Fin n → Real)) (f i)) :=
      (hhome.isClosed_image (s := epigraph (Set.univ : Set (Fin n → Real)) (f i))).2 hclosed_epi
    simpa [C', hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hCconv : ∀ i, Convex ℝ (C' i) := by
    intro i
    have hconv_epi :
        Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := (hC i).2.2
    simpa [C'] using hconv_epi.linear_image e.toLinearMap
  have hK : ∀ i, Set.recessionCone (C' i) =
      e '' epigraph (Set.univ : Set (Fin n → Real)) k := by
    intro i
    have hrec_i :
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) k :=
      (recessionCone_epigraph_eq_epigraph_k (f := f) (k := k)
        (hconv := fun j => (hC j).2.2) (hproper := hproper) hk) i
    calc
      Set.recessionCone (C' i) =
          e '' Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
            simpa [C'] using
              (recessionCone_image_linearEquiv (e := e)
                (C := epigraph (Set.univ : Set (Fin n → Real)) (f i)))
      _ = e '' epigraph (Set.univ : Set (Fin n → Real)) k := by
            simp [hrec_i]
  have hC0' :
      IsClosed (convexHull ℝ (⋃ i, C' i)) ∧
        Set.recessionCone (convexHull ℝ (⋃ i, C' i)) =
          e '' epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa using
      (convexHull_iUnion_closed_and_recessionCone_eq (C := C')
        (K := e '' epigraph (Set.univ : Set (Fin n → Real)) k)
        hCne hCclosed hCconv hK hm)
  have hC0_image :
      e '' C0 = convexHull ℝ (⋃ i, C' i) := by
    have himage :
        e '' (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          ⋃ i, e '' epigraph (Set.univ : Set (Fin n → Real)) (f i) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
        exact Set.mem_iUnion.2 ⟨i, ⟨x, hx, rfl⟩⟩
      · intro hy
        rcases Set.mem_iUnion.1 hy with ⟨i, hy⟩
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩, rfl⟩
    calc
      e '' C0 =
          convexHull ℝ
            (e '' (⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i))) := by
              simpa [C0] using
                (LinearMap.image_convexHull (f := e.toLinearMap)
                  (s := ⋃ i, epigraph (Set.univ : Set (Fin n → Real)) (f i)))
      _ =
          convexHull ℝ
            (⋃ i, e '' epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
            simp [himage]
      _ = convexHull ℝ (⋃ i, C' i) := by rfl
  have hclosed_image : IsClosed (e '' C0) := by
    simpa [hC0_image] using hC0'.1
  let hhome := (e.toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosed : IsClosed C0 := by
    have hclosed' : IsClosed ((hhome : _ → _) '' C0) := by
      simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed_image
    exact (hhome.isClosed_image (s := C0)).1 hclosed'
  have hrec_image :
      Set.recessionCone (e '' C0) =
        e '' epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa [hC0_image] using hC0'.2
  have hrec_image' :
      e '' Set.recessionCone C0 =
        e '' epigraph (Set.univ : Set (Fin n → Real)) k := by
    simpa [recessionCone_image_linearEquiv (e := e) (C := C0)] using hrec_image
  have hrec : Set.recessionCone C0 = epigraph (Set.univ : Set (Fin n → Real)) k := by
    ext v
    constructor
    · intro hv
      have hv' : e v ∈ e '' epigraph (Set.univ : Set (Fin n → Real)) k := by
        have hv'' : e v ∈ e '' Set.recessionCone C0 := ⟨v, hv, rfl⟩
        simpa [hrec_image'] using hv''
      rcases hv' with ⟨w, hw, hw_eq⟩
      have hw' : w = v := by
        apply e.injective
        simp [hw_eq]
      simpa [hw'] using hw
    · intro hv
      have hv' : e v ∈ e '' Set.recessionCone C0 := by
        have hv'' : e v ∈ e '' epigraph (Set.univ : Set (Fin n → Real)) k := ⟨v, hv, rfl⟩
        simpa [hrec_image'] using hv''
      rcases hv' with ⟨w, hw, hw_eq⟩
      have hw' : w = v := by
        apply e.injective
        simp [hw_eq]
      simpa [hw'] using hw
  exact ⟨hclosed, hrec⟩

end Section09
end Chap02
