/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part13

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology

section Chap02
section Section09

/-- Closure of the lifted cone over `convexHull` equals the closure of the sum of lifted cones
when the index type is `Fin (Nat.succ m)`. -/
lemma closure_cone_over_convexHull_eq_closure_sum_cones_succ (n m : Nat)
    (C : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCconv : ∀ i, Convex Real (C i)) :
    let C0 : Set (EuclideanSpace Real (Fin n)) := convexHull Real (⋃ i, C i)
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
    let S : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    closure K0 = closure (∑ i, K i) := by
  classical
  intro C0 coords first tail S0 K0 S K
  apply subset_antisymm
  · have hsubset : K0 ⊆ closure (∑ i, K i) := by
      simpa [C0, coords, first, tail, S0, K0, S, K] using
        (K0_subset_closure_sum_cones (n := n) (m := m) (C := C) hCne hCconv)
    have hclosure := closure_mono hsubset
    simpa [closure_closure] using hclosure
  · have hsubset : (∑ i, K i) ⊆ K0 := by
      simpa [C0, coords, first, tail, S0, K0, S, K] using
        (sum_cones_subset_K0 (n := n) (m := m) (C := C))
    exact closure_mono hsubset

/-- Points in the closure of a lifted cone have nonnegative first coordinate. -/
lemma first_nonneg_of_mem_closure_lifted_cone {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex Real C) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, v ∈ closure K → 0 ≤ first v := by
  classical
  intro coords first tail S K v hv
  have hclosure :
      closure K =
        K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C} := by
    simpa [coords, first, tail, S, K] using
      (closure_cone_eq_union_recession (n := n) (C := C) hCne hCclosed hCconv)
  have hmemK :
      ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
    simpa [coords, first, tail, S, K] using
      (mem_K_iff_first_tail (n := n) (C := C) hCconv)
  have hv' :
      v ∈ K ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone C} := by
    simpa [hclosure] using hv
  rcases hv' with hvK | hv0
  · exact le_of_lt ((hmemK v).1 hvK).1
  · exact le_of_eq hv0.1.symm

/-- The lifted cone over a nonempty set is nonempty. -/
lemma lifted_cone_nonempty {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hCne : C.Nonempty) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    Set.Nonempty K := by
  classical
  intro coords first tail S K
  rcases hCne with ⟨x0, hx0⟩
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
  let v : EuclideanSpace Real (Fin (1 + n)) := append y0 x0
  have hfirst_tail :
      first v = 1 ∧ tail v = x0 := by
    have h := first_tail_append (n := n) (y := y0) (z := x0)
    simpa [coords, first, tail, append, v, y0] using h
  have hvS : v ∈ S := by
    refine ⟨hfirst_tail.1, ?_⟩
    simpa [hfirst_tail.2] using hx0
  have hvK : v ∈ K := by
    exact (ConvexCone.subset_hull (s := S) hvS)
  exact ⟨v, hvK⟩

/-- The coordinate image of a lifted cone is a convex cone. -/
lemma lifted_cone_isConvexCone {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    IsConvexCone (1 + n)
      (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))) K) := by
  classical
  intro coords first tail S K
  let e := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  have hKconv : Convex Real K := by
    simpa [K] using (ConvexCone.convex (C := ConvexCone.hull Real S))
  have hcone :
      IsConeSet (1 + n) (Set.image e K) := by
    intro x hx t ht
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : t • y ∈ K := by
      have hy'' :
          t • y ∈ (ConvexCone.hull Real S : Set _) :=
        (ConvexCone.hull Real S).smul_mem ht (by simpa [K] using hy)
      simpa [K] using hy''
    refine ⟨t • y, hy', ?_⟩
    simp
  have hconv_image : Convex Real (Set.image e K) :=
    hKconv.linear_image (e.toLinearMap)
  exact ⟨hcone, hconv_image⟩

/-- Zero-sum families in closures of lifted cones are lineality directions. -/
lemma lineality_of_zero_sum_closure_lifted_cones {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCclosed : ∀ i, IsClosed (C i))
    (hCconv : ∀ i, Convex Real (C i))
    (hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (C i)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (C i)) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ z : Fin m → EuclideanSpace Real (Fin (1 + n)),
      (∀ i, z i ∈ closure (K i)) →
      (∑ i, z i) = 0 →
      ∀ i, z i ∈ Set.linealitySpace (closure (K i)) := by
  classical
  intro coords first tail S K z hz hsum i
  have hfirst_nonneg :
      ∀ i, ∀ v, v ∈ closure (K i) → 0 ≤ first v := by
    intro i v hv
    simpa [coords, first, tail, S, K] using
      (first_nonneg_of_mem_closure_lifted_cone (n := n) (C := C i) (hCne i) (hCclosed i)
        (hCconv i) v hv)
  have hfirst_sum :
      first (Finset.univ.sum (fun i => z i)) =
        Finset.univ.sum (fun i => first (z i)) := by
    simp [first, coords]
  have hfirst_sum0 :
      Finset.univ.sum (fun i => first (z i)) = 0 := by
    have hsum0' : first (Finset.univ.sum (fun i => z i)) = 0 := by
      have := congrArg first hsum
      simpa [first, coords] using this
    simpa [hfirst_sum] using hsum0'
  have hfirst0 : ∀ i, first (z i) = 0 := by
    have hnonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ first (z i) := by
      intro i hi
      exact hfirst_nonneg i (z i) (hz i)
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hfirst_sum0
    intro i
    exact hzero i (by simp)
  have htail_rec : ∀ i, tail (z i) ∈ Set.recessionCone (C i) := by
    intro i
    simpa [coords, first, tail, S, K, hfirst0 i] using
      (tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n) (C := C i)
        (hCclosed i) (hCconv i) (z i) (hz i) (hfirst0 i))
  have htail_sum :
      tail (Finset.univ.sum (fun i => z i)) =
        Finset.univ.sum (fun i => tail (z i)) := by
    apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
    funext j
    simp [tail, coords]
  have htail_sum0 :
      Finset.univ.sum (fun i => tail (z i)) = 0 := by
    have hsum0' : tail (Finset.univ.sum (fun i => z i)) = 0 := by
      have := congrArg tail hsum
      simpa [tail, coords] using this
    simpa [htail_sum] using hsum0'
  have htail_lineal : ∀ i, tail (z i) ∈ Set.linealitySpace (C i) :=
    hlineal (fun i => tail (z i)) htail_rec htail_sum0
  have htail_rec_neg : ∀ i, -tail (z i) ∈ Set.recessionCone (C i) := by
    intro i
    have hmem : tail (z i) ∈ (-Set.recessionCone (C i)) ∩ Set.recessionCone (C i) := by
      simpa [Set.linealitySpace] using htail_lineal i
    have hneg : tail (z i) ∈ -Set.recessionCone (C i) := hmem.1
    simpa [Set.mem_neg] using hneg
  have hKne : ∀ i, Set.Nonempty (K i) := by
    intro i
    simpa [coords, first, tail, S, K] using
      (lifted_cone_nonempty (n := n) (C := C i) (hCne i))
  have hKcone :
      ∀ i,
        IsConvexCone (1 + n)
          (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))) (K i)) := by
    intro i
    simpa [coords, first, tail, S, K] using (lifted_cone_isConvexCone (n := n) (C := C i))
  have hrec_eq :
      ∀ i, Set.recessionCone (closure (K i)) = closure (K i) := by
    intro i
    exact recessionCone_closure_eq_of_convexCone (K := K i) (hKne i) (hKcone i)
  have hlineal_eq :
      ∀ i, Set.linealitySpace (closure (K i)) = closure (K i) ∩ -closure (K i) := by
    intro i
    exact Set.linealitySpace_eq_inter_of_recessionCone_eq (C := closure (K i)) (hrec_eq i)
  have hz_in : z i ∈ closure (K i) := hz i
  have hneg_in : -z i ∈ closure (K i) := by
    have hclosure :
        closure (K i) =
          K i ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} := by
      simpa [coords, first, tail, S, K] using
        (closure_cone_eq_union_recession (n := n) (C := C i) (hCne i) (hCclosed i)
          (hCconv i))
    have hfirst0' : first (-z i) = 0 := by
      have hfirst_neg : first (-z i) = -first (z i) := by
        simp [first, coords]
      simpa [hfirst0 i] using hfirst_neg
    have htail_rec' : tail (-z i) ∈ Set.recessionCone (C i) := by
      have htail_eq : tail (-z i) = -tail (z i) := by
        apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
        funext j
        simp [tail, coords]
      simpa [htail_eq] using htail_rec_neg i
    have hmem :
        -z i ∈ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} := by
      exact ⟨hfirst0', htail_rec'⟩
    have : -z i ∈ K i ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} :=
      Or.inr hmem
    simpa [hclosure] using this
  have hz_inter : z i ∈ closure (K i) ∩ -closure (K i) := by
    refine ⟨hz_in, ?_⟩
    simpa [Set.mem_neg] using hneg_in
  simpa [hlineal_eq i] using hz_inter

/-- Closure of the sum of lifted cones equals the sum of their closures. -/
lemma closure_sum_cones_eq_sum_closure_cones {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCclosed : ∀ i, IsClosed (C i))
    (hCconv : ∀ i, Convex Real (C i))
    (hlineal :
      ∀ z : Fin m → EuclideanSpace Real (Fin n),
        (∀ i, z i ∈ Set.recessionCone (C i)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (C i)) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    closure (∑ i, K i) = ∑ i, closure (K i) := by
  classical
  intro coords first tail S K
  have hKne : ∀ i, Set.Nonempty (K i) := by
    intro i
    simpa [coords, first, tail, S, K] using
      (lifted_cone_nonempty (n := n) (C := C i) (hCne i))
  have hKcone :
      ∀ i,
        IsConvexCone (1 + n)
          (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))) (K i)) := by
    intro i
    simpa [coords, first, tail, S, K] using (lifted_cone_isConvexCone (n := n) (C := C i))
  have hlineal' :
      ∀ z : Fin m → EuclideanSpace Real (Fin (1 + n)),
        (∀ i, z i ∈ closure (K i)) →
        (∑ i, z i) = 0 →
        ∀ i, z i ∈ Set.linealitySpace (closure (K i)) := by
    intro z hz hsum
    simpa [coords, first, tail, S, K] using
      (lineality_of_zero_sum_closure_lifted_cones (n := n) (m := m) (C := C) hCne hCclosed
        hCconv hlineal z hz hsum)
  exact
    (closure_sum_eq_sum_closure_of_convexCone_sum_zero_lineality (K := K) hKne hKcone
        hlineal')

/-- The closure of the lifted cone over `C0` agrees with the closure of the lifted cone over
`closure C0`. -/
lemma closure_lifted_cone_eq_closure_lifted_cone_closure {n : Nat}
    (C0 : Set (EuclideanSpace Real (Fin n))) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
    let S0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
      {v | first v = 1 ∧ tail v ∈ closure C0}
    let K0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S0bar : Set (EuclideanSpace Real (Fin (1 + n))))
    closure K0 = closure K0bar := by
  classical
  intro coords first tail S0 K0 S0bar K0bar
  apply subset_antisymm
  · have hS0subset : S0 ⊆ S0bar := by
      intro v hv
      exact ⟨hv.1, subset_closure hv.2⟩
    have hS0subset' : S0 ⊆ (ConvexCone.hull Real S0bar : Set _) := by
      intro v hv
      have hv' : v ∈ S0bar := hS0subset hv
      exact (ConvexCone.subset_hull (s := S0bar) hv')
    have hK0subset' :
        (ConvexCone.hull Real S0) ≤ (ConvexCone.hull Real S0bar) :=
      ConvexCone.hull_min (s := S0) (C := ConvexCone.hull Real S0bar) hS0subset'
    have hK0subset : K0 ⊆ K0bar := by
      simpa [K0, K0bar] using hK0subset'
    exact closure_mono hK0subset
  · have hS0bar : S0bar ⊆ closure K0 := by
      intro v hv
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
      let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
        fun x => append y0 x
      have hfirst_tail_lift :
          ∀ x, first (lift x) = 1 ∧ tail (lift x) = x := by
        intro x
        have h := (first_tail_append (n := n) (y := y0) (z := x))
        simpa [coords, first, tail, append, lift, y0] using h
      have hv_eq : v = lift (tail v) := by
        have hfirst : first v = first (lift (tail v)) := by
          calc
            first v = 1 := hv.1
            _ = first (lift (tail v)) := (hfirst_tail_lift (tail v)).1.symm
        have htail : tail v = tail (lift (tail v)) := by
          simpa using (hfirst_tail_lift (tail v)).2.symm
        exact
          (eq_of_first_tail_eq (n := n)
            (u := v) (v := lift (tail v)) hfirst htail)
      have hcont_lift : Continuous lift := by
        have hcont_append : Continuous (appendAffineEquiv 1 n : _ → _) :=
          (appendAffineEquiv 1 n).continuous_of_finiteDimensional
        have hcont_inner :
            Continuous fun x : EuclideanSpace Real (Fin n) => (y0, x) := by
          fun_prop
        have hlift : lift = fun x => appendAffineEquiv 1 n (y0, x) := by
          funext x
          simp [lift, append, appendAffineEquiv_apply]
        simpa [hlift] using hcont_append.comp hcont_inner
      have himage :
          lift '' closure C0 ⊆ closure (lift '' C0) :=
        image_closure_subset_closure_image hcont_lift
      have hv_in : v ∈ lift '' closure C0 := by
        refine ⟨tail v, hv.2, ?_⟩
        exact hv_eq.symm
      have hv_in_closure : v ∈ closure (lift '' C0) := himage hv_in
      have hsubset_K0 : lift '' C0 ⊆ K0 := by
        intro w hw
        rcases hw with ⟨x, hxC0, rfl⟩
        have hwS0 : lift x ∈ S0 := by
          refine ⟨(hfirst_tail_lift x).1, ?_⟩
          simpa [(hfirst_tail_lift x).2] using hxC0
        exact (ConvexCone.subset_hull (s := S0) hwS0)
      exact (closure_mono hsubset_K0) hv_in_closure
    have hS0bar' : S0bar ⊆ (ConvexCone.hull Real S0).closure := by
      simpa [K0, ConvexCone.coe_closure] using hS0bar
    have hK0bar :
        (ConvexCone.hull Real S0bar) ≤ (ConvexCone.hull Real S0).closure :=
      ConvexCone.hull_min (s := S0bar) (C := (ConvexCone.hull Real S0).closure) hS0bar'
    have hK0bar_subset : K0bar ⊆ closure K0 := by
      simpa [K0bar, K0, ConvexCone.coe_closure] using hK0bar
    simpa [closure_closure] using (closure_mono hK0bar_subset)

/-- The `first = 1` slice of the closure of the lifted cone over `C0` is `closure C0`. -/
lemma closure_C0_eq_first_one_slice_closure_lifted_cone {n : Nat}
    {C0 : Set (EuclideanSpace Real (Fin n))} (hC0conv : Convex Real C0) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S0 : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S0 : Set (EuclideanSpace Real (Fin (1 + n))))
    closure C0 =
      {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
  classical
  intro coords first tail S0 K0
  let S0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
    {v | first v = 1 ∧ tail v ∈ closure C0}
  let K0bar : Set (EuclideanSpace Real (Fin (1 + n))) :=
    (ConvexCone.hull Real S0bar : Set (EuclideanSpace Real (Fin (1 + n))))
  have hclosureK : closure K0 = closure K0bar := by
    simpa [coords, first, tail, S0, K0, S0bar, K0bar] using
      (closure_lifted_cone_eq_closure_lifted_cone_closure (n := n) (C0 := C0))
  ext x
  constructor
  · intro hx
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
    let lift : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (1 + n)) :=
      fun x => append y0 x
    have hfirst_tail_lift :
        ∀ x, first (lift x) = 1 ∧ tail (lift x) = x := by
      intro x
      have h := (first_tail_append (n := n) (y := y0) (z := x))
      simpa [coords, first, tail, append, lift, y0] using h
    let v : EuclideanSpace Real (Fin (1 + n)) := lift x
    have hvS0bar : v ∈ S0bar := by
      refine ⟨(hfirst_tail_lift x).1, ?_⟩
      simpa [v, (hfirst_tail_lift x).2] using hx
    have hvK0bar : v ∈ K0bar := by
      exact (ConvexCone.subset_hull (s := S0bar) hvS0bar)
    have hvcl : v ∈ closure K0 := by
      have : v ∈ closure K0bar := subset_closure hvK0bar
      simpa [hclosureK] using this
    exact ⟨v, hvcl, (hfirst_tail_lift x).1, (hfirst_tail_lift x).2⟩
  · rintro ⟨v, hvcl, hv1, hvx⟩
    have hvclbar : v ∈ closure K0bar := by
      simpa [hclosureK] using hvcl
    have hpos : 0 < first v := by
      simp [hv1]
    have hvK0bar :
        v ∈ K0bar := by
      simpa [coords, first, tail, S0bar, K0bar] using
        (mem_K_of_mem_closure_K_first_pos (n := n) (C := closure C0) (hCclosed := isClosed_closure)
          (hCconv := (Convex.closure hC0conv)) v hvclbar hpos)
    have hmem :
        0 < first v ∧ tail v ∈ (first v) • closure C0 := by
      have hmem' :
          v ∈ K0bar ↔
            0 < first v ∧ tail v ∈ (first v) • closure C0 := by
        simpa [coords, first, tail, S0bar, K0bar] using
        (mem_K_iff_first_tail (n := n) (C := closure C0) (hC := (Convex.closure hC0conv))
            (v := v))
      exact (hmem').1 hvK0bar
    rcases hmem.2 with ⟨y, hy, hytail⟩
    have hy_eq : y = tail v := by
      simpa [hv1] using hytail
    have hy_eq' : y = x := by
      simpa [hvx] using hy_eq
    simpa [hy_eq'] using hy

/-- The `first = 1` slice of the sum of closures of lifted cones. -/
lemma mem_sum_closure_cones_first_eq_one_iff {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCclosed : ∀ i, IsClosed (C i))
    (hCconv : ∀ i, Convex Real (C i)) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, first v = 1 →
      (v ∈ ∑ i, closure (K i) ↔
        ∃ (lam : Fin m → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
          tail v ∈ ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) := by
  classical
  intro coords first tail S K v hv1
  have hfirst_nonneg :
      ∀ i, ∀ v, v ∈ closure (K i) → 0 ≤ first v := by
    intro i v hv
    simpa [coords, first, tail, S, K] using
      (first_nonneg_of_mem_closure_lifted_cone (n := n) (C := C i) (hCne i) (hCclosed i)
        (hCconv i) v hv)
  constructor
  · intro hvsum
    rcases
        (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
            (f := fun i => closure (K i)) (a := v)).1 hvsum with ⟨z, hzmem, hsum⟩
    have hzmem' : ∀ i, z i ∈ closure (K i) := by
      intro i
      exact hzmem (i := i) (by simp)
    let lam : Fin m → ℝ := fun i => first (z i)
    have hlam_nonneg : ∀ i, 0 ≤ lam i := by
      intro i
      exact hfirst_nonneg i (z i) (hzmem' i)
    have hfirst_sum :
        first (∑ i, z i) = ∑ i, first (z i) := by
      simp [first, coords]
    have hsum_lam : (∑ i, lam i) = 1 := by
      have hsum' : first (∑ i, z i) = first v := by
        simpa using congrArg first hsum
      calc
        ∑ i, lam i = first (∑ i, z i) := by simp [lam, hfirst_sum]
        _ = first v := hsum'
        _ = 1 := hv1
    have htail_sum :
        tail (∑ i, z i) = ∑ i, tail (z i) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext j
      simp [tail, coords]
    have htail_sum' : ∑ i, tail (z i) = tail v := by
      have hsum' : tail (∑ i, z i) = tail v := by
        simpa [tail, coords] using congrArg tail hsum
      exact htail_sum.symm.trans hsum'
    have htail_mem :
        ∀ i, tail (z i) ∈
          (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) := by
      intro i
      by_cases hzero : lam i = 0
      · have hfirst0 : first (z i) = 0 := by simp [lam, hzero]
        have htail_rec :
            tail (z i) ∈ Set.recessionCone (C i) := by
          simpa [coords, first, tail, S, K, hfirst0] using
            (tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n) (C := C i)
              (hCclosed i) (hCconv i) (z i) (hzmem' i) hfirst0)
        simpa [hzero] using htail_rec
      · have hpos : 0 < lam i := lt_of_le_of_ne (hlam_nonneg i) (Ne.symm hzero)
        have hzK :
            z i ∈ K i := by
          simpa [coords, first, tail, S, K, lam] using
            (mem_K_of_mem_closure_K_first_pos (n := n) (C := C i) (hCclosed i) (hCconv i)
              (z i) (hzmem' i) hpos)
        have hmem :
            0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • C i := by
          have hmem' :
              z i ∈ K i ↔
                0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • C i := by
            simpa [coords, first, tail, S, K] using
              (mem_K_iff_first_tail (n := n) (C := C i) (hCconv i) (v := z i))
          exact (hmem').1 hzK
        have htail_mem' : tail (z i) ∈ lam i • C i := by
          simpa [lam] using hmem.2
        simpa [hzero] using htail_mem'
    have hmem_sum :
        tail v ∈
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) := by
      refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
        (f := fun i => (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))
        (a := tail v)).2 ?_
      refine ⟨fun i => tail (z i), ?_, ?_⟩
      · intro i hi
        exact htail_mem i
      · simp [htail_sum']
    exact ⟨lam, hlam_nonneg, hsum_lam, hmem_sum⟩
  · rintro ⟨lam, hlam, hsum_lam, htail_mem⟩
    rcases
        (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
          (f := fun i =>
            (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))
          (a := tail v)).1 htail_mem with ⟨x, hxmem, hxsum⟩
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let y : Fin m → EuclideanSpace Real (Fin 1) :=
      fun i => (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => lam i)
    let z : Fin m → EuclideanSpace Real (Fin (1 + n)) :=
      fun i => append (y i) (x i)
    have hfirst_tail_z :
        ∀ i, first (z i) = lam i ∧ tail (z i) = x i := by
      intro i
      have h := first_tail_append (n := n) (y := y i) (z := x i)
      simpa [append, y, z, coords, first, tail] using h
    have hfirst_z : ∀ i, first (z i) = lam i := fun i => (hfirst_tail_z i).1
    have htail_z : ∀ i, tail (z i) = x i := fun i => (hfirst_tail_z i).2
    have hzmem :
        ∀ i, z i ∈ closure (K i) := by
      intro i
      by_cases hzero : lam i = 0
      · have hxrec : x i ∈ Set.recessionCone (C i) := by
          have := hxmem (i := i) (by simp)
          simpa [hzero] using this
        have hclosure :
            closure (K i) =
              K i ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} := by
          simpa [coords, first, tail, S, K] using
            (closure_cone_eq_union_recession (n := n) (C := C i) (hCne i) (hCclosed i)
              (hCconv i))
        have hmem :
            z i ∈ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} := by
          refine ⟨?_, ?_⟩
          · simp [hfirst_z i, hzero]
          · simpa [htail_z i] using hxrec
        have :
            z i ∈ K i ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} :=
          Or.inr hmem
        simpa [hclosure] using this
      · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm hzero)
        have hxmem' :
            x i ∈ lam i • C i := by
          have := hxmem (i := i) (by simp)
          simpa [hzero] using this
        rcases hxmem' with ⟨x0, hx0C, hx0eq⟩
        have htail_mem : tail (z i) ∈ (lam i) • C i := by
          refine ⟨x0, hx0C, ?_⟩
          calc
            lam i • x0 = x i := hx0eq
            _ = tail (z i) := (htail_z i).symm
        have hzK :
            z i ∈ K i := by
          have hmem :
              0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • C i := by
            refine ⟨?_, ?_⟩
            · simpa [hfirst_z i] using hpos
            · simpa [hfirst_z i] using htail_mem
          have hmem' :
              z i ∈ K i ↔
                0 < first (z i) ∧ tail (z i) ∈ (first (z i)) • C i := by
            simpa [coords, first, tail, S, K] using
              (mem_K_iff_first_tail (n := n) (C := C i) (hCconv i) (v := z i))
          exact (hmem').2 hmem
        exact subset_closure hzK
    have hfirst_sum :
        first (∑ i, z i) = ∑ i, first (z i) := by
      simp [first, coords]
    have htail_sum :
        tail (∑ i, z i) = ∑ i, tail (z i) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext j
      simp [tail, coords]
    have hfirst_eq : first (∑ i, z i) = first v := by
      calc
        first (∑ i, z i) = ∑ i, first (z i) := hfirst_sum
        _ = ∑ i, lam i := by simp [hfirst_z]
        _ = 1 := hsum_lam
        _ = first v := by simp [hv1]
    have htail_eq : tail (∑ i, z i) = tail v := by
      calc
        tail (∑ i, z i) = ∑ i, tail (z i) := htail_sum
        _ = ∑ i, x i := by simp [htail_z]
        _ = tail v := by simp [hxsum]
    have hEq :
        ∀ u v, first u = first v → tail u = tail v → u = v := by
      simpa [coords, first, tail] using (eq_of_first_tail_eq (n := n))
    have hsum_z : ∑ i, z i = v := hEq _ _ hfirst_eq htail_eq
    refine
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
          (f := fun i => closure (K i)) (a := v)).2 ?_
    refine ⟨z, ?_, hsum_z⟩
    intro i hi
    exact hzmem (i := i)

/-- The `first = 0` slice of the sum of closures of lifted cones. -/
lemma mem_sum_closure_cones_first_eq_zero_iff {n m : Nat}
    (C : Fin m → Set (EuclideanSpace Real (Fin n)))
    (hCne : ∀ i, Set.Nonempty (C i)) (hCclosed : ∀ i, IsClosed (C i))
    (hCconv : ∀ i, Convex Real (C i)) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let S : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin m → Set (EuclideanSpace Real (Fin (1 + n))) :=
      fun i => (ConvexCone.hull Real (S i) : Set (EuclideanSpace Real (Fin (1 + n))))
    ∀ v, first v = 0 →
      (v ∈ ∑ i, closure (K i) ↔ tail v ∈ ∑ i, Set.recessionCone (C i)) := by
  classical
  intro coords first tail S K v hv0
  have hfirst_nonneg :
      ∀ i, ∀ v, v ∈ closure (K i) → 0 ≤ first v := by
    intro i v hv
    simpa [coords, first, tail, S, K] using
      (first_nonneg_of_mem_closure_lifted_cone (n := n) (C := C i) (hCne i) (hCclosed i)
        (hCconv i) v hv)
  constructor
  · intro hvsum
    rcases
        (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
            (f := fun i => closure (K i)) (a := v)).1 hvsum with ⟨z, hzmem, hsum⟩
    have hzmem' : ∀ i, z i ∈ closure (K i) := by
      intro i
      exact hzmem (i := i) (by simp)
    have hfirst_sum :
        first (∑ i, z i) = ∑ i, first (z i) := by
      simp [first, coords]
    have hsum0 : ∑ i, first (z i) = 0 := by
      have hsum' : first (∑ i, z i) = first v := by
        simpa using congrArg first hsum
      calc
        ∑ i, first (z i) = first (∑ i, z i) := by simp [hfirst_sum]
        _ = first v := hsum'
        _ = 0 := hv0
    have hfirst0 : ∀ i, first (z i) = 0 := by
      have hnonneg :
          ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ first (z i) := by
        intro i hi
        exact hfirst_nonneg i (z i) (hzmem' i)
      have hzero :=
        (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum0
      intro i
      exact hzero i (by simp)
    have htail_rec : ∀ i, tail (z i) ∈ Set.recessionCone (C i) := by
      intro i
      simpa [coords, first, tail, S, K, hfirst0 i] using
        (tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n) (C := C i)
          (hCclosed i) (hCconv i) (z i) (hzmem' i) (hfirst0 i))
    have htail_sum :
        tail (∑ i, z i) = ∑ i, tail (z i) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext j
      simp [tail, coords]
    have htail_sum' : ∑ i, tail (z i) = tail v := by
      have hsum' : tail (∑ i, z i) = tail v := by
        simpa [tail, coords] using congrArg tail hsum
      exact htail_sum.symm.trans hsum'
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => Set.recessionCone (C i)) (a := tail v)).2 ?_
    refine ⟨fun i => tail (z i), ?_, ?_⟩
    · intro i hi
      exact htail_rec i
    · simp [htail_sum']
  · intro hvsum
    rcases
        (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
            (f := fun i => Set.recessionCone (C i)) (a := tail v)).1 hvsum with
      ⟨x, hxmem, hxsum⟩
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
    let z : Fin m → EuclideanSpace Real (Fin (1 + n)) :=
      fun i => append y0 (x i)
    have hfirst_tail_z :
        ∀ i, first (z i) = 0 ∧ tail (z i) = x i := by
      intro i
      have h := first_tail_append (n := n) (y := y0) (z := x i)
      simpa [append, z, coords, first, tail, y0] using h
    have hfirst_z : ∀ i, first (z i) = 0 := fun i => (hfirst_tail_z i).1
    have htail_z : ∀ i, tail (z i) = x i := fun i => (hfirst_tail_z i).2
    have hzmem :
        ∀ i, z i ∈ closure (K i) := by
      intro i
      have hxrec : x i ∈ Set.recessionCone (C i) := by
        exact hxmem (i := i) (by simp)
      have hclosure :
          closure (K i) =
            K i ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} := by
        simpa [coords, first, tail, S, K] using
          (closure_cone_eq_union_recession (n := n) (C := C i) (hCne i) (hCclosed i)
            (hCconv i))
      have hmem :
          z i ∈ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} := by
        refine ⟨hfirst_z i, ?_⟩
        simpa [htail_z i] using hxrec
      have :
          z i ∈ K i ∪ {v | first v = 0 ∧ tail v ∈ Set.recessionCone (C i)} :=
        Or.inr hmem
      simpa [hclosure] using this
    have hfirst_sum :
        first (∑ i, z i) = ∑ i, first (z i) := by
      simp [first, coords]
    have htail_sum :
        tail (∑ i, z i) = ∑ i, tail (z i) := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext j
      simp [tail, coords]
    have hfirst_eq : first (∑ i, z i) = first v := by
      calc
        first (∑ i, z i) = ∑ i, first (z i) := hfirst_sum
        _ = 0 := by simp [hfirst_z]
        _ = first v := by simp [hv0]
    have htail_eq : tail (∑ i, z i) = tail v := by
      calc
        tail (∑ i, z i) = ∑ i, tail (z i) := htail_sum
        _ = ∑ i, x i := by simp [htail_z]
        _ = tail v := by simp [hxsum]
    have hEq :
        ∀ u v, first u = first v → tail u = tail v → u = v := by
      simpa [coords, first, tail] using (eq_of_first_tail_eq (n := n))
    have hsum_z : ∑ i, z i = v := hEq _ _ hfirst_eq htail_eq
    refine
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
          (f := fun i => closure (K i)) (a := v)).2 ?_
    refine ⟨z, ?_, hsum_z⟩
    intro i hi
    exact hzmem (i := i)

end Section09
end Chap02
