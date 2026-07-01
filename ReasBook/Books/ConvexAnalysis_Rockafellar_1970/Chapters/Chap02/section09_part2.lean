/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part1

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- The lifted linear map preserves first coordinate and applies `A` to the tail. -/
lemma lifted_linearMap_first_tail {n m : Nat}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    let coords₁ : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first₁ : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords₁ v 0
    let tail₁ : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords₁ v (Fin.natAdd 1 i))
    let coords₂ : EuclideanSpace Real (Fin (1 + m)) → (Fin (1 + m) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))
    let first₂ : EuclideanSpace Real (Fin (1 + m)) → Real := fun v => coords₂ v 0
    let tail₂ : EuclideanSpace Real (Fin (1 + m)) → EuclideanSpace Real (Fin m) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
          (fun i => coords₂ v (Fin.natAdd 1 i))
    let B : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin (1 + m)) :=
      let lift :
          (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n)) →ₗ[Real]
            (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin m)) :=
        (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin 1))
              (M₂ := EuclideanSpace Real (Fin n))).prod
          (A.comp (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
            (M₂ := EuclideanSpace Real (Fin n))))
      (appendAffineEquiv 1 m).linear.toLinearMap.comp
        (lift.comp (appendAffineEquiv 1 n).symm.linear.toLinearMap)
    ∀ v, first₂ (B v) = first₁ v ∧ tail₂ (B v) = A (tail₁ v) := by
  classical
  intro coords₁ first₁ tail₁ coords₂ first₂ tail₂ B v
  let e1 : (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n)) ≃ₗ[Real]
      EuclideanSpace Real (Fin (1 + n)) := (appendAffineEquiv 1 n).linear
  let e2 : (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin m)) ≃ₗ[Real]
      EuclideanSpace Real (Fin (1 + m)) := (appendAffineEquiv 1 m).linear
  let yz := e1.symm v
  let y : EuclideanSpace Real (Fin 1) := yz.1
  let z : EuclideanSpace Real (Fin n) := yz.2
  have hfun1 : ∀ x, appendAffineEquiv 1 n x = e1 x := by
    intro x
    simpa [e1] using
      congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv 1 n)
  have hfun2 : ∀ x, appendAffineEquiv 1 m x = e2 x := by
    intro x
    simpa [e2] using
      congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv 1 m)
  have hv : appendAffineEquiv 1 n (y, z) = v := by
    have : e1 (y, z) = v := by
      simp [y, z, yz]
    simpa [hfun1 (y, z)] using this
  let append₁ :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
        EuclideanSpace Real (Fin (1 + n)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  let append₂ :
      EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin m) →
        EuclideanSpace Real (Fin (1 + m)) :=
    fun y z =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))).symm
        ((Fin.appendIsometry 1 m)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) z))
  have hv_append : append₁ y z = v := by
    simpa [append₁, appendAffineEquiv_apply] using hv
  have hB' : B v = e2 (y, A z) := by
    simp [B, e1, e2, y, z, yz]
  have hB : B v = appendAffineEquiv 1 m (y, A z) := by
    simpa [hfun2 (y, A z)] using hB'
  have hB_append : append₂ y (A z) = B v := by
    simpa [append₂, appendAffineEquiv_apply] using hB.symm
  have hfirst_tail_v :
      first₁ v = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 ∧ tail₁ v = z := by
    have h :=
      (first_tail_append (n := n) (y := y) (z := z))
    simpa [coords₁, first₁, tail₁, append₁, hv_append] using h
  have hfirst_tail_B :
      first₂ (B v) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 ∧
        tail₂ (B v) = A z := by
    have h :=
      (first_tail_append (n := m) (y := y) (z := A z))
    simpa [coords₂, first₂, tail₂, append₂, hB_append] using h
  refine ⟨?_, ?_⟩
  · simpa [hfirst_tail_v.1] using hfirst_tail_B.1
  · simpa [hfirst_tail_v.2] using hfirst_tail_B.2

/-- The lifted map sends the cone over `C` to the cone over `A '' C`. -/
lemma image_cone_eq_cone_image {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCconv : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    let coords₁ : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first₁ : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords₁ v 0
    let tail₁ : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords₁ v (Fin.natAdd 1 i))
    let coords₂ : EuclideanSpace Real (Fin (1 + m)) → (Fin (1 + m) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))
    let first₂ : EuclideanSpace Real (Fin (1 + m)) → Real := fun v => coords₂ v 0
    let tail₂ : EuclideanSpace Real (Fin (1 + m)) → EuclideanSpace Real (Fin m) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
          (fun i => coords₂ v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first₁ v = 1 ∧ tail₁ v ∈ C}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    let S' : Set (EuclideanSpace Real (Fin (1 + m))) :=
      {v | first₂ v = 1 ∧ tail₂ v ∈ A '' C}
    let K' : Set (EuclideanSpace Real (Fin (1 + m))) :=
      (ConvexCone.hull Real S' : Set (EuclideanSpace Real (Fin (1 + m))))
    let B : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin (1 + m)) :=
      let lift :
          (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n)) →ₗ[Real]
            (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin m)) :=
        (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin 1))
              (M₂ := EuclideanSpace Real (Fin n))).prod
          (A.comp (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
            (M₂ := EuclideanSpace Real (Fin n))))
      (appendAffineEquiv 1 m).linear.toLinearMap.comp
        (lift.comp (appendAffineEquiv 1 n).symm.linear.toLinearMap)
    B '' K = K' := by
  classical
  intro coords₁ first₁ tail₁ coords₂ first₂ tail₂ S K S' K' B
  have hfirst_tail :
      ∀ v, first₂ (B v) = first₁ v ∧ tail₂ (B v) = A (tail₁ v) := by
    simpa [coords₁, first₁, tail₁, coords₂, first₂, tail₂, B] using
      (lifted_linearMap_first_tail (A := A))
  have hmemK :
      ∀ v, v ∈ K ↔ 0 < first₁ v ∧ tail₁ v ∈ (first₁ v) • C := by
    simpa [coords₁, first₁, tail₁, S, K] using
      (mem_K_iff_first_tail (n := n) (C := C) hCconv)
  have hCconv' : Convex Real (A '' C) := hCconv.linear_image A
  have hmemK' :
      ∀ v, v ∈ K' ↔ 0 < first₂ v ∧ tail₂ v ∈ (first₂ v) • (A '' C) := by
    simpa [coords₂, first₂, tail₂, S', K'] using
      (mem_K_iff_first_tail (n := m) (C := A '' C) hCconv')
  apply Set.Subset.antisymm
  · intro w hw
    rcases hw with ⟨v, hvK, rfl⟩
    rcases (hmemK v).1 hvK with ⟨hpos, htail⟩
    rcases htail with ⟨x, hxC, htail_eq⟩
    have hfirst : 0 < first₂ (B v) := by simpa [(hfirst_tail v).1] using hpos
    have htail' :
        tail₂ (B v) ∈ (first₂ (B v)) • (A '' C) := by
      have hAx : A x ∈ A '' C := ⟨x, hxC, rfl⟩
      have htail_eq' :
          tail₂ (B v) = (first₂ (B v)) • A x := by
        calc
          tail₂ (B v) = A (tail₁ v) := (hfirst_tail v).2
          _ = A ((first₁ v) • x) := by simp [htail_eq]
          _ = (first₁ v) • A x := by simp
          _ = (first₂ (B v)) • A x := by simp [(hfirst_tail v).1]
      exact ⟨A x, hAx, htail_eq'.symm⟩
    exact (hmemK' (B v)).2 ⟨hfirst, htail'⟩
  · intro w hw
    rcases (hmemK' w).1 hw with ⟨hpos, htail⟩
    rcases htail with ⟨y, hyC, htail_eq⟩
    rcases hyC with ⟨x, hxC, rfl⟩
    let append₁ :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    let y0 : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => first₂ w)
    let v : EuclideanSpace Real (Fin (1 + n)) := append₁ y0 ((first₂ w) • x)
    have hvK :
        v ∈ K := by
      have hfirst_tail_v :
          first₁ v = first₂ w ∧ tail₁ v = (first₂ w) • x := by
        have h :=
          (first_tail_append (n := n) (y := y0) (z := (first₂ w) • x))
        simpa [coords₁, first₁, tail₁, append₁, v, y0] using h
      have hfirst_pos : 0 < first₁ v := by simpa [hfirst_tail_v.1] using hpos
      have htail_mem : tail₁ v ∈ (first₁ v) • C := by
        refine ⟨x, hxC, ?_⟩
        simp [hfirst_tail_v.1, hfirst_tail_v.2]
      exact (hmemK v).2 ⟨hfirst_pos, htail_mem⟩
    have hfirst_tail_v :
        first₁ v = first₂ w ∧ tail₁ v = (first₂ w) • x := by
      have h :=
        (first_tail_append (n := n) (y := y0) (z := (first₂ w) • x))
      simpa [coords₁, first₁, tail₁, append₁, v, y0] using h
    have hBw : B v = w := by
      have hfirst_Bv :
          first₂ (B v) = first₂ w := by
        simpa [hfirst_tail_v.1] using (hfirst_tail v).1
      have htail_Bv :
          tail₂ (B v) = tail₂ w := by
        have htail_Bv' :
          tail₂ (B v) = (first₂ w) • A x := by
          calc
            tail₂ (B v) = A (tail₁ v) := (hfirst_tail v).2
            _ = A ((first₂ w) • x) := by simp [hfirst_tail_v.2]
            _ = (first₂ w) • A x := by simp
        simpa [htail_eq] using htail_Bv'
      have hEq :
          ∀ u v,
            first₂ u = first₂ v → tail₂ u = tail₂ v → u = v := by
        simpa [coords₂, first₂, tail₂] using (eq_of_first_tail_eq (n := m))
      exact (hEq _ _ hfirst_Bv htail_Bv)
    exact ⟨v, hvK, hBw⟩

/-- Kernel-lineality for the lifted cone over `closure C`. -/
lemma kernel_lineality_for_cone {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : Set.Nonempty C) (hCconv : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C) → A z = 0 →
        z ∈ Set.linealitySpace (closure C)) :
    let Cbar : Set (EuclideanSpace Real (Fin n)) := closure C
    let coords₁ : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first₁ : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords₁ v 0
    let tail₁ : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords₁ v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first₁ v = 1 ∧ tail₁ v ∈ Cbar}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    let B : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin (1 + m)) :=
      let lift :
          (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n)) →ₗ[Real]
            (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin m)) :=
        (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin 1))
              (M₂ := EuclideanSpace Real (Fin n))).prod
          (A.comp (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
            (M₂ := EuclideanSpace Real (Fin n))))
      (appendAffineEquiv 1 m).linear.toLinearMap.comp
        (lift.comp (appendAffineEquiv 1 n).symm.linear.toLinearMap)
    ∀ v, v ≠ 0 → v ∈ Set.recessionCone (closure K) → B v = 0 →
      v ∈ Set.linealitySpace (closure K) := by
  classical
  intro Cbar coords₁ first₁ tail₁ S K B v hv0 hvrec hB0
  let coords₂ : EuclideanSpace Real (Fin (1 + m)) → (Fin (1 + m) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))
  let first₂ : EuclideanSpace Real (Fin (1 + m)) → Real := fun v => coords₂ v 0
  let tail₂ : EuclideanSpace Real (Fin (1 + m)) → EuclideanSpace Real (Fin m) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
        (fun i => coords₂ v (Fin.natAdd 1 i))
  have hCbar_closed : IsClosed Cbar := by simp [Cbar]
  have hCbar_conv : Convex Real Cbar := by
    simpa [Cbar] using (convex_closure_of_convex n C hCconv)
  have hCbar_ne : Cbar.Nonempty := by simpa [Cbar] using hCne.closure
  have hfirst_tail :
      ∀ v, first₂ (B v) = first₁ v ∧ tail₂ (B v) = A (tail₁ v) := by
    simpa [coords₁, first₁, tail₁, coords₂, first₂, tail₂, B] using
      (lifted_linearMap_first_tail (A := A))
  have hfirst : first₁ v = 0 := by
    have h0 : first₂ (B v) = 0 := by
      simpa using congrArg first₂ hB0
    simpa [(hfirst_tail v).1] using h0
  have hA : A (tail₁ v) = 0 := by
    have h0 : tail₂ (B v) = 0 := by
      simpa using congrArg tail₂ hB0
    simpa [(hfirst_tail v).2] using h0
  have hclosureK :
      closure K =
        K ∪ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
    simpa [coords₁, first₁, tail₁, S, K, Cbar] using
      (closure_cone_eq_union_recession (n := n) (C := Cbar) hCbar_ne hCbar_closed hCbar_conv)
  have hrec0 : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone Cbar := by
    intro x hx t ht
    simpa using hx
  have hzero_mem : (0 : EuclideanSpace Real (Fin (1 + n))) ∈ closure K := by
    have hmem :
        (0 : EuclideanSpace Real (Fin (1 + n))) ∈
          {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
      have hfirst0 : first₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
        change coords₁ 0 0 = 0
        have hzero : coords₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
          simp [coords₁]
        simp [hzero]
      have htail0 : tail₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
        ext i
        change coords₁ 0 (Fin.natAdd 1 i) = 0
        have hzero : coords₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
          simp [coords₁]
        simp [hzero]
      refine ⟨hfirst0, ?_⟩
      simpa [htail0] using hrec0
    have : (0 : EuclideanSpace Real (Fin (1 + n))) ∈
        K ∪ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
      exact Or.inr hmem
    simpa [hclosureK] using this
  have hv_closure : v ∈ closure K := by
    have hv' := hvrec (x := (0 : EuclideanSpace Real (Fin (1 + n)))) hzero_mem
      (t := (1 : ℝ)) (by norm_num)
    simpa using hv'
  have htail_rec : tail₁ v ∈ Set.recessionCone Cbar := by
    have h :=
      tail_mem_recessionCone_of_mem_closure_K_first_zero (n := n)
        (C := Cbar) hCbar_closed hCbar_conv
    have h' :
        ∀ w, w ∈ closure K → first₁ w = 0 → tail₁ w ∈ Set.recessionCone Cbar := by
      simpa [coords₁, first₁, tail₁, S, K, Cbar] using h
    exact h' v hv_closure hfirst
  have hEq :
      ∀ u v,
        first₁ u = first₁ v → tail₁ u = tail₁ v → u = v := by
    simpa [coords₁, first₁, tail₁] using (eq_of_first_tail_eq (n := n))
  have htail_ne : tail₁ v ≠ 0 := by
    intro htail0
    have hfirst0 : first₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
      change coords₁ 0 0 = 0
      have hzero : coords₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
        simp [coords₁]
      simp [hzero]
    have htail0' : tail₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
      ext i
      change coords₁ 0 (Fin.natAdd 1 i) = 0
      have hzero : coords₁ (0 : EuclideanSpace Real (Fin (1 + n))) = 0 := by
        simp [coords₁]
      simp [hzero]
    have h0 : first₁ v = first₁ (0 : EuclideanSpace Real (Fin (1 + n))) := by
      simp [hfirst0, hfirst]
    have h0' : tail₁ v = tail₁ (0 : EuclideanSpace Real (Fin (1 + n))) := by
      simp [htail0', htail0]
    have hv0' := hEq v 0 h0 h0'
    exact hv0 (by simpa using hv0')
  have htail_lineal : tail₁ v ∈ Set.linealitySpace Cbar :=
    hlineal (tail₁ v) htail_ne htail_rec hA
  have htail_lineal' :
      tail₁ v ∈ (-Set.recessionCone Cbar) ∩ Set.recessionCone Cbar := by
    simpa [Set.linealitySpace] using htail_lineal
  have htail_rec_neg : -tail₁ v ∈ Set.recessionCone Cbar := by
    simpa using htail_lineal'.1
  have hmemK :
      ∀ v, v ∈ K ↔ 0 < first₁ v ∧ tail₁ v ∈ (first₁ v) • Cbar := by
    simpa [coords₁, first₁, tail₁, S, K, Cbar] using
      (mem_K_iff_first_tail (n := n) (C := Cbar) hCbar_conv)
  let tailMap : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
        (M₂ := EuclideanSpace Real (Fin n))).comp
      (appendAffineEquiv 1 n).symm.linear.toLinearMap
  have htailMap : ∀ w, tailMap w = tail₁ w := by
    simpa [coords₁, tail₁, tailMap] using (tail_linearMap_apply (n := n))
  have hneg_rec : -v ∈ Set.recessionCone (closure K) := by
    intro x hx t ht
    have hx' :
        x ∈ K ∪ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
      simpa [hclosureK] using hx
    rcases hx' with hxK | hxrec
    · rcases (hmemK x).1 hxK with ⟨hpos, hx_tail⟩
      rcases hx_tail with ⟨c, hcC, htail_eq⟩
      have hne : (first₁ x : ℝ) ≠ 0 := ne_of_gt hpos
      have hnonneg : 0 ≤ t / first₁ x := by
        exact div_nonneg ht (le_of_lt hpos)
      have hshift :
          c + (t / first₁ x) • (-tail₁ v) ∈ Cbar := by
        have hmem := htail_rec_neg (x := c) hcC (t := t / first₁ x) hnonneg
        simpa using hmem
      have htail_add :
          tail₁ (x + t • (-v)) = tail₁ x + t • (-tail₁ v) := by
        have h' :
            tailMap (x + t • (-v)) = tailMap x + t • tailMap (-v) := by
          simp [tailMap]
        have h'' :
            tail₁ (x + t • (-v)) = tail₁ x + t • tail₁ (-v) := by
          simpa [htailMap] using h'
        have hneg : tail₁ (-v) = -tail₁ v := by
          have hneg' : tailMap (-v) = -tailMap v := by simp [tailMap]
          simpa [htailMap] using hneg'
        simpa [hneg] using h''
      have hmul : (first₁ x : ℝ) * (t / first₁ x) = t := by
        field_simp [hne]
      have htail_mem :
          tail₁ (x + t • (-v)) ∈ (first₁ x) • Cbar := by
        refine ⟨c + (t / first₁ x) • (-tail₁ v), hshift, ?_⟩
        symm
        calc
          tail₁ (x + t • (-v))
              = tail₁ x + t • (-tail₁ v) := htail_add
          _ = (first₁ x) • c + t • (-tail₁ v) := by simp [htail_eq]
          _ = (first₁ x) • (c + (t / first₁ x) • (-tail₁ v)) := by
                simp [smul_add, smul_smul, hmul, add_comm]
      have hfirst_add : first₁ (x + t • (-v)) = first₁ x := by
        have hfirst_smul : first₁ (-(t • v)) = t * first₁ (-v) := by
          simp [coords₁, first₁]
        have hfirst_neg : first₁ (-v) = -first₁ v := by
          simp [coords₁, first₁]
        calc
          first₁ (x + t • (-v)) = first₁ x + first₁ (t • (-v)) := by
            simp [coords₁, first₁]
          _ = first₁ x + t * first₁ (-v) := by
            simp [hfirst_smul]
          _ = first₁ x := by
            simp [hfirst, hfirst_neg]
      have hpos' : 0 < first₁ (x + t • (-v)) := by
        rw [hfirst_add]
        exact hpos
      have htail_mem' :
          tail₁ (x + t • (-v)) ∈ (first₁ (x + t • (-v))) • Cbar := by
        rw [hfirst_add]
        exact htail_mem
      have hxK' : x + t • (-v) ∈ K := (hmemK _).2 ⟨hpos', htail_mem'⟩
      exact subset_closure hxK'
    · rcases hxrec with ⟨hx0, hxrec⟩
      have htail_sum :
          tail₁ (x + t • (-v)) ∈ Set.recessionCone Cbar := by
        have htail_add :
            tail₁ (x + t • (-v)) = tail₁ x + t • (-tail₁ v) := by
          have h' :
              tailMap (x + t • (-v)) = tailMap x + t • tailMap (-v) := by
            simp [tailMap]
          have h'' :
              tail₁ (x + t • (-v)) = tail₁ x + t • tail₁ (-v) := by
            simpa [htailMap] using h'
          have hneg : tail₁ (-v) = -tail₁ v := by
            have hneg' : tailMap (-v) = -tailMap v := by simp [tailMap]
            simpa [htailMap] using hneg'
          simpa [hneg] using h''
        by_cases ht0 : t = 0
        · subst ht0
          simpa [htail_add]
        · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
          have hsmul :
              t • (-tail₁ v) ∈ Set.recessionCone Cbar :=
            recessionCone_smul_pos (C := Cbar) htail_rec_neg htpos
          have hsum_mem :
              tail₁ x + t • (-tail₁ v) ∈ Set.recessionCone Cbar :=
            recessionCone_add_mem (C := Cbar) hCbar_conv hxrec hsmul
          simpa [htail_add] using hsum_mem
      have hfirst_add : first₁ (x + t • (-v)) = 0 := by
        have hfirst_smul : first₁ (-(t • v)) = t * first₁ (-v) := by
          simp [coords₁, first₁]
        have hfirst_neg : first₁ (-v) = -first₁ v := by
          simp [coords₁, first₁]
        calc
          first₁ (x + t • (-v)) = first₁ x + first₁ (t • (-v)) := by
            simp [coords₁, first₁]
          _ = first₁ x + t * first₁ (-v) := by
            simp [hfirst_smul]
          _ = 0 := by
            simp [hx0, hfirst, hfirst_neg]
      have hmem :
          x + t • (-v) ∈
            {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
        exact ⟨hfirst_add, htail_sum⟩
      have : x + t • (-v) ∈
          K ∪ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
        exact Or.inr hmem
      simpa [hclosureK] using this
  have hvneg : v ∈ -Set.recessionCone (closure K) := by
    simpa using hneg_rec
  exact ⟨hvneg, hvrec⟩

theorem linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
    {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : Set.Nonempty C) (hCconv : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
  (hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C) → A z = 0 →
        z ∈ Set.linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C ∧
      Set.recessionCone (A '' closure C) = A '' Set.recessionCone (closure C) ∧
      (IsClosed C →
        (∀ z, z ∈ Set.recessionCone C → A z = 0 → z = 0) →
        IsClosed (A '' C)) := by
  classical
  have hcl : closure (A '' C) = A '' closure C :=
    closure_image_eq_image_closure_of_kernel_lineality (hCne := hCne) (hCconv := hCconv) A
      hlineal
  have hrec :
      Set.recessionCone (A '' closure C) = A '' Set.recessionCone (closure C) := by
    classical
    let Cbar : Set (EuclideanSpace Real (Fin n)) := closure C
    have hCbar_ne : Cbar.Nonempty := by
      simpa [Cbar] using hCne.closure
    have hCbar_closed : IsClosed Cbar := by simp [Cbar]
    have hCbar_conv : Convex Real Cbar := by
      simpa [Cbar] using (convex_closure_of_convex n C hCconv)
    have hAconv : Convex Real (A '' Cbar) := hCbar_conv.linear_image A
    have hlineal' :
        ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure Cbar) → A z = 0 →
          z ∈ Set.linealitySpace (closure Cbar) := by
      simpa [Cbar] using hlineal
    have hAclosed : IsClosed (A '' Cbar) := by
      have hcl' :
          closure (A '' Cbar) = A '' Cbar := by
        simpa [Cbar] using
          (closure_image_eq_image_closure_of_kernel_lineality
            (hCne := hCbar_ne) (hCconv := hCbar_conv) A hlineal')
      exact (closure_eq_iff_isClosed).1 hcl'
    let coords₁ : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first₁ : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords₁ v 0
    let tail₁ : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords₁ v (Fin.natAdd 1 i))
    let coords₂ : EuclideanSpace Real (Fin (1 + m)) → (Fin (1 + m) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))
    let first₂ : EuclideanSpace Real (Fin (1 + m)) → Real := fun v => coords₂ v 0
    let tail₂ : EuclideanSpace Real (Fin (1 + m)) → EuclideanSpace Real (Fin m) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm
          (fun i => coords₂ v (Fin.natAdd 1 i))
    let S : Set (EuclideanSpace Real (Fin (1 + n))) := {v | first₁ v = 1 ∧ tail₁ v ∈ Cbar}
    let K : Set (EuclideanSpace Real (Fin (1 + n))) :=
      (ConvexCone.hull Real S : Set (EuclideanSpace Real (Fin (1 + n))))
    let S' : Set (EuclideanSpace Real (Fin (1 + m))) :=
      {v | first₂ v = 1 ∧ tail₂ v ∈ A '' Cbar}
    let K' : Set (EuclideanSpace Real (Fin (1 + m))) :=
      (ConvexCone.hull Real S' : Set (EuclideanSpace Real (Fin (1 + m))))
    let B : EuclideanSpace Real (Fin (1 + n)) →ₗ[Real] EuclideanSpace Real (Fin (1 + m)) :=
      let lift :
          (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin n)) →ₗ[Real]
            (EuclideanSpace Real (Fin 1) × EuclideanSpace Real (Fin m)) :=
        (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin 1))
              (M₂ := EuclideanSpace Real (Fin n))).prod
          (A.comp (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin 1))
            (M₂ := EuclideanSpace Real (Fin n))))
      (appendAffineEquiv 1 m).linear.toLinearMap.comp
        (lift.comp (appendAffineEquiv 1 n).symm.linear.toLinearMap)
    have hBK : B '' K = K' := by
      simpa [coords₁, first₁, tail₁, coords₂, first₂, tail₂, S, K, S', K', B, Cbar] using
        (image_cone_eq_cone_image (C := Cbar) hCbar_conv A)
    have hlinealK :
        ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure K) → B z = 0 →
          z ∈ Set.linealitySpace (closure K) := by
      simpa [Cbar, coords₁, first₁, tail₁, S, K, coords₂, first₂, tail₂, B] using
        (kernel_lineality_for_cone (C := C) hCne hCconv A hlineal)
    have hKconv : Convex Real K := by
      simpa [K] using (ConvexCone.convex (C := ConvexCone.hull Real S))
    have hKne : Set.Nonempty K := by
      rcases hCbar_ne with ⟨x0, hx0⟩
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (1 : ℝ))
      let append₁ :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
            EuclideanSpace Real (Fin (1 + n)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
            ((Fin.appendIsometry 1 n)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
      let v : EuclideanSpace Real (Fin (1 + n)) := append₁ y0 x0
      have hvS : v ∈ S := by
        have h :=
          (first_tail_append (n := n) (y := y0) (z := x0))
        have hfirst_tail : first₁ v = 1 ∧ tail₁ v = x0 := by
          simpa [coords₁, first₁, tail₁, append₁, v, y0] using h
        refine ⟨by simp [hfirst_tail.1], ?_⟩
        rw [hfirst_tail.2]
        exact hx0
      have hvK : v ∈ K := by
        exact (ConvexCone.subset_hull (s := S) hvS)
      exact ⟨v, hvK⟩
    have hclK :
        closure (B '' K) = B '' closure K := by
      exact
        (closure_image_eq_image_closure_of_kernel_lineality (C := K) (hCne := hKne)
            (hCconv := hKconv) B hlinealK)
    have hclK' : closure K' = B '' closure K := by
      simpa [hBK] using hclK
    have hclosureK :
        closure K =
          K ∪ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
      simpa [coords₁, first₁, tail₁, S, K, Cbar] using
        (closure_cone_eq_union_recession (n := n) (C := Cbar) hCbar_ne hCbar_closed hCbar_conv)
    have hclosureK' :
        closure K' =
          K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} := by
      have hAne : (A '' Cbar).Nonempty := hCbar_ne.image A
      simpa [coords₂, first₂, tail₂, S', K', Cbar] using
        (closure_cone_eq_union_recession (n := m) (C := A '' Cbar) hAne hAclosed hAconv)
    have hfirst_tail :
        ∀ v, first₂ (B v) = first₁ v ∧ tail₂ (B v) = A (tail₁ v) := by
      simpa [coords₁, first₁, tail₁, coords₂, first₂, tail₂, B] using
        (lifted_linearMap_first_tail (A := A))
    have hBboundary :
        B '' {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} =
          {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        rcases hv with ⟨hv0, hvrec⟩
        have hfirst : first₂ (B v) = 0 := by simpa [hv0] using (hfirst_tail v).1
        have htail : tail₂ (B v) ∈ A '' Set.recessionCone Cbar := by
          refine ⟨tail₁ v, hvrec, ?_⟩
          simpa using (hfirst_tail v).2.symm
        exact ⟨hfirst, htail⟩
      · rintro ⟨hfirst, htail⟩
        rcases htail with ⟨z, hzrec, hztail⟩
        let y0 : EuclideanSpace Real (Fin 1) :=
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))
        let append₁ :
            EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
              EuclideanSpace Real (Fin (1 + n)) :=
          fun y z =>
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
              ((Fin.appendIsometry 1 n)
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
                 (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
        let v : EuclideanSpace Real (Fin (1 + n)) := append₁ y0 z
        have hfirst_tail_v : first₁ v = 0 ∧ tail₁ v = z := by
          have h :=
            (first_tail_append (n := n) (y := y0) (z := z))
          simpa [coords₁, first₁, tail₁, append₁, v, y0] using h
        have hv :
            v ∈ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
          exact ⟨hfirst_tail_v.1, by simpa [hfirst_tail_v.2] using hzrec⟩
        have hEq :
            ∀ u v,
              first₂ u = first₂ v → tail₂ u = tail₂ v → u = v := by
          simpa [coords₂, first₂, tail₂] using (eq_of_first_tail_eq (n := m))
        have hBw : B v = w := by
          have hfirst_Bv : first₂ (B v) = first₂ w := by
            simpa [hfirst_tail_v.1, hfirst] using (hfirst_tail v).1
          have htail_Bv : tail₂ (B v) = tail₂ w := by
            have htail_Bv' : tail₂ (B v) = A z := by
              simpa [hfirst_tail_v.2] using (hfirst_tail v).2
            exact htail_Bv'.trans hztail
          exact hEq _ _ hfirst_Bv htail_Bv
        exact ⟨v, hv, hBw⟩
    have hBclosure :
        B '' closure K =
          K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
      calc
        B '' closure K =
            B '' (K ∪ {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar}) := by
              simp [hclosureK]
        _ =
            B '' K ∪ B '' {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
              simp [Set.image_union]
        _ = K' ∪ B '' {v | first₁ v = 0 ∧ tail₁ v ∈ Set.recessionCone Cbar} := by
              simp [hBK]
        _ = K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
              simp [hBboundary]
    have hUnionEq :
        K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} =
          K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
      calc
        K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} =
            closure K' := by
              symm
              exact hclosureK'
        _ = B '' closure K := hclK'
        _ = K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := hBclosure
    have hUeq :
        {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} =
          {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
      ext w
      constructor
      · intro hw
        have hw' : w ∈ K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
          have : w ∈
              K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} := by
            exact Or.inr hw
          simpa [hUnionEq] using this
        rcases hw with ⟨hfirst0, htail⟩
        rcases hw' with hwK | hwU
        · have hmemK' :
              ∀ v, v ∈ K' → 0 < first₂ v ∧ tail₂ v ∈ (first₂ v) • (A '' Cbar) := by
            have hAconv' : Convex Real (A '' Cbar) := hCbar_conv.linear_image A
            intro v hv
            exact
              (mem_K_iff_first_tail (n := m) (C := A '' Cbar) hAconv' v).1 hv
          have hpos' : (0 : ℝ) < 0 := by
            simpa [hfirst0] using (hmemK' w hwK).1
          exact (lt_irrefl _ hpos').elim
        · exact hwU
      · intro hw
        have hw' :
            w ∈ K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} := by
          have : w ∈
              K' ∪ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
            exact Or.inr hw
          simpa [hUnionEq] using this
        rcases hw with ⟨hfirst0, htail⟩
        rcases hw' with hwK | hwU
        · have hmemK' :
              ∀ v, v ∈ K' → 0 < first₂ v ∧ tail₂ v ∈ (first₂ v) • (A '' Cbar) := by
            have hAconv' : Convex Real (A '' Cbar) := hCbar_conv.linear_image A
            intro v hv
            exact
              (mem_K_iff_first_tail (n := m) (C := A '' Cbar) hAconv' v).1 hv
          have hpos' : (0 : ℝ) < 0 := by
            simpa [hfirst0] using (hmemK' w hwK).1
          exact (lt_irrefl _ hpos').elim
        · exact hwU
    ext y
    constructor
    · intro hy
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))
      let append₂ :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin m) →
            EuclideanSpace Real (Fin (1 + m)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))).symm
            ((Fin.appendIsometry 1 m)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) z))
      let w : EuclideanSpace Real (Fin (1 + m)) := append₂ y0 y
      have hfirst_tail_w : first₂ w = 0 ∧ tail₂ w = y := by
        have h :=
          (first_tail_append (n := m) (y := y0) (z := y))
        simpa [coords₂, first₂, tail₂, append₂, w, y0] using h
      have hwU :
          w ∈ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} := by
        exact ⟨hfirst_tail_w.1, by simpa [hfirst_tail_w.2] using hy⟩
      have hwU' :
          w ∈ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
        simpa [hUeq] using hwU
      simpa [hfirst_tail_w.2] using hwU'.2
    · intro hy
      let y0 : EuclideanSpace Real (Fin 1) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => (0 : ℝ))
      let append₂ :
          EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin m) →
            EuclideanSpace Real (Fin (1 + m)) :=
        fun y z =>
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + m))).symm
            ((Fin.appendIsometry 1 m)
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
               (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) z))
      let w : EuclideanSpace Real (Fin (1 + m)) := append₂ y0 y
      have hfirst_tail_w : first₂ w = 0 ∧ tail₂ w = y := by
        have h :=
          (first_tail_append (n := m) (y := y0) (z := y))
        simpa [coords₂, first₂, tail₂, append₂, w, y0] using h
      have hwU :
          w ∈ {v | first₂ v = 0 ∧ tail₂ v ∈ A '' Set.recessionCone Cbar} := by
        exact ⟨hfirst_tail_w.1, by simpa [hfirst_tail_w.2] using hy⟩
      have hwU' :
          w ∈ {v | first₂ v = 0 ∧ tail₂ v ∈ Set.recessionCone (A '' Cbar)} := by
        simpa [hUeq] using hwU
      simpa [hfirst_tail_w.2] using hwU'.2
  refine ⟨hcl, hrec, ?_⟩
  intro hCclosed hker
  have hclC : closure C = C := hCclosed.closure_eq
  have hclA : closure (A '' C) = A '' C := by
    simpa [hclC] using hcl
  exact (closure_eq_iff_isClosed).1 hclA

end Section09
end Chap02
