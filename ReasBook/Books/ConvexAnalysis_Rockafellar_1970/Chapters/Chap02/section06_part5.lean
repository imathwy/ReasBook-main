/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part4

noncomputable section
open scoped Pointwise

section Chap02
section Section06

/-- The Minkowski sum is the image of the product under addition. -/
lemma image_add_prod_eq_add {E : Type*} [Add E] (C1 C2 : Set E) :
    (fun xy : E × E => xy.1 + xy.2) '' Set.prod C1 C2 = C1 + C2 := by
  ext x; constructor
  · rintro ⟨⟨x1, x2⟩, hx, rfl⟩
    rcases hx with ⟨hx1, hx2⟩
    change x1 + x2 ∈ Set.image2 (· + ·) C1 C2
    exact ⟨x1, hx1, x2, hx2, rfl⟩
  · intro hx
    change x ∈ Set.image2 (· + ·) C1 C2 at hx
    rcases hx with ⟨x1, hx1, x2, hx2, rfl⟩
    exact ⟨(x1, x2), ⟨hx1, hx2⟩, rfl⟩

/-- The append affine equivalence fixes the origin, hence equals its linear part. -/
lemma appendAffineEquiv_eq_linear_toAffineEquiv (m p : Nat) :
    (appendAffineEquiv m p :
        (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) →ᵃ[Real]
          EuclideanSpace Real (Fin (m + p))) =
      (appendAffineEquiv m p).linear.toAffineEquiv := by
  apply (AffineMap.ext_linear_iff).2
  refine ⟨rfl, ?_⟩
  refine ⟨0, ?_⟩
  have happend : (Fin.appendIsometry m p) (0, 0) = (0 : Fin (m + p) → ℝ) := by
    funext i
    refine Fin.addCases (m := m) (n := p) ?_ ?_ i <;> intro i
    · simp [Fin.appendIsometry, Fin.appendEquiv, Fin.append_left]
    · simp [Fin.appendIsometry, Fin.appendEquiv, Fin.append_right]
  have h0 : appendAffineEquiv m p (0, 0) = 0 := by
    simp [appendAffineEquiv_apply, happend]
  simpa using h0

/-- The addition linear map sends the direct-sum set to the Minkowski sum. -/
lemma addLinearMap_image_directSum_eq_add (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) :
    let A : EuclideanSpace Real (Fin (n + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
      ((LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin n))) +
        (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin n)))).comp
        (appendAffineEquiv n n).symm.linear.toLinearMap
    A '' directSumSetEuclidean n n C1 C2 = C1 + C2 := by
  classical
  intro A
  let e : (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin n)) ≃ₗ[Real]
      EuclideanSpace Real (Fin (n + n)) := (appendAffineEquiv n n).linear
  let B : (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin n)) →ₗ[Real]
      EuclideanSpace Real (Fin n) :=
    (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
          (M₂ := EuclideanSpace Real (Fin n))) +
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
          (M₂ := EuclideanSpace Real (Fin n)))
  have hfun : ∀ x, appendAffineEquiv n n x = e x := by
    intro x
    simpa [e] using
      congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv n n)
  have hdirect :
      directSumSetEuclidean n n C1 C2 = e '' Set.prod C1 C2 := by
    have hdirect' :=
      directSumSetEuclidean_eq_image_appendAffineEquiv (m := n) (p := n) (C1 := C1) (C2 := C2)
    refine hdirect'.trans ?_
    refine Set.image_congr' ?_
    intro x
    exact hfun x
  have himage : A '' directSumSetEuclidean n n C1 C2 = B '' Set.prod C1 C2 := by
    have hAe : ∀ x, A (e x) = B x := by
      intro x
      simp [A, B, e, LinearMap.comp_apply, AffineEquiv.linear_symm]
    calc
      A '' directSumSetEuclidean n n C1 C2 =
          A '' (e '' Set.prod C1 C2) := by simp [hdirect]
      _ = (fun x => A (e x)) '' Set.prod C1 C2 := by
          simp [Set.image_image]
      _ = B '' Set.prod C1 C2 := by
          refine Set.image_congr' ?_
          intro x
          exact hAe x
  have hB : B '' Set.prod C1 C2 = C1 + C2 := by
    simpa [B, LinearMap.add_apply] using (image_add_prod_eq_add (C1 := C1) (C2 := C2))
  exact himage.trans hB

/-- Convexity of the direct-sum set. -/
lemma convex_directSumSetEuclidean (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) :
    Convex Real (directSumSetEuclidean n n C1 C2) := by
  have hprod : Convex Real (Set.prod C1 C2) := by
    simpa using (Convex.prod hC1 hC2)
  simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using
    (Convex.affine_image (f := (appendAffineEquiv n n).toAffineMap) hprod)

/-- Convexity of a direct-sum set in general dimensions. -/
lemma convex_directSumSetEuclidean_general (n m : Nat)
    (C1 : Set (EuclideanSpace Real (Fin n))) (C2 : Set (EuclideanSpace Real (Fin m)))
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    Convex Real (directSumSetEuclidean n m C1 C2) := by
  have hprod : Convex Real (Set.prod C1 C2) := by
    simpa using (Convex.prod hC1 hC2)
  simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using
    (Convex.affine_image (f := (appendAffineEquiv n m).toAffineMap) hprod)

/-- Corollary 6.6.2. For any convex sets `C1` and `C2` in `R^n`,
`ri (C1 + C2) = ri C1 + ri C2`, and `cl (C1 + C2) ⊇ cl C1 + cl C2`. -/
theorem euclideanRelativeInterior_add_eq_and_closure_add_superset (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) :
    euclideanRelativeInterior n (C1 + C2) =
        euclideanRelativeInterior n C1 + euclideanRelativeInterior n C2 ∧
      closure C1 + closure C2 ⊆ closure (C1 + C2) := by
  classical
  let D : Set (EuclideanSpace Real (Fin (n + n))) := directSumSetEuclidean n n C1 C2
  let A : EuclideanSpace Real (Fin (n + n)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    ((LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
          (M₂ := EuclideanSpace Real (Fin n))) +
        (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
          (M₂ := EuclideanSpace Real (Fin n)))).comp
      (appendAffineEquiv n n).symm.linear.toLinearMap
  have hconv : Convex Real D := by
    simpa [D] using (convex_directSumSetEuclidean n C1 C2 hC1 hC2)
  have hlin :=
    euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
      (n := n + n) (m := n) (C := D) hconv A
  have hdirect :=
    euclideanRelativeInterior_directSumSetEuclidean_eq_and_closure_eq n n C1 C2
  have himage : A '' D = C1 + C2 := by
    simpa [A, D] using
      (addLinearMap_image_directSum_eq_add (n := n) (C1 := C1) (C2 := C2))
  have himage_ri :
      A '' euclideanRelativeInterior (n + n) D =
        euclideanRelativeInterior n C1 + euclideanRelativeInterior n C2 := by
    have htmp :
        A '' directSumSetEuclidean n n (euclideanRelativeInterior n C1)
            (euclideanRelativeInterior n C2) =
          euclideanRelativeInterior n C1 + euclideanRelativeInterior n C2 := by
      simpa [A] using
        (addLinearMap_image_directSum_eq_add (n := n)
          (C1 := euclideanRelativeInterior n C1)
          (C2 := euclideanRelativeInterior n C2))
    simpa [D, hdirect.1] using htmp
  have himage_closure : A '' closure D = closure C1 + closure C2 := by
    have htmp :
        A '' directSumSetEuclidean n n (closure C1) (closure C2) =
          closure C1 + closure C2 := by
      simpa [A] using
        (addLinearMap_image_directSum_eq_add (n := n) (C1 := closure C1) (C2 := closure C2))
    simpa [D, hdirect.2] using htmp
  refine ⟨?_, ?_⟩
  · simpa [himage, himage_ri] using hlin.1
  · simpa [himage, himage_closure] using hlin.2

/-- Projection of a graph intersected with a direct-sum set recovers the preimage. -/
lemma preimage_eq_proj_graph_inter_directSum (n m : Nat)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (S : Set (EuclideanSpace Real (Fin m))) :
    let e := appendAffineEquiv n m
    let P : EuclideanSpace Real (Fin (n + m)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
      (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
          (M₂ := EuclideanSpace Real (Fin m))).comp e.symm.linear.toLinearMap
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + m))) :=
      (A.graph).toAffineSubspace.map e.toAffineMap
    let D_S : Set (EuclideanSpace Real (Fin (n + m))) :=
      directSumSetEuclidean n m Set.univ S
    P '' ((M : Set _) ∩ D_S) = A ⁻¹' S := by
  classical
  intro e P M D_S
  have hP : ∀ x, P (e x) = x.1 := by
    intro x
    have hfun : e x = e.linear x := by
      simpa using
        congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv n m)
    simp [P, LinearMap.comp_apply, hfun, AffineEquiv.linear_symm]
  ext x; constructor
  · rintro ⟨z, ⟨hzM, hzD⟩, rfl⟩
    have hzD' : z ∈ e '' Set.prod Set.univ S := by
      simpa [D_S, directSumSetEuclidean_eq_image_appendAffineEquiv] using hzD
    rcases hzD' with ⟨xy, hxy, rfl⟩
    rcases hxy with ⟨-, hxyS⟩
    have hzM' : ∃ uv ∈ (A.graph : Set _), e uv = e xy := by
      simpa [M, AffineSubspace.coe_map] using hzM
    rcases hzM' with ⟨uv, huv, huvEq⟩
    have huv_eq : uv = xy := e.injective huvEq
    have hgraph : xy.2 = A xy.1 := by
      have huv' : uv.2 = A uv.1 := by
        exact (LinearMap.mem_graph_iff (f := A) (x := uv)).1 huv
      simpa [huv_eq] using huv'
    have hA : A (P (e xy)) = xy.2 := by
      simpa [hP] using hgraph.symm
    simpa [hA] using hxyS
  · intro hx
    have hxS : A x ∈ S := hx
    let z : EuclideanSpace Real (Fin (n + m)) := e (x, A x)
    have hxgraph : (x, A x) ∈ (A.graph : Set _) := by
      simp [LinearMap.mem_graph_iff]
    have hzM : z ∈ (M : Set _) := by
      have hzM' : z ∈ e '' ((A.graph).toAffineSubspace : Set _) := by
        refine ⟨(x, A x), ?_, rfl⟩
        simp
      simpa [M, AffineSubspace.coe_map] using hzM'
    have hzD : z ∈ D_S := by
      have hzD' : z ∈ e '' Set.prod Set.univ S := by
        refine ⟨(x, A x), ⟨by simp, hxS⟩, rfl⟩
      simpa [D_S, directSumSetEuclidean_eq_image_appendAffineEquiv] using hzD'
    refine ⟨z, ⟨hzM, hzD⟩, ?_⟩
    simp [z, hP]

/-- Relative interior and closure of `univ ⊕ C`. -/
lemma ri_closure_directSum_univ_eq (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin m))) :
    let D := directSumSetEuclidean n m Set.univ C
    euclideanRelativeInterior (n + m) D =
        directSumSetEuclidean n m Set.univ (euclideanRelativeInterior m C) ∧
      closure D = directSumSetEuclidean n m Set.univ (closure C) := by
  classical
  intro D
  have h :=
    euclideanRelativeInterior_directSumSetEuclidean_eq_and_closure_eq
      (m := n) (p := m)
      (C1 := (Set.univ : Set (EuclideanSpace Real (Fin n)))) (C2 := C)
  have hri_univ :
      euclideanRelativeInterior n (Set.univ : Set (EuclideanSpace Real (Fin n))) = Set.univ := by
    simpa using
      (euclideanRelativeInterior_affineSubspace_eq n
        (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin n))))
  refine ⟨?_, ?_⟩
  · simpa [D, hri_univ] using h.1
  · simpa [D] using h.2

/-- A preimage point gives a graph point in the relative interior of the direct-sum set. -/
lemma graph_inter_ri_directSum_nonempty (n m : Nat)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (C : Set (EuclideanSpace Real (Fin m)))
    (hri : (A ⁻¹' euclideanRelativeInterior m C).Nonempty) :
    let e := appendAffineEquiv n m
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + m))) :=
      (A.graph).toAffineSubspace.map e.toAffineMap
    let D : Set (EuclideanSpace Real (Fin (n + m))) :=
      directSumSetEuclidean n m Set.univ C
    ((M : Set _) ∩ euclideanRelativeInterior (n + m) D).Nonempty := by
  classical
  intro e M D
  rcases hri with ⟨x, hx⟩
  let z : EuclideanSpace Real (Fin (n + m)) := e (x, A x)
  have hxgraph : (x, A x) ∈ (A.graph : Set _) := by
    simp [LinearMap.mem_graph_iff]
  have hzM : z ∈ (M : Set _) := by
    have hzM' : z ∈ e '' ((A.graph).toAffineSubspace : Set _) := by
      refine ⟨(x, A x), ?_, rfl⟩
      simp
    simpa [M, AffineSubspace.coe_map] using hzM'
  have hDri :
      euclideanRelativeInterior (n + m) D =
        directSumSetEuclidean n m Set.univ (euclideanRelativeInterior m C) :=
    (ri_closure_directSum_univ_eq n m C).1
  have hzri : z ∈ directSumSetEuclidean n m Set.univ (euclideanRelativeInterior m C) := by
    have hzri' : z ∈ e '' Set.prod Set.univ (euclideanRelativeInterior m C) := by
      refine ⟨(x, A x), ⟨by simp, hx⟩, rfl⟩
    simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using hzri'
  have hzD : z ∈ euclideanRelativeInterior (n + m) D := by
    simpa [hDri] using hzri
  exact ⟨z, ⟨hzM, hzD⟩⟩

/-- Theorem 6.7: Let `A` be a linear transformation from `R^n` to `R^m`. Let `C` be a convex
set in `R^m` such that `A ⁻¹' (ri C)` is nonempty. Then
`ri (A ⁻¹' C) = A ⁻¹' (ri C)` and `cl (A ⁻¹' C) = A ⁻¹' (cl C)`. -/
theorem euclideanRelativeInterior_preimage_linearMap_eq_and_closure_preimage (n m : Nat)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (C : Set (EuclideanSpace Real (Fin m))) (hC : Convex Real C)
    (hri : (A ⁻¹' euclideanRelativeInterior m C).Nonempty) :
    euclideanRelativeInterior n (A ⁻¹' C) = A ⁻¹' euclideanRelativeInterior m C ∧
      closure (A ⁻¹' C) = A ⁻¹' closure C := by
  classical
  let e := appendAffineEquiv n m
  let P : EuclideanSpace Real (Fin (n + m)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
        (M₂ := EuclideanSpace Real (Fin m))).comp e.symm.linear.toLinearMap
  let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + m))) :=
    (A.graph).toAffineSubspace.map e.toAffineMap
  let D : Set (EuclideanSpace Real (Fin (n + m))) :=
    directSumSetEuclidean n m Set.univ C
  have hconvD : Convex Real D := by
    simpa [D] using
      (convex_directSumSetEuclidean_general n m Set.univ C convex_univ hC)
  have hM_nonempty :
      ((M : Set _) ∩ euclideanRelativeInterior (n + m) D).Nonempty := by
    simpa [e, M, D] using
      (graph_inter_ri_directSum_nonempty n m A C hri)
  have hMD :=
    euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq
      (n := n + m) (C := D) hconvD M hM_nonempty
  have hconvM : Convex Real (M : Set (EuclideanSpace Real (Fin (n + m)))) := by
    simpa using (AffineSubspace.convex (Q := M))
  have hconvMD : Convex Real ((M : Set _) ∩ D) := hconvM.inter hconvD
  have hlin :=
    euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
      (n := n + m) (m := n) (C := (M : Set _) ∩ D) hconvMD P
  have hDri :
      euclideanRelativeInterior (n + m) D =
        directSumSetEuclidean n m Set.univ (euclideanRelativeInterior m C) :=
    (ri_closure_directSum_univ_eq n m C).1
  have hDcl :
      closure D = directSumSetEuclidean n m Set.univ (closure C) :=
    (ri_closure_directSum_univ_eq n m C).2
  have hpre :
      P '' ((M : Set _) ∩ D) = A ⁻¹' C := by
    simpa [P, M, D] using
      (preimage_eq_proj_graph_inter_directSum (n := n) (m := m) (A := A) (S := C))
  have hpre_ri :
      P '' ((M : Set _) ∩ directSumSetEuclidean n m Set.univ
        (euclideanRelativeInterior m C)) = A ⁻¹' euclideanRelativeInterior m C := by
    simpa [P, M] using
      (preimage_eq_proj_graph_inter_directSum (n := n) (m := m) (A := A)
        (S := euclideanRelativeInterior m C))
  have hpre_cl :
      P '' ((M : Set _) ∩ directSumSetEuclidean n m Set.univ (closure C)) =
        A ⁻¹' closure C := by
    simpa [P, M] using
      (preimage_eq_proj_graph_inter_directSum (n := n) (m := m) (A := A) (S := closure C))
  have hri_eq :
      euclideanRelativeInterior n (A ⁻¹' C) = A ⁻¹' euclideanRelativeInterior m C := by
    calc
      euclideanRelativeInterior n (A ⁻¹' C) =
          P '' ((M : Set _) ∩ euclideanRelativeInterior (n + m) D) := by
            calc
              euclideanRelativeInterior n (A ⁻¹' C) =
                  euclideanRelativeInterior n (P '' ((M : Set _) ∩ D)) := by
                    simp [hpre]
              _ = P '' euclideanRelativeInterior (n + m) ((M : Set _) ∩ D) := hlin.1
              _ = P '' ((M : Set _) ∩ euclideanRelativeInterior (n + m) D) := by
                  simp [hMD.1]
      _ = P '' ((M : Set _) ∩ directSumSetEuclidean n m Set.univ
            (euclideanRelativeInterior m C)) := by
            simp [hDri]
      _ = A ⁻¹' euclideanRelativeInterior m C := hpre_ri
  have hcl_superset : A ⁻¹' closure C ⊆ closure (A ⁻¹' C) := by
    have h2 :
        P '' ((M : Set _) ∩ directSumSetEuclidean n m Set.univ (closure C)) ⊆
          closure (A ⁻¹' C) := by
      simpa [hpre, hMD.2, hDcl] using hlin.2
    simpa [hpre_cl] using h2
  have hcl_subset : closure (A ⁻¹' C) ⊆ A ⁻¹' closure C :=
    (A.continuous_of_finiteDimensional).closure_preimage_subset C
  refine ⟨hri_eq, ?_⟩
  exact subset_antisymm hcl_subset hcl_superset

/-- The projection from `R^{m+p}` onto `R^m` identifies the section domain. -/
lemma section_D_eq_image_projection (m p : Nat)
    (C : Set (EuclideanSpace Real (Fin (m + p))))
    (y : EuclideanSpace Real (Fin m)) (z : EuclideanSpace Real (Fin p)) :
    let e := appendAffineEquiv m p
    let P : EuclideanSpace Real (Fin (m + p)) →ₗ[Real] EuclideanSpace Real (Fin m) :=
      (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin m))
          (M₂ := EuclideanSpace Real (Fin p))).comp e.symm.linear.toLinearMap
    let Cy : EuclideanSpace Real (Fin m) → Set (EuclideanSpace Real (Fin p)) :=
      fun y => {z | e (y, z) ∈ C}
    let D : Set (EuclideanSpace Real (Fin m)) := {y | (Cy y).Nonempty}
    D = P '' C ∧ P (e (y, z)) = y := by
  classical
  intro e P Cy D
  have hP : ∀ x, P (e x) = x.1 := by
    intro x
    have hfun : e x = e.linear x := by
      simpa using
        congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv m p)
    simp [P, LinearMap.comp_apply, hfun, AffineEquiv.linear_symm]
  have hCy : ∀ y z, z ∈ Cy y ↔ e (y, z) ∈ C := by
    intro y z
    simp [Cy]
  have hD : ∀ y, y ∈ D ↔ ∃ z, e (y, z) ∈ C := by
    intro y
    constructor
    · intro hy
      rcases hy with ⟨z, hz⟩
      exact ⟨z, (hCy y z).1 hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, (hCy y z).2 hz⟩
  have hD_image : D = P '' C := by
    ext y; constructor
    · intro hy
      rcases (hD y).1 hy with ⟨z, hz⟩
      refine ⟨e (y, z), hz, ?_⟩
      simpa using (hP (y, z))
    · rintro ⟨x, hxC, rfl⟩
      have : ∃ z, e (P x, z) ∈ C := by
        let yz := e.symm x
        have hx' : x = e yz := by
          simp [yz]
        have hPx : P x = yz.1 := by
          simp [hx', hP]
        refine ⟨yz.2, ?_⟩
        have hxeq : e (P x, yz.2) = x := by
          calc
            e (P x, yz.2) = e (yz.1, yz.2) := by simp [hPx]
            _ = e yz := rfl
            _ = x := by simp [yz]
        simpa [hxeq] using hxC
      exact (hD (P x)).2 this
  exact ⟨hD_image, by simpa using (hP (y, z))⟩

/-- The projection fiber is an affine subspace, and its intersection with `C` is the section. -/
lemma section_fiber_affineSubspace_eq (m p : Nat)
    (C : Set (EuclideanSpace Real (Fin (m + p))))
    (y : EuclideanSpace Real (Fin m)) :
    let e := appendAffineEquiv m p
    let P : EuclideanSpace Real (Fin (m + p)) →ₗ[Real] EuclideanSpace Real (Fin m) :=
      (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin m))
          (M₂ := EuclideanSpace Real (Fin p))).comp e.symm.linear.toLinearMap
    let Cy : EuclideanSpace Real (Fin m) → Set (EuclideanSpace Real (Fin p)) :=
      fun y => {z | e (y, z) ∈ C}
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (m + p))) :=
      AffineSubspace.mk' (e (y, 0)) (LinearMap.ker P)
    (M : Set _) = {w | P w = y} ∧
      (M : Set _) ∩ C = (fun z => e (y, z)) '' (Cy y) := by
  classical
  intro e P Cy M
  have hP : ∀ x, P (e x) = x.1 := by
    intro x
    have hfun : e x = e.linear x := by
      simpa using
        congrArg (fun f => f x) (appendAffineEquiv_eq_linear_toAffineEquiv m p)
    simp [P, LinearMap.comp_apply, hfun, AffineEquiv.linear_symm]
  have hP0 : P (e (y, 0)) = y := by
    simpa using (hP (y, 0))
  have hmap_sub : ∀ u v, P (u - v) = P u - P v := by
    intro u v
    simp [sub_eq_add_neg, map_add, map_neg]
  have hM : (M : Set _) = {w | P w = y} := by
    ext w; constructor
    · intro hw
      have hw' : w -ᵥ e (y, 0) ∈ LinearMap.ker P :=
        (AffineSubspace.mem_mk').1 hw
      have hw'' : P (w -ᵥ e (y, 0)) = 0 := by
        simpa using hw'
      have hw''' : P (w - e (y, 0)) = 0 := by
        simpa [vsub_eq_sub] using hw''
      have hw'''' : P w - P (e (y, 0)) = 0 := by
        simpa [hmap_sub] using hw'''
      have hw''''' : P w = P (e (y, 0)) := sub_eq_zero.mp hw''''
      have : P w = y := by
        simpa [hP0] using hw'''''
      simpa [Set.mem_setOf_eq] using this
    · intro hw
      have hw' : P w = y := by
        simpa [Set.mem_setOf_eq] using hw
      have hw'' : P w - P (e (y, 0)) = 0 := by
        simp [hw', hP0]
      have hw''' : P (w - e (y, 0)) = 0 := by
        simpa [hmap_sub] using hw''
      have hw'''' : P (w -ᵥ e (y, 0)) = 0 := by
        simpa [vsub_eq_sub] using hw'''
      have hw''''' : w -ᵥ e (y, 0) ∈ LinearMap.ker P := by
        simpa using hw''''
      exact (AffineSubspace.mem_mk').2 hw'''''
  have hCy : ∀ z, z ∈ Cy y ↔ e (y, z) ∈ C := by
    intro z
    simp [Cy]
  have hMC : (M : Set _) ∩ C = (fun z => e (y, z)) '' (Cy y) := by
    ext w; constructor
    · rintro ⟨hwM, hwC⟩
      have hwP : P w = y := by
        have : w ∈ {w | P w = y} := by
          simpa [hM] using hwM
        simpa [Set.mem_setOf_eq] using this
      let yz := e.symm w
      have hw_eq : w = e yz := by
        simp [yz]
      have hyz1 : yz.1 = y := by
        have : P (e yz) = y := by
          simpa [hw_eq] using hwP
        simpa [hP yz] using this
      have hw' : e (y, yz.2) = w := by
        calc
          e (y, yz.2) = e (yz.1, yz.2) := by simp [hyz1]
          _ = e yz := rfl
          _ = w := by simp [yz]
      have hzC : e (y, yz.2) ∈ C := by
        simpa [hw'] using hwC
      refine ⟨yz.2, (hCy yz.2).2 hzC, hw'⟩
    · rintro ⟨z, hz, rfl⟩
      have hC' : e (y, z) ∈ C := (hCy z).1 hz
      have hM' : e (y, z) ∈ (M : Set _) := by
        have : e (y, z) ∈ {w | P w = y} := by
          simpa [Set.mem_setOf_eq] using (hP (y, z))
        simpa [hM] using this
      exact ⟨hM', hC'⟩
  exact ⟨hM, hMC⟩

/-- Relative interior of a section `{y} ⊕ C_y` is the image of `ri C_y`. -/
lemma ri_fiber_eq_ri_section (m p : Nat)
    (C : Set (EuclideanSpace Real (Fin (m + p)))) (hC : Convex Real C)
    (y : EuclideanSpace Real (Fin m)) :
    let e := appendAffineEquiv m p
    let Cy : EuclideanSpace Real (Fin m) → Set (EuclideanSpace Real (Fin p)) :=
      fun y => {z | e (y, z) ∈ C}
    euclideanRelativeInterior (m + p) (directSumSetEuclidean m p ({y}) (Cy y)) =
      (fun z => e (y, z)) '' euclideanRelativeInterior p (Cy y) := by
  classical
  intro e Cy
  have hconv_Cy : Convex Real (Cy y) := by
    let f1 : EuclideanSpace Real (Fin p) →ᵃ[Real] EuclideanSpace Real (Fin m) :=
      AffineMap.const (k := Real) (P1 := EuclideanSpace Real (Fin p)) y
    let f2 : EuclideanSpace Real (Fin p) →ᵃ[Real] EuclideanSpace Real (Fin p) :=
      AffineMap.id (k := Real) (V1 := EuclideanSpace Real (Fin p))
        (P1 := EuclideanSpace Real (Fin p))
    let f : EuclideanSpace Real (Fin p) →ᵃ[Real]
        (EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) :=
      AffineMap.prod f1 f2
    let g : EuclideanSpace Real (Fin p) →ᵃ[Real] EuclideanSpace Real (Fin (m + p)) :=
      (appendAffineEquiv m p).toAffineMap.comp f
    have hpre : Cy y = g ⁻¹' C := by
      ext z
      simp [Cy, g, f, f1, f2, e]
    have : Convex Real (g ⁻¹' C) := Convex.affine_preimage (f := g) hC
    simpa [hpre] using this
  have hri :=
    (euclideanRelativeInterior_directSumSetEuclidean_eq_and_closure_eq
      (m := m) (p := p) (C1 := ({y} : Set (EuclideanSpace Real (Fin m))))
      (C2 := Cy y)).1
  have hri_singleton :
      euclideanRelativeInterior m ({y} : Set (EuclideanSpace Real (Fin m))) = {y} := by
    let s : AffineSubspace Real (EuclideanSpace Real (Fin m)) :=
      AffineSubspace.mk' y (⊥)
    have hs : (s : Set (EuclideanSpace Real (Fin m))) = ({y} : Set _) := by
      ext x; constructor
      · intro hx
        have hx' : x -ᵥ y ∈ (⊥ : Submodule Real (EuclideanSpace Real (Fin m))) :=
          (AffineSubspace.mem_mk').1 hx
        have hx'' : x -ᵥ y = 0 := by
          simpa using hx'
        have : x = y := by
          simpa using (vsub_eq_zero_iff_eq.mp hx'')
        simp [this]
      · intro hx
        have hx' : x = y := by
          simpa [Set.mem_singleton_iff] using hx
        subst hx'
        simp [s]
    simpa [hs] using (euclideanRelativeInterior_affineSubspace_eq m s)
  have hri' :
      euclideanRelativeInterior (m + p) (directSumSetEuclidean m p ({y}) (Cy y)) =
        directSumSetEuclidean m p ({y}) (euclideanRelativeInterior p (Cy y)) := by
    simpa [hri_singleton] using hri
  have himage :
      directSumSetEuclidean m p ({y}) (euclideanRelativeInterior p (Cy y)) =
        (fun z => e (y, z)) '' euclideanRelativeInterior p (Cy y) := by
    ext w; constructor
    · intro hw
      have hw' :
          w ∈ e '' Set.prod ({y} : Set (EuclideanSpace Real (Fin m)))
            (euclideanRelativeInterior p (Cy y)) := by
        simpa [directSumSetEuclidean_eq_image_appendAffineEquiv, e] using hw
      rcases hw' with ⟨⟨y', z'⟩, hmem, rfl⟩
      rcases hmem with ⟨hy', hz'⟩
      have hy' : y' = y := by
        simpa [Set.mem_singleton_iff] using hy'
      refine ⟨z', hz', ?_⟩
      simp [hy']
    · rintro ⟨z', hz', rfl⟩
      have hprod :
          (y, z') ∈ Set.prod ({y} : Set (EuclideanSpace Real (Fin m)))
            (euclideanRelativeInterior p (Cy y)) := by
        exact ⟨by simp, hz'⟩
      have : e (y, z') ∈
          e '' Set.prod ({y} : Set (EuclideanSpace Real (Fin m)))
            (euclideanRelativeInterior p (Cy y)) := by
        exact ⟨(y, z'), hprod, rfl⟩
      simpa [directSumSetEuclidean_eq_image_appendAffineEquiv, e] using this
  simpa [himage] using hri'

/-- Theorem 6.8: Let `C` be a convex set in `R^{m+p}`. For each `y ∈ R^m`, let `C_y` be the set
of vectors `z ∈ R^p` such that `(y, z) ∈ C`. Let `D = {y | C_y ≠ ∅}`. Then `(y, z) ∈ ri C` if and
only if `y ∈ ri D` and `z ∈ ri C_y`. -/
theorem euclideanRelativeInterior_mem_iff_relativeInterior_section (m p : Nat)
    (C : Set (EuclideanSpace Real (Fin (m + p)))) (hC : Convex Real C)
    (y : EuclideanSpace Real (Fin m)) (z : EuclideanSpace Real (Fin p)) :
    let append :
        EuclideanSpace Real (Fin m) → EuclideanSpace Real (Fin p) →
          EuclideanSpace Real (Fin (m + p)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + p))).symm
          ((Fin.appendIsometry m p)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin p)) z))
    let Cy : EuclideanSpace Real (Fin m) → Set (EuclideanSpace Real (Fin p)) :=
      fun y => {z | append y z ∈ C}
    let D : Set (EuclideanSpace Real (Fin m)) := {y | (Cy y).Nonempty}
    append y z ∈ euclideanRelativeInterior (m + p) C ↔
      y ∈ euclideanRelativeInterior m D ∧ z ∈ euclideanRelativeInterior p (Cy y) := by
  classical
  intro append Cy D
  let e := appendAffineEquiv m p
  let P : EuclideanSpace Real (Fin (m + p)) →ₗ[Real] EuclideanSpace Real (Fin m) :=
    (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin m))
        (M₂ := EuclideanSpace Real (Fin p))).comp e.symm.linear.toLinearMap
  have happend : ∀ y z, append y z = e (y, z) := by
    intro y z
    simp [append, appendAffineEquiv_apply, e]
  have hCy_eq : Cy = fun y => {z | e (y, z) ∈ C} := by
    funext y
    ext z
    simp [Cy, happend]
  have hD_eq : D = {y | Set.Nonempty {z | e (y, z) ∈ C}} := by
    ext y
    simp [D, hCy_eq]
  have hproj : D = P '' C ∧ P (e (y, z)) = y := by
    simpa [e, P, hD_eq] using
      (section_D_eq_image_projection (m := m) (p := p) (C := C) (y := y) (z := z))
  have hDproj : D = P '' C := hproj.1
  have hP : P (e (y, z)) = y := hproj.2
  have hriD :
      euclideanRelativeInterior m D =
        P '' euclideanRelativeInterior (m + p) C := by
    have hlin :=
      euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
        (n := m + p) (m := m) (C := C) hC P
    simpa [hDproj] using hlin.1
  let M : AffineSubspace Real (EuclideanSpace Real (Fin (m + p))) :=
    AffineSubspace.mk' (e (y, 0)) (LinearMap.ker P)
  have hM :
      (M : Set _) = {w | P w = y} ∧
        (M : Set _) ∩ C = (fun z => e (y, z)) '' (Cy y) := by
    simpa [e, P, M, hCy_eq] using
      (section_fiber_affineSubspace_eq (m := m) (p := p) (C := C) (y := y))
  have hMset : (M : Set _) = {w | P w = y} := hM.1
  have hMC : (M : Set _) ∩ C = (fun z => e (y, z)) '' (Cy y) := hM.2
  have hMC_direct :
      (M : Set _) ∩ C = directSumSetEuclidean m p ({y}) (Cy y) := by
    have himage :
        directSumSetEuclidean m p ({y}) (Cy y) = (fun z => e (y, z)) '' (Cy y) := by
      ext w; constructor
      · intro hw
        have hw' :
            w ∈ e '' Set.prod ({y} : Set (EuclideanSpace Real (Fin m))) (Cy y) := by
          simpa [directSumSetEuclidean_eq_image_appendAffineEquiv, e] using hw
        rcases hw' with ⟨⟨y', z'⟩, hmem, rfl⟩
        rcases hmem with ⟨hy', hz'⟩
        have hy' : y' = y := by
          simpa [Set.mem_singleton_iff] using hy'
        refine ⟨z', hz', ?_⟩
        simp [hy']
      · rintro ⟨z', hz', rfl⟩
        have hprod :
            (y, z') ∈ Set.prod ({y} : Set (EuclideanSpace Real (Fin m))) (Cy y) := by
          exact ⟨by simp, hz'⟩
        have : e (y, z') ∈
            e '' Set.prod ({y} : Set (EuclideanSpace Real (Fin m))) (Cy y) := by
          exact ⟨(y, z'), hprod, rfl⟩
        simpa [directSumSetEuclidean_eq_image_appendAffineEquiv, e] using this
    exact hMC.trans himage.symm
  have hri_section :
      euclideanRelativeInterior (m + p) (directSumSetEuclidean m p ({y}) (Cy y)) =
        (fun z => e (y, z)) '' euclideanRelativeInterior p (Cy y) := by
    simpa [e, hCy_eq] using
      (ri_fiber_eq_ri_section (m := m) (p := p) (C := C) (hC := hC) (y := y))
  constructor
  · intro hzC
    have hzC' : e (y, z) ∈ euclideanRelativeInterior (m + p) C := by
      simpa [happend] using hzC
    have hyD : y ∈ euclideanRelativeInterior m D := by
      have : y ∈ P '' euclideanRelativeInterior (m + p) C := by
        exact ⟨e (y, z), hzC', hP⟩
      simpa [hriD] using this
    have hMmem : e (y, z) ∈ (M : Set _) := by
      have : e (y, z) ∈ {w | P w = y} := by
        simpa [Set.mem_setOf_eq] using hP
      simpa [hMset] using this
    have hM_nonempty :
        ((M : Set _) ∩ euclideanRelativeInterior (m + p) C).Nonempty := by
      exact ⟨e (y, z), ⟨hMmem, hzC'⟩⟩
    have hriM :
        euclideanRelativeInterior (m + p) ((M : Set _) ∩ C) =
          (M : Set _) ∩ euclideanRelativeInterior (m + p) C := by
      exact
        (euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq
            (n := m + p) (C := C) hC M hM_nonempty).1
    have hzMri : e (y, z) ∈ euclideanRelativeInterior (m + p) ((M : Set _) ∩ C) := by
      have : e (y, z) ∈ (M : Set _) ∩ euclideanRelativeInterior (m + p) C := by
        exact ⟨hMmem, hzC'⟩
      simpa [hriM] using this
    have hz_image :
        e (y, z) ∈ (fun z => e (y, z)) '' euclideanRelativeInterior p (Cy y) := by
      have : e (y, z) ∈
          euclideanRelativeInterior (m + p) (directSumSetEuclidean m p ({y}) (Cy y)) := by
        simpa [hMC_direct] using hzMri
      simpa [hri_section] using this
    rcases hz_image with ⟨z', hz', hzEq⟩
    have hpair : (y, z') = (y, z) := (appendAffineEquiv m p).injective hzEq
    have hz'' : z' = z := by
      simpa using congrArg Prod.snd hpair
    have hzCy : z ∈ euclideanRelativeInterior p (Cy y) := by
      simpa [hz''] using hz'
    exact ⟨hyD, hzCy⟩
  · rintro ⟨hyD, hzCy⟩
    have hyD' : y ∈ P '' euclideanRelativeInterior (m + p) C := by
      simpa [hriD] using hyD
    rcases hyD' with ⟨x, hxC, hxP⟩
    have hxM : x ∈ (M : Set _) := by
      have : x ∈ {w | P w = y} := by
        simpa [Set.mem_setOf_eq] using hxP
      simpa [hMset] using this
    have hM_nonempty :
        ((M : Set _) ∩ euclideanRelativeInterior (m + p) C).Nonempty := by
      exact ⟨x, ⟨hxM, hxC⟩⟩
    have hriM :
        euclideanRelativeInterior (m + p) ((M : Set _) ∩ C) =
          (M : Set _) ∩ euclideanRelativeInterior (m + p) C := by
      exact
        (euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq
            (n := m + p) (C := C) hC M hM_nonempty).1
    have hz_image :
        e (y, z) ∈ (fun z => e (y, z)) '' euclideanRelativeInterior p (Cy y) := by
      exact ⟨z, hzCy, rfl⟩
    have hz_direct :
        e (y, z) ∈
          euclideanRelativeInterior (m + p) (directSumSetEuclidean m p ({y}) (Cy y)) := by
      simpa [hri_section] using hz_image
    have hzMri : e (y, z) ∈ euclideanRelativeInterior (m + p) ((M : Set _) ∩ C) := by
      simpa [hMC_direct] using hz_direct
    have hzMri' :
        e (y, z) ∈ (M : Set _) ∩ euclideanRelativeInterior (m + p) C := by
      simpa [hriM] using hzMri
    have hzC : e (y, z) ∈ euclideanRelativeInterior (m + p) C := hzMri'.2
    simpa [happend] using hzC

/-- Convexity of the slice `{v | first v = 1 ∧ tail v ∈ C}`. -/
lemma convex_S_first_tail (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) :
    Convex Real
      {v : EuclideanSpace Real (Fin (1 + n)) |
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n)) v) 0 = 1 ∧
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
              (fun i =>
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n)) v) (Fin.natAdd 1 i)) ∈
            C} := by
  classical
  let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
  let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
  let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (fun i => coords v (Fin.natAdd 1 i))
  have hconv : Convex Real {v | first v = 1 ∧ tail v ∈ C} := by
    refine (convex_iff_add_mem).2 ?_
    intro v hv w hw a b ha hb hab
    have hv' : first v = 1 ∧ tail v ∈ C := by
      simpa using hv
    have hw' : first w = 1 ∧ tail w ∈ C := by
      simpa using hw
    have hv1 : first v = 1 := hv'.1
    have hvC : tail v ∈ C := hv'.2
    have hw1 : first w = 1 := hw'.1
    have hwC : tail w ∈ C := hw'.2
    have hfirst :
        first (a • v + b • w) = (a : Real) * first v + b * first w := by
      simp [first, coords]
    have htail :
        tail (a • v + b • w) = a • tail v + b • tail w := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext i
      simp [tail, coords]
    have htailC : tail (a • v + b • w) ∈ C := by
      have : a • tail v + b • tail w ∈ C := hC hvC hwC ha hb hab
      simpa [htail] using this
    have hfirst_eq : first (a • v + b • w) = 1 := by
      calc
        first (a • v + b • w) = a * first v + b * first w := hfirst
        _ = a * 1 + b * 1 := by simp [hv1, hw1]
        _ = 1 := by nlinarith
    exact ⟨hfirst_eq, htailC⟩
  simpa [coords, first, tail] using hconv

/-- Membership in the generated cone in terms of the first and tail coordinates. -/
lemma mem_K_iff_first_tail (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) :
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
    ∀ v, v ∈ K ↔ 0 < first v ∧ tail v ∈ (first v) • C := by
  classical
  intro coords first tail S K v
  have hconvS : Convex Real S := by
    simpa [S, coords, first, tail] using
      (convex_S_first_tail (n := n) (C := C) hC)
  constructor
  · intro hvK
    rcases (ConvexCone.mem_hull_of_convex (s := S) hconvS).1 hvK with ⟨r, hr, hrS⟩
    rcases hrS with ⟨w, hwS, rfl⟩
    rcases hwS with ⟨hw1, hwC⟩
    have hfirst :
        first (r • w) = (r : Real) * first w := by
      simp [first, coords]
    have htail : tail (r • w) = r • tail w := by
      apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
      funext i
      simp [tail, coords]
    have hfirst_pos : 0 < first (r • w) := by
      simpa [hfirst, hw1] using hr
    have htail_mem : tail (r • w) ∈ (first (r • w)) • C := by
      have : tail (r • w) ∈ r • C := by
        exact ⟨tail w, hwC, by simp [htail]⟩
      simpa [hfirst, hw1] using this
    exact ⟨hfirst_pos, htail_mem⟩
  · rintro ⟨hv_pos, hvC⟩
    rcases hvC with ⟨x, hxC, hx⟩
    have htail : tail v = first v • x := by
      simpa using hx.symm
    have hfirst_ne : (first v : Real) ≠ 0 := ne_of_gt hv_pos
    let w : EuclideanSpace Real (Fin (1 + n)) := (first v)⁻¹ • v
    have hw1 : first w = 1 := by
      have hfirst :
          first w = (first v)⁻¹ * first v := by
        simp [w, first, coords]
      have hmul : (first v)⁻¹ * first v = 1 := by
        field_simp [hfirst_ne]
      simp [hfirst, hmul]
    have htailw : tail w = x := by
      have htailw' : tail w = (first v)⁻¹ • tail v := by
        apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
        funext i
        simp [w, tail, coords]
      calc
        tail w = (first v)⁻¹ • tail v := htailw'
        _ = (first v)⁻¹ • (first v • x) := by simp [htail]
        _ = x := by
          have hmul : (first v)⁻¹ * first v = 1 := by
            field_simp [hfirst_ne]
          simp [smul_smul, hmul]
    have hwS : w ∈ S := by
      exact ⟨hw1, by simpa [htailw] using hxC⟩
    have hvK : v ∈ K := by
      have hvw : (first v : Real) • w = v := by
        have hmul : (first v : Real) * (first v)⁻¹ = 1 := by
          field_simp [hfirst_ne]
        calc
          (first v : Real) • w = (first v : Real) • ((first v)⁻¹ • v) := rfl
          _ = ((first v : Real) * (first v)⁻¹) • v := by simp [smul_smul]
          _ = v := by simp [hmul]
      have : v = first v • w := hvw.symm
      refine (ConvexCone.mem_hull_of_convex (s := S) hconvS).2 ?_
      refine ⟨first v, hv_pos, ?_⟩
      refine ⟨w, hwS, ?_⟩
      exact this.symm
    simpa using hvK

/-- First and tail coordinates of the append map for `m = 1`. -/
lemma first_tail_append (n : Nat) (y : EuclideanSpace Real (Fin 1))
    (z : EuclideanSpace Real (Fin n)) :
    let coords : EuclideanSpace Real (Fin (1 + n)) → (Fin (1 + n) → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))
    let first : EuclideanSpace Real (Fin (1 + n)) → Real := fun v => coords v 0
    let tail : EuclideanSpace Real (Fin (1 + n)) → EuclideanSpace Real (Fin n) :=
      fun v =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
          (fun i => coords v (Fin.natAdd 1 i))
    let append :
        EuclideanSpace Real (Fin 1) → EuclideanSpace Real (Fin n) →
          EuclideanSpace Real (Fin (1 + n)) :=
      fun y z =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).symm
          ((Fin.appendIsometry 1 n)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
             (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
    first (append y z) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 ∧
      tail (append y z) = z := by
  classical
  intro coords first tail append
  have hcoords :
      coords (append y z) =
        (Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z) := by
    dsimp [coords, append]
    simpa using
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (1 + n))).apply_symm_apply
        ((Fin.appendIsometry 1 n)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) y,
           (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) z))
  have hfirst :
      first (append y z) = (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) y) 0 := by
    have := congrArg (fun f => f 0) hcoords
    simpa [first] using this
  have htail : tail (append y z) = z := by
    apply (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).injective
    funext i
    have := congrArg (fun f => f (Fin.natAdd 1 i)) hcoords
    simpa [tail] using this
  exact ⟨hfirst, htail⟩

end Section06
end Chap02
