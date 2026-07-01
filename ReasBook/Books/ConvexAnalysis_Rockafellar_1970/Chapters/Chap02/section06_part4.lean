/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3

noncomputable section
open scoped Pointwise

section Chap02
section Section06

/-- A set not contained in the relative boundary is nonempty. -/
lemma C2_nonempty_of_not_subset_relativeBoundary (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n)))
    (hC2not : ¬ C2 ⊆ euclideanRelativeBoundary n C1) : C2.Nonempty := by
  by_contra hC2ne
  have hC2empty : C2 = ∅ := by
    simpa [Set.not_nonempty_iff_eq_empty] using hC2ne
  have hsubset : C2 ⊆ euclideanRelativeBoundary n C1 := by
    simp [hC2empty]
  exact hC2not hsubset

/-- A relative interior point has a smaller ball in the affine span contained in the
relative interior. -/
lemma euclideanRelativeInterior_ball_subset (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) {x : EuclideanSpace Real (Fin n)}
    (hx : x ∈ euclideanRelativeInterior n C) :
    ∃ ε : ℝ, 0 < ε ∧
      ((fun y => x + y) '' (ε • euclideanUnitBall n)) ∩
        (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ⊆
        euclideanRelativeInterior n C := by
  rcases hx with ⟨-, ε, hε, hxsub⟩
  refine ⟨ε / 2, by linarith [hε], ?_⟩
  intro y hy
  rcases hy with ⟨hy_ball, hy_aff⟩
  rcases hy_ball with ⟨v, hv, rfl⟩
  refine ⟨by simpa using hy_aff, ε / 2, by linarith [hε], ?_⟩
  intro z hz
  rcases hz with ⟨hz_ball, hz_aff⟩
  rcases hz_ball with ⟨w, hw, rfl⟩
  have hv_norm : ‖v‖ ≤ ε / 2 := by
    have hε0 : 0 ≤ ε / 2 := by linarith [hε]
    simpa using (norm_le_of_mem_smul_unitBall (n := n) (ε := ε / 2) hε0 hv)
  have hw_norm : ‖w‖ ≤ ε / 2 := by
    have hε0 : 0 ≤ ε / 2 := by linarith [hε]
    simpa using (norm_le_of_mem_smul_unitBall (n := n) (ε := ε / 2) hε0 hw)
  have hnorm : ‖v + w‖ ≤ ε := by
    have hsum : ‖v‖ + ‖w‖ ≤ ε := by linarith [hv_norm, hw_norm]
    exact (norm_add_le v w).trans hsum
  have hz_ball' :
      x + (v + w) ∈ (fun t => x + t) '' (ε • euclideanUnitBall n) := by
    refine ⟨v + w, ?_, by simp⟩
    exact mem_smul_unitBall_of_norm_le (n := n) (ε := ε) hε hnorm
  have hz_aff' :
      x + (v + w) ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
    simpa [add_assoc] using hz_aff
  have hzC : x + (v + w) ∈ C := hxsub ⟨hz_ball', hz_aff'⟩
  simpa [add_assoc] using hzC

/-- Under the corollary hypotheses, the relative interiors of `C1` and `C2` intersect. -/
lemma riC2_inter_riC1_nonempty (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n)))
    (hC2 : Convex Real C2) (hC2sub : C2 ⊆ closure C1)
    (hC2not : ¬ C2 ⊆ euclideanRelativeBoundary n C1) :
    (euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n C1).Nonempty := by
  classical
  rcases Set.not_subset.mp hC2not with ⟨x, hxC2, hxnot⟩
  have hxclC1 : x ∈ closure C1 := hC2sub hxC2
  have hxriC1 : x ∈ euclideanRelativeInterior n C1 := by
    by_contra hxri
    exact hxnot ⟨hxclC1, hxri⟩
  obtain ⟨ε, hε, hball⟩ :=
    euclideanRelativeInterior_ball_subset n C1 (x := x) hxriC1
  have hcl_eq :
      closure (euclideanRelativeInterior n C2) = closure C2 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C2 hC2).1
  have hxclri : x ∈ closure (euclideanRelativeInterior n C2) := by
    have hxclC2 : x ∈ closure C2 := subset_closure hxC2
    simpa [hcl_eq] using hxclC2
  rcases (Metric.mem_closure_iff.mp hxclri) (ε / 2) (by linarith [hε]) with
    ⟨y, hyri, hydist⟩
  have hyC2 : y ∈ C2 := (euclideanRelativeInterior_subset_closure n C2).1 hyri
  have hyclC1 : y ∈ closure C1 := hC2sub hyC2
  have hy_aff :
      y ∈ (affineSpan Real C1 : Set (EuclideanSpace Real (Fin n))) :=
    mem_affineSpan_of_mem_closure (n := n) (C := C1) hyclC1
  have hnorm : ‖y - x‖ ≤ ε := by
    have hdist' : ‖y - x‖ < ε / 2 := by
      have hdist' : dist y x < ε / 2 := by
        simpa [dist_comm] using hydist
      simpa [dist_eq_norm] using hdist'
    linarith [hdist']
  have hy_ball :
      y ∈ (fun z => x + z) '' (ε • euclideanUnitBall n) := by
    refine ⟨y - x, ?_, by simp⟩
    exact mem_smul_unitBall_of_norm_le (n := n) (ε := ε) hε hnorm
  have hyriC1 : y ∈ euclideanRelativeInterior n C1 := hball ⟨hy_ball, hy_aff⟩
  exact ⟨y, ⟨hyri, hyriC1⟩⟩

/-- Relative interiors of two convex sets coincide with the relative interior of their
intersection when their relative interiors meet. -/
lemma ri_intersection_fin_two (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2)
    (hri :
      (euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1)).Nonempty) :
    euclideanRelativeInterior n (C2 ∩ closure C1) =
      euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1) := by
  classical
  let D : Fin 2 → Set (EuclideanSpace Real (Fin n)) := fun i =>
    if i = 0 then C2 else closure C1
  have hconv : ∀ i, Convex Real (D i) := by
    intro i
    fin_cases i
    · simpa [D] using hC2
    · simpa [D] using (convex_closure_of_convex n C1 hC1)
  have hri' : (⋂ i, euclideanRelativeInterior n (D i)).Nonempty := by
    simpa [D] using hri
  have hri_eq :
      euclideanRelativeInterior n (⋂ i, D i) = ⋂ i, euclideanRelativeInterior n (D i) :=
    euclideanRelativeInterior_iInter_eq_iInter_relativeInterior_of_finite n D hconv hri'
  have hInter : (⋂ i, D i) = C2 ∩ closure C1 := by
    simpa [D] using (iInter_fin_two_eq_inter D)
  have hInter_ri :
      (⋂ i, euclideanRelativeInterior n (D i)) =
        euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1) := by
    simpa [D] using (iInter_fin_two_eq_inter (fun i => euclideanRelativeInterior n (D i)))
  simpa [hInter, hInter_ri] using hri_eq

/-- Corollary 6.5.2. Let `C1` be a convex set. Let `C2` be a convex set contained in `cl C1`
but not entirely contained in the relative boundary of `C1`. Then `ri C2 ⊆ ri C1`. -/
theorem euclideanRelativeInterior_subset_of_subset_closure_not_subset_relativeBoundary (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) (hC2sub : C2 ⊆ closure C1)
    (hC2not : ¬ C2 ⊆ euclideanRelativeBoundary n C1) :
    euclideanRelativeInterior n C2 ⊆ euclideanRelativeInterior n C1 := by
  classical
  have hri_nonempty :
      (euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n C1).Nonempty :=
    riC2_inter_riC1_nonempty n C1 C2 hC2 hC2sub hC2not
  have hri_closure_eq :
      euclideanRelativeInterior n (closure C1) = euclideanRelativeInterior n C1 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C1 hC1).2
  have hri_nonempty' :
      (euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1)).Nonempty := by
    simpa [hri_closure_eq] using hri_nonempty
  have hri_eq :
      euclideanRelativeInterior n (C2 ∩ closure C1) =
        euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1) :=
    ri_intersection_fin_two n C1 C2 hC1 hC2 hri_nonempty'
  have hInter : C2 ∩ closure C1 = C2 := by
    ext x; constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, hC2sub hx⟩
  have hri_eq' :
      euclideanRelativeInterior n C2 =
        euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1) := by
    simpa [hInter] using hri_eq
  intro x hx
  have hx' :
      x ∈ euclideanRelativeInterior n C2 ∩ euclideanRelativeInterior n (closure C1) := by
    exact (Eq.mp (congrArg (fun s => x ∈ s) hri_eq') hx)
  have hxC1 : x ∈ euclideanRelativeInterior n C1 := by
    simpa [hri_closure_eq] using hx'.2
  exact hxC1

/-- Linear maps send closures into the closure of the image. -/
lemma image_closure_subset_closure_image_linearMap (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n)))
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    A '' closure C ⊆ closure (A '' C) := by
  simpa using
    (image_closure_subset_closure_image (f := A) (s := C) A.continuous_of_finiteDimensional)

/-- Linear images of relative interior points stay in the relative interior of the image. -/
lemma image_relativeInterior_subset_relativeInterior_image (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    A '' euclideanRelativeInterior n C ⊆ euclideanRelativeInterior m (A '' C) := by
  rintro z ⟨z', hz', rfl⟩
  have hzC : z' ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hz'
  have hCne : C.Nonempty := ⟨z', hzC⟩
  have hconv : Convex Real (A '' C) := hC.linear_image A
  have hne : (A '' C).Nonempty := ⟨A z', ⟨z', hzC, rfl⟩⟩
  have hz_prop :
      ∀ x ∈ C, ∃ μ > (1 : Real), (1 - μ) • x + μ • z' ∈ C :=
    (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem n C hC hCne z').1 hz'
  refine
    (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem m (A '' C) hconv hne
        (A z')).2 ?_
  intro x hx
  rcases hx with ⟨x', hx', rfl⟩
  rcases hz_prop x' hx' with ⟨μ, hμ, hmem⟩
  refine ⟨μ, hμ, ?_⟩
  refine ⟨(1 - μ) • x' + μ • z', hmem, ?_⟩
  simp [map_add, map_smul]

/-- Linear images of a convex set and its relative interior have the same closure. -/
lemma closure_image_eq_closure_image_ri (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    closure (A '' C) = closure (A '' euclideanRelativeInterior n C) := by
  have hcl_eq :
      closure (euclideanRelativeInterior n C) = closure C :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hC).1
  have hsubset1 :
      closure (A '' euclideanRelativeInterior n C) ⊆ closure (A '' C) :=
    closure_mono (Set.image_mono (euclideanRelativeInterior_subset_closure n C).1)
  have hsubset2 :
      closure (A '' C) ⊆ closure (A '' euclideanRelativeInterior n C) := by
    have himage_closure :
        A '' closure (euclideanRelativeInterior n C) ⊆
          closure (A '' euclideanRelativeInterior n C) :=
      image_closure_subset_closure_image_linearMap n m (euclideanRelativeInterior n C) A
    have hsubset : A '' C ⊆ closure (A '' euclideanRelativeInterior n C) := by
      intro x hx
      rcases hx with ⟨y, hyC, rfl⟩
      have hycl : y ∈ closure (euclideanRelativeInterior n C) := by
        have hycl' : y ∈ closure C := subset_closure hyC
        simpa [hcl_eq] using hycl'
      have : A y ∈ A '' closure (euclideanRelativeInterior n C) := ⟨y, hycl, rfl⟩
      exact himage_closure this
    simpa [closure_closure] using (closure_mono hsubset)
  exact le_antisymm hsubset2 hsubset1

/-- The relative interior of a linear image lies in the image of the relative interior. -/
lemma relativeInterior_image_subset_image_relativeInterior (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    euclideanRelativeInterior m (A '' C) ⊆ A '' euclideanRelativeInterior n C := by
  have hconv1 : Convex Real (A '' C) := hC.linear_image A
  have hconv2 : Convex Real (A '' euclideanRelativeInterior n C) :=
    (convex_euclideanRelativeInterior n C hC).linear_image A
  have hcl_eq :
      closure (A '' C) = closure (A '' euclideanRelativeInterior n C) :=
    closure_image_eq_closure_image_ri n m C hC A
  have hbetween' :=
    ((euclidean_closure_eq_iff_relativeInterior_eq_and_between m (A '' C)
        (A '' euclideanRelativeInterior n C) hconv1 hconv2).2).mp hcl_eq
  exact hbetween'.1

/-- Theorem 6.6: Let `C` be a convex set in `R^n`, and let `A` be a linear transformation from
`R^n` to `R^m`. Then `ri (A C) = A (ri C)` and `cl (A C) ⊇ A (cl C)`. -/
theorem euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    euclideanRelativeInterior m (A '' C) = A '' euclideanRelativeInterior n C ∧
      A '' closure C ⊆ closure (A '' C) := by
  refine ⟨?_, ?_⟩
  · refine le_antisymm ?_ ?_
    · exact relativeInterior_image_subset_image_relativeInterior n m C hC A
    · exact image_relativeInterior_subset_relativeInterior_image n m C hC A
  · exact image_closure_subset_closure_image_linearMap n m C A

/-- Relative interior commutes with `LinearMap.lsmul` as a linear image. -/
lemma ri_image_lsmul_eq (n : Nat) (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (r : Real) :
    euclideanRelativeInterior n
        ((LinearMap.lsmul Real (EuclideanSpace Real (Fin n)) r) '' C) =
      (LinearMap.lsmul Real (EuclideanSpace Real (Fin n)) r) ''
        euclideanRelativeInterior n C := by
  simpa using
    (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset n n C hC
        (LinearMap.lsmul Real (EuclideanSpace Real (Fin n)) r)).1

/-- The image of a set under `LinearMap.lsmul` is pointwise scalar multiplication. -/
lemma image_lsmul_eq_smul_set (n : Nat) (C : Set (EuclideanSpace Real (Fin n))) (r : Real) :
    (LinearMap.lsmul Real (EuclideanSpace Real (Fin n)) r) '' C = r • C := by
  ext x; constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by simp⟩

/-- Corollary 6.6.1. For any convex set `C` and any real number `λ`,
`ri (λ C) = λ ri C`. -/
theorem euclideanRelativeInterior_smul (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) (r : Real) :
    euclideanRelativeInterior n (r • C) = r • euclideanRelativeInterior n C := by
  have h := ri_image_lsmul_eq n C hC r
  simpa [image_lsmul_eq_smul_set] using h

end Section06
end Chap02
