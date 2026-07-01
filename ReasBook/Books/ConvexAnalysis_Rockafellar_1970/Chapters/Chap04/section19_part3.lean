/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part2

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Theorem 19.1: lift finite generation along a lineality projection. -/
lemma helperForTheorem_19_1_liftFiniteGeneration_from_projection
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) (hCne : C.Nonempty)
    {L W : Submodule ℝ (Fin n → ℝ)} (hWL : IsCompl W L)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hker : LinearMap.ker π = L)
    (hrange : LinearMap.range π = W) (hprojW : ∀ w ∈ W, π w = w)
    (hL : (L : Set _) = linealitySpace_fin C) :
    let K := π '' C;
      IsFinitelyGeneratedConvexSet n K →
      (∃ SL, Set.Finite SL ∧ SL ⊆ (L : Set _) ∧ (L : Set _) ⊆ cone n SL) →
      IsFinitelyGeneratedConvexSet n C := by
  classical
  intro K hKgen hSL
  rcases hKgen with ⟨S₀K, S₁K, hS₀Kfinite, hS₁Kfinite, hKeq⟩
  rcases hSL with ⟨SL, hSLfinite, hSLsubset, hLsubset⟩
  have hpre :
      (C = π ⁻¹' K) ∧ (K ⊆ (W : Set _)) ∧ K.Nonempty := by
    simpa [K] using
      (helperForTheorem_19_1_projection_preimage_image_eq_of_linealityKernel
        (n := n) (C := C) hc hCne (L := L) (W := W) hWL (π := π) hker hrange hL)
  have hCpre : C = π ⁻¹' K := hpre.1
  have hKsubsetW : K ⊆ (W : Set _) := hpre.2.1
  have hKne : K.Nonempty := hpre.2.2
  let S₁ : Set (Fin n → ℝ) := S₁K ∪ SL
  have hS₁finite : Set.Finite S₁ := hS₁Kfinite.union hSLfinite
  refine ⟨S₀K, S₁, hS₀Kfinite, hS₁finite, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hxK : π x ∈ K := by
      have hx' : x ∈ π ⁻¹' K := by
        simpa [hCpre] using hx
      simpa using hx'
    have hxK' : π x ∈ mixedConvexHull (n := n) S₀K S₁K := by
      simpa [hKeq] using hxK
    have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀K S₁K
    have hxK'' : π x ∈ conv S₀K + cone n S₁K := by
      have hxK''' : π x ∈ conv (S₀K + ray n S₁K) := by
        simpa [hrepr.1] using hxK'
      simpa [hrepr.2] using hxK'''
    rcases (Set.mem_add).1 hxK'' with ⟨u, huS₀, v, hvS₁, hsum⟩
    have hxL : x - π x ∈ (L : Set _) := by
      have hkerxy : x - π x ∈ LinearMap.ker π := by
        apply (LinearMap.mem_ker).2
        calc
          π (x - π x) = π x - π (π x) := by simp
          _ = 0 := by
            have hpx : π (π x) = π x := by
              have hpx' : π x ∈ W := hKsubsetW hxK
              exact hprojW (π x) hpx'
            simp [hpx]
      simpa [hker] using hkerxy
    have hxLcone : x - π x ∈ cone n SL := hLsubset hxL
    have hvS₁' : v ∈ cone n S₁ := by
      have hsub : S₁K ⊆ S₁ := by
        intro d hd
        exact Or.inl hd
      exact helperForTheorem_19_1_cone_mono (n := n) (S := S₁K) (T := S₁) hsub hvS₁
    have hxLcone' : x - π x ∈ cone n S₁ := by
      have hsub : SL ⊆ S₁ := by
        intro d hd
        exact Or.inr hd
      exact helperForTheorem_19_1_cone_mono (n := n) (S := SL) (T := S₁) hsub hxLcone
    have hconeS₁ : IsConvexCone n (cone n S₁) := by
      simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₁)] using
        (isConvexCone_convexConeGenerated (n := n) (S₁ := S₁))
    have hadd :
        ∀ a ∈ cone n S₁, ∀ b ∈ cone n S₁, a + b ∈ cone n S₁ :=
      isConvexCone_add_closed n (cone n S₁) hconeS₁
    have hsum' : v + (x - π x) ∈ cone n S₁ := hadd v hvS₁' (x - π x) hxLcone'
    have hxmem : x ∈ conv S₀K + cone n S₁ := by
      refine Set.mem_add.2 ?_
      refine ⟨u, huS₀, v + (x - π x), hsum', ?_⟩
      have hsum'' : u + (v + (x - π x)) = x := by
        calc
          u + (v + (x - π x)) = (u + v) + (x - π x) := by
            simp [add_assoc]
          _ = π x + (x - π x) := by
            simpa [hsum]
          _ = x := by abel
      exact hsum''
    have hreprS₁ := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀K S₁
    have hxmem' : x ∈ mixedConvexHull (n := n) S₀K S₁ := by
      have hxmem'' : x ∈ conv (S₀K + ray n S₁) := by
        simpa [hreprS₁.2] using hxmem
      simpa [hreprS₁.1] using hxmem''
    simpa using hxmem'
  · have hconv : Convex ℝ C := hc
    have hS₀subsetC : S₀K ⊆ C := by
      intro x hx
      have hx' : x ∈ mixedConvexHull (n := n) S₀K S₁K := by
        have hxray : x ∈ S₀K + ray n S₁K := by
          have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁K := by
            change (0 : Fin n → ℝ) ∈ Set.insert 0 (rayNonneg n S₁K)
            exact (Set.mem_insert_iff).2 (Or.inl rfl)
          have hxray' : x + 0 ∈ S₀K + ray n S₁K := Set.add_mem_add hx h0ray
          simpa using hxray'
        exact (add_ray_subset_mixedConvexHull (n := n) S₀K S₁K) hxray
      have hxK : x ∈ K := by
        simpa [hKeq] using hx'
      have hxW : x ∈ W := hKsubsetW hxK
      have hpx : π x = x := hprojW x hxW
      have hxpre : x ∈ π ⁻¹' K := by
        have : π x ∈ K := by simpa [hpx] using hxK
        simpa using this
      simpa [hCpre] using hxpre
    have hrecC :
        ∀ d ∈ S₁, ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C := by
      intro d hd x hx t ht
      rcases hd with hd | hd
      · have hdrecK : d ∈ Set.recessionCone K := by
          intro z hz s hs
          have hz' : z ∈ mixedConvexHull (n := n) S₀K S₁K := by
            simpa [hKeq] using hz
          have hrec :=
            helperForTheorem_19_1_mixedConvexHull_recedes
              (n := n) (S₀ := S₀K) (S₁ := S₁K) (d := d) (x := z) hd hz' s hs
          simpa [hKeq] using hrec
        have hdW : d ∈ W :=
          helperForTheorem_19_1_recessionCone_subset_submodule
            (n := n) (K := K) (W := W) hKsubsetW hKne hdrecK
        have hpd : π d = d := hprojW d hdW
        have hxK : π x ∈ K := by
          have hx' : x ∈ π ⁻¹' K := by
            simpa [hCpre] using hx
          simpa using hx'
        have hxK' : π x + t • d ∈ K := by
          have hxK'' : π x ∈ mixedConvexHull (n := n) S₀K S₁K := by
            simpa [hKeq] using hxK
          have hrec :=
            helperForTheorem_19_1_mixedConvexHull_recedes
              (n := n) (S₀ := S₀K) (S₁ := S₁K) (d := d) (x := π x) hd hxK'' t ht
          simpa [hKeq] using hrec
        have hpi : π (x + t • d) = π x + t • d := by
          calc
            π (x + t • d) = π x + π (t • d) := by simp
            _ = π x + t • π d := by simp
            _ = π x + t • d := by simpa [hpd]
        have hxpre : x + t • d ∈ π ⁻¹' K := by
          have : π (x + t • d) ∈ K := by
            simpa [hpi] using hxK'
          simpa using this
        simpa [hCpre] using hxpre
      ·
        have hdL : d ∈ (L : Set _) := hSLsubset hd
        have hdLineal : d ∈ linealitySpace_fin C := by
          simpa [hL] using hdL
        have hdrec : d ∈ Set.recessionCone C := hdLineal.2
        have hdrec' :
            ∀ x ∈ C, ∀ s : ℝ, 0 ≤ s → x + s • d ∈ C := by
          simpa [Set.recessionCone] using hdrec
        exact hdrec' x hx t ht
    have hmem_family :
        Convex ℝ C ∧ S₀K ⊆ C ∧
          ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C := by
      refine ⟨hconv, hS₀subsetC, ?_⟩
      intro d hd x hx t ht
      exact hrecC d hd x hx t ht
    have hxsub :
        mixedConvexHull (n := n) S₀K S₁ ⊆ C := by
      simpa [mixedConvexHull] using (Set.sInter_subset_of_mem hmem_family)
    exact hxsub
/-- Helper for Theorem 19.1: closed convex sets with finitely many faces are finitely generated,
via a lineality split. -/
lemma helperForTheorem_19_1_closed_finiteFaces_imp_finitelyGenerated_via_linealitySplit
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) :
    (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite) →
      IsFinitelyGeneratedConvexSet n C := by
  classical
  intro hC
  rcases hC with ⟨hclosed, hfaces⟩
  by_cases hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C
  ·
    have hCeq :
        C =
          mixedConvexHull (n := n)
            {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
      exact
        helperForTheorem_19_1_closed_finiteFaces_eq_mixedConvexHull_extremePoints_extremeDirections
          (n := n) (C := C) hc hclosed hNoLines
    have hS₀finite :
        Set.Finite {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x} := by
      exact
        helperForTheorem_19_1_finiteFaces_imp_finite_extremePoints
          (n := n) (C := C) hc hfaces
    obtain ⟨S₁, hS₁finite, hpos, hS₁subset⟩ :=
      helperForTheorem_19_1_finiteFaces_imp_exists_finite_direction_reps
        (n := n) (C := C) hfaces
    have hpos' :
        ∀ d ∈ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d},
          ∃ d0 ∈ S₁, ∃ t : ℝ, 0 < t ∧ d = t • d0 := by
      intro d hd
      exact hpos d hd
    have hEq :
        mixedConvexHull (n := n)
            {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}
          =
        mixedConvexHull (n := n)
            {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
            S₁ := by
      have hEq' :
          mixedConvexHull (n := n)
              {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
              {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}
            =
          mixedConvexHull (n := n)
              {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
              S₁ := by
        have hEq'' :=
          helperForTheorem_19_1_mixedConvexHull_directionSet_eq_of_posMul_cover
            (n := n)
            (S₀ := {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x})
            (S₁ := S₁)
            (S₁' := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})
            hS₁subset hpos'
        exact hEq''
      exact hEq'
    refine ⟨{x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}, S₁, hS₀finite, hS₁finite, ?_⟩
    calc
      C =
          mixedConvexHull (n := n)
            {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := hCeq
      _ =
          mixedConvexHull (n := n)
            {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
            S₁ := hEq
  ·
    by_cases hCne : C.Nonempty
    ·
      rcases
          helperForTheorem_19_1_linealitySplit_projection_setup
            (n := n) (C := C) hc hCne with
        ⟨L, hL, W, hWL, π, hker, hrange, hprojW, hprojL⟩
      let K : Set (Fin n → ℝ) := π '' C
      have hpre :
          (C = π ⁻¹' K) ∧ (K ⊆ (W : Set _)) ∧ K.Nonempty := by
        simpa [K] using
          (helperForTheorem_19_1_projection_preimage_image_eq_of_linealityKernel
            (n := n) (C := C) hc hCne (L := L) (W := W) hWL (π := π) hker hrange hL)
      have hKprops :
          IsClosed K ∧
            {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) K F}.Finite ∧
              (¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone K) ∩ Set.recessionCone K) := by
        simpa [K] using
          (helperForTheorem_19_1_closed_finiteFaces_noLines_of_linealityProjection
            (n := n) (C := C) hc hclosed hfaces hCne (L := L) (W := W) hWL (π := π)
            hker hrange hprojW hL)
      have hKconv : Convex ℝ K := by
        simpa [K] using hc.linear_image π
      have hKeq :
          K =
            mixedConvexHull (n := n)
              {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x}
              {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) K d} := by
        exact
          helperForTheorem_19_1_closed_finiteFaces_eq_mixedConvexHull_extremePoints_extremeDirections
            (n := n) (C := K) hKconv hKprops.1 hKprops.2.2
      have hS₀Kfinite :
          Set.Finite {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x} := by
        exact
          helperForTheorem_19_1_finiteFaces_imp_finite_extremePoints
            (n := n) (C := K) hKconv hKprops.2.1
      obtain ⟨S₁K, hS₁Kfinite, hposK, hS₁Ksubset⟩ :=
        helperForTheorem_19_1_finiteFaces_imp_exists_finite_direction_reps
          (n := n) (C := K) hKprops.2.1
      have hposK' :
          ∀ d ∈ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) K d},
            ∃ d0 ∈ S₁K, ∃ t : ℝ, 0 < t ∧ d = t • d0 := by
        intro d hd
        exact hposK d hd
      have hEqK :
          mixedConvexHull (n := n)
              {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x}
              {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) K d}
            =
          mixedConvexHull (n := n)
              {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x}
              S₁K := by
        exact
          helperForTheorem_19_1_mixedConvexHull_directionSet_eq_of_posMul_cover
            (n := n)
            (S₀ := {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x})
            (S₁ := S₁K)
            (S₁' := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) K d})
            hS₁Ksubset hposK'
      have hKgen : IsFinitelyGeneratedConvexSet n K := by
        refine ⟨{x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x}, S₁K, hS₀Kfinite, hS₁Kfinite, ?_⟩
        calc
          K =
              mixedConvexHull (n := n)
                {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x}
                {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) K d} := hKeq
          _ =
              mixedConvexHull (n := n)
                {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) K x}
                S₁K := hEqK
      obtain ⟨SL, hSLfinite, hSLsubset, hLsubset⟩ :=
        helperForTheorem_19_1_submodule_subset_cone_of_finiteBasis (n := n) L
      have hgenC :
          IsFinitelyGeneratedConvexSet n C := by
        have hlift :=
          helperForTheorem_19_1_liftFiniteGeneration_from_projection
            (n := n) (C := C) hc hCne (L := L) (W := W) hWL (π := π)
            hker hrange hprojW hL
        have hlift' := hlift hKgen ⟨SL, hSLfinite, hSLsubset, hLsubset⟩
        simpa [K] using hlift'
      exact hgenC
    ·
      have hCempty : C = (∅ : Set (Fin n → ℝ)) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hCne ⟨x, hx⟩
      refine ⟨(∅ : Set (Fin n → ℝ)), (∅ : Set (Fin n → ℝ)),
        Set.finite_empty, Set.finite_empty, ?_⟩
      have hEq :
          mixedConvexHull (n := n) (∅ : Set (Fin n → ℝ)) (∅ : Set (Fin n → ℝ)) =
            (∅ : Set (Fin n → ℝ)) := by
        simpa using
          (mixedConvexHull_empty_points (n := n) (S₁ := (∅ : Set (Fin n → ℝ))))
      calc
        C = (∅ : Set (Fin n → ℝ)) := hCempty
        _ = mixedConvexHull (n := n) (∅ : Set (Fin n → ℝ)) (∅ : Set (Fin n → ℝ)) := by
            symm
            exact hEq

/-- Helper for Theorem 19.1: closed convex sets with finitely many faces are finitely generated. -/
lemma helperForTheorem_19_1_closed_finiteFaces_imp_finitelyGenerated
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) :
    (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite) →
      IsFinitelyGeneratedConvexSet n C := by
  exact
    helperForTheorem_19_1_closed_finiteFaces_imp_finitelyGenerated_via_linealitySplit
      (n := n) (C := C) hc

/-- Helper for Theorem 19.1: split the dot-product with a lifted vector. -/
lemma helperForTheorem_19_1_dotProduct_lift_split
    {n : ℕ} (x : Fin n → ℝ) (b : Fin (n + 1) → ℝ) :
    (Fin.cases (1 : ℝ) x) ⬝ᵥ b = b 0 + x ⬝ᵥ (fun i => b (Fin.succ i)) := by
  have hsum :
      (Fin.cases (1 : ℝ) x) ⬝ᵥ b =
        (1 : ℝ) * b 0 + ∑ i : Fin n, x i * b (Fin.succ i) := by
    simp [dotProduct, Fin.sum_univ_succ, Fin.cases]
  calc
    (Fin.cases (1 : ℝ) x) ⬝ᵥ b = (1 : ℝ) * b 0 + ∑ i : Fin n, x i * b (Fin.succ i) := hsum
    _ = b 0 + x ⬝ᵥ (fun i => b (Fin.succ i)) := by
      simp [dotProduct]

/-- Helper for Theorem 19.1: the lifting hyperplane is the set of points with first coordinate 1. -/
lemma helperForTheorem_19_1_liftingHyperplane_eq_set
    (n : ℕ) :
    liftingHyperplane n = {y : Fin (n + 1) → ℝ | y 0 = 1} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hy
    let x : Fin n → ℝ := fun i => y (Fin.succ i)
    have hy' : y = Fin.cases (1 : ℝ) x := by
      ext i
      cases i using Fin.cases with
      | zero => simpa [x] using hy
      | succ j => simp [x]
    exact ⟨x, hy'.symm⟩

/-- Helper for Theorem 19.1: preimage of a closed half-space under the lift map. -/
lemma helperForTheorem_19_1_lift_preimage_closedHalfSpaceLE
    {n : ℕ} (b : Fin (n + 1) → ℝ) (β : ℝ) :
    {x : Fin n → ℝ | (Fin.cases (1 : ℝ) x) ∈ closedHalfSpaceLE (n + 1) b β} =
      closedHalfSpaceLE n (fun i => b (Fin.succ i)) (β - b 0) := by
  ext x
  constructor
  · intro hx
    have hx' : (Fin.cases (1 : ℝ) x) ⬝ᵥ b ≤ β := by
      simpa [closedHalfSpaceLE] using hx
    have hsplit : (Fin.cases (1 : ℝ) x) ⬝ᵥ b =
        b 0 + x ⬝ᵥ (fun i => b (Fin.succ i)) :=
      helperForTheorem_19_1_dotProduct_lift_split (x := x) (b := b)
    have hx'' : x ⬝ᵥ (fun i => b (Fin.succ i)) ≤ β - b 0 := by
      have hle : b 0 + x ⬝ᵥ (fun i => b (Fin.succ i)) ≤ β := by
        simpa [hsplit] using hx'
      linarith
    simpa [closedHalfSpaceLE] using hx''
  · intro hx
    have hx' : x ⬝ᵥ (fun i => b (Fin.succ i)) ≤ β - b 0 := by
      simpa [closedHalfSpaceLE] using hx
    have hsplit : (Fin.cases (1 : ℝ) x) ⬝ᵥ b =
        b 0 + x ⬝ᵥ (fun i => b (Fin.succ i)) :=
      helperForTheorem_19_1_dotProduct_lift_split (x := x) (b := b)
    have hx'' : (Fin.cases (1 : ℝ) x) ⬝ᵥ b ≤ β := by
      have hle : b 0 + x ⬝ᵥ (fun i => b (Fin.succ i)) ≤ β := by
        linarith
      simpa [hsplit] using hle
    simpa [closedHalfSpaceLE] using hx''

/-- Helper for Theorem 19.1: the lifting hyperplane is polyhedral. -/
lemma helperForTheorem_19_1_liftingHyperplane_polyhedral
    (n : ℕ) : IsPolyhedralConvexSet (n + 1) (liftingHyperplane n) := by
  classical
  let e0 : Fin (n + 1) → ℝ := Pi.single (0 : Fin (n + 1)) (1 : ℝ)
  have hdot : ∀ y : Fin (n + 1) → ℝ, y ⬝ᵥ e0 = y 0 := by
    intro y
    simpa [e0] using (dotProduct_single_one (v := y) (i := (0 : Fin (n + 1))))
  let b : Fin 2 → Fin (n + 1) → ℝ := fun i =>
    Fin.cases e0 (fun _ => -e0) i
  let β : Fin 2 → ℝ := fun i =>
    Fin.cases (1 : ℝ) (fun _ => (-1 : ℝ)) i
  refine ⟨Fin 2, inferInstance, b, β, ?_⟩
  ext y
  constructor
  · intro hy
    have hy0 : y 0 = 1 := by
      have hy' : y ∈ liftingHyperplane n := hy
      have hy'' : y 0 = 1 := by
        have hset := helperForTheorem_19_1_liftingHyperplane_eq_set n
        have hyset : y ∈ {y : Fin (n + 1) → ℝ | y 0 = 1} := by
          simpa [hset] using hy'
        simpa using hyset
      exact hy''
    have hEq : y ⬝ᵥ e0 = 1 := by
      simpa [hdot y, hy0] using hy0
    have hineq :=
      (helperForText_19_0_2_eq_iff_le_and_neg_le (x := y) (a := e0) (α := (1 : ℝ))).1 hEq
    have hle1 : y ⬝ᵥ b 0 ≤ β 0 := by
      simpa [b, β] using hineq.1
    have hle2 : y ⬝ᵥ b 1 ≤ β 1 := by
      have hneg : y ⬝ᵥ (-e0) ≤ -1 := hineq.2
      simpa [b, β, -dotProduct_neg] using hneg
    refine Set.mem_iInter.2 ?_
    intro i
    fin_cases i
    · simpa using hle1
    · simpa using hle2
  · intro hy
    have hy' : y ∈ ⋂ i, closedHalfSpaceLE (n + 1) (b i) (β i) := hy
    have hle0 : y ⬝ᵥ b 0 ≤ β 0 := by
      have hmem := (Set.mem_iInter.1 hy') 0
      simpa [closedHalfSpaceLE] using hmem
    have hle1 : y ⬝ᵥ b 1 ≤ β 1 := by
      have hmem := (Set.mem_iInter.1 hy') 1
      simpa [closedHalfSpaceLE] using hmem
    have hEq : y ⬝ᵥ e0 = 1 := by
      have hEq' : (y ⬝ᵥ e0 ≤ (1 : ℝ)) ∧ (y ⬝ᵥ (-e0) ≤ (-1 : ℝ)) := by
        refine ⟨?_, ?_⟩
        · simpa [b, β] using hle0
        · simpa [b, β, -dotProduct_neg] using hle1
      exact (helperForText_19_0_2_eq_iff_le_and_neg_le (x := y) (a := e0) (α := (1 : ℝ))).2 hEq'
    have hy0 : y 0 = 1 := by
      simpa [hdot y] using hEq
    have hset := helperForTheorem_19_1_liftingHyperplane_eq_set n
    have : y ∈ {y : Fin (n + 1) → ℝ | y 0 = 1} := by
      simpa using hy0
    simpa [hset] using this

/-- Helper for Theorem 19.1: intersection of polyhedral convex sets is polyhedral. -/
lemma helperForTheorem_19_1_polyhedral_inter
    {n : ℕ} {C D : Set (Fin n → ℝ)}
    (hC : IsPolyhedralConvexSet n C) (hD : IsPolyhedralConvexSet n D) :
    IsPolyhedralConvexSet n (C ∩ D) := by
  classical
  rcases hC with ⟨ι, _hfinι, b, β, hCeq⟩
  rcases hD with ⟨κ, _hfinκ, c, γ, hDeq⟩
  let b' : Sum ι κ → Fin n → ℝ :=
    fun s =>
      match s with
      | Sum.inl i => b i
      | Sum.inr j => c j
  let β' : Sum ι κ → ℝ :=
    fun s =>
      match s with
      | Sum.inl i => β i
      | Sum.inr j => γ j
  refine ⟨Sum ι κ, inferInstance, b', β', ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxC, hxD⟩
    have hxC' : x ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
      simpa [hCeq] using hxC
    have hxD' : x ∈ ⋂ j, closedHalfSpaceLE n (c j) (γ j) := by
      simpa [hDeq] using hxD
    have hxC'' := Set.mem_iInter.1 hxC'
    have hxD'' := Set.mem_iInter.1 hxD'
    refine Set.mem_iInter.2 ?_
    intro s
    cases s with
    | inl i =>
        simpa [b', β'] using hxC'' i
    | inr j =>
        simpa [b', β'] using hxD'' j
  · intro hx
    have hx' := Set.mem_iInter.1 hx
    have hxC' : x ∈ ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
      refine Set.mem_iInter.2 ?_
      intro i
      have hxi : x ∈ closedHalfSpaceLE n (b' (Sum.inl i)) (β' (Sum.inl i)) := hx' (Sum.inl i)
      simpa [b', β'] using hxi
    have hxD' : x ∈ ⋂ j, closedHalfSpaceLE n (c j) (γ j) := by
      refine Set.mem_iInter.2 ?_
      intro j
      have hxi : x ∈ closedHalfSpaceLE n (b' (Sum.inr j)) (β' (Sum.inr j)) := hx' (Sum.inr j)
      simpa [b', β'] using hxi
    have hxC : x ∈ C := by
      simpa [hCeq] using hxC'
    have hxD : x ∈ D := by
      simpa [hDeq] using hxD'
    exact ⟨hxC, hxD⟩

/-- Helper for Theorem 19.1: pull back a polyhedral set under the lift map. -/
lemma helperForTheorem_19_1_lift_preimage_polyhedral
    {n : ℕ} {K : Set (Fin (n + 1) → ℝ)}
    (hK : IsPolyhedralConvexSet (n + 1) K) :
    IsPolyhedralConvexSet n {x : Fin n → ℝ | (Fin.cases (1 : ℝ) x) ∈ K} := by
  classical
  rcases hK with ⟨ι, _hfin, b, β, hKeq⟩
  let b' : ι → Fin n → ℝ := fun i => fun j => b i (Fin.succ j)
  let β' : ι → ℝ := fun i => β i - b i 0
  refine ⟨ι, inferInstance, b', β', ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : (Fin.cases (1 : ℝ) x) ∈ ⋂ i, closedHalfSpaceLE (n + 1) (b i) (β i) := by
      simpa [hKeq] using hx
    have hx'' := Set.mem_iInter.1 hx'
    refine Set.mem_iInter.2 ?_
    intro i
    have hxi : (Fin.cases (1 : ℝ) x) ∈ closedHalfSpaceLE (n + 1) (b i) (β i) := hx'' i
    have hxpre :
        x ∈ {x : Fin n → ℝ |
          (Fin.cases (1 : ℝ) x) ∈ closedHalfSpaceLE (n + 1) (b i) (β i)} := by
      simpa using hxi
    have hxpre' :
        x ∈ closedHalfSpaceLE n (fun j => b i (Fin.succ j)) (β i - b i 0) := by
      simpa [helperForTheorem_19_1_lift_preimage_closedHalfSpaceLE] using hxpre
    simpa [b', β'] using hxpre'
  · intro hx
    have hx' : x ∈ ⋂ i, closedHalfSpaceLE n (b' i) (β' i) := hx
    have hx'' := Set.mem_iInter.1 hx'
    have hxK' : (Fin.cases (1 : ℝ) x) ∈ ⋂ i, closedHalfSpaceLE (n + 1) (b i) (β i) := by
      refine Set.mem_iInter.2 ?_
      intro i
      have hxi : x ∈ closedHalfSpaceLE n (b' i) (β' i) := hx'' i
      have hxpre :
          x ∈ {x : Fin n → ℝ |
            (Fin.cases (1 : ℝ) x) ∈ closedHalfSpaceLE (n + 1) (b i) (β i)} := by
        simpa [b', β', (helperForTheorem_19_1_lift_preimage_closedHalfSpaceLE (n := n)
          (b := b i) (β := β i)).symm] using hxi
      simpa using hxpre
    have hxK : (Fin.cases (1 : ℝ) x) ∈ K := by
      simpa [hKeq] using hxK'
    exact hxK

/-- Helper for Theorem 19.1: polar of a generated cone is a half-space intersection. -/
lemma helperForTheorem_19_1_cone_polar_eq_iInter_halfspaces
    {m : ℕ} {T : Set (Fin m → ℝ)} :
    {xStar : Fin m → ℝ | ∀ x ∈ cone m T, dotProduct x xStar ≤ 0} =
      ⋂ t ∈ T, closedHalfSpaceLE m t 0 := by
  ext xStar
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro t
    refine Set.mem_iInter.2 ?_
    intro ht
    have ht_ray : t ∈ ray m T :=
      mem_ray_of_mem (n := m) (S := T) (x := t) ht
    have ht_cone : t ∈ cone m T := by
      have ht' : t ∈ convexHull ℝ (ray m T) :=
        (subset_convexHull (𝕜 := ℝ) (s := ray m T)) ht_ray
      simpa [cone, conv] using ht'
    have hdot : dotProduct t xStar ≤ 0 := hx t ht_cone
    have hdot' : dotProduct xStar t ≤ 0 := by
      simpa [dotProduct_comm] using hdot
    simpa [closedHalfSpaceLE] using hdot'
  · intro hx
    have hx' : ∀ t ∈ T, dotProduct t xStar ≤ 0 := by
      intro t ht
      have htmem : xStar ∈ ⋂ t ∈ T, closedHalfSpaceLE m t 0 := hx
      have htmem' : xStar ∈ closedHalfSpaceLE m t 0 := by
        have h1 := Set.mem_iInter.1 htmem t
        exact (Set.mem_iInter.1 h1 ht)
      have htmem'' : dotProduct xStar t ≤ 0 := by
        simpa [closedHalfSpaceLE] using htmem'
      simpa [dotProduct_comm] using htmem''
    refine Set.mem_setOf.2 ?_
    intro x hxcone
    have hconv :
        Convex ℝ {x : Fin m → ℝ | dotProduct x xStar ≤ 0} := by
      simpa [closedHalfSpaceLE] using
        (convex_dotProduct_le (n := m) (b := xStar) (β := 0))
    have hray :
        ray m T ⊆ {x : Fin m → ℝ | dotProduct x xStar ≤ 0} := by
      intro r hr
      rcases ray_mem_decompose (n := m) (S := T) (v := r) hr with rfl | hdecomp
      · simp
      · rcases hdecomp with ⟨s, hsT, t, ht, rfl⟩
        have hs : dotProduct s xStar ≤ 0 := hx' s hsT
        have hmul : t * dotProduct s xStar ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ht hs
        have hdot : dotProduct (t • s) xStar ≤ 0 := by
          simpa [smul_dotProduct] using hmul
        simpa using hdot
    have hsubset :
        cone m T ⊆ {x : Fin m → ℝ | dotProduct x xStar ≤ 0} := by
      have hsubset' :
          conv (ray m T) ⊆ {x : Fin m → ℝ | dotProduct x xStar ≤ 0} :=
        convexHull_min hray hconv
      simpa [cone, conv] using hsubset'
    exact hsubset hxcone

/-- Helper for Theorem 19.1: choose a nonnegative `t` so `a + t * b` is positive. -/
lemma helperForTheorem_19_1_exists_t_pos_of_neg_offset_pos_slope
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 < b) :
    ∃ t : ℝ, 0 ≤ t ∧ 0 < a + t * b := by
  refine ⟨(-a) / b + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ (-a) / b := by
      have hnonneg_a : 0 ≤ -a := by
        exact neg_nonneg.mpr ha
      exact div_nonneg hnonneg_a (le_of_lt hb)
    linarith
  · have hbne : b ≠ 0 := ne_of_gt hb
    have hmul : (-a) / b * b = -a := by
      field_simp [hbne]
    have hcalc : a + ((-a) / b + 1) * b = b := by
      calc
        a + ((-a) / b + 1) * b
            = a + (-a) / b * b + 1 * b := by
                ring
        _ = a + (-a) + b := by
                simp [hmul, add_comm]
        _ = b := by ring
    have hpos : 0 < b := hb
    simpa [hcalc] using hpos

/-- Helper for Theorem 19.1: polar of a mixed convex hull is an intersection of half-spaces. -/
lemma helperForTheorem_19_1_polar_of_mixedConvexHull_eq_iInter
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)} (hS₀ne : S₀.Nonempty) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ mixedConvexHull (n := n) S₀ S₁, dotProduct x xStar ≤ 0} =
      (⋂ s ∈ S₀, closedHalfSpaceLE n s 0) ∩
        (⋂ d ∈ S₁, closedHalfSpaceLE n d 0) := by
  classical
  ext xStar
  constructor
  · intro hx
    refine Set.mem_inter ?_ ?_
    · refine Set.mem_iInter.2 ?_
      intro s
      refine Set.mem_iInter.2 ?_
      intro hs
      have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁ := by
        change (0 : Fin n → ℝ) ∈ Set.insert 0 (rayNonneg n S₁)
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      have hs_add : s + 0 ∈ S₀ + ray n S₁ := Set.add_mem_add hs h0ray
      have hsubset :
          S₀ + ray n S₁ ⊆ mixedConvexHull (n := n) S₀ S₁ :=
        add_ray_subset_mixedConvexHull (n := n) S₀ S₁
      have hs_mem : s ∈ mixedConvexHull (n := n) S₀ S₁ := by
        have hs_add' : s ∈ S₀ + ray n S₁ := by
          simpa using hs_add
        exact hsubset hs_add'
      have hdot : dotProduct s xStar ≤ 0 := hx s hs_mem
      have hdot' : dotProduct xStar s ≤ 0 := by
        simpa [dotProduct_comm] using hdot
      simpa [closedHalfSpaceLE] using hdot'
    · refine Set.mem_iInter.2 ?_
      intro d
      refine Set.mem_iInter.2 ?_
      intro hd
      rcases hS₀ne with ⟨s0, hs0⟩
      have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁ := by
        change (0 : Fin n → ℝ) ∈ Set.insert 0 (rayNonneg n S₁)
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      have hs0_add : s0 + 0 ∈ S₀ + ray n S₁ := Set.add_mem_add hs0 h0ray
      have hsubset :
          S₀ + ray n S₁ ⊆ mixedConvexHull (n := n) S₀ S₁ :=
        add_ray_subset_mixedConvexHull (n := n) S₀ S₁
      have hs0_mem : s0 ∈ mixedConvexHull (n := n) S₀ S₁ := by
        have hs0_add' : s0 ∈ S₀ + ray n S₁ := by
          simpa using hs0_add
        exact hsubset hs0_add'
      have ha : dotProduct s0 xStar ≤ 0 := hx s0 hs0_mem
      have hforall :
          ∀ t : ℝ, 0 ≤ t → dotProduct (s0 + t • d) xStar ≤ 0 := by
        intro t ht
        have ht_ray : t • d ∈ ray n S₁ := by
          refine (Set.mem_insert_iff).2 ?_
          refine Or.inr ?_
          exact ⟨d, hd, t, ht, rfl⟩
        have hs0t : s0 + t • d ∈ S₀ + ray n S₁ :=
          Set.add_mem_add hs0 ht_ray
        have hs0t' : s0 + t • d ∈ mixedConvexHull (n := n) S₀ S₁ :=
          hsubset hs0t
        exact hx _ hs0t'
      have hd_le : dotProduct d xStar ≤ 0 := by
        by_contra hpos
        have hpos' : 0 < dotProduct d xStar := lt_of_not_ge (by simpa using hpos)
        obtain ⟨t, ht0, htpos⟩ :=
          helperForTheorem_19_1_exists_t_pos_of_neg_offset_pos_slope
            (a := dotProduct s0 xStar) (b := dotProduct d xStar) ha hpos'
        have hdot :
            dotProduct (s0 + t • d) xStar =
              dotProduct s0 xStar + t * dotProduct d xStar := by
          have hsum :
              dotProduct (s0 + t • d) xStar =
                dotProduct s0 xStar + dotProduct (t • d) xStar := by
            simpa using (add_dotProduct s0 (t • d) xStar)
          have hsmul : dotProduct (t • d) xStar = t * dotProduct d xStar := by
            simp [smul_dotProduct]
          calc
            dotProduct (s0 + t • d) xStar
                = dotProduct s0 xStar + dotProduct (t • d) xStar := hsum
            _ = dotProduct s0 xStar + t * dotProduct d xStar := by
                simp [hsmul]
        have hle : dotProduct (s0 + t • d) xStar ≤ 0 := hforall t ht0
        have hgt : 0 < dotProduct s0 xStar + t * dotProduct d xStar := by
          simpa [hdot] using htpos
        exact (not_le_of_gt hgt) (by simpa [hdot] using hle)
      have hd_le' : dotProduct xStar d ≤ 0 := by
        simpa [dotProduct_comm] using hd_le
      simpa [closedHalfSpaceLE] using hd_le'
  · intro hx
    rcases hx with ⟨hxS₀, hxS₁⟩
    have hxS₀' : ∀ s ∈ S₀, dotProduct s xStar ≤ 0 := by
      intro s hs
      have hs_mem : xStar ∈ ⋂ s ∈ S₀, closedHalfSpaceLE n s 0 := hxS₀
      have hs_mem' : xStar ∈ closedHalfSpaceLE n s 0 := by
        have h1 := Set.mem_iInter.1 hs_mem s
        exact (Set.mem_iInter.1 h1 hs)
      have hs_le : dotProduct xStar s ≤ 0 := by
        simpa [closedHalfSpaceLE] using hs_mem'
      simpa [dotProduct_comm] using hs_le
    have hxS₁' : ∀ d ∈ S₁, dotProduct d xStar ≤ 0 := by
      intro d hd
      have hd_mem : xStar ∈ ⋂ d ∈ S₁, closedHalfSpaceLE n d 0 := hxS₁
      have hd_mem' : xStar ∈ closedHalfSpaceLE n d 0 := by
        have h1 := Set.mem_iInter.1 hd_mem d
        exact (Set.mem_iInter.1 h1 hd)
      have hd_le : dotProduct xStar d ≤ 0 := by
        simpa [closedHalfSpaceLE] using hd_mem'
      simpa [dotProduct_comm] using hd_le
    let H : Set (Fin n → ℝ) := {x : Fin n → ℝ | dotProduct x xStar ≤ 0}
    have hconv : Convex ℝ H := by
      simpa [H, closedHalfSpaceLE] using
        (convex_dotProduct_le (n := n) (b := xStar) (β := 0))
    have hray : ray n S₁ ⊆ H := by
      intro r hr
      rcases ray_mem_decompose (n := n) (S := S₁) (v := r) hr with rfl | hdecomp
      · simp [H]
      · rcases hdecomp with ⟨d, hdS₁, t, ht, rfl⟩
        have hd : dotProduct d xStar ≤ 0 := hxS₁' d hdS₁
        have hmul : t * dotProduct d xStar ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos ht hd
        have hdot : dotProduct (t • d) xStar ≤ 0 := by
          simpa [smul_dotProduct] using hmul
        simpa [H] using hdot
    have hsubset : S₀ + ray n S₁ ⊆ H := by
      intro x hx'
      rcases (Set.mem_add).1 hx' with ⟨s, hs, r, hr, rfl⟩
      have hs' : dotProduct s xStar ≤ 0 := hxS₀' s hs
      have hr' : dotProduct r xStar ≤ 0 := by
        have hrH : r ∈ H := hray hr
        simpa [H] using hrH
      have hsum : dotProduct (s + r) xStar ≤ 0 := by
        have hdot :
            dotProduct (s + r) xStar =
              dotProduct s xStar + dotProduct r xStar := by
          simpa using (add_dotProduct s r xStar)
        have hsum' : dotProduct s xStar + dotProduct r xStar ≤ 0 := by
          linarith
        simpa [hdot] using hsum'
      simpa [H] using hsum
    have hsubset_conv : conv (S₀ + ray n S₁) ⊆ H := convexHull_min hsubset hconv
    have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁
    refine Set.mem_setOf.2 ?_
    intro x hx'
    have hx'' : x ∈ conv (S₀ + ray n S₁) := by
      simpa [hrepr.1] using hx'
    have hxH : x ∈ H := hsubset_conv hx''
    simpa [H] using hxH

/-- Helper for Theorem 19.1: simplicial cones are closed. -/
lemma helperForTheorem_19_1_isClosed_simplicialCone_of_linearIndependent
    {m k : ℕ} (v : Fin k → Fin m → ℝ) (hlin : LinearIndependent ℝ v) :
    IsClosed {x : Fin m → ℝ | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} := by
  classical
  let F : (Fin k → ℝ) →ₗ[ℝ] (Fin m → ℝ) := Fintype.linearCombination ℝ v
  have hclosed_nonneg : IsClosed {c : Fin k → ℝ | ∀ i, 0 ≤ c i} := by
    have hclosed_iInter :
        IsClosed (⋂ i, {c : Fin k → ℝ | (0 : ℝ) ≤ c i}) := by
      refine isClosed_iInter ?_
      intro i
      have hclosed_i :
          IsClosed {c : Fin k → ℝ | (0 : ℝ) ≤ c i} := by
        simpa using
          (isClosed_le (f := fun _ : Fin k → ℝ => (0 : ℝ))
            (g := fun c : Fin k → ℝ => c i) continuous_const (continuous_apply i))
      exact hclosed_i
    have hEq :
        {c : Fin k → ℝ | ∀ i, 0 ≤ c i} =
          ⋂ i, {c : Fin k → ℝ | (0 : ℝ) ≤ c i} := by
      ext c
      constructor
      · intro hc
        refine Set.mem_iInter.2 ?_
        intro i
        exact hc i
      · intro hc
        have hc' := Set.mem_iInter.1 hc
        intro i
        exact hc' i
    simpa [hEq] using hclosed_iInter
  have hker : LinearMap.ker F = ⊥ := by
    have hinj : Function.Injective F :=
      LinearIndependent.fintypeLinearCombination_injective hlin
    exact LinearMap.ker_eq_bot_of_injective hinj
  have hclosedEmbedding : IsClosedEmbedding F :=
    LinearMap.isClosedEmbedding_of_injective (f := F) hker
  have hclosed_image :
      IsClosed (F '' {c : Fin k → ℝ | ∀ i, 0 ≤ c i}) :=
    (IsClosedEmbedding.isClosedMap hclosedEmbedding) _ hclosed_nonneg
  have hEq :
      {x : Fin m → ℝ | ∃ c : Fin k → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i} =
        F '' {c : Fin k → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨c, hc, hxsum⟩
      refine ⟨c, hc, ?_⟩
      have hxsum' : F c = x := by
        simpa [F, Fintype.linearCombination_apply] using hxsum.symm
      exact hxsum'
    · intro hx
      rcases hx with ⟨c, hc, hxF⟩
      refine ⟨c, hc, ?_⟩
      have hxF' : x = F c := hxF.symm
      simpa [F, Fintype.linearCombination_apply] using hxF'
  simpa [hEq] using hclosed_image

/-- Helper for Theorem 19.1: finitely generated cones are closed. -/
lemma helperForTheorem_19_1_isClosed_cone_of_finite_generators
    {m : ℕ} {T : Set (Fin m → ℝ)} (hT : Set.Finite T) :
    IsClosed (cone m T) := by
  classical
  by_cases hTne : T.Nonempty
  ·
    let ι0 : Type := {t : Fin m → ℝ // t ∈ T}
    haveI : Fintype ι0 := hT.fintype
    let ι : Type :=
      Σ k : Fin (m + 1), {v : Fin k → ι0 // LinearIndependent ℝ (fun i => (v i).1)}
    let S : ι → Set (Fin m → ℝ) := fun i =>
      {x : Fin m → ℝ | ∃ c : Fin i.1 → ℝ, (∀ j, 0 ≤ c j) ∧
        x = ∑ j, c j • (i.2.1 j).1}
    have hEq : cone m T = ⋃ i, S i := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ convexConeGenerated m T := by
          have hcone_eq := cone_eq_convexConeGenerated (n := m) (S₁ := T)
          simpa [hcone_eq] using hx
        rcases
            mem_convexConeGenerated_imp_exists_nonnegLinearCombination_le
              (n := m) (T := T) hTne hx' with
          ⟨k, hk_le, v, c, hvT, hc, hxsum⟩
        by_cases hx0 : x = 0
        · subst hx0
          have hk0 : (0 : Nat) < m + 1 := Nat.succ_pos m
          let k0 : Fin (m + 1) := ⟨0, hk0⟩
          let v0 : Fin 0 → ι0 := fun i => (Fin.elim0 i)
          have hlin0 : LinearIndependent ℝ (fun i => (v0 i).1) := by
            simpa using
              (linearIndependent_empty_type (R := ℝ)
                (v := fun i : Fin 0 => (v0 i).1))
          let i0 : ι := ⟨k0, ⟨v0, hlin0⟩⟩
          refine Set.mem_iUnion.2 ?_
          refine ⟨i0, ?_⟩
          refine ⟨(fun i : Fin 0 => 0), ?_, ?_⟩
          · intro i
            simp
          · simp
        ·
          rcases
              exists_linearIndependent_nonnegLinearCombination_subfamily
                (n := m) (k := k) (v := v) (c := c) (hc := hc) (hx := hxsum) hx0 with
            ⟨k', hk'_le, e, c', hc', hlin, hxsum'⟩
          have hk'le : k' ≤ m := le_trans hk'_le hk_le
          have hk'lt : k' < m + 1 := Nat.lt_succ_of_le hk'le
          let kfin : Fin (m + 1) := ⟨k', hk'lt⟩
          let v' : Fin k' → ι0 := fun j => ⟨v (e j), hvT (e j)⟩
          have hlin' : LinearIndependent ℝ (fun j => (v' j).1) := by
            simpa [v'] using hlin
          let idx : ι := ⟨kfin, ⟨v', hlin'⟩⟩
          refine Set.mem_iUnion.2 ?_
          refine ⟨idx, ?_⟩
          refine ⟨c', hc', ?_⟩
          simpa [idx, v'] using hxsum'
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
        rcases hx with ⟨c, hc, hxsum⟩
        let d : Fin i.1 → Fin m → ℝ := fun j => (i.2.1 j).1
        have hd : ∀ j, d j ∈ ray m T := by
          intro j
          have hmem : d j ∈ T := (i.2.1 j).2
          exact mem_ray_of_mem (n := m) (S := T) (x := d j) hmem
        have hxcone :
            (∑ j, c j • d j) ∈ cone m T :=
          sum_smul_mem_cone_of_nonneg_mem_ray
            (n := m) (m := i.1) (S₁ := T) d c hd hc
        have hxsum' : x = ∑ j, c j • d j := by
          simpa [d] using hxsum
        simpa [hxsum'] using hxcone
    have hclosed : ∀ i, IsClosed (S i) := by
      intro i
      have hclosed_i :
          IsClosed {x : Fin m → ℝ | ∃ c : Fin i.1 → ℝ, (∀ j, 0 ≤ c j) ∧
            x = ∑ j, c j • (i.2.1 j).1} :=
        helperForTheorem_19_1_isClosed_simplicialCone_of_linearIndependent
          (m := m) (k := i.1) (v := fun j => (i.2.1 j).1) (hlin := i.2.2)
      simpa [S] using hclosed_i
    have hclosedUnion : IsClosed (⋃ i, S i) :=
      isClosed_iUnion_of_finite (fun i => hclosed i)
    simpa [hEq] using hclosedUnion
  ·
    have hTempty : T = (∅ : Set (Fin m → ℝ)) :=
      (Set.not_nonempty_iff_eq_empty).1 hTne
    subst hTempty
    have hcone :
        cone m (∅ : Set (Fin m → ℝ)) = ({0} : Set (Fin m → ℝ)) := by
      have hconv :
          convexConeGenerated m (∅ : Set (Fin m → ℝ)) =
            ({0} : Set (Fin m → ℝ)) := by
        simpa using (convexConeGenerated_empty (n := m))
      have hcone_eq := cone_eq_convexConeGenerated (n := m) (S₁ := (∅ : Set (Fin m → ℝ)))
      simpa [hconv] using hcone_eq
    simpa [hcone] using (isClosed_singleton : IsClosed ({0} : Set (Fin m → ℝ)))

/-- Helper for Theorem 19.1: the singleton `{0}` is polyhedral. -/
lemma helperForTheorem_19_1_zero_set_polyhedral {m : ℕ} :
    IsPolyhedralConvexSet m ({0} : Set (Fin m → ℝ)) := by
  classical
  let ι : Type := Sum (Fin m) (Fin m)
  let b : ι → Fin m → ℝ := fun s =>
    match s with
    | Sum.inl i => Pi.single i (1 : ℝ)
    | Sum.inr i => -Pi.single i (1 : ℝ)
  let β : ι → ℝ := fun _ => 0
  refine ⟨ι, inferInstance, b, β, ?_⟩
  ext x
  constructor
  · intro hx
    have hx0 : x = 0 := by
      simpa [Set.mem_singleton_iff] using hx
    subst hx0
    refine Set.mem_iInter.2 ?_
    intro s
    simp [closedHalfSpaceLE, b, β]
  · intro hx
    have hx' : ∀ s : ι, dotProduct x (b s) ≤ 0 := by
      intro s
      have hxmem : x ∈ ⋂ s, closedHalfSpaceLE m (b s) (β s) := hx
      have hxmem' := Set.mem_iInter.1 hxmem s
      simpa [closedHalfSpaceLE, β] using hxmem'
    have hxcoord : ∀ i : Fin m, x i = 0 := by
      intro i
      have hle : x i ≤ 0 := by
        have h := hx' (Sum.inl i)
        simpa [b, dotProduct_single, mul_one] using h
      have hge : 0 ≤ x i := by
        have h := hx' (Sum.inr i)
        have hneg : -(x i) ≤ 0 := by
          simpa [b, dotProduct_neg, dotProduct_single, mul_one] using h
        have hneg' : -(x i) ≤ -(0 : ℝ) := by
          simpa using hneg
        have hge' : (0 : ℝ) ≤ x i := (neg_le_neg_iff).1 hneg'
        simpa using hge'
      exact le_antisymm hle hge
    have hx0 : x = 0 := by
      ext i
      exact hxcoord i
    simpa [Set.mem_singleton_iff] using hx0


end Section19
end Chap19
