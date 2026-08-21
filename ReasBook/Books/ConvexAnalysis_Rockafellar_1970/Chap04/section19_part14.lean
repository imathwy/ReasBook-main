/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part13

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Theorem 19.7: for nonempty `C`, adjoining `0` to the cone hull does not change
the closure. -/
lemma helperForTheorem_19_7_closure_convexConeGenerated_eq_closure_hull
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) :
    closure (convexConeGenerated n C) =
      closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
  have hzero_rec : (0 : Fin n → ℝ) ∈ Set.recessionCone C := by
    intro x hx t ht
    simpa [zero_smul, add_zero] using hx
  have hzero_mem_closure_hull :
      (0 : Fin n → ℝ) ∈ closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
    helperForTheorem_19_6_recessionDirection_mem_closure_convexConeHull_of_nonempty
      (d := n) (C := C) hCne hzero_rec
  have hKdef :
      convexConeGenerated n C =
        ({0} : Set (Fin n → ℝ)) ∪ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      have hx' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := by
        simpa [convexConeGenerated, Set.mem_insert_iff] using hx
      rcases hx' with hx0 | hxHull
      · have hx0_singleton : x ∈ ({0} : Set (Fin n → ℝ)) := by
          simpa [Set.mem_singleton_iff] using hx0
        exact Or.inl hx0_singleton
      · exact Or.inr hxHull
    · intro hx
      rcases hx with hx0 | hxHull
      · have hx0' : x = 0 := by simpa [Set.mem_singleton_iff] using hx0
        exact (Set.mem_insert_iff).2 (Or.inl hx0')
      · exact (Set.mem_insert_iff).2 (Or.inr hxHull)
  calc
    closure (convexConeGenerated n C)
        = closure (({0} : Set (Fin n → ℝ)) ∪ (ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
          simp [hKdef]
    _ = closure ({0} : Set (Fin n → ℝ)) ∪ closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
          simpa using
            (closure_union
              (s := ({0} : Set (Fin n → ℝ)))
              (t := (ConvexCone.hull ℝ C : Set (Fin n → ℝ))))
    _ = closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
          apply Set.union_eq_right.mpr
          intro x hx
          have hx0 : x = 0 := by
            have hx' : x ∈ ({0} : Set (Fin n → ℝ)) := by
              simpa [closure_singleton] using hx
            simpa [Set.mem_singleton_iff] using hx'
          simpa [hx0] using hzero_mem_closure_hull

/-- Helper for Theorem 19.7: the Euclidean-coordinate transport of the recession cone term
equals the ambient-space recession cone. -/
lemma helperForTheorem_19_7_recessionCone_transport_eq
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
    Set.image e (Set.recessionCone (Set.image e.symm C)) = Set.recessionCone C := by
  intro e
  have hrec :
      Set.recessionCone (Set.image e.symm C) = Set.image e.symm (Set.recessionCone C) := by
    simpa using (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
  calc
    Set.image e (Set.recessionCone (Set.image e.symm C))
        = Set.image e (Set.image e.symm (Set.recessionCone C)) := by
            simp [hrec]
    _ = Set.recessionCone C := by
          simp [Set.image_image]

/-- Helper for Theorem 19.7: rewriting the positive-scaling union from nested existential
indices to a subtype index. -/
lemma helperForTheorem_19_7_iUnion_pos_subtype_rewrite
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) =
      ⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨t, ht⟩
    rcases Set.mem_iUnion.1 ht with ⟨htpos, hxt⟩
    exact Set.mem_iUnion.2 ⟨⟨t, htpos⟩, hxt⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨lam, hxl⟩
    exact Set.mem_iUnion.2 ⟨(lam : ℝ), Set.mem_iUnion.2 ⟨lam.property, hxl⟩⟩

/-- Helper for Theorem 19.7: if `0 ∈ C = mixedConvexHull S₀ S₁`, then every direction generator
belongs to `C`. -/
lemma helperForTheorem_19_7_originMem_directions_subset_carrier
    {n : ℕ} {C S₀ S₁ : Set (Fin n → ℝ)}
    (hCeq : C = mixedConvexHull (n := n) S₀ S₁)
    (hC0 : (0 : Fin n → ℝ) ∈ C) :
    S₁ ⊆ C := by
  intro dir hdir
  have hdir_rec_mixed : dir ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) :=
    helperForTheorem_19_6_directions_subset_recessionCone_mixedConvexHull
      (d := n) (S₀ := S₀) (S₁ := S₁) hdir
  have hdir_rec : dir ∈ Set.recessionCone C := by
    simpa [hCeq] using hdir_rec_mixed
  have h1nonneg : (0 : ℝ) ≤ 1 := by
    norm_num
  have hmem : (0 : Fin n → ℝ) + (1 : ℝ) • dir ∈ C :=
    hdir_rec (x := (0 : Fin n → ℝ)) hC0 (t := (1 : ℝ)) h1nonneg
  simpa using hmem

/-- Helper for Theorem 19.7: if the origin belongs to C, then every recession direction of C
lies in C. -/
lemma helperForTheorem_19_7_recessionCone_subset_of_origin_mem
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC0 : (0 : Fin n → ℝ) ∈ C) :
    Set.recessionCone C ⊆ C := by
  intro dir hdir
  have h1nonneg : (0 : ℝ) ≤ 1 := by
    norm_num
  have hmem : (0 : Fin n → ℝ) + (1 : ℝ) • dir ∈ C :=
    hdir (x := (0 : Fin n → ℝ)) hC0 (t := (1 : ℝ)) h1nonneg
  simpa using hmem

/-- Helper for Theorem 19.7: with finite mixed-hull data and `0 ∈ C`, the generated cone of `C`
coincides with the finite cone generated by points and directions. -/
lemma helperForTheorem_19_7_originMem_convexConeGenerated_eq_finiteCone
    {n : ℕ} {C S₀ S₁ : Set (Fin n → ℝ)}
    (hCeq : C = mixedConvexHull (n := n) S₀ S₁)
    (hS₀fin : Set.Finite S₀)
    (hS₁fin : Set.Finite S₁)
    (hC0 : (0 : Fin n → ℝ) ∈ C) :
    convexConeGenerated n C = cone n (S₀ ∪ S₁) := by
  have hCne : C.Nonempty := ⟨0, hC0⟩
  have hMixed_nonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [hCeq] using hC0
  have hS₀ne : S₀.Nonempty :=
    helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
      (n := n) (S₀ := S₀) (S₁ := S₁) hMixed_nonempty
  have hclosure_hull_eq_cone :
      closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) = cone n (S₀ ∪ S₁) := by
    calc
      closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ)))
          = closure ((ConvexCone.hull ℝ (mixedConvexHull (n := n) S₀ S₁) : Set (Fin n → ℝ))) := by
              simp [hCeq]
      _ = cone n (S₀ ∪ S₁) :=
        helperForTheorem_19_6_closure_convexConeHull_eq_cone_of_finiteMixedData
          (d := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hclosureK_eq_cone :
      closure (convexConeGenerated n C) = cone n (S₀ ∪ S₁) := by
    calc
      closure (convexConeGenerated n C)
          = closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
              helperForTheorem_19_7_closure_convexConeGenerated_eq_closure_hull
                (n := n) (C := C) hCne
      _ = cone n (S₀ ∪ S₁) := hclosure_hull_eq_cone
  have hS₀_subset_C : S₀ ⊆ C := by
    intro x hx
    have hxMixed : x ∈ mixedConvexHull (n := n) S₀ S₁ :=
      helperForTheorem_19_6_points_subset_mixedConvexHull
        (d := n) (S₀ := S₀) (S₁ := S₁) hx
    simpa [hCeq] using hxMixed
  have hS₁_subset_C : S₁ ⊆ C :=
    helperForTheorem_19_7_originMem_directions_subset_carrier
      (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCeq hC0
  have hUnion_subset_C : S₀ ∪ S₁ ⊆ C := by
    intro x hx
    rcases hx with hx0 | hx1
    · exact hS₀_subset_C hx0
    · exact hS₁_subset_C hx1
  have hUnion_subset_hullC : S₀ ∪ S₁ ⊆ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := by
    intro x hx
    exact ConvexCone.subset_hull (hUnion_subset_C hx)
  have hHull_subset :
      (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin n → ℝ)) ⊆ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) :=
    ConvexCone.hull_min (s := S₀ ∪ S₁) (C := ConvexCone.hull ℝ C) hUnion_subset_hullC
  have hcone_subset_K : cone n (S₀ ∪ S₁) ⊆ convexConeGenerated n C := by
    intro x hx
    have hx' : x ∈ convexConeGenerated n (S₀ ∪ S₁) := by
      simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₀ ∪ S₁)] using hx
    have hx'' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin n → ℝ)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hx'
    rcases hx'' with hx0 | hxHull
    · subst hx0
      exact Set.mem_insert (0 : Fin n → ℝ) (ConvexCone.hull ℝ C : Set (Fin n → ℝ))
    · have hxHullC : x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := hHull_subset hxHull
      have hxK : x = 0 ∨ x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := Or.inr hxHullC
      simpa [convexConeGenerated, Set.mem_insert_iff] using hxK
  have hK_subset_cone : convexConeGenerated n C ⊆ cone n (S₀ ∪ S₁) := by
    intro x hx
    have hxcl : x ∈ closure (convexConeGenerated n C) := subset_closure hx
    simpa [hclosureK_eq_cone] using hxcl
  exact Set.Subset.antisymm hK_subset_cone hcone_subset_K

/-- Theorem 19.7: Let `C` be a non-empty polyhedral convex set, and let `K` be the closure of the
convex cone generated by `C`. Then `K` is a polyhedral convex cone, and
`K = ⋃ {λ C | λ > 0 or λ = 0^+}`. -/
theorem polyhedralConvexCone_closure_convexConeGenerated
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    C.Nonempty →
    IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet n (closure (convexConeGenerated n C)) ∧
        IsConeSet n (closure (convexConeGenerated n C)) ∧
        closure (convexConeGenerated n C) =
          (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
  intro hCne hCpoly
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hCclosed : IsClosed C :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n) (C := C) hCpoly).1
  have hpolyClosureHull :
      IsPolyhedralConvexSet n (closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ)))) :=
    helperForTheorem_19_6_polyhedral_closure_convexConeHull_of_polyhedral
      (d := n) (S := C) hCne hCpoly
  have hclosure_eq_hull :
      closure (convexConeGenerated n C) =
        closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
    helperForTheorem_19_7_closure_convexConeGenerated_eq_closure_hull
      (n := n) (C := C) hCne
  have hpolyK : IsPolyhedralConvexSet n (closure (convexConeGenerated n C)) := by
    simpa [hclosure_eq_hull] using hpolyClosureHull
  have hconeBase : IsConeSet n (convexConeGenerated n C) :=
    (isConvexCone_convexConeGenerated (n := n) (S₁ := C)).1
  have hconeClosure : IsConeSet n (closure (convexConeGenerated n C)) :=
    cor11_7_2_isConeSet_closure (n := n) (K := convexConeGenerated n C) hconeBase
  have hrepr :
      closure (convexConeGenerated n C) =
        (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
    by_cases hC0 : (0 : Fin n → ℝ) ∈ C
    · have hTFAE :
        [IsPolyhedralConvexSet n C,
          (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
          IsFinitelyGeneratedConvexSet n C].TFAE :=
        polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
      have hCfg : IsFinitelyGeneratedConvexSet n C := (hTFAE.out 0 2).1 hCpoly
      rcases hCfg with ⟨S₀, S₁, hS₀fin, hS₁fin, hCeq⟩
      have hK_eq_cone :
          convexConeGenerated n C = cone n (S₀ ∪ S₁) :=
        helperForTheorem_19_7_originMem_convexConeGenerated_eq_finiteCone
          (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCeq hS₀fin hS₁fin hC0
      have hcone_poly : IsPolyhedralConvexSet n (cone n (S₀ ∪ S₁)) :=
        helperForTheorem_19_1_cone_polyhedral_of_finite_generators
          (m := n) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
      have hcone_closed : IsClosed (cone n (S₀ ∪ S₁)) :=
        (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
          (n := n) (C := cone n (S₀ ∪ S₁)) hcone_poly).1
      have hclosureK : closure (convexConeGenerated n C) = convexConeGenerated n C := by
        calc
          closure (convexConeGenerated n C)
              = closure (cone n (S₀ ∪ S₁)) := by
                  simp [hK_eq_cone]
          _ = cone n (S₀ ∪ S₁) :=
                (closure_eq_iff_isClosed (s := cone n (S₀ ∪ S₁))).2 hcone_closed
          _ = convexConeGenerated n C := by
                simp [hK_eq_cone]
      have hrec_subset_C : Set.recessionCone C ⊆ C :=
        helperForTheorem_19_7_recessionCone_subset_of_origin_mem
          (n := n) (C := C) hC0
      have hC_subset_K : C ⊆ convexConeGenerated n C := by
        intro x hx
        have hxHull : x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) :=
          ConvexCone.subset_hull hx
        have hxK : x = 0 ∨ x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := Or.inr hxHull
        simpa [convexConeGenerated, Set.mem_insert_iff] using hxK
      have hrec_subset_K : Set.recessionCone C ⊆ convexConeGenerated n C :=
        hrec_subset_C.trans hC_subset_K
      have hrec0 : (0 : Fin n → ℝ) ∈ Set.recessionCone C := by
        intro x hx t ht
        simpa [zero_smul, add_zero] using hx
      have hK_union :
          convexConeGenerated n C ∪ Set.recessionCone C =
            (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := by
        simpa using
          (convexConeGenerated_union_recession_eq_iUnion_pos (C := C) hCconv
            (recC := Set.recessionCone C) hrec0)
      have hK_eq_union :
          convexConeGenerated n C =
            (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := by
        calc
          convexConeGenerated n C = convexConeGenerated n C ∪ Set.recessionCone C := by
            symm
            exact Set.union_eq_left.mpr hrec_subset_K
          _ = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := hK_union
      calc
        closure (convexConeGenerated n C) = convexConeGenerated n C := hclosureK
        _ = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := hK_eq_union
        _ = (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
              rw [helperForTheorem_19_7_iUnion_pos_subtype_rewrite (n := n) (C := C)]
    · let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
      let C' : Set (EuclideanSpace ℝ (Fin n)) := Set.image e.symm C
      let recC : Set (Fin n → ℝ) := Set.image e (Set.recessionCone C')
      let K : Set (Fin n → ℝ) := convexConeGenerated n C
      have hcore :
          closure K = K ∪ recC ∧
            K ∪ recC = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ recC := by
        simpa [e, C', recC, K] using
          (closure_convexConeGenerated_eq_union_recessionCone
            (C := C) hCne hCclosed hCconv hC0)
      have hrec_transport : recC = Set.recessionCone C := by
        simpa [e, C', recC] using
          (helperForTheorem_19_7_recessionCone_transport_eq (n := n) (C := C))
      calc
        closure (convexConeGenerated n C) = K ∪ recC := by
          simpa [K] using hcore.1
        _ = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ recC := hcore.2
        _ = (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ recC := by
              rw [helperForTheorem_19_7_iUnion_pos_subtype_rewrite (n := n) (C := C)]
        _ = (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
              simp [hrec_transport]
  exact ⟨hpolyK, hconeClosure, hrepr⟩

/-- Helper for Corollary 19.7.1: a polyhedral convex set is finitely generated. -/
lemma helperForCorollary_19_7_1_finitelyGenerated_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsFinitelyGeneratedConvexSet n C := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
        (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  exact (hTFAE.out 0 2).1 hCpoly

/-- Corollary 19.7.1: If `C` is a polyhedral convex set containing the origin, the convex cone
generated by `C` is polyhedral. -/
theorem polyhedral_convexConeGenerated_of_origin_mem
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C →
      (0 : Fin n → ℝ) ∈ C →
        IsPolyhedralConvexSet n (convexConeGenerated n C) := by
  intro hCpoly hC0
  have hCfg : IsFinitelyGeneratedConvexSet n C :=
    helperForCorollary_19_7_1_finitelyGenerated_of_polyhedral
      (n := n) (C := C) hCpoly
  rcases hCfg with ⟨S₀, S₁, hS₀fin, hS₁fin, hCeq⟩
  have hK_eq_cone :
      convexConeGenerated n C = cone n (S₀ ∪ S₁) :=
    helperForTheorem_19_7_originMem_convexConeGenerated_eq_finiteCone
      (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCeq hS₀fin hS₁fin hC0
  have hcone_poly : IsPolyhedralConvexSet n (cone n (S₀ ∪ S₁)) :=
    helperForTheorem_19_1_cone_polyhedral_of_finite_generators
      (m := n) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
  simpa [hK_eq_cone] using hcone_poly


end Section19
end Chap19
