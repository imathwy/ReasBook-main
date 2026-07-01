/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part6

open scoped Pointwise

section Chap03
section Section11

/-- If `a ∉ C`, then `{a}` and `C` have disjoint intrinsic interiors. -/
lemma cor11_5_2_disjoint_intrinsicInterior_singleton {n : Nat} {a : Fin n → Real}
    {C : Set (Fin n → Real)} (ha : a ∉ C) :
    Disjoint (intrinsicInterior Real ({a} : Set (Fin n → Real))) (intrinsicInterior Real C) := by
  classical
  refine Set.disjoint_left.2 ?_
  intro x hx_single hxC
  have hx_eq : x = a := by
    simpa [intrinsicInterior_singleton] using hx_single
  have hx_memC : x ∈ C := (intrinsicInterior_subset (𝕜 := Real) (s := C)) hxC
  exact ha (by simpa [hx_eq] using hx_memC)

/-- A point outside a nonempty convex set can be properly separated from it by a hyperplane. -/
lemma cor11_5_2_exists_hyperplaneSeparatesProperly_point {n : Nat} {C : Set (Fin n → Real)}
    {a : Fin n → Real} (hCne : C.Nonempty) (hCconv : Convex Real C) (ha : a ∉ C) :
    ∃ H, HyperplaneSeparatesProperly n H ({a} : Set (Fin n → Real)) C := by
  classical
  have hdisj :
      Disjoint (intrinsicInterior Real ({a} : Set (Fin n → Real))) (intrinsicInterior Real C) :=
    cor11_5_2_disjoint_intrinsicInterior_singleton (n := n) (a := a) (C := C) ha
  have hiff :=
    exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior (n := n)
      (C₁ := ({a} : Set (Fin n → Real))) (C₂ := C)
      (hC₁ne := Set.singleton_nonempty a) (hC₂ne := hCne)
      (hC₁conv := convex_singleton a) (hC₂conv := hCconv)
  exact hiff.2 hdisj

/-- From a proper separating hyperplane between `{a}` and `C`, extract a nontrivial closed
half-space of the form `{x | x ⬝ᵥ b ≤ β}` containing `C`. -/
lemma cor11_5_2_extract_closedHalfspace_from_separation {n : Nat} {C : Set (Fin n → Real)}
    {a : Fin n → Real} {H : Set (Fin n → Real)}
    (hsep : HyperplaneSeparatesProperly n H ({a} : Set (Fin n → Real)) C) :
    ∃ (b : Fin n → Real) (β : Real), b ≠ 0 ∧ C ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  classical
  rcases hyperplaneSeparatesProperly_oriented n H ({a} : Set (Fin n → Real)) C hsep with
    ⟨b, β, hb0, _hH, _hSingleton, hCβ, _hnot⟩
  refine ⟨b, β, hb0, ?_⟩
  intro x hx
  exact hCβ x hx

/-- Corollary 11.5.2. Let `C` be a convex subset of `ℝ^n` other than `ℝ^n` itself. Then there
exists a closed half-space containing `C`. In other words, there exists some `b ∈ ℝ^n` such that
the linear function `x ↦ ⟪x, b⟫` (i.e. `x ⬝ᵥ b`) is bounded above on `C`. -/
theorem exists_closedHalfspace_superset_of_convex_ne_univ (n : Nat) (C : Set (Fin n → Real))
    (hn : 0 < n) (hCconv : Convex Real C) (hCne : C ≠ (Set.univ : Set (Fin n → Real))) :
    ∃ (b : Fin n → Real) (β : Real), b ≠ 0 ∧ C ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  classical
  by_cases hCempty : C = ∅
  · -- Any nontrivial half-space contains `∅`.
    let i0 : Fin n := ⟨0, hn⟩
    refine ⟨Pi.single i0 (1 : Real), 0, ?_, by simp [hCempty]⟩
    intro hb0
    have h1 := congrArg (fun f : Fin n → Real => f i0) hb0
    simp [Pi.single_eq_same] at h1
  · have hCne' : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
    rcases ((Set.ne_univ_iff_exists_notMem (s := C)).1 hCne) with ⟨a, haC⟩
    rcases
        cor11_5_2_exists_hyperplaneSeparatesProperly_point (n := n) (C := C) (a := a) hCne'
          hCconv haC with
      ⟨H, hsep⟩
    exact
      cor11_5_2_extract_closedHalfspace_from_separation (n := n) (C := C) (a := a) (H := H) hsep

/-- If `D ⊆ C`, a nontrivial supporting hyperplane to `C` containing `D` is the same as a
properly separating hyperplane between `D` and `C`. -/
lemma exists_nontrivialSupportingHyperplane_containing_iff_exists_hyperplaneSeparatesProperly
    {n : Nat} {C D : Set (Fin n → Real)} (hDne : D.Nonempty) (hDC : D ⊆ C) :
    (∃ H, IsNontrivialSupportingHyperplane n C H ∧ D ⊆ H) ↔
      (∃ H, HyperplaneSeparatesProperly n H D C) := by
  classical
  constructor
  · rintro ⟨H, hHnontriv, hDH⟩
    rcases hHnontriv with ⟨hHsupport, hCnot⟩
    rcases hHsupport with ⟨b, β, hb0, hHdef, hC_le, hx_touch⟩
    have hCne : C.Nonempty := hDne.mono hDC
    refine ⟨H, ?_, ?_⟩
    · -- `H` separates `D` and `C` (with `C` in the `≤ β` half-space).
      refine ⟨hDne, hCne, b, β, hb0, hHdef, ?_⟩
      refine Or.inr ?_
      refine ⟨?_, ?_⟩
      · intro x hxC
        exact hC_le x hxC
      · intro x hxD
        have hxH : x ∈ H := hDH hxD
        have hxEq : x ⬝ᵥ b = β := by simpa [hHdef] using hxH
        simp [hxEq]
    · -- properness: since `C` is not contained in `H`.
      intro hboth
      exact hCnot hboth.2
  · rintro ⟨H, hsep⟩
    rcases hyperplaneSeparatesProperly_oriented n H D C hsep with
      ⟨b, β, hb0, hHdef, hD_ge, hC_le, hnot⟩
    have hDH : D ⊆ H := by
      intro x hxD
      have hxC : x ∈ C := hDC hxD
      have h₁ : β ≤ x ⬝ᵥ b := hD_ge x hxD
      have h₂ : x ⬝ᵥ b ≤ β := hC_le x hxC
      have hxEq : x ⬝ᵥ b = β := le_antisymm h₂ h₁
      simpa [hHdef] using hxEq
    have hCnot : ¬ C ⊆ H :=
      (subset_left_imp_not_subset_right (A := D) (B := C) (H := H) hnot) hDH
    refine ⟨H, ⟨?_, hCnot⟩, hDH⟩
    rcases hDne with ⟨x0, hx0D⟩
    have hx0C : x0 ∈ C := hDC hx0D
    have hx0H : x0 ∈ H := hDH hx0D
    have hx0Eq : x0 ⬝ᵥ b = β := by simpa [hHdef] using hx0H
    refine ⟨b, β, hb0, hHdef, ?_, ⟨x0, hx0C, hx0Eq⟩⟩
    intro x hxC
    exact hC_le x hxC

/-- If `D ⊆ C`, then `ri D` is disjoint from `ri C` iff `D` is disjoint from `ri C`. -/
lemma disjoint_intrinsicInterior_left_iff_disjoint_of_subset {n : Nat} {C D : Set (Fin n → Real)}
    (hCconv : Convex Real C) (hDne : D.Nonempty) (hDconv : Convex Real D) (hDC : D ⊆ C) :
    Disjoint (intrinsicInterior ℝ D) (intrinsicInterior ℝ C) ↔ Disjoint D (intrinsicInterior ℝ C) := by
  classical
  constructor
  · intro hdisj
    -- Contrapositive: if `D` meets `ri C`, then `ri D` meets `ri C`.
    by_contra hnot
    have hx : (D ∩ intrinsicInterior ℝ C).Nonempty :=
      (Set.not_disjoint_iff_nonempty_inter).1 hnot
    rcases hx with ⟨x0, hx0D, hx0riC⟩
    -- Transport to Euclidean space and apply Corollary 6.5.2.
    let E := EuclideanSpace Real (Fin n)
    let e : E ≃L[Real] (Fin n → Real) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
    let CE : Set E := e ⁻¹' C
    let DE : Set E := e ⁻¹' D
    have hCEconv : Convex Real CE := hCconv.affine_preimage (e.toAffineEquiv.toAffineMap)
    have hDEconv : Convex Real DE := hDconv.affine_preimage (e.toAffineEquiv.toAffineMap)
    have hDEsub : DE ⊆ closure CE := by
      intro y hyDE
      have hyC : e y ∈ C := hDC hyDE
      have hyCE : y ∈ CE := hyC
      exact subset_closure hyCE
    have hDEnot : ¬ DE ⊆ euclideanRelativeBoundary n CE := by
      intro hsub
      have hy0DE : e.symm x0 ∈ DE := by
        simpa [DE] using hx0D
      have hy0intCE : e.symm x0 ∈ intrinsicInterior ℝ CE := by
        have hy0img : e.symm x0 ∈ e.symm '' intrinsicInterior ℝ C :=
          ⟨x0, hx0riC, by simp⟩
        have himage :
            intrinsicInterior ℝ (e.symm '' C) = e.symm '' intrinsicInterior ℝ C :=
          ContinuousLinearEquiv.image_intrinsicInterior (e := e.symm) (s := C)
        have hCEset : e.symm '' C = CE := by
          ext y
          constructor
          · rintro ⟨x, hxC, rfl⟩
            simpa [CE] using hxC
          · intro hyCE
            refine ⟨e y, hyCE, ?_⟩
            simp
        have : e.symm x0 ∈ intrinsicInterior ℝ (e.symm '' C) := by
          -- rewrite using `himage`.
          rw [himage]
          exact hy0img
        simpa [hCEset] using this
      have hy0riCE : e.symm x0 ∈ euclideanRelativeInterior n CE := by
        simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := CE)] using hy0intCE
      have hy0not : e.symm x0 ∉ euclideanRelativeBoundary n CE := by
        intro hy0B
        exact hy0B.2 hy0riCE
      exact hy0not (hsub hy0DE)
    have hriIncl :
        euclideanRelativeInterior n DE ⊆ euclideanRelativeInterior n CE :=
      euclideanRelativeInterior_subset_of_subset_closure_not_subset_relativeBoundary (n := n)
        CE DE hCEconv hDEconv hDEsub hDEnot
    have hriIncl' : intrinsicInterior ℝ DE ⊆ intrinsicInterior ℝ CE := by
      intro y hy
      have hy' : y ∈ euclideanRelativeInterior n DE := by
        simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := DE)] using hy
      have hy'' : y ∈ euclideanRelativeInterior n CE := hriIncl hy'
      simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := CE)] using hy''
    have heDE : e '' DE = D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hxD
        refine ⟨e.symm x, ?_, by simp⟩
        simpa [DE] using hxD
    have heCE : e '' CE = C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hxC
        refine ⟨e.symm x, ?_, by simp⟩
        simpa [CE] using hxC
    have hriD_eq : intrinsicInterior ℝ D = e '' intrinsicInterior ℝ DE := by
      simpa [heDE] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := DE))
    have hriC_eq : intrinsicInterior ℝ C = e '' intrinsicInterior ℝ CE := by
      simpa [heCE] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := CE))
    have hriDC : intrinsicInterior ℝ D ⊆ intrinsicInterior ℝ C := by
      intro z hz
      have hz' : z ∈ e '' intrinsicInterior ℝ DE := by simpa [hriD_eq] using hz
      rcases hz' with ⟨y, hy, rfl⟩
      have hyC : y ∈ intrinsicInterior ℝ CE := hriIncl' hy
      have : e y ∈ e '' intrinsicInterior ℝ CE := ⟨y, hyC, rfl⟩
      simpa [hriC_eq] using this
    rcases (Set.Nonempty.intrinsicInterior hDconv hDne) with ⟨y, hy⟩
    have hyC : y ∈ intrinsicInterior ℝ C := hriDC hy
    have hnonempty : (intrinsicInterior ℝ D ∩ intrinsicInterior ℝ C).Nonempty := ⟨y, hy, hyC⟩
    have : ¬ Disjoint (intrinsicInterior ℝ D) (intrinsicInterior ℝ C) :=
      (Set.not_disjoint_iff_nonempty_inter).2 hnonempty
    exact this hdisj
  · intro hdisj
    refine Set.disjoint_left.2 ?_
    intro x hxDint hxCint
    have hxD : x ∈ D := (intrinsicInterior_subset (𝕜 := ℝ) (s := D)) hxDint
    exact Set.disjoint_left.1 hdisj hxD hxCint

/-- Theorem 11.6: Let `C` be a convex set, and let `D` be a non-empty convex subset of `C` (for
instance, a subset consisting of a single point). In order that there exist a non-trivial
supporting hyperplane to `C` containing `D`, it is necessary and sufficient that `D` be disjoint
from `ri C` (the relative/intrinsic interior of `C`). -/
theorem exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n : Nat)
    (C D : Set (Fin n → Real)) (hCconv : Convex Real C) (hDne : D.Nonempty) (hDconv : Convex Real D)
    (hDC : D ⊆ C) :
    (∃ H, IsNontrivialSupportingHyperplane n C H ∧ D ⊆ H) ↔
      Disjoint D (intrinsicInterior ℝ C) := by
  have hCne : C.Nonempty := hDne.mono hDC
  calc
    (∃ H, IsNontrivialSupportingHyperplane n C H ∧ D ⊆ H) ↔
        (∃ H, HyperplaneSeparatesProperly n H D C) := by
          simpa using
            (exists_nontrivialSupportingHyperplane_containing_iff_exists_hyperplaneSeparatesProperly
              (n := n) (C := C) (D := D) hDne hDC)
    _ ↔ Disjoint (intrinsicInterior ℝ D) (intrinsicInterior ℝ C) := by
          simpa using
            (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior (n := n) (C₁ := D)
              (C₂ := C) (hC₁ne := hDne) (hC₂ne := hCne) (hC₁conv := hDconv) (hC₂conv := hCconv))
    _ ↔ Disjoint D (intrinsicInterior ℝ C) := by
          simpa using
            (disjoint_intrinsicInterior_left_iff_disjoint_of_subset (n := n) (C := C) (D := D)
              hCconv hDne hDconv hDC)

end Section11
end Chap03
