/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part3

open scoped Pointwise

section Chap03
section Section11

/-- `intrinsicInterior` equals `euclideanRelativeInterior` in Euclidean space. -/
lemma intrinsicInterior_eq_euclideanRelativeInterior (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    intrinsicInterior Real C = euclideanRelativeInterior n C := by
  ext x
  constructor
  · intro hx
    exact intrinsicInterior_subset_euclideanRelativeInterior n C hx
  · intro hx
    exact euclideanRelativeInterior_subset_intrinsicInterior (n := n) (C := C) hx

/-- Relative interior commutes with Minkowski subtraction for convex sets in `Fin n → ℝ`. -/
lemma intrinsicInterior_sub_eq (n : Nat) (C₁ C₂ : Set (Fin n → Real))
    (hC₁ : Convex Real C₁) (hC₂ : Convex Real C₂) :
    intrinsicInterior Real (C₁ - C₂) =
      intrinsicInterior Real C₁ - intrinsicInterior Real C₂ := by
  classical
  -- Transport to Euclidean space using `EuclideanSpace.equiv`.
  let E := EuclideanSpace Real (Fin n)
  let e : E ≃L[Real] (Fin n → Real) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let C₁E : Set E := e ⁻¹' C₁
  let C₂E : Set E := e ⁻¹' C₂
  have hC₁E : Convex Real C₁E := hC₁.affine_preimage (e.toAffineEquiv.toAffineMap)
  have hC₂E : Convex Real C₂E := hC₂.affine_preimage (e.toAffineEquiv.toAffineMap)
  have hsubE : C₁E - C₂E = C₁E + (-C₂E) := set_sub_eq_add_neg C₁E C₂E
  have hnegE : euclideanRelativeInterior n (-C₂E) = -euclideanRelativeInterior n C₂E := by
    calc
      euclideanRelativeInterior n (-C₂E)
          = euclideanRelativeInterior n ((-1 : Real) • C₂E) := by
              exact congrArg (fun S : Set E => euclideanRelativeInterior n S)
                (neg_set_eq_smul (C := C₂E))
      _ = (-1 : Real) • euclideanRelativeInterior n C₂E := by
            simpa using (euclideanRelativeInterior_smul n C₂E hC₂E (-1 : Real))
      _ = -euclideanRelativeInterior n C₂E := by
            exact (neg_set_eq_smul (C := euclideanRelativeInterior n C₂E)).symm
  have hriSubE :
      intrinsicInterior Real (C₁E - C₂E) =
        intrinsicInterior Real C₁E - intrinsicInterior Real C₂E := by
    calc
      intrinsicInterior Real (C₁E - C₂E)
          = euclideanRelativeInterior n (C₁E - C₂E) := by
              simp [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C₁E - C₂E)]
      _ = euclideanRelativeInterior n (C₁E + (-C₂E)) := by simp [hsubE]
      _ = euclideanRelativeInterior n C₁E + euclideanRelativeInterior n (-C₂E) := by
            simpa using
              (euclideanRelativeInterior_add_eq_and_closure_add_superset n C₁E (-C₂E) hC₁E
                    (hC₂E.neg)).1
      _ = euclideanRelativeInterior n C₁E + (-euclideanRelativeInterior n C₂E) := by
            simp [hnegE]
      _ = euclideanRelativeInterior n C₁E - euclideanRelativeInterior n C₂E := by
            simpa using
              (set_sub_eq_add_neg (euclideanRelativeInterior n C₁E)
                (euclideanRelativeInterior n C₂E)).symm
      _ = intrinsicInterior Real C₁E - intrinsicInterior Real C₂E := by
            simp [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C₁E),
              intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C₂E)]
  -- Push the statement back to `Fin n → ℝ`.
  have himage_sub : e '' (C₁E - C₂E) = (C₁ - C₂) := by
    ext x
    constructor
    · rintro ⟨y, ⟨y1, hy1, y2, hy2, rfl⟩, rfl⟩
      refine ⟨e y1, hy1, e y2, hy2, ?_⟩
      simp [sub_eq_add_neg, map_add, map_neg]
    · rintro ⟨x1, hx1, x2, hx2, rfl⟩
      refine ⟨e.symm x1 - e.symm x2, ?_, ?_⟩
      · refine ⟨e.symm x1, ?_, e.symm x2, ?_, rfl⟩ <;> simpa [C₁E, C₂E]
      · simp [sub_eq_add_neg, map_add, map_neg]
  have himage_sub_ri :
      e '' (intrinsicInterior Real (C₁E - C₂E)) = intrinsicInterior Real (C₁ - C₂) := by
    simpa [himage_sub] using
      (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := C₁E - C₂E)).symm
  have himage_ri₁ : e '' intrinsicInterior Real C₁E = intrinsicInterior Real C₁ := by
    have : e '' C₁E = C₁ := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨e.symm x, by simpa [C₁E] using hx, by simp⟩
    simpa [this] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := C₁E)).symm
  have himage_ri₂ : e '' intrinsicInterior Real C₂E = intrinsicInterior Real C₂ := by
    have : e '' C₂E = C₂ := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨e.symm x, by simpa [C₂E] using hx, by simp⟩
    simpa [this] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := C₂E)).symm
  -- Map `hriSubE` by `e` and simplify.
  have : intrinsicInterior Real (C₁ - C₂) =
        intrinsicInterior Real C₁ - intrinsicInterior Real C₂ := by
    -- apply `e ''` to `hriSubE` and rewrite images.
    have := congrArg (fun s : Set E => e '' s) hriSubE
    -- `e '' intrinsicInterior (C₁E - C₂E)` is the LHS.
    -- For the RHS, use that `e` is linear: `e '' (A - B) = e '' A - e '' B`.
    -- Here we expand once with elementwise reasoning.
    -- First rewrite the LHS and the two single-set images:
    have hL : e '' intrinsicInterior Real (C₁E - C₂E) = intrinsicInterior Real (C₁ - C₂) := by
      simpa using himage_sub_ri
    have hR1 : e '' intrinsicInterior Real C₁E = intrinsicInterior Real C₁ := by
      simpa using himage_ri₁
    have hR2 : e '' intrinsicInterior Real C₂E = intrinsicInterior Real C₂ := by
      simpa using himage_ri₂
    -- Now compute the image of the set difference.
    have hImSub :
        e '' (intrinsicInterior Real C₁E - intrinsicInterior Real C₂E) =
          intrinsicInterior Real C₁ - intrinsicInterior Real C₂ := by
      ext x
      constructor
      · rintro ⟨y, ⟨y1, hy1, y2, hy2, rfl⟩, rfl⟩
        refine ⟨e y1, ?_, e y2, ?_, ?_⟩
        · -- `e y1 ∈ intrinsicInterior C₁`
          rw [← hR1]
          exact ⟨y1, hy1, rfl⟩
        · -- `e y2 ∈ intrinsicInterior C₂`
          rw [← hR2]
          exact ⟨y2, hy2, rfl⟩
        · simp [sub_eq_add_neg, map_add, map_neg]
      · rintro ⟨x1, hx1, x2, hx2, rfl⟩
        have hx1' : x1 ∈ e '' intrinsicInterior Real C₁E := by
          -- rewrite the target set using `hR1`
          -- (no `simp`, to avoid heavy typeclass search).
          rw [hR1]
          exact hx1
        have hx2' : x2 ∈ e '' intrinsicInterior Real C₂E := by
          rw [hR2]
          exact hx2
        rcases hx1' with ⟨y1, hy1, rfl⟩
        rcases hx2' with ⟨y2, hy2, rfl⟩
        refine ⟨y1 - y2, ⟨y1, hy1, y2, hy2, rfl⟩, ?_⟩
        simp [sub_eq_add_neg, map_add, map_neg]
    -- Finish by rewriting `this`.
    simpa [hL, hImSub] using this
  exact this

/-- Disjointness of intrinsic interiors is equivalent to `0` not lying in the intrinsic interior
of the Minkowski difference. -/
lemma disjoint_intrinsicInterior_iff_zero_not_mem_intrinsicInterior_sub (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ : Convex Real C₁) (hC₂ : Convex Real C₂) :
    Disjoint (intrinsicInterior Real C₁) (intrinsicInterior Real C₂) ↔
      (0 : Fin n → Real) ∉ intrinsicInterior Real (C₁ - C₂) := by
  classical
  rw [intrinsicInterior_sub_eq (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ hC₂]
  let A : Set (Fin n → Real) := intrinsicInterior Real C₁
  let B : Set (Fin n → Real) := intrinsicInterior Real C₂
  have h0 : (0 : Fin n → Real) ∈ A - B ↔ ∃ x, x ∈ A ∧ x ∈ B := by
    constructor
    · intro hmem
      change (0 : Fin n → Real) ∈ Set.image2 (fun a b : Fin n → Real => a - b) A B at hmem
      rcases hmem with ⟨a, ha, b, hb, hab⟩
      have : a = b := sub_eq_zero.mp hab
      subst this
      exact ⟨a, ha, hb⟩
    · rintro ⟨a, ha, hb⟩
      change (0 : Fin n → Real) ∈ Set.image2 (fun a b : Fin n → Real => a - b) A B
      exact ⟨a, ha, a, hb, sub_self a⟩
  constructor
  · intro hdisj hmem
    rcases (h0.1 hmem) with ⟨x, hxA, hxB⟩
    exact (Set.disjoint_left.1 hdisj hxA hxB)
  · intro h0not
    refine Set.disjoint_left.2 ?_
    intro x hxA hxB
    have : (0 : Fin n → Real) ∈ A - B := h0.2 ⟨x, hxA, hxB⟩
    exact h0not this

/-- `intrinsicInterior` is relatively open in its affine span. -/
lemma exists_isOpen_inter_affineSpan_eq_intrinsicInterior (n : Nat) (s : Set (Fin n → Real)) :
    ∃ U : Set (Fin n → Real), IsOpen U ∧
      intrinsicInterior Real s = U ∩ (affineSpan Real s : Set (Fin n → Real)) := by
  classical
  let A : AffineSubspace Real (Fin n → Real) := affineSpan Real s
  let t : Set A := interior (((↑) : A → (Fin n → Real)) ⁻¹' s)
  have htopen : IsOpen t := isOpen_interior
  rcases (isOpen_induced_iff.1 htopen) with ⟨U, hUopen, hpre⟩
  refine ⟨U, hUopen, ?_⟩
  have hrange : Set.range ((↑) : A → (Fin n → Real)) = (A : Set (Fin n → Real)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  calc
    intrinsicInterior Real s
        = ((↑) : A → (Fin n → Real)) '' t := by
            simp [intrinsicInterior, t, A]
    _ = ((↑) : A → (Fin n → Real)) '' (((↑) : A → (Fin n → Real)) ⁻¹' U) := by
          simp [hpre]
    _ = U ∩ Set.range ((↑) : A → (Fin n → Real)) := by
          simp [Set.image_preimage_eq_inter_range]
    _ = U ∩ (affineSpan Real s : Set (Fin n → Real)) := by
          simp [A, hrange]

/-- The intrinsic interior of a convex set in `Fin n → ℝ` is convex. -/
lemma convex_intrinsicInterior_of_convex (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) : Convex Real (intrinsicInterior Real C) := by
  classical
  let E := EuclideanSpace Real (Fin n)
  let e : E ≃L[Real] (Fin n → Real) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let CE : Set E := e ⁻¹' C
  have hCE : Convex Real CE := hC.affine_preimage (e.toAffineEquiv.toAffineMap)
  have hCEconv : Convex Real (intrinsicInterior Real CE) := by
    have : Convex Real (euclideanRelativeInterior n CE) := convex_euclideanRelativeInterior n CE hCE
    simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := CE)] using this
  have hCe : e '' CE = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa [CE] using hx, by simp⟩
  have hI : intrinsicInterior Real C = e '' intrinsicInterior Real CE := by
    simpa [hCe] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := CE))
  have : Convex Real (e '' intrinsicInterior Real CE) :=
    Convex.affine_image (f := e.toAffineEquiv.toAffineMap) hCEconv
  simpa [hI] using this

/-- For a nonempty convex set in `Fin n → ℝ`, the affine span of the intrinsic interior equals the
affine span of the set. -/
lemma affineSpan_intrinsicInterior_eq_of_convex_nonempty (n : Nat) (C : Set (Fin n → Real))
    (hC : Convex Real C) (hCne : C.Nonempty) :
    affineSpan Real (intrinsicInterior Real C) = affineSpan Real C := by
  classical
  let E := EuclideanSpace Real (Fin n)
  let e : E ≃L[Real] (Fin n → Real) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let CE : Set E := e ⁻¹' C
  have hCE : Convex Real CE := hC.affine_preimage (e.toAffineEquiv.toAffineMap)
  have hCEne : CE.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨e.symm x, by simpa [CE] using hx⟩
  have hCe : e '' CE = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa [CE] using hx, by simp⟩
  have hI : intrinsicInterior Real C = e '' intrinsicInterior Real CE := by
    simpa [hCe] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := CE))
  have haffE :
      affineSpan Real (intrinsicInterior Real CE) = affineSpan Real CE :=
    affineSpan_intrinsicInterior_eq (n := n) (C := CE) hCE hCEne
  calc
    affineSpan Real (intrinsicInterior Real C)
        = affineSpan Real (e '' intrinsicInterior Real CE) := by simp [hI]
    _ = (affineSpan Real (intrinsicInterior Real CE)).map e.toAffineEquiv.toAffineMap := by
          simpa using
            (AffineSubspace.map_span (k := Real) (f := e.toAffineEquiv.toAffineMap)
              (s := intrinsicInterior Real CE)).symm
    _ = (affineSpan Real CE).map e.toAffineEquiv.toAffineMap := by simp [haffE]
    _ = affineSpan Real (e '' CE) := by
          simpa using
            (AffineSubspace.map_span (k := Real) (f := e.toAffineEquiv.toAffineMap) (s := CE))
    _ = affineSpan Real C := by simp [hCe]

/-- For a nonempty convex set in `Fin n → ℝ`, `closure C ⊆ closure (intrinsicInterior C)`. -/
lemma closure_subset_closure_intrinsicInterior_of_convex_nonempty (n : Nat)
    (C : Set (Fin n → Real)) (hC : Convex Real C) (hCne : C.Nonempty) :
    closure C ⊆ closure (intrinsicInterior Real C) := by
  classical
  let E := EuclideanSpace Real (Fin n)
  let e : E ≃L[Real] (Fin n → Real) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let CE : Set E := e ⁻¹' C
  have hCE : Convex Real CE := hC.affine_preimage (e.toAffineEquiv.toAffineMap)
  have hCEne : CE.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨e.symm x, by simpa [CE] using hx⟩
  have hCe : e '' CE = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa [CE] using hx, by simp⟩
  have hI : intrinsicInterior Real C = e '' intrinsicInterior Real CE := by
    simpa [hCe] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := CE))
  have hclosureE :
      closure CE ⊆ closure (euclideanRelativeInterior n CE) :=
    euclidean_closure_subset_closure_relativeInterior_of_nonempty (n := n) (C := CE) hCE hCEne
  have hIE : euclideanRelativeInterior n CE = intrinsicInterior Real CE :=
    (intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := CE)).symm
  have hclosureE' : closure CE ⊆ closure (intrinsicInterior Real CE) := by
    simpa [hIE] using hclosureE
  have himage :
      e '' closure CE ⊆ e '' closure (intrinsicInterior Real CE) :=
    Set.image_mono hclosureE'
  have himageC : e '' closure CE = closure C := by
    simpa [hCe] using (e.toHomeomorph.image_closure CE)
  have himageI : e '' closure (intrinsicInterior Real CE) = closure (intrinsicInterior Real C) := by
    -- map the closure of the intrinsic interior and rewrite the image via `hI`.
    simpa [hI.symm] using (e.toHomeomorph.image_closure (intrinsicInterior Real CE))
  -- Rewrite `himage` using `himageC` and `himageI`.
  simpa [himageC, himageI] using himage

/-- Proper separation implies `0` is not in the intrinsic interior of the Minkowski difference. -/
lemma zero_not_mem_intrinsicInterior_sub_of_exists_hyperplaneSeparatesProperly (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty) :
    (∃ H, HyperplaneSeparatesProperly n H C₁ C₂) →
      (0 : Fin n → Real) ∉ intrinsicInterior Real (C₁ - C₂) := by
  classical
  rintro ⟨H, hsep⟩
  rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hsep with
    ⟨b, β, _hb0, hH, hC₁β, hC₂β, hnot⟩
  let C : Set (Fin n → Real) := C₁ - C₂
  have hCsub : C ⊆ {x : Fin n → Real | 0 ≤ x ⬝ᵥ b} := by
    intro x hx
    rcases hx with ⟨x1, hx1, x2, hx2, rfl⟩
    have hx1' : β ≤ x1 ⬝ᵥ b := hC₁β x1 hx1
    have hx2' : x2 ⬝ᵥ b ≤ β := hC₂β x2 hx2
    have hx2_le_x1 : x2 ⬝ᵥ b ≤ x1 ⬝ᵥ b := le_trans hx2' hx1'
    have : 0 ≤ x1 ⬝ᵥ b - x2 ⬝ᵥ b := sub_nonneg.mpr hx2_le_x1
    simpa [C, sub_dotProduct] using this
  have hexistsPos : ∃ w ∈ C, 0 < w ⬝ᵥ b := by
    have hnot' :
        ¬ (C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} ∧
            C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β}) := by
      simpa [hH] using hnot
    rcases hC₁ne with ⟨x1₀, hx1₀⟩
    rcases hC₂ne with ⟨x2₀, hx2₀⟩
    by_cases hC₁H : C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β}
    · have hC₂H : ¬ C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} := by
        intro hC₂H
        exact hnot' ⟨hC₁H, hC₂H⟩
      rcases (Set.not_subset.mp hC₂H) with ⟨x2, hx2, hx2not⟩
      have hx2ne : x2 ⬝ᵥ b ≠ β := by simpa using hx2not
      have hx2lt : x2 ⬝ᵥ b < β :=
        lt_of_le_of_ne (hC₂β x2 hx2) (by simpa [eq_comm] using hx2ne)
      refine ⟨x1₀ - x2, ⟨x1₀, hx1₀, x2, hx2, rfl⟩, ?_⟩
      have hx1ge : β ≤ x1₀ ⬝ᵥ b := hC₁β x1₀ hx1₀
      have hx2lt' : x2 ⬝ᵥ b < x1₀ ⬝ᵥ b := lt_of_lt_of_le hx2lt hx1ge
      have : 0 < x1₀ ⬝ᵥ b - x2 ⬝ᵥ b := sub_pos.mpr hx2lt'
      simpa [sub_dotProduct] using this
    · rcases (Set.not_subset.mp hC₁H) with ⟨x1, hx1, hx1not⟩
      have hx1ne : x1 ⬝ᵥ b ≠ β := by simpa using hx1not
      have hx1gt : β < x1 ⬝ᵥ b :=
        lt_of_le_of_ne (hC₁β x1 hx1) (by simpa using hx1ne.symm)
      refine ⟨x1 - x2₀, ⟨x1, hx1, x2₀, hx2₀, rfl⟩, ?_⟩
      have hx2le : x2₀ ⬝ᵥ b ≤ β := hC₂β x2₀ hx2₀
      have hx2lt : x2₀ ⬝ᵥ b < x1 ⬝ᵥ b := lt_of_le_of_lt hx2le hx1gt
      have : 0 < x1 ⬝ᵥ b - x2₀ ⬝ᵥ b := sub_pos.mpr hx2lt
      simpa [sub_dotProduct] using this
  intro h0
  rcases hexistsPos with ⟨w, hwC, hwpos⟩
  let A : AffineSubspace Real (Fin n → Real) := affineSpan Real C
  let sA : Set A := ((↑) : A → (Fin n → Real)) ⁻¹' C
  rcases (mem_intrinsicInterior.mp h0) with ⟨y0, hy0, hy0eq⟩
  have hy0eq' : (y0 : Fin n → Real) = 0 := hy0eq
  have h0A : (0 : Fin n → Real) ∈ (A : Set (Fin n → Real)) := by
    simpa [A, hy0eq'] using (y0.property)
  have hwA : w ∈ (A : Set (Fin n → Real)) := subset_affineSpan (k := Real) (s := C) hwC
  have hsA_nhds : sA ∈ nhds y0 := (mem_interior_iff_mem_nhds).1 hy0
  rcases (Metric.mem_nhds_iff.1 hsA_nhds) with ⟨ε, hε, hball⟩
  have hw_ne0 : w ≠ (0 : Fin n → Real) := by
    intro hw0
    simpa [hw0] using hwpos.ne'
  have hnormw_pos : 0 < ‖w‖ := norm_pos_iff.2 hw_ne0
  let t : Real := ε / (2 * ‖w‖)
  have htpos : 0 < t := by
    have hden : 0 < 2 * ‖w‖ := by nlinarith [hnormw_pos]
    exact div_pos hε hden
  have ht_lt : ‖(-t) • w‖ < ε := by
    have hwne : (‖w‖ : Real) ≠ 0 := ne_of_gt hnormw_pos
    have hmul : t * ‖w‖ = ε / 2 := by
      -- `(ε / (2‖w‖)) * ‖w‖ = ε/2`
      dsimp [t]
      calc
        (ε / (2 * ‖w‖)) * ‖w‖ = (ε * ‖w‖) / (2 * ‖w‖) := by
          simp [div_mul_eq_mul_div]
        _ = ε / 2 := by
          simpa [mul_assoc] using (mul_div_mul_right ε (2 : Real) hwne)
    calc
      ‖(-t) • w‖ = |(-t)| * ‖w‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ = t * ‖w‖ := by simp [abs_neg, abs_of_pos htpos]
      _ = ε / 2 := hmul
      _ < ε := by linarith [hε]
  have hw_dir : w ∈ A.direction := by
    have : w -ᵥ (0 : Fin n → Real) ∈ A.direction := AffineSubspace.vsub_mem_direction hwA h0A
    simpa [vsub_eq_sub] using this
  have ht_dir : (-t) • w ∈ A.direction := A.direction.smul_mem (-t) hw_dir
  have htA : (-t) • w ∈ (A : Set (Fin n → Real)) := by
    have : (-t) • w +ᵥ (0 : Fin n → Real) ∈ A :=
      AffineSubspace.vadd_mem_of_mem_direction (s := A) ht_dir h0A
    simpa using this
  let z0 : A := ⟨(-t) • w, htA⟩
  have hz0_ball : z0 ∈ Metric.ball y0 ε := by
    have hz0_dist : dist z0 y0 < ε := by
      -- `dist` on `A` is induced by coercion to the ambient space.
      change dist (z0 : Fin n → Real) (y0 : Fin n → Real) < ε
      simpa [z0, hy0eq', dist_zero_right] using ht_lt
    simpa [Metric.ball] using hz0_dist
  have hz0_mem : z0 ∈ sA := hball hz0_ball
  have hz0C : (z0 : Fin n → Real) ∈ C := by
    simpa [sA] using hz0_mem
  have hz0_nonneg : 0 ≤ (z0 : Fin n → Real) ⬝ᵥ b := hCsub hz0C
  have hz0_neg : (z0 : Fin n → Real) ⬝ᵥ b < 0 := by
    have htneg : (-t) < 0 := neg_neg_of_pos htpos
    have hdot : ((-t) • w) ⬝ᵥ b = (-t) * (w ⬝ᵥ b) := by
      simp [smul_dotProduct]
    have : (-t) * (w ⬝ᵥ b) < 0 := mul_neg_of_neg_of_pos htneg hwpos
    simpa [z0, hdot] using this
  exact (not_lt_of_ge hz0_nonneg) hz0_neg

/-- If `0` is not in the intrinsic interior of the Minkowski difference, then the sets admit a
properly separating hyperplane. -/
lemma exists_hyperplaneSeparatesProperly_of_zero_not_mem_intrinsicInterior_sub (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂) :
    (0 : Fin n → Real) ∉ intrinsicInterior Real (C₁ - C₂) →
      ∃ H, HyperplaneSeparatesProperly n H C₁ C₂ := by
  classical
  intro h0not
  let C : Set (Fin n → Real) := C₁ - C₂
  let C0 : Set (Fin n → Real) := intrinsicInterior Real C
  let M : AffineSubspace Real (Fin n → Real) := affineSpan Real ({(0 : Fin n → Real)} : Set (Fin n → Real))
  have hCne : C.Nonempty := by
    rcases hC₁ne with ⟨x1, hx1⟩
    rcases hC₂ne with ⟨x2, hx2⟩
    refine ⟨x1 - x2, ⟨x1, hx1, x2, hx2, rfl⟩⟩
  have hCconv : Convex Real C := hC₁conv.sub hC₂conv
  have hC0ne : C0.Nonempty := Set.Nonempty.intrinsicInterior hCconv hCne
  have hC0conv : Convex Real C0 := by
    simpa [C0] using (convex_intrinsicInterior_of_convex (n := n) (C := C) hCconv)
  have hC0relopen :
      ∃ U : Set (Fin n → Real), IsOpen U ∧
        C0 = U ∩ (affineSpan Real C0 : Set (Fin n → Real)) := by
    rcases exists_isOpen_inter_affineSpan_eq_intrinsicInterior n C with ⟨U, hUopen, hEq⟩
    have haff :
        affineSpan Real (intrinsicInterior Real C) = affineSpan Real C :=
      affineSpan_intrinsicInterior_eq_of_convex_nonempty (n := n) (C := C) hCconv hCne
    refine ⟨U, hUopen, ?_⟩
    simpa [C0, haff.symm] using hEq
  have hMne : (M : Set (Fin n → Real)).Nonempty := by
    refine ⟨0, by simp [M]⟩
  have hCM : Disjoint C0 (M : Set (Fin n → Real)) := by
    refine Set.disjoint_left.2 ?_
    intro x hxC0 hxM
    have hx0 : x = (0 : Fin n → Real) := by simpa [M] using hxM
    subst hx0
    simpa [C0, C] using h0not hxC0
  rcases
      exists_hyperplane_contains_affine_of_convex_relativelyOpen n C0 M hC0ne hC0conv hC0relopen
        hMne hCM with
    ⟨H, hMH, b, β, _hb0, hH, hcases⟩
  have hβ : β = 0 := by
    have h0M : (0 : Fin n → Real) ∈ M := by simp [M]
    have h0H : (0 : Fin n → Real) ∈ H := hMH h0M
    have : (0 : Fin n → Real) ⬝ᵥ b = β := by simpa [hH] using h0H
    simpa using this.symm
  subst hβ
  have hexists_bpos : ∃ b' : Fin n → Real, ∀ x ∈ C0, 0 < x ⬝ᵥ b' := by
    rcases hcases with hlt | hgt
    · refine ⟨-b, ?_⟩
      intro x hx
      have : x ⬝ᵥ b < 0 := hlt hx
      have : 0 < -(x ⬝ᵥ b) := by simpa using (neg_pos.mpr this)
      simpa [dotProduct_neg] using this
    · refine ⟨b, ?_⟩
      intro x hx
      exact hgt hx
  rcases hexists_bpos with ⟨b', hb'pos⟩
  have hclosure : closure C ⊆ closure C0 := by
    simpa [C0] using
      closure_subset_closure_intrinsicInterior_of_convex_nonempty (n := n) (C := C) hCconv hCne
  have hC_closure : C ⊆ closure C0 := by
    intro x hx
    exact hclosure (subset_closure hx)
  have hclosedHalf : IsClosed {x : Fin n → Real | 0 ≤ x ⬝ᵥ b'} := by
    have hcont : Continuous fun x : Fin n → Real => x ⬝ᵥ b' := by
      simpa using
        (Continuous.dotProduct (A := fun x : Fin n → Real => x) (B := fun _ => b') continuous_id
          continuous_const)
    have : IsClosed ((fun x : Fin n → Real => x ⬝ᵥ b') ⁻¹' Set.Ici (0 : Real)) :=
      isClosed_Ici.preimage hcont
    simpa [Set.preimage, Set.Ici] using this
  have hclosureHalf : closure C0 ⊆ {x : Fin n → Real | 0 ≤ x ⬝ᵥ b'} :=
    closure_minimal (by
      intro x hx
      exact le_of_lt (hb'pos x hx)) hclosedHalf
  have hCnonneg : ∀ x ∈ C, 0 ≤ x ⬝ᵥ b' := by
    intro x hx
    exact hclosureHalf (hC_closure hx)
  let f : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ b' : Real) : EReal)
  have ha : sInf (f '' C₁) ≥ sSup (f '' C₂) := by
    have hSup_le : ∀ x1 ∈ C₁, sSup (f '' C₂) ≤ f x1 := by
      intro x1 hx1
      refine sSup_le ?_
      rintro _ ⟨x2, hx2, rfl⟩
      have hx : 0 ≤ (x1 - x2) ⬝ᵥ b' :=
        hCnonneg (x1 - x2) ⟨x1, hx1, x2, hx2, rfl⟩
      have hx' : x2 ⬝ᵥ b' ≤ x1 ⬝ᵥ b' := by
        have : 0 ≤ x1 ⬝ᵥ b' - x2 ⬝ᵥ b' := by
          simpa [sub_dotProduct] using hx
        exact sub_nonneg.mp this
      exact (EReal.coe_le_coe_iff.2 hx')
    have : sSup (f '' C₂) ≤ sInf (f '' C₁) := by
      refine le_sInf ?_
      rintro _ ⟨x1, hx1, rfl⟩
      exact hSup_le x1 hx1
    exact this
  have hb : sSup (f '' C₁) > sInf (f '' C₂) := by
    rcases hC0ne with ⟨x, hxC0⟩
    have hxpos : 0 < x ⬝ᵥ b' := hb'pos x hxC0
    have hxC : x ∈ C := (intrinsicInterior_subset (𝕜 := Real) (s := C)) hxC0
    rcases hxC with ⟨x1, hx1, x2, hx2, rfl⟩
    have hxlt : x2 ⬝ᵥ b' < x1 ⬝ᵥ b' := by
      have : 0 < x1 ⬝ᵥ b' - x2 ⬝ᵥ b' := by
        simpa [sub_dotProduct] using hxpos
      exact sub_pos.mp this
    have hxlt' : f x2 < f x1 := EReal.coe_lt_coe_iff.2 hxlt
    have hx1mem : f x1 ∈ f '' C₁ := ⟨x1, hx1, rfl⟩
    have hx2mem : f x2 ∈ f '' C₂ := ⟨x2, hx2, rfl⟩
    have hsInf_le : sInf (f '' C₂) ≤ f x2 := sInf_le hx2mem
    have hlt : sInf (f '' C₂) < f x1 := lt_of_le_of_lt hsInf_le hxlt'
    have : sInf (f '' C₂) < sSup (f '' C₁) := lt_of_lt_of_le hlt (le_sSup hx1mem)
    simpa [gt_iff_lt] using this
  exact
    exists_hyperplaneSeparatesProperly_of_EReal_inf_sup_conditions n C₁ C₂ hC₁ne hC₂ne b' ha hb

/-- Theorem 11.3: Let `C₁` and `C₂` be non-empty convex sets in `ℝ^n`. In order that there exist a
hyperplane separating `C₁` and `C₂` properly, it is necessary and sufficient that `ri C₁` and
`ri C₂` have no point in common, where `ri` denotes the relative (intrinsic) interior. -/
theorem exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior (n : Nat)
    (C₁ C₂ : Set (Fin n → Real)) (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex Real C₁) (hC₂conv : Convex Real C₂) :
    (∃ H, HyperplaneSeparatesProperly n H C₁ C₂) ↔
      Disjoint (intrinsicInterior Real C₁) (intrinsicInterior Real C₂) := by
  classical
  rw [disjoint_intrinsicInterior_iff_zero_not_mem_intrinsicInterior_sub n C₁ C₂ hC₁conv hC₂conv]
  constructor
  · intro hsep
    exact
      zero_not_mem_intrinsicInterior_sub_of_exists_hyperplaneSeparatesProperly n C₁ C₂ hC₁ne hC₂ne
        hsep
  · intro h0not
    exact
      exists_hyperplaneSeparatesProperly_of_zero_not_mem_intrinsicInterior_sub n C₁ C₂ hC₁ne hC₂ne
        hC₁conv hC₂conv h0not
  /-
  /-- Minkowski subtraction is Minkowski addition with pointwise negation. -/
  have set_sub_eq_add_neg {E : Type*} [AddGroup E] (A B : Set E) : A - B = A + (-B) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a, ha, -b, ?_, ?_⟩
      · simpa using hb
      · simp [sub_eq_add_neg]
    · rintro ⟨a, ha, c, hc, rfl⟩
      have hc' : -c ∈ B := by simpa using hc
      refine ⟨a, ha, -c, hc', ?_⟩
      simp [sub_eq_add_neg]

  /-- Pointwise negation equals scalar multiplication by `-1`. -/
  have neg_set_eq_smul {E : Type*} [AddCommGroup E] [Module Real E] (C : Set E) :
      -C = ((-1 : Real) • C) := by
    ext x
    constructor
    · intro hx
      have hx' : -x ∈ C := by simpa using hx
      refine ⟨-x, hx', ?_⟩
      simp
    · rintro ⟨y, hy, rfl⟩
      simpa using hy

  /-- The book's `euclideanRelativeInterior` is contained in mathlib's `intrinsicInterior`. -/
  have euclideanRelativeInterior_subset_intrinsicInterior (n : Nat) (C : Set (Fin n → Real)) :
      euclideanRelativeInterior n C ⊆ intrinsicInterior Real C := by
    classical
    intro x hx
    rcases hx with ⟨hx_aff, ε, hε, hxsub⟩
    let A : AffineSubspace Real (Fin n → Real) := affineSpan Real C
    let sA : Set A := ((↑) : A → (Fin n → Real)) ⁻¹' C
    refine (mem_intrinsicInterior).2 ?_
    refine ⟨(⟨x, hx_aff⟩ : A), ?_, rfl⟩
    have hball : Metric.ball (⟨x, hx_aff⟩ : A) ε ⊆ sA := by
      intro y hy
      have hyBall : dist (y : Fin n → Real) x < ε := by
        simpa using hy
      have hyClosed : (y : Fin n → Real) ∈ Metric.closedBall x ε := by
        exact (Metric.mem_closedBall).2 (le_of_lt hyBall)
      have hclosed :
          (fun z : Fin n → Real => x + z) '' (ε • euclideanUnitBall n) =
            Metric.closedBall x ε := by
        simpa using (translate_smul_unitBall_eq_closedBall n x ε hε)
      have hyLeft :
          (y : Fin n → Real) ∈ (fun z : Fin n → Real => x + z) '' (ε • euclideanUnitBall n) := by
        simpa [hclosed] using hyClosed
      have hyC : (y : Fin n → Real) ∈ C := hxsub ⟨hyLeft, y.property⟩
      simpa [sA] using hyC
    have hsA_nhds : sA ∈ nhds (⟨x, hx_aff⟩ : A) :=
      Metric.mem_nhds_iff.2 ⟨ε, hε, hball⟩
    exact (mem_interior_iff_mem_nhds).2 hsA_nhds

  /-- `intrinsicInterior` equals `euclideanRelativeInterior` in `ℝ^n`. -/
  have intrinsicInterior_eq_euclideanRelativeInterior (n : Nat) (C : Set (Fin n → Real)) :
      intrinsicInterior Real C = euclideanRelativeInterior n C := by
    ext x
    constructor
    · intro hx
      exact intrinsicInterior_subset_euclideanRelativeInterior n C hx
    · intro hx
      exact euclideanRelativeInterior_subset_intrinsicInterior n C hx

  /-- Relative interior commutes with Minkowski subtraction for convex sets. -/
  have intrinsicInterior_sub_eq (n : Nat) (C₁ C₂ : Set (Fin n → Real))
      (hC₁ : Convex Real C₁) (hC₂ : Convex Real C₂) :
      intrinsicInterior Real (C₁ - C₂) =
        intrinsicInterior Real C₁ - intrinsicInterior Real C₂ := by
    have hsub : C₁ - C₂ = C₁ + (-C₂) := set_sub_eq_add_neg C₁ C₂
    have hneg : euclideanRelativeInterior n (-C₂) = -euclideanRelativeInterior n C₂ := by
      calc
        euclideanRelativeInterior n (-C₂)
            = euclideanRelativeInterior n ((-1 : Real) • C₂) := by
                simpa [neg_set_eq_smul (C := C₂)]
        _ = (-1 : Real) • euclideanRelativeInterior n C₂ := by
              simpa using (euclideanRelativeInterior_smul n C₂ hC₂ (-1 : Real))
        _ = -euclideanRelativeInterior n C₂ := by
              simpa using (neg_set_eq_smul (C := euclideanRelativeInterior n C₂)).symm
    calc
      intrinsicInterior Real (C₁ - C₂)
          = euclideanRelativeInterior n (C₁ - C₂) := by
              simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C₁ - C₂)]
      _ = euclideanRelativeInterior n (C₁ + (-C₂)) := by simpa [hsub]
      _ = euclideanRelativeInterior n C₁ + euclideanRelativeInterior n (-C₂) := by
            simpa using
              (euclideanRelativeInterior_add_eq_and_closure_add_superset n C₁ (-C₂) hC₁
                    (hC₂.neg)).1
      _ = euclideanRelativeInterior n C₁ + (-euclideanRelativeInterior n C₂) := by simpa [hneg]
      _ = euclideanRelativeInterior n C₁ - euclideanRelativeInterior n C₂ := by
            simpa using
              (set_sub_eq_add_neg (euclideanRelativeInterior n C₁) (euclideanRelativeInterior n C₂)).symm
      _ = intrinsicInterior Real C₁ - intrinsicInterior Real C₂ := by
            -- rewrite `euclideanRelativeInterior` back to `intrinsicInterior`
            simp [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C₁),
              intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C₂)]

  /-- Disjointness of intrinsic interiors is equivalent to `0` not lying in the intrinsic interior
  of the Minkowski difference. -/
  have disjoint_intrinsicInterior_iff_zero_not_mem_intrinsicInterior_sub (n : Nat)
      (C₁ C₂ : Set (Fin n → Real)) (hC₁ : Convex Real C₁) (hC₂ : Convex Real C₂) :
      Disjoint (intrinsicInterior Real C₁) (intrinsicInterior Real C₂) ↔
        (0 : Fin n → Real) ∉ intrinsicInterior Real (C₁ - C₂) := by
    classical
    -- Rewrite `intrinsicInterior (C₁ - C₂)` into `intrinsicInterior C₁ - intrinsicInterior C₂`.
    rw [intrinsicInterior_sub_eq (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ hC₂]
    let A : Set (Fin n → Real) := intrinsicInterior Real C₁
    let B : Set (Fin n → Real) := intrinsicInterior Real C₂
    have h0 :
        (0 : Fin n → Real) ∈ A - B ↔ ∃ x, x ∈ A ∧ x ∈ B := by
      constructor
      · intro hmem
        change (0 : Fin n → Real) ∈ Set.image2 (fun a b : Fin n → Real => a - b) A B at hmem
        rcases hmem with ⟨a, ha, b, hb, hab⟩
        have : a = b := sub_eq_zero.mp hab
        subst this
        exact ⟨a, ha, hb⟩
      · rintro ⟨a, ha, hb⟩
        change (0 : Fin n → Real) ∈ Set.image2 (fun a b : Fin n → Real => a - b) A B
        exact ⟨a, ha, a, hb, sub_self a⟩
    constructor
    · intro hdisj
      intro hmem
      rcases (h0.1 hmem) with ⟨x, hxA, hxB⟩
      exact (Set.disjoint_left.1 hdisj hxA hxB)
    · intro h0not
      refine Set.disjoint_left.2 ?_
      intro x hxA hxB
      have : (0 : Fin n → Real) ∈ A - B := h0.2 ⟨x, hxA, hxB⟩
      exact h0not this

  -- Reduce the statement to `0 ∉ intrinsicInterior (C₁ - C₂)`.
  have hdisj :
      Disjoint (intrinsicInterior Real C₁) (intrinsicInterior Real C₂) ↔
        (0 : Fin n → Real) ∉ intrinsicInterior Real (C₁ - C₂) := by
    exact disjoint_intrinsicInterior_iff_zero_not_mem_intrinsicInterior_sub n C₁ C₂ hC₁conv hC₂conv
  rw [hdisj]

  -- Set up the Minkowski difference `C = C₁ - C₂`.
  let C : Set (Fin n → Real) := C₁ - C₂
  have hCne : C.Nonempty := by
    rcases hC₁ne with ⟨x1, hx1⟩
    rcases hC₂ne with ⟨x2, hx2⟩
    refine ⟨x1 - x2, ?_⟩
    change x1 - x2 ∈ Set.image2 (fun a b : Fin n → Real => a - b) C₁ C₂
    exact ⟨x1, hx1, x2, hx2, rfl⟩
  have hCconv : Convex Real C := hC₁conv.sub hC₂conv

  -- (→) Proper separation ⇒ `0 ∉ intrinsicInterior C`.
  -- (←) `0 ∉ intrinsicInterior C` ⇒ build a properly separating hyperplane.
  constructor
  · rintro ⟨H, hsep⟩
    rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hsep with
      ⟨b, β, hb0, hH, hC₁β, hC₂β, hnot⟩
    have hCsub : C ⊆ {x : Fin n → Real | 0 ≤ x ⬝ᵥ b} := by
      intro x hx
      rcases hx with ⟨x1, hx1, x2, hx2, rfl⟩
      have hx1' : β ≤ x1 ⬝ᵥ b := hC₁β x1 hx1
      have hx2' : x2 ⬝ᵥ b ≤ β := hC₂β x2 hx2
      have hx2_le_x1 : x2 ⬝ᵥ b ≤ x1 ⬝ᵥ b := le_trans hx2' hx1'
      have : 0 ≤ x1 ⬝ᵥ b - x2 ⬝ᵥ b := sub_nonneg.mpr hx2_le_x1
      simpa [sub_dotProduct] using this
    have hexistsPos : ∃ w ∈ C, 0 < w ⬝ᵥ b := by
      -- Rewrite the properness condition to the level set `{x | x ⬝ᵥ b = β}`.
      have hnot' :
          ¬ (C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} ∧
              C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β}) := by
        simpa [hH] using hnot
      rcases hC₁ne with ⟨x1₀, hx1₀⟩
      rcases hC₂ne with ⟨x2₀, hx2₀⟩
      by_cases hC₁H : C₁ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β}
      · have hC₂H : ¬ C₂ ⊆ {x : Fin n → Real | x ⬝ᵥ b = β} := by
          intro hC₂H
          exact hnot' ⟨hC₁H, hC₂H⟩
        rcases (Set.not_subset.mp hC₂H) with ⟨x2, hx2, hx2ne⟩
        have hx2ne' : x2 ⬝ᵥ b ≠ β := by simpa using hx2ne
        have hx2lt : x2 ⬝ᵥ b < β :=
          lt_of_le_of_ne (hC₂β x2 hx2) (by simpa [eq_comm] using hx2ne')
        refine ⟨x1₀ - x2, ?_, ?_⟩
        · exact ⟨x1₀, hx1₀, x2, hx2, rfl⟩
        · have hx1ge : β ≤ x1₀ ⬝ᵥ b := hC₁β x1₀ hx1₀
          have hx2lt' : x2 ⬝ᵥ b < x1₀ ⬝ᵥ b := lt_of_lt_of_le hx2lt hx1ge
          have : 0 < x1₀ ⬝ᵥ b - x2 ⬝ᵥ b := sub_pos.mpr hx2lt'
          simpa [sub_dotProduct] using this
      · rcases (Set.not_subset.mp hC₁H) with ⟨x1, hx1, hx1ne⟩
        have hx1ne' : x1 ⬝ᵥ b ≠ β := by simpa using hx1ne
        have hx1gt : β < x1 ⬝ᵥ b :=
          lt_of_le_of_ne (hC₁β x1 hx1) (by simpa using hx1ne'.symm)
        refine ⟨x1 - x2₀, ?_, ?_⟩
        · exact ⟨x1, hx1, x2₀, hx2₀, rfl⟩
        · have hx2le : x2₀ ⬝ᵥ b ≤ β := hC₂β x2₀ hx2₀
          have hx2lt' : x2₀ ⬝ᵥ b < x1 ⬝ᵥ b := lt_of_le_of_lt hx2le hx1gt
          have : 0 < x1 ⬝ᵥ b - x2₀ ⬝ᵥ b := sub_pos.mpr hx2lt'
          simpa [sub_dotProduct] using this
    -- If `0 ∈ intrinsicInterior C`, a small negative multiple of the strictly-positive `w` lies in
    -- `C`, contradicting `C ⊆ {x | 0 ≤ x ⬝ᵥ b}`.
    intro h0
    rcases hexistsPos with ⟨w, hwC, hwpos⟩
    -- Work in the affine span of `C`.
    let A : AffineSubspace Real (Fin n → Real) := affineSpan Real C
    let sA : Set A := ((↑) : A → (Fin n → Real)) ⁻¹' C
    rcases (mem_intrinsicInterior.mp h0) with ⟨y0, hy0, hy0eq⟩
    have hy0eq' : (y0 : Fin n → Real) = 0 := hy0eq
    have h0A : (0 : Fin n → Real) ∈ (A : Set (Fin n → Real)) := by
      simpa [A, hy0eq'] using (y0.property)
    have hwA : w ∈ (A : Set (Fin n → Real)) := by
      exact subset_affineSpan (k := Real) (s := C) hwC
    -- Extract a metric ball around `0` contained in `C`.
    have hsA_nhds : sA ∈ nhds y0 := (mem_interior_iff_mem_nhds).1 hy0
    rcases (Metric.mem_nhds_iff.1 hsA_nhds) with ⟨ε, hε, hball⟩
    have hw_ne0 : w ≠ (0 : Fin n → Real) := by
      intro hw0
      simpa [hw0] using hwpos.ne'
    have hnormw_pos : 0 < ‖w‖ := norm_pos_iff.2 hw_ne0
    -- Choose `t > 0` small enough so that `(-t) • w` lies in the ball around `0`.
    let t : Real := ε / (2 * ‖w‖)
    have htpos : 0 < t := by
      have hden : 0 < 2 * ‖w‖ := by nlinarith [hnormw_pos]
      exact div_pos hε hden
    have ht_lt : ‖(-t) • w‖ < ε := by
      have hwne : (‖w‖ : Real) ≠ 0 := ne_of_gt hnormw_pos
      have hmul : t * ‖w‖ = ε / 2 := by
        calc
          t * ‖w‖ = (ε / (2 * ‖w‖)) * ‖w‖ := by rfl
          _ = (ε * ‖w‖) / (2 * ‖w‖) := by
                simp [div_mul_eq_mul_div, mul_assoc, mul_comm, mul_left_comm]
          _ = ε / 2 := by
                simpa [mul_assoc] using (mul_div_mul_right ε (‖w‖) (2 : Real))
      have habs : |(-t)| = t := by
        simpa [abs_neg, abs_of_pos htpos] using (rfl : |(-t)| = |(-t)|)
      calc
        ‖(-t) • w‖ = |(-t)| * ‖w‖ := by simpa [norm_smul]
        _ = t * ‖w‖ := by simp [habs]
        _ = ε / 2 := hmul
        _ < ε := by linarith [hε]
    have ht_dist : dist ((-t) • w) 0 < ε := by
      simpa [dist_zero_right] using ht_lt
    -- Show `(-t) • w` lies in the affine span, hence defines a point in `A`.
    have hw_dir : w ∈ A.direction := by
      have : w - (0 : Fin n → Real) ∈ A.direction :=
        AffineSubspace.vsub_mem_direction (p1 := w) (p2 := 0) hwA h0A
      simpa [vsub_eq_sub] using this
    have ht_dir : (-t) • w ∈ A.direction := A.direction.smul_mem (-t) hw_dir
    have htA : (-t) • w ∈ (A : Set (Fin n → Real)) := by
      have : (-t) • w +ᵥ (0 : Fin n → Real) ∈ A :=
        vadd_mem_of_mem_direction h0A ht_dir
      simpa using this
    let z0 : A := ⟨(-t) • w, htA⟩
    have hz0_ball : z0 ∈ Metric.ball y0 ε := by
      -- `dist z0 y0 < ε`, using `↑y0 = 0`.
      have : dist (z0 : Fin n → Real) (y0 : Fin n → Real) < ε := by
        simpa [hy0eq', dist_comm] using ht_dist
      simpa using this
    have hz0_mem : z0 ∈ sA := hball hz0_ball
    have hz0C : ((z0 : A) : Fin n → Real) ∈ C := by
      simpa [sA] using hz0_mem
    have hz0_nonneg : 0 ≤ ((z0 : A) : Fin n → Real) ⬝ᵥ b := hCsub hz0C
    have hz0_neg : ((z0 : A) : Fin n → Real) ⬝ᵥ b < 0 := by
      -- `((-t) • w) ⬝ᵥ b = (-t) * (w ⬝ᵥ b)` is strictly negative.
      have : ((-t) • w) ⬝ᵥ b = (-t) * (w ⬝ᵥ b) := by
        simpa using (smul_dotProduct (-t) w b)
      have hwpos' : 0 < w ⬝ᵥ b := hwpos
      have htneg : (-t) < 0 := neg_neg_of_pos htpos
      have : (-t) * (w ⬝ᵥ b) < 0 := mul_neg_of_neg_of_pos htneg hwpos'
      simpa [this] using this
    exact (not_lt_of_ge hz0_nonneg) hz0_neg
  · intro h0not
    -- Apply Theorem 11.2 to `ri C` and the affine subspace `{0}`.
    let C0 : Set (Fin n → Real) := intrinsicInterior Real C
    let M : AffineSubspace Real (Fin n → Real) := AffineSubspace.singleton (0 : Fin n → Real)
    have hC0ne : C0.Nonempty := Set.Nonempty.intrinsicInterior hCconv hCne
    have hC0conv : Convex Real C0 := by
      -- `C0 = euclideanRelativeInterior n C` and the book proves convexity for the latter.
      simpa [C0, intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C)] using
        (convex_euclideanRelativeInterior n C hCconv)
    -- `C0` is relatively open in its affine span.
    have hC0relopen :
        ∃ U : Set (Fin n → Real), IsOpen U ∧ C0 = U ∩ (affineSpan Real C0 : Set (Fin n → Real)) := by
      -- Start from the general description `intrinsicInterior s = U ∩ aff s`.
      let A' : AffineSubspace Real (Fin n → Real) := affineSpan Real C
      let t' : Set A' := interior (((↑) : A' → (Fin n → Real)) ⁻¹' C)
      have ht'open : IsOpen t' := isOpen_interior
      rcases (isOpen_induced_iff.1 ht'open) with ⟨U, hUopen, hpre⟩
      refine ⟨U, hUopen, ?_⟩
      have haff :
          affineSpan Real (intrinsicInterior Real C) = affineSpan Real C :=
        affineSpan_intrinsicInterior_eq (n := n) (C := C) hCconv hCne
      -- Convert the image description of `intrinsicInterior` into an intersection form.
      have hrepr :
          intrinsicInterior Real C =
            U ∩ (affineSpan Real C : Set (Fin n → Real)) := by
        -- `intrinsicInterior` is the image of an open set in `affineSpan`.
        have :
            intrinsicInterior Real C =
              ((↑) : A' → (Fin n → Real)) '' (((↑) : A' → (Fin n → Real)) ⁻¹' U) := by
          -- unfold `intrinsicInterior` and rewrite the interior using `hpre`.
          simp [intrinsicInterior, t', hpre, A']
        -- simplify `image_preimage` and identify the range with the affine span
        simpa [Set.image_preimage_eq_inter_range, Set.range_comp, A'] using this
      -- Rewrite `affineSpan C` as `affineSpan C0` using `haff`.
      simpa [C0, haff.symm] using hrepr
    have hMne : (M : Set (Fin n → Real)).Nonempty := by
      refine ⟨0, ?_⟩
      simp [M]
    have hCM : Disjoint C0 (M : Set (Fin n → Real)) := by
      refine Set.disjoint_left.2 ?_
      intro x hxC0 hxM
      have hx0 : x = (0 : Fin n → Real) := by simpa [M] using hxM
      subst hx0
      exact h0not hxC0
    rcases
        exists_hyperplane_contains_affine_of_convex_relativelyOpen n C0 M hC0ne hC0conv hC0relopen
          hMne hCM with
      ⟨H, hMH, b, β, hb0, hH, hcases⟩
    have hβ : β = 0 := by
      have h0M : (0 : Fin n → Real) ∈ M := by simp [M]
      have h0H : (0 : Fin n → Real) ∈ H := hMH h0M
      have : (0 : Fin n → Real) ⬝ᵥ b = β := by simpa [hH] using h0H
      simpa using this.symm
    subst hβ
    -- Orient the separator so that `C0 ⊆ {x | 0 < x ⬝ᵥ b}`.
    rcases hcases with hlt | hgt
    · -- `C0 ⊆ {x | x ⬝ᵥ b < 0}`; replace `b` by `-b`.
      have hpos : ∀ x ∈ C0, 0 < x ⬝ᵥ (-b) := by
        intro x hx
        have : x ⬝ᵥ b < 0 := hlt hx
        have : 0 < -(x ⬝ᵥ b) := by simpa using (neg_pos.mpr this)
        simpa [dotProduct_neg] using this
      -- Show `C ⊆ {x | 0 ≤ x ⬝ᵥ (-b)}` using `C ⊆ closure C0`.
      have hclosure : closure C ⊆ closure C0 := by
        have h :=
          euclidean_closure_subset_closure_relativeInterior_of_nonempty (n := n) (C := C) hCconv
            hCne
        -- rewrite `euclideanRelativeInterior` to `intrinsicInterior`
        simpa [C0, intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C)] using h
      have hC_closure : C ⊆ closure C0 := by
        intro x hx
        exact hclosure (subset_closure hx)
      have hclosedHalf : IsClosed {x : Fin n → Real | 0 ≤ x ⬝ᵥ (-b)} := by
        have hcont :
            Continuous fun x : Fin n → Real => x ⬝ᵥ (-b) := by
          simpa using
            (Continuous.dotProduct (A := fun x : Fin n → Real => x) (B := fun _ => (-b))
              continuous_id continuous_const)
        have : IsClosed ((fun x : Fin n → Real => x ⬝ᵥ (-b)) ⁻¹' Set.Ici (0 : Real)) :=
          isClosed_Ici.preimage hcont
        simpa [Set.preimage, Set.Ici] using this
      have hclosureHalf : closure C0 ⊆ {x : Fin n → Real | 0 ≤ x ⬝ᵥ (-b)} :=
        closure_minimal (by
          intro x hx
          exact le_of_lt (hpos x hx)) hclosedHalf
      have hCnonneg : ∀ x ∈ C, 0 ≤ x ⬝ᵥ (-b) := by
        intro x hx
        exact hclosureHalf (hC_closure hx)
      -- Derive the EReal inf/sup conditions for Theorem 11.1.
      let f : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ (-b) : Real) : EReal)
      have ha :
          sInf (f '' C₁) ≥ sSup (f '' C₂) := by
        have hSup_le : ∀ x1 ∈ C₁, sSup (f '' C₂) ≤ f x1 := by
          intro x1 hx1
          refine sSup_le ?_
          rintro _ ⟨x2, hx2, rfl⟩
          have hx : 0 ≤ (x1 - x2) ⬝ᵥ (-b) :=
            hCnonneg (x1 - x2) ⟨x1, hx1, x2, hx2, rfl⟩
          have hx' : x2 ⬝ᵥ (-b) ≤ x1 ⬝ᵥ (-b) := by
            have : 0 ≤ x1 ⬝ᵥ (-b) - x2 ⬝ᵥ (-b) := by
              simpa [sub_dotProduct] using hx
            exact sub_nonneg.mp this
          exact (EReal.coe_le_coe_iff.2 hx')
        have : sSup (f '' C₂) ≤ sInf (f '' C₁) := by
          refine le_sInf ?_
          rintro _ ⟨x1, hx1, rfl⟩
          exact hSup_le x1 hx1
        exact this
      have hb :
          sSup (f '' C₁) > sInf (f '' C₂) := by
        rcases hC0ne with ⟨x, hxC0⟩
        have hxpos : 0 < x ⬝ᵥ (-b) := hpos x hxC0
        have hxC : x ∈ C := (intrinsicInterior_subset (𝕜 := Real) (s := C)) hxC0
        rcases hxC with ⟨x1, hx1, x2, hx2, rfl⟩
        have hxlt : x2 ⬝ᵥ (-b) < x1 ⬝ᵥ (-b) := by
          have : 0 < x1 ⬝ᵥ (-b) - x2 ⬝ᵥ (-b) := by
            simpa [sub_dotProduct] using hxpos
          exact sub_pos.mp this
        have hxlt' : f x2 < f x1 := EReal.coe_lt_coe_iff.2 hxlt
        have hx1mem : f x1 ∈ f '' C₁ := ⟨x1, hx1, rfl⟩
        have hx2mem : f x2 ∈ f '' C₂ := ⟨x2, hx2, rfl⟩
        have hsInf_le : sInf (f '' C₂) ≤ f x2 := sInf_le hx2mem
        have hlt : sInf (f '' C₂) < f x1 := lt_of_le_of_lt hsInf_le hxlt'
        have : sInf (f '' C₂) < sSup (f '' C₁) := lt_of_lt_of_le hlt (le_sSup hx1mem)
        simpa [gt_iff_lt] using this
      exact
        exists_hyperplaneSeparatesProperly_of_EReal_inf_sup_conditions n C₁ C₂ hC₁ne hC₂ne (-b) ha hb
    · -- `C0 ⊆ {x | 0 < x ⬝ᵥ b}` already.
      have hpos : ∀ x ∈ C0, 0 < x ⬝ᵥ b := by
        intro x hx
        exact hgt hx
      have hclosure : closure C ⊆ closure C0 := by
        have h :=
          euclidean_closure_subset_closure_relativeInterior_of_nonempty (n := n) (C := C) hCconv
            hCne
        simpa [C0, intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := C)] using h
      have hC_closure : C ⊆ closure C0 := by
        intro x hx
        exact hclosure (subset_closure hx)
      have hclosedHalf : IsClosed {x : Fin n → Real | 0 ≤ x ⬝ᵥ b} := by
        have hcont :
            Continuous fun x : Fin n → Real => x ⬝ᵥ b := by
          simpa using
            (Continuous.dotProduct (A := fun x : Fin n → Real => x) (B := fun _ => b)
              continuous_id continuous_const)
        have : IsClosed ((fun x : Fin n → Real => x ⬝ᵥ b) ⁻¹' Set.Ici (0 : Real)) :=
          isClosed_Ici.preimage hcont
        simpa [Set.preimage, Set.Ici] using this
      have hclosureHalf : closure C0 ⊆ {x : Fin n → Real | 0 ≤ x ⬝ᵥ b} :=
        closure_minimal (by
          intro x hx
          exact le_of_lt (hpos x hx)) hclosedHalf
      have hCnonneg : ∀ x ∈ C, 0 ≤ x ⬝ᵥ b := by
        intro x hx
        exact hclosureHalf (hC_closure hx)
      let f : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ b : Real) : EReal)
      have ha :
          sInf (f '' C₁) ≥ sSup (f '' C₂) := by
        have hSup_le : ∀ x1 ∈ C₁, sSup (f '' C₂) ≤ f x1 := by
          intro x1 hx1
          refine sSup_le ?_
          rintro _ ⟨x2, hx2, rfl⟩
          have hx : 0 ≤ (x1 - x2) ⬝ᵥ b :=
            hCnonneg (x1 - x2) ⟨x1, hx1, x2, hx2, rfl⟩
          have hx' : x2 ⬝ᵥ b ≤ x1 ⬝ᵥ b := by
            have : 0 ≤ x1 ⬝ᵥ b - x2 ⬝ᵥ b := by
              simpa [sub_dotProduct] using hx
            exact sub_nonneg.mp this
          exact (EReal.coe_le_coe_iff.2 hx')
        have : sSup (f '' C₂) ≤ sInf (f '' C₁) := by
          refine le_sInf ?_
          rintro _ ⟨x1, hx1, rfl⟩
          exact hSup_le x1 hx1
        exact this
      have hb :
          sSup (f '' C₁) > sInf (f '' C₂) := by
        rcases hC0ne with ⟨x, hxC0⟩
        have hxpos : 0 < x ⬝ᵥ b := hpos x hxC0
        have hxC : x ∈ C := (intrinsicInterior_subset (𝕜 := Real) (s := C)) hxC0
        rcases hxC with ⟨x1, hx1, x2, hx2, rfl⟩
        have hxlt : x2 ⬝ᵥ b < x1 ⬝ᵥ b := by
          have : 0 < x1 ⬝ᵥ b - x2 ⬝ᵥ b := by
            simpa [sub_dotProduct] using hxpos
          exact sub_pos.mp this
        have hxlt' : f x2 < f x1 := EReal.coe_lt_coe_iff.2 hxlt
        have hx1mem : f x1 ∈ f '' C₁ := ⟨x1, hx1, rfl⟩
        have hx2mem : f x2 ∈ f '' C₂ := ⟨x2, hx2, rfl⟩
        have hsInf_le : sInf (f '' C₂) ≤ f x2 := sInf_le hx2mem
        have hlt : sInf (f '' C₂) < f x1 := lt_of_le_of_lt hsInf_le hxlt'
        have : sInf (f '' C₂) < sSup (f '' C₁) := lt_of_lt_of_le hlt (le_sSup hx1mem)
        simpa [gt_iff_lt] using this
      exact
        exists_hyperplaneSeparatesProperly_of_EReal_inf_sup_conditions n C₁ C₂ hC₁ne hC₂ne b ha hb
-/

end Section11
end Chap03
