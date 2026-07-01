/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part9

section Chap03
section Section12

/-- Defn 12.1: A closed half-space in `ℝ^(n+1)` (written with coordinates `(x, μ)` where
`x ∈ ℝ^n` and `μ ∈ ℝ`) is classified into three types by its defining inequality:

1. (Vertical) a set `{(x, μ) | ⟪x, b⟫ ≤ β}` with `b ≠ 0`;
2. (Upper) a set `{(x, μ) | μ ≥ ⟪x, b⟫ - β}` (the epigraph of an affine function);
3. (Lower) a set `{(x, μ) | μ ≤ ⟪x, b⟫ - β}`. -/
def IsVerticalHalfSpace (n : Nat) (H : Set ((Fin n → Real) × Real)) : Prop :=
  ∃ (b : Fin n → Real) (β : Real),
    b ≠ 0 ∧ H = {p : (Fin n → Real) × Real | p.1 ⬝ᵥ b ≤ β}

/-- Defn 12.1 (Upper): `H ⊆ ℝ^n × ℝ` has the form `{(x, μ) | μ ≥ ⟪x, b⟫ - β}`. -/
def IsUpperHalfSpace (n : Nat) (H : Set ((Fin n → Real) × Real)) : Prop :=
  ∃ (b : Fin n → Real) (β : Real),
    H = {p : (Fin n → Real) × Real | p.2 ≥ p.1 ⬝ᵥ b - β}

/-- Defn 12.1 (Lower): `H ⊆ ℝ^n × ℝ` has the form `{(x, μ) | μ ≤ ⟪x, b⟫ - β}`. -/
def IsLowerHalfSpace (n : Nat) (H : Set ((Fin n → Real) × Real)) : Prop :=
  ∃ (b : Fin n → Real) (β : Real),
    H = {p : (Fin n → Real) × Real | p.2 ≤ p.1 ⬝ᵥ b - β}

/-- If `b ≠ 0`, then `b ⬝ᵥ b ≠ 0`. -/
lemma dotProduct_self_ne_zero {n : Nat} (b : Fin n → Real) (hb : b ≠ 0) : b ⬝ᵥ b ≠ 0 := by
  intro h
  have : b = 0 := (dotProduct_self_eq_zero (v := b)).1 h
  exact hb this

/-- For a nonzero vector `b`, there exists an `x` with `x ⬝ᵥ b ≤ β`. -/
lemma exists_dotProduct_le {n : Nat} (b : Fin n → Real) (hb : b ≠ 0) (β : Real) :
    ∃ x : Fin n → Real, x ⬝ᵥ b ≤ β := by
  have hbb : b ⬝ᵥ b ≠ 0 := dotProduct_self_ne_zero b hb
  let c : Real := (-(|β| + 1)) / (b ⬝ᵥ b)
  refine ⟨c • b, ?_⟩
  have hdot : (c • b) ⬝ᵥ b = -(|β| + 1) := by
    have hc : c * (b ⬝ᵥ b) = -(|β| + 1) := by
      have : (-(|β| + 1) / (b ⬝ᵥ b)) * (b ⬝ᵥ b) = -(|β| + 1) := by
        field_simp [hbb]
      simpa [c, smul_eq_mul] using this
    calc
      (c • b) ⬝ᵥ b = b ⬝ᵥ (c • b) := by simp [dotProduct_comm]
      _ = c • (b ⬝ᵥ b) := by simp [dotProduct_smul]
      _ = c * (b ⬝ᵥ b) := by simp [smul_eq_mul]
      _ = -(|β| + 1) := hc
  have hβ : -(|β| + 1) ≤ β := by
    have h1 : -|β| ≤ β := neg_abs_le β
    linarith
  simpa [hdot] using hβ

/-- If `H` has a representation with `t = 0`, then it is a vertical half-space. -/
lemma closedHalfSpace_isVertical_of_repr_t_eq_zero {n : Nat} {H : Set ((Fin n → Real) × Real)}
    {b : Fin n → Real} {t β : Real} (hnonzero : b ≠ 0 ∨ t ≠ 0) (ht : t = 0)
    (hrepr : H = {p : (Fin n → Real) × Real | p.1 ⬝ᵥ b + p.2 * t ≤ β}) :
    IsVerticalHalfSpace n H := by
  have hb : b ≠ 0 := by
    rcases hnonzero with hb | htne
    · exact hb
    · exfalso
      exact htne ht
  refine ⟨b, β, hb, ?_⟩
  refine hrepr.trans ?_
  ext p
  simp [ht]

/-- If `H = {p | p.1 ⬝ᵥ b + p.2 * t ≤ β}` with `t < 0`, then `H` is an upper half-space. -/
lemma closedHalfSpace_isUpper_of_repr_t_neg {n : Nat} {H : Set ((Fin n → Real) × Real)}
    {b : Fin n → Real} {t β : Real} (ht : t < 0)
    (hrepr : H = {p : (Fin n → Real) × Real | p.1 ⬝ᵥ b + p.2 * t ≤ β}) :
    IsUpperHalfSpace n H := by
  refine ⟨(-(t⁻¹)) • b, -(β / t), ?_⟩
  ext p
  have h_aff :
      p.1 ⬝ᵥ ((-(t⁻¹)) • b) - (-(β / t)) = (β - p.1 ⬝ᵥ b) / t := by
    simp [dotProduct_smul, div_eq_mul_inv, sub_eq_add_neg]
    ring
  constructor
  · intro hp
    have hp' : p.1 ⬝ᵥ b + p.2 * t ≤ β := by simpa [hrepr] using hp
    have hp'' : p.2 * t ≤ β - p.1 ⬝ᵥ b := by linarith
    have hdiv : (β - p.1 ⬝ᵥ b) / t ≤ p.2 := (div_le_iff_of_neg ht).2 hp''
    have : p.1 ⬝ᵥ ((-(t⁻¹)) • b) - (-(β / t)) ≤ p.2 := by
      rw [h_aff]
      exact hdiv
    have : p.2 ≥ p.1 ⬝ᵥ ((-(t⁻¹)) • b) - (-(β / t)) := by
      simpa [ge_iff_le] using this
    exact this
  · intro hp
    have hp_le : p.1 ⬝ᵥ ((-(t⁻¹)) • b) - (-(β / t)) ≤ p.2 := by
      simpa [ge_iff_le] using hp
    have hdiv : (β - p.1 ⬝ᵥ b) / t ≤ p.2 := by
      rw [← h_aff]
      exact hp_le
    have hp'' : p.2 * t ≤ β - p.1 ⬝ᵥ b := (div_le_iff_of_neg ht).1 hdiv
    have : p.1 ⬝ᵥ b + p.2 * t ≤ β := by linarith
    simpa [hrepr] using this

/-- If `H = {p | p.1 ⬝ᵥ b + p.2 * t ≤ β}` with `0 < t`, then `H` is a lower half-space. -/
lemma closedHalfSpace_isLower_of_repr_t_pos {n : Nat} {H : Set ((Fin n → Real) × Real)}
    {b : Fin n → Real} {t β : Real} (ht : 0 < t)
    (hrepr : H = {p : (Fin n → Real) × Real | p.1 ⬝ᵥ b + p.2 * t ≤ β}) :
    IsLowerHalfSpace n H := by
  refine ⟨(-(t⁻¹)) • b, -(β / t), ?_⟩
  ext p
  have h_aff :
      p.1 ⬝ᵥ ((-(t⁻¹)) • b) - (-(β / t)) = (β - p.1 ⬝ᵥ b) / t := by
    simp [dotProduct_smul, div_eq_mul_inv, sub_eq_add_neg]
    ring
  constructor
  · intro hp
    have hp' : p.1 ⬝ᵥ b + p.2 * t ≤ β := by simpa [hrepr] using hp
    have hp'' : p.2 * t ≤ β - p.1 ⬝ᵥ b := by linarith
    have hdiv : p.2 ≤ (β - p.1 ⬝ᵥ b) / t := (le_div_iff₀ ht).2 hp''
    have : p.2 ≤ p.1 ⬝ᵥ ((-(t⁻¹)) • b) - (-(β / t)) := by
      rw [h_aff]
      exact hdiv
    exact this
  · intro hp
    have hdiv : p.2 ≤ (β - p.1 ⬝ᵥ b) / t := by
      rw [← h_aff]
      exact hp
    have hp'' : p.2 * t ≤ β - p.1 ⬝ᵥ b := (le_div_iff₀ ht).1 hdiv
    have : p.1 ⬝ᵥ b + p.2 * t ≤ β := by linarith
    simpa [hrepr] using this

/-- The three half-space types (vertical, upper, lower) are pairwise incompatible. -/
lemma halfSpaceTypes_pairwise_disjoint {n : Nat} {H : Set ((Fin n → Real) × Real)} :
    (¬ (IsVerticalHalfSpace n H ∧ IsUpperHalfSpace n H)) ∧
      (¬ (IsVerticalHalfSpace n H ∧ IsLowerHalfSpace n H)) ∧
        (¬ (IsUpperHalfSpace n H ∧ IsLowerHalfSpace n H)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hV, hU⟩
    rcases hV with ⟨b, β, hb, hHb⟩
    rcases hU with ⟨b', β', hHb'⟩
    rcases exists_dotProduct_le b hb β with ⟨x, hx⟩
    let μ : Real := (x ⬝ᵥ b' - β') - 1
    have hin : ((x, μ) : (Fin n → Real) × Real) ∈ H := by
      rw [hHb]
      simpa using hx
    have hout : ((x, μ) : (Fin n → Real) × Real) ∉ H := by
      rw [hHb']
      have : ¬ (μ ≥ x ⬝ᵥ b' - β') := by
        dsimp [μ]
        linarith
      simpa [Set.mem_setOf_eq] using this
    exact hout hin
  · rintro ⟨hV, hL⟩
    rcases hV with ⟨b, β, hb, hHb⟩
    rcases hL with ⟨b', β', hHb'⟩
    rcases exists_dotProduct_le b hb β with ⟨x, hx⟩
    let μ : Real := (x ⬝ᵥ b' - β') + 1
    have hin : ((x, μ) : (Fin n → Real) × Real) ∈ H := by
      rw [hHb]
      simpa using hx
    have hout : ((x, μ) : (Fin n → Real) × Real) ∉ H := by
      rw [hHb']
      have : ¬ (μ ≤ x ⬝ᵥ b' - β') := by
        dsimp [μ]
        linarith
      simpa [Set.mem_setOf_eq] using this
    exact hout hin
  · rintro ⟨hU, hL⟩
    rcases hU with ⟨bU, βU, hHU⟩
    rcases hL with ⟨bL, βL, hHL⟩
    let g : Real := (0 : Fin n → Real) ⬝ᵥ bU - βU
    let h : Real := (0 : Fin n → Real) ⬝ᵥ bL - βL
    let μ : Real := max g (h + 1)
    have hin : ((0, μ) : (Fin n → Real) × Real) ∈ H := by
      rw [hHU]
      dsimp [μ, g]
      exact le_max_left _ _
    have hout : ((0, μ) : (Fin n → Real) × Real) ∉ H := by
      rw [hHL]
      have h1 : h + 1 ≤ μ := by
        dsimp [μ]
        exact le_max_right _ _
      have hhμ : h < μ := by linarith [h1]
      have hhμ' := hhμ
      dsimp [h] at hhμ'
      have hhμ'' := hhμ'
      simp at hhμ''
      simp [Set.mem_setOf_eq]
      exact hhμ''
    exact hout hin

/-- Text 12.0.1: Every closed half-space in `ℝ^(n+1)` belongs to exactly one of the following
categories: vertical, upper, or lower. -/
theorem closedHalfSpace_trichotomy (n : Nat) (H : Set ((Fin n → Real) × Real))
    (hH :
      ∃ (b : Fin n → Real) (t β : Real),
        (b ≠ 0 ∨ t ≠ 0) ∧
          H = {p : (Fin n → Real) × Real | p.1 ⬝ᵥ b + p.2 * t ≤ β}) :
    (IsVerticalHalfSpace n H ∨ IsUpperHalfSpace n H ∨ IsLowerHalfSpace n H) ∧
      ¬ (IsVerticalHalfSpace n H ∧ IsUpperHalfSpace n H) ∧
      ¬ (IsVerticalHalfSpace n H ∧ IsLowerHalfSpace n H) ∧
      ¬ (IsUpperHalfSpace n H ∧ IsLowerHalfSpace n H) := by
  rcases hH with ⟨b, t, β, hnonzero, hrepr⟩
  have htypes : IsVerticalHalfSpace n H ∨ IsUpperHalfSpace n H ∨ IsLowerHalfSpace n H := by
    rcases lt_trichotomy t 0 with ht | ht | ht
    · exact Or.inr (Or.inl (closedHalfSpace_isUpper_of_repr_t_neg (n := n) (ht := ht) hrepr))
    · exact Or.inl (closedHalfSpace_isVertical_of_repr_t_eq_zero (n := n)
        (hnonzero := hnonzero) (ht := ht) hrepr)
    · exact Or.inr (Or.inr (closedHalfSpace_isLower_of_repr_t_pos (n := n) (ht := ht) hrepr))
  have hdisj := halfSpaceTypes_pairwise_disjoint (n := n) (H := H)
  rcases hdisj with ⟨hVU, hrest⟩
  rcases hrest with ⟨hVL, hUL⟩
  refine ⟨htypes, ?_⟩
  refine ⟨hVU, ?_⟩
  exact ⟨hVL, hUL⟩

/-- A continuous linear functional on `E × ℝ` evaluates as `l (x, μ) = l (x, 0) + μ * l (0, 1)`. -/
lemma strongDual_apply_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : StrongDual ℝ (E × ℝ)) (x : E) (μ : ℝ) :
    l (x, μ) = l (x, (0 : ℝ)) + μ * l ((0 : E), (1 : ℝ)) := by
  have hdecomp : (x, μ) = (x, (0 : ℝ)) + ((0 : E), μ) := by
    ext <;> simp
  have hsmul : ((0 : E), μ) = μ • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  have hl0 : l ((0 : E), μ) = μ * l ((0 : E), (1 : ℝ)) := by
    calc
      l ((0 : E), μ) = l (μ • ((0 : E), (1 : ℝ))) := congrArg l hsmul
      _ = μ • l ((0 : E), (1 : ℝ)) := l.map_smul μ ((0 : E), (1 : ℝ))
      _ = μ * l ((0 : E), (1 : ℝ)) := by simp [smul_eq_mul]
  calc
    l (x, μ) = l ((x, (0 : ℝ)) + ((0 : E), μ)) := congrArg l hdecomp
    _ = l (x, (0 : ℝ)) + l ((0 : E), μ) := l.map_add (x, (0 : ℝ)) ((0 : E), μ)
    _ = l (x, (0 : ℝ)) + μ * l ((0 : E), (1 : ℝ)) := by simp [hl0]

/-- The epigraph `{(x, μ) | f x ≤ μ}` of a convex lower-semicontinuous function is closed and convex. -/
lemma epigraph_closed_convex_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f) (hf_closed : LowerSemicontinuous f) :
    let C : Set (E × ℝ) := {p : E × ℝ | f p.1 ≤ p.2}
    Convex ℝ C ∧ IsClosed C := by
  intro C
  constructor
  · simpa [C, and_true] using hf_convex.convex_epigraph
  · simpa [C] using hf_closed.isClosed_epigraph

/-- Any point strictly below the epigraph can be strictly separated by an affine minorant. -/
lemma exists_affineMap_strictly_above_below_point {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_closed : LowerSemicontinuous f) :
    ∀ (x0 : E) (μ0 : ℝ),
      μ0 < f x0 →
        ∃ h : AffineMap ℝ E ℝ, (∀ y : E, h y ≤ f y) ∧ μ0 < h x0 := by
  classical
  intro x0 μ0 hμ0
  let C : Set (E × ℝ) := {p : E × ℝ | f p.1 ≤ p.2}
  have hC : Convex ℝ C ∧ IsClosed C := epigraph_closed_convex_univ f hf_convex hf_closed
  have hx0 : (x0, μ0) ∉ C := by
    intro hx0
    have : f x0 ≤ μ0 := by simpa [C] using hx0
    exact (not_lt_of_ge this) hμ0
  obtain ⟨l, u, hl, hu⟩ :=
    geometric_hahn_banach_closed_point (E := E × ℝ) (s := C) (x := (x0, μ0)) hC.1 hC.2 hx0
  let t : ℝ := l ((0 : E), (1 : ℝ))
  let φ : E →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inl ℝ E ℝ)
  have ht : t < 0 := by
    have ht_le : t ≤ 0 := by
      by_contra ht0
      have ht0' : 0 < t := lt_of_not_ge ht0
      let μ : ℝ := max (f (0 : E)) ((u + 1) / t)
      have hμC : ((0 : E), μ) ∈ C := by
        have : f (0 : E) ≤ μ := le_max_left _ _
        simpa [C] using this
      have hlt : l ((0 : E), μ) < u := hl _ hμC
      have hμge : (u + 1) / t ≤ μ := le_max_right _ _
      have hmul' : ((u + 1) / t) * t ≤ μ * t :=
        mul_le_mul_of_nonneg_right hμge (le_of_lt ht0')
      have hmul : u + 1 ≤ μ * t := by
        have htne : t ≠ 0 := ne_of_gt ht0'
        simpa [div_eq_mul_inv, htne] using hmul'
      have hu_lt : u < u + 1 := by linarith
      have hlt' : u < l ((0 : E), μ) := by
        have : u < μ * t := lt_of_lt_of_le hu_lt hmul
        have hl0 : l ((0 : E), μ) = μ * t := by
          have := strongDual_apply_prod (l := l) (x := (0 : E)) (μ := μ)
          have hl00 : l ((0 : E), (0 : ℝ)) = 0 := by
            change l (0 : E × ℝ) = 0
            exact l.map_zero
          simpa [t, hl00] using this
        simpa [hl0] using this
      exact (lt_irrefl u) (lt_trans hlt' hlt)
    have ht_ne : t ≠ 0 := by
      by_contra ht0
      have ht0' : t = 0 := by simpa using ht0
      have hpos_u : 0 < u := by
        have hC0 : ((0 : E), f (0 : E)) ∈ C := by simp [C]
        have hlt : l ((0 : E), f (0 : E)) < u := hl _ hC0
        have hl0 : l ((0 : E), f (0 : E)) = 0 := by
          have := strongDual_apply_prod (l := l) (x := (0 : E)) (μ := f (0 : E))
          have hl00 : l ((0 : E), (0 : ℝ)) = 0 := by
            change l (0 : E × ℝ) = 0
            exact l.map_zero
          simpa [t, ht0', hl00] using this
        simpa [hl0] using hlt
      have hφ_lt : ∀ y : E, φ y < u := by
        intro y
        have hyC : (y, f y) ∈ C := by simp [C]
        have hlt : l (y, f y) < u := hl _ hyC
        have hdecomp : l (y, f y) = φ y := by
          have := strongDual_apply_prod (l := l) (x := y) (μ := f y)
          simpa [φ, t, ht0', smul_eq_mul, add_zero] using this
        simpa [hdecomp] using hlt
      have hφ_zero : φ = 0 := by
        by_contra hφ0
        have hex : ∃ y : E, φ y ≠ 0 := by
          by_contra h'
          push_neg at h'
          apply hφ0
          ext y
          simpa using h' y
        rcases hex with ⟨y, hy⟩
        have hpos : ∃ y' : E, 0 < φ y' := by
          rcases lt_or_gt_of_ne hy with hylt | hygt
          · refine ⟨-y, ?_⟩
            have : 0 < -(φ y) := neg_pos.mpr hylt
            simpa using (by simpa [map_neg] using this)
          · exact ⟨y, hygt⟩
        rcases hpos with ⟨y', hy'pos⟩
        let r : ℝ := (u + 1) / (φ y')
        have hr : 0 < r := by
          have : 0 < u + 1 := lt_trans hpos_u (by linarith)
          exact div_pos this hy'pos
        let z : E := r • y'
        have hz : φ z = u + 1 := by
          have hne : φ y' ≠ 0 := ne_of_gt hy'pos
          simp [z, r, div_eq_mul_inv, hne, smul_eq_mul]
        have : φ z < u := hφ_lt z
        linarith
      have hlx0 : l (x0, μ0) = 0 := by
        have := strongDual_apply_prod (l := l) (x := x0) (μ := μ0)
        have hlx0' : l (x0, (0 : ℝ)) = φ x0 := by
          simp [φ]
        simpa [φ, t, ht0', hφ_zero, hlx0', smul_eq_mul, add_zero] using this
      have : u < 0 := by simpa [hlx0] using hu
      exact (lt_asymm hpos_u this).elim
    exact lt_of_le_of_ne ht_le ht_ne
  let h : AffineMap ℝ E ℝ :=
    ((1 / (-t)) • φ.toAffineMap) + AffineMap.const ℝ E ((-u) / (-t))
  have h_apply (y : E) : h y = (φ y - u) / (-t) := by
    simp [h, div_eq_mul_inv, sub_eq_add_neg, add_mul]
    ring
  refine ⟨h, ?_, ?_⟩
  · intro y
    have hyC : (y, f y) ∈ C := by simp [C]
    have hlt : l (y, f y) < u := hl _ hyC
    have hlt' : φ y + f y * t < u := by
      have hdecomp := strongDual_apply_prod (l := l) (x := y) (μ := f y)
      have hy0 : l (y, (0 : ℝ)) = φ y := by simp [φ]
      have : φ y + f y * t < u := by
        have : l (y, (0 : ℝ)) + f y * t < u := by simpa [t, hdecomp] using hlt
        simpa [hy0] using this
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    have hhy : h y < f y := by
      have htpos : 0 < -t := by linarith
      have : (φ y - u) / (-t) < f y := by
        have : φ y - u < f y * (-t) := by linarith [hlt']
        exact (div_lt_iff₀ htpos).2 this
      simpa [h_apply] using this
    exact le_of_lt hhy
  · have hlt : u < l (x0, μ0) := hu
    have hlt' : u < φ x0 + μ0 * t := by
      have hdecomp := strongDual_apply_prod (l := l) (x := x0) (μ := μ0)
      have hx0_0 : l (x0, (0 : ℝ)) = φ x0 := by simp [φ]
      have : u < l (x0, (0 : ℝ)) + μ0 * t := by simpa [t, hdecomp] using hlt
      simpa [hx0_0] using this
    have hx0 : μ0 < h x0 := by
      have htpos : 0 < -t := by linarith
      have : μ0 < (φ x0 - u) / (-t) := by
        have : μ0 * (-t) < φ x0 - u := by linarith [hlt']
        exact (lt_div_iff₀ htpos).2 this
      simpa [h_apply] using this
    exact hx0

/-- Theorem 12.1. A closed convex function `f` is the pointwise supremum of the collection of all
affine maps `h` such that `h ≤ f`. -/
theorem closedConvex_eq_sSup_affineMap_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f) (hf_closed : LowerSemicontinuous f) :
    ∀ x : E,
      f x =
        sSup
          ((fun h : AffineMap ℝ E ℝ => h x) '' {h : AffineMap ℝ E ℝ | ∀ y : E, h y ≤ f y}) := by
  classical
  intro x
  set Sx : Set ℝ :=
    (fun h : AffineMap ℝ E ℝ => h x) '' {h : AffineMap ℝ E ℝ | ∀ y : E, h y ≤ f y}
  have hSx_bdd : BddAbove Sx := by
    refine ⟨f x, ?_⟩
    rintro z ⟨h, hh, rfl⟩
    exact hh x
  have hSx_nonempty : Sx.Nonempty := by
    obtain ⟨h, hh, _hx⟩ :=
      exists_affineMap_strictly_above_below_point f hf_convex hf_closed x (f x - 1) (by linarith)
    refine ⟨h x, ?_⟩
    exact ⟨h, hh, rfl⟩
  have hsSup_le : sSup Sx ≤ f x := by
    refine csSup_le hSx_nonempty ?_
    rintro z ⟨h, hh, rfl⟩
    exact hh x
  have hle_sSup : f x ≤ sSup Sx := by
    refine le_of_forall_lt ?_
    intro μ hμ
    obtain ⟨h, hh, hxμ⟩ := exists_affineMap_strictly_above_below_point f hf_convex hf_closed x μ hμ
    have hxmem : h x ∈ Sx := ⟨h, hh, rfl⟩
    have hxle : h x ≤ sSup Sx := le_csSup hSx_bdd hxmem
    exact lt_of_lt_of_le hxμ hxle
  exact le_antisymm hle_sSup hsSup_le

/-- `clConv n f` is a Lean stand-in for the book's `cl (conv f)` for an extended-real-valued
function `f : ℝ^n → [-∞, ∞]`. It is defined pointwise as the supremum of all affine functions
majorized by `f`. -/
noncomputable def clConv (n : Nat) (f : (Fin n → Real) → EReal) : (Fin n → Real) → EReal :=
  fun x =>
    sSup
      ((fun h : AffineMap ℝ (Fin n → Real) Real => (h x : EReal)) ''
        {h : AffineMap ℝ (Fin n → Real) Real | ∀ y : Fin n → Real, (h y : EReal) ≤ f y})

/-- Corollary 12.1.1. If `f : ℝ^n → [-∞, ∞]` is any function, then `cl (conv f)` (here represented
by `clConv n f`) is the pointwise supremum of the collection of all affine functions on `ℝ^n`
majorized by `f`. -/
theorem clConv_eq_sSup_affineMap_le (n : Nat) (f : (Fin n → Real) → EReal) :
    ∀ x : Fin n → Real,
      clConv n f x =
        sSup
          ((fun h : AffineMap ℝ (Fin n → Real) Real => (h x : EReal)) ''
            {h : AffineMap ℝ (Fin n → Real) Real | ∀ y : Fin n → Real, (h y : EReal) ≤ f y}) := by
  intro x
  rfl

/-- A proper convex function on `ℝ^n` has a point where it takes a finite real value. -/
lemma properConvexFunctionOn_exists_finite_point {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∃ x0 : Fin n → Real, ∃ r0 : Real, f x0 = (r0 : EReal) := by
  have hne_dom : (effectiveDomain (Set.univ : Set (Fin n → Real)) f).Nonempty :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain (S := (Set.univ : Set (Fin n → Real)))
      (f := f)).1 hf.2.1
  rcases hne_dom with ⟨x0, hx0⟩
  have hx0_ne_top :
      f x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx0
  have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hf.2.2 x0 (by simp)
  refine ⟨x0, (f x0).toReal, ?_⟩
  simpa using (EReal.coe_toReal (x := f x0) hx0_ne_top hx0_ne_bot).symm

/-- The `Real`-valued function `x ↦ (f x).toReal` is convex on the effective domain
of a proper convex function `f`. -/
lemma convexOn_toReal_effectiveDomain {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (fun x => (f x).toReal) := by
  classical
  let C : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hconvC : Convex ℝ C := by
    exact
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
  refine ⟨hconvC, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_le_one : b ≤ (1 : Real) := by linarith [hab, ha]
  have hx_univ : x ∈ (Set.univ : Set (Fin n → Real)) := by simp
  have hy_univ : y ∈ (Set.univ : Set (Fin n → Real)) := by simp
  have hx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hy_ne_bot : f y ≠ (⊥ : EReal) := hf.2.2 y (by simp)
  have hx_ne_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx
  have hy_ne_top : f y ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hy
  have hx_eq : f x = ((f x).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := f x) hx_ne_top hx_ne_bot).symm
  have hy_eq : f y = ((f y).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := f y) hy_ne_top hy_ne_bot).symm
  have hμ : f x ≤ ((f x).toReal : EReal) := le_of_eq hx_eq
  have hν : f y ≤ ((f y).toReal : EReal) := le_of_eq hy_eq
  have hcond :=
    convexFunctionOn_epigraph_condition (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
      x hx_univ y hy_univ (f x).toReal (f y).toReal hμ hν b hb hb_le_one
  rcases hcond with ⟨_, hle⟩
  let rhs : Real := a * (f x).toReal + b * (f y).toReal
  have hxcombo : f (a • x + b • y) ≤ (rhs : EReal) := by
    have ha_eq : a = 1 - b := by linarith [hab]
    simpa [ha_eq, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
      add_comm, sub_eq_add_neg, rhs] using hle
  have htoReal_le : (f (a • x + b • y)).toReal ≤ rhs := by
    have hy_rhs : (rhs : EReal) ≠ ⊤ := by simp
    have htoReal :=
      EReal.toReal_le_toReal hxcombo (hf.2.2 (a • x + b • y) (by simp)) hy_rhs
    simpa [rhs] using htoReal
  simpa [C, rhs] using htoReal_le

/-- If `x0` lies in the intrinsic interior of the effective domain of a proper convex function,
then the point `(x0, f x0 - 1)` lies outside the closure of the epigraph. -/
lemma point_below_not_mem_closure_epigraph_of_mem_intrinsicInterior {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x0 : Fin n → Real} {r0 : Real}
    (hx0 : x0 ∈ intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hr0 : f x0 = (r0 : EReal)) :
    ((x0, r0 - 1) : (Fin n → Real) × Real) ∉
      closure (epigraph (Set.univ : Set (Fin n → Real)) f) := by
  classical
  let C : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let g : (Fin n → Real) → Real := fun x => (f x).toReal
  have hg : ConvexOn ℝ C g := convexOn_toReal_effectiveDomain (f := f) hf
  have hx0C : x0 ∈ C := by
    have hx0' :
        x0 ∈ intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := hx0
    have hx0C' :
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
      intrinsicInterior_subset (𝕜 := ℝ)
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx0'
    simpa [C] using hx0C'
  let A : AffineSubspace ℝ (Fin n → Real) := affineSpan ℝ C
  let p0 : A := ⟨x0, subset_affineSpan ℝ C hx0C⟩
  haveI : Nonempty A := ⟨p0⟩
  have hp0 : (p0 : A) ∈ interior ((↑) ⁻¹' C : Set A) := by
    rcases
        (mem_intrinsicInterior (𝕜 := ℝ)
          (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) (x := x0)).1 hx0 with
      ⟨y0, hy0, hy0x0⟩
    have hy0p0 : y0 = p0 := by
      apply Subtype.ext
      simpa [p0] using hy0x0
    have hy0' : y0 ∈ interior ((↑) ⁻¹' C : Set A) := by
      simpa [C] using hy0
    simpa [hy0p0] using hy0'
  let τ : A.direction →ᵃ[ℝ] (Fin n → Real) :=
    (A.direction.subtype).toAffineMap + AffineMap.const ℝ A.direction x0
  have hτ (v : A.direction) : τ v = (v : (Fin n → Real)) + x0 := by
    simp [τ, add_comm]
  let D : Set A.direction := τ ⁻¹' C
  have h0D : (0 : A.direction) ∈ interior D := by
    -- Use the open neighborhood in the affine span coming from `hp0`, then pull it back along `τ`.
    have hsA_nhds : ((↑) ⁻¹' C : Set A) ∈ nhds p0 := by
      simpa [mem_interior_iff_mem_nhds] using hp0
    rcases mem_nhds_iff.1 hsA_nhds with ⟨W, hWsub_sA, hWopen, hp0W⟩
    rcases (isOpen_induced_iff.1 hWopen) with ⟨V0, hV0open, rfl⟩
    have hx0V0 : x0 ∈ V0 := by simpa [p0] using hp0W
    let Udir : Set A.direction := τ ⁻¹' V0
    have hUdir_open : IsOpen Udir :=
      hV0open.preimage (AffineMap.continuous_of_finiteDimensional τ)
    have h0Udir : (0 : A.direction) ∈ Udir := by
      simp [Udir, hτ, hx0V0]
    have hUdir_sub : Udir ⊆ D := by
      intro v hv
      have hvV0 : τ v ∈ V0 := hv
      have hx0A : x0 ∈ A := subset_affineSpan ℝ C hx0C
      have hvA : τ v ∈ A := by
        have : (v : (Fin n → Real)) +ᵥ x0 ∈ A :=
          A.vadd_mem_of_mem_direction v.property hx0A
        simpa [hτ, vadd_eq_add] using this
      let y : A := ⟨τ v, hvA⟩
      have hyW : y ∈ ((↑) ⁻¹' V0 : Set A) := by
        simpa [y] using hvV0
      have hyC : (y : Fin n → Real) ∈ C := hWsub_sA hyW
      simpa [D, y] using hyC
    have hDnhds : D ∈ nhds (0 : A.direction) :=
      Filter.mem_of_superset (hUdir_open.mem_nhds h0Udir) hUdir_sub
    simpa [mem_interior_iff_mem_nhds] using hDnhds
  have hgv : ConvexOn ℝ D (g ∘ τ) := by
    simpa [D, Function.comp] using (hg.comp_affineMap τ)
  have hcont : ContinuousOn (g ∘ τ) (interior D) := hgv.continuousOn_interior
  have hcont0 : ContinuousAt (g ∘ τ) (0 : A.direction) := by
    have hwithin : ContinuousWithinAt (g ∘ τ) (interior D) 0 := hcont 0 h0D
    exact hwithin.continuousAt (isOpen_interior.mem_nhds h0D)
  have hgx0 : g x0 = r0 := by
    -- `g x0 = (f x0).toReal = r0`.
    simp [g, hr0]
  have hτ0 : τ (0 : A.direction) = x0 := by
    simp [hτ]
  have hnhds_pre :
      (g ∘ τ) ⁻¹' Set.Ioi (r0 - (1 / 2 : Real)) ∈ nhds (0 : A.direction) := by
    have h0Ioi : (g ∘ τ) 0 ∈ Set.Ioi (r0 - (1 / 2 : Real)) := by
      simp [Function.comp, hτ0, hgx0]
    exact hcont0 (isOpen_Ioi.mem_nhds h0Ioi)
  rcases mem_nhds_iff.1 hnhds_pre with ⟨W, hWsub, hWopen, h0W⟩
  -- Rewrite the open neighborhood `W` in `A.direction` as a preimage of an open set in `E`.
  rcases (isOpen_induced_iff.1 hWopen) with ⟨U, hUopen, rfl⟩
  have h0U : (0 : Fin n → Real) ∈ U := by simpa using h0W
  let V : Set (Fin n → Real) := (fun x : Fin n → Real => x - x0) ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage (continuous_id.sub continuous_const)
  have hx0V : x0 ∈ V := by
    simp [V, h0U]
  let O : Set ((Fin n → Real) × Real) :=
    (Prod.fst ⁻¹' V) ∩ (Prod.snd ⁻¹' Set.Iio (r0 - (1 / 2 : Real)))
  have hOopen : IsOpen O :=
    (hVopen.preimage continuous_fst).inter ((isOpen_Iio).preimage continuous_snd)
  have hqO : ((x0, r0 - 1) : (Fin n → Real) × Real) ∈ O := by
    refine ⟨?_, ?_⟩
    · simp [V, hx0V]
    · simp
      linarith
  have hOnhds : O ∈ nhds ((x0, r0 - 1) : (Fin n → Real) × Real) := hOopen.mem_nhds hqO
  have hOdisj :
      (O ∩ epigraph (Set.univ : Set (Fin n → Real)) f) = (∅ : Set _ ) := by
    ext p
    constructor
    · rintro ⟨hpO, hpEpi⟩
      rcases hpO with ⟨hpV, hpμ⟩
      have hxC : p.1 ∈ C := by
        refine ⟨p.2, ?_⟩
        simpa [epigraph] using hpEpi
      have hdx : p.1 - x0 ∈ U := by simpa [V] using hpV
      have hdir : p.1 - x0 ∈ A.direction := by
        have hxA : p.1 ∈ A := subset_affineSpan ℝ C hxC
        have hx0A : x0 ∈ A := subset_affineSpan ℝ C hx0C
        have hvsub : p.1 -ᵥ x0 ∈ A.direction := A.vsub_mem_direction hxA hx0A
        simpa [vsub_eq_sub] using hvsub
      let v : A.direction := ⟨p.1 - x0, hdir⟩
      have hvW : v ∈ ((↑) ⁻¹' U : Set A.direction) := by
        simpa using hdx
      have hg_lower : r0 - (1 / 2 : Real) < g (τ v) := by
        have : v ∈ (g ∘ τ) ⁻¹' Set.Ioi (r0 - (1 / 2 : Real)) := hWsub hvW
        simpa [Function.comp] using this
      have hτv : τ v = p.1 := by
        simp [hτ, v]
      have hg_lower' : r0 - (1 / 2 : Real) < g p.1 := by simpa [hτv] using hg_lower
      have hleμ : g p.1 ≤ p.2 := by
        have hle : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hpEpi
        have := EReal.toReal_le_toReal hle (hf.2.2 p.1 (by simp)) (by simp)
        simpa [g, EReal.toReal_coe] using this
      have hg_upper : g p.1 < r0 - (1 / 2 : Real) := lt_of_le_of_lt hleμ hpμ
      exact (lt_asymm hg_lower' hg_upper).elim
    · intro hp
      cases hp
  intro hq
  have hnonempty :
      (O ∩ epigraph (Set.univ : Set (Fin n → Real)) f).Nonempty :=
    (mem_closure_iff_nhds.1 hq) O hOnhds
  simp [hOdisj] at hnonempty

/-- A linear functional on `ℝ^n` can be represented as a dot product with a coefficient vector. -/
lemma linearMap_exists_dotProduct_representation {n : Nat} (φ : (Fin n → Real) →ₗ[ℝ] Real) :
    ∃ b : Fin n → Real, ∀ x : Fin n → Real, φ x = x ⬝ᵥ b := by
  classical
  let b : Fin n → Real := fun i => φ (Pi.single (M := fun _ : Fin n => Real) i (1 : Real))
  refine ⟨b, ?_⟩
  intro x
  have hx :
      x = ∑ i : Fin n, x i • Pi.single (M := fun _ : Fin n => Real) i (1 : Real) := by
    simpa using (pi_eq_sum_univ' x)
  calc
    φ x = φ (∑ i : Fin n, x i • Pi.single (M := fun _ : Fin n => Real) i (1 : Real)) := by
          rw [← hx]
    _ = ∑ i : Fin n, x i * φ (Pi.single (M := fun _ : Fin n => Real) i (1 : Real)) := by
          simp [smul_eq_mul]
    _ = ∑ i : Fin n, x i * b i := by simp [b]
    _ = x ⬝ᵥ b := by
          simp [dotProduct]

/-- Corollary 12.1.2. Given any proper convex function `f` on `ℝ^n`, there exist `b : ℝ^n` and
`β : ℝ` such that `f x ≥ ⟪x, b⟫ - β` for every `x`. -/
theorem properConvexFunctionOn_exists_linear_lowerBound {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∃ (b : Fin n → Real) (β : Real),
      ∀ x : Fin n → Real, f x ≥ ((x ⬝ᵥ b - β : Real) : EReal) := by
  classical
  let C : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hconv_epi : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunctionOn] using
      (hf.1 : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
  have hC_nonempty : C.Nonempty :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain (S := (Set.univ : Set (Fin n → Real)))
      (f := f)).1 hf.2.1
  have hC_conv : Convex ℝ C :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
  have hri_nonempty : (intrinsicInterior ℝ C).Nonempty :=
    (intrinsicInterior_nonempty (s := C) hC_conv).2 hC_nonempty
  rcases hri_nonempty with ⟨x0, hx0ri⟩
  have hx0C : x0 ∈ C := intrinsicInterior_subset (𝕜 := ℝ) (s := C) hx0ri
  have hx0_ne_top : f x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx0C
  have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hf.2.2 x0 (by simp)
  let r0 : Real := (f x0).toReal
  have hr0 : f x0 = (r0 : EReal) := by
    simpa [r0] using (EReal.coe_toReal (x := f x0) hx0_ne_top hx0_ne_bot).symm
  have hq_not :
      ((x0, r0 - 1) : (Fin n → Real) × Real) ∉
        closure (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    exact
      point_below_not_mem_closure_epigraph_of_mem_intrinsicInterior (f := f) hf
        (x0 := x0) (r0 := r0) hx0ri hr0
  let C' : Set ((Fin n → Real) × Real) := closure (epigraph (Set.univ : Set (Fin n → Real)) f)
  have hC' : Convex ℝ C' ∧ IsClosed C' := by
    refine ⟨?_, ?_⟩
    · simpa [C'] using (Convex.closure hconv_epi)
    · simp [C']
  have hq_not' : (x0, r0 - 1) ∉ C' := by simpa [C'] using hq_not
  obtain ⟨l, u, hl, hu⟩ :=
    geometric_hahn_banach_closed_point (E := (Fin n → Real) × ℝ) (s := C') (x := (x0, r0 - 1))
      hC'.1 hC'.2 hq_not'
  let t : ℝ := l ((0 : (Fin n → Real)), (1 : ℝ))
  let φ : (Fin n → Real) →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inl ℝ (Fin n → Real) ℝ)
  have ht : t < 0 := by
    have ht_le : t ≤ 0 := by
      by_contra ht0
      have htpos : 0 < t := lt_of_not_ge ht0
      let μ : ℝ := max r0 ((u + 1 - φ x0) / t)
      have hμ_ge : r0 ≤ μ := le_max_left _ _
      have hμ_epi :
          ((x0, μ) : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
        have : f x0 ≤ (μ : EReal) := by
          -- `f x0 = r0 ≤ μ`.
          simpa [hr0] using (EReal.coe_le_coe_iff.2 hμ_ge)
        exact (mem_epigraph_univ_iff (f := f)).2 this
      have hμC : ((x0, μ) : (Fin n → Real) × Real) ∈ C' := subset_closure hμ_epi
      have hlt : l (x0, μ) < u := hl _ hμC
      have hdecomp : l (x0, μ) = φ x0 + μ * t := by
        have h := strongDual_apply_prod (l := l) (x := x0) (μ := μ)
        have hx0_0 : l (x0, (0 : ℝ)) = φ x0 := by simp [φ]
        simpa [t, hx0_0, smul_eq_mul, add_assoc] using h
      have hμge : (u + 1 - φ x0) / t ≤ μ := le_max_right _ _
      have hmul' : ((u + 1 - φ x0) / t) * t ≤ μ * t :=
        mul_le_mul_of_nonneg_right hμge (le_of_lt htpos)
      have hmul : u + 1 - φ x0 ≤ μ * t := by
        have htne : t ≠ 0 := ne_of_gt htpos
        simpa [div_eq_mul_inv, htne, mul_assoc] using hmul'
      have hu_lt : u < u + 1 := by linarith
      have hlt' : u < l (x0, μ) := by
        have : u + 1 ≤ φ x0 + μ * t := by linarith [hmul]
        have : u < φ x0 + μ * t := lt_of_lt_of_le hu_lt this
        simpa [hdecomp] using this
      exact (lt_irrefl u) (lt_trans hlt' (by simpa [hdecomp] using hlt))
    have ht_ne : t ≠ 0 := by
      intro ht0
      have hx0_epi :
          ((x0, r0) : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
        have : f x0 ≤ (r0 : EReal) := by simp [hr0]
        exact (mem_epigraph_univ_iff (f := f)).2 this
      have hx0C : ((x0, r0) : (Fin n → Real) × Real) ∈ C' := subset_closure hx0_epi
      have hlt0 : l (x0, r0) < u := hl _ hx0C
      have hlq : l (x0, r0 - 1) = l (x0, r0) := by
        have h1 := strongDual_apply_prod (l := l) (x := x0) (μ := r0 - 1)
        have h2 := strongDual_apply_prod (l := l) (x := x0) (μ := r0)
        have hl1 : l (x0, r0 - 1) = l (x0, (0 : ℝ)) := by
          simpa [t, ht0, smul_eq_mul, add_assoc] using h1
        have hl2 : l (x0, r0) = l (x0, (0 : ℝ)) := by
          simpa [t, ht0, smul_eq_mul, add_assoc] using h2
        simp [hl1, hl2]
      have huq : u < l (x0, r0 - 1) := hu
      have hltq : l (x0, r0 - 1) < u := by simpa [hlq] using hlt0
      exact (lt_asymm huq hltq).elim
    exact lt_of_le_of_ne ht_le ht_ne
  let h : AffineMap ℝ (Fin n → Real) ℝ :=
    ((1 / (-t)) • φ.toAffineMap) + AffineMap.const ℝ (Fin n → Real) ((-u) / (-t))
  have h_apply (x : Fin n → Real) : h x = (φ x - u) / (-t) := by
    simp [h, div_eq_mul_inv, sub_eq_add_neg, add_mul]
    ring
  have hh : ∀ x : Fin n → Real, (h x : EReal) ≤ f x := by
    intro x
    by_cases hx_top : f x = (⊤ : EReal)
    · simp [hx_top]
    · have hx_ne_top : f x ≠ (⊤ : EReal) := hx_top
      have hx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      let rx : ℝ := (f x).toReal
      have hfx : f x = (rx : EReal) := by
        simpa [rx] using (EReal.coe_toReal (x := f x) hx_ne_top hx_ne_bot).symm
      have hx_epi :
          ((x, rx) : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
        have : f x ≤ (rx : EReal) := by simp [hfx]
        exact (mem_epigraph_univ_iff (f := f)).2 this
      have hxC : ((x, rx) : (Fin n → Real) × Real) ∈ C' := subset_closure hx_epi
      have hlt : l (x, rx) < u := hl _ hxC
      have hlt' : φ x + rx * t < u := by
        have hdecomp := strongDual_apply_prod (l := l) (x := x) (μ := rx)
        have hx_0 : l (x, (0 : ℝ)) = φ x := by simp [φ]
        have : l (x, (0 : ℝ)) + rx * t < u := by simpa [t, hdecomp] using hlt
        simpa [hx_0, mul_comm, mul_assoc, mul_left_comm] using this
      have hhy : h x < rx := by
        have htpos : 0 < -t := by linarith
        have : (φ x - u) / (-t) < rx := by
          have : φ x - u < rx * (-t) := by linarith [hlt']
          exact (div_lt_iff₀ htpos).2 this
        simpa [h_apply] using this
      have : ((h x : Real) : EReal) ≤ (rx : EReal) := by
        simpa [EReal.coe_le_coe_iff] using (le_of_lt hhy)
      simpa [hfx] using this
  let ψ : (Fin n → Real) →ₗ[ℝ] ℝ := (1 / (-t)) • φ
  rcases linearMap_exists_dotProduct_representation (n := n) ψ with ⟨b, hb⟩
  let β : ℝ := -((-u) / (-t))
  refine ⟨b, β, ?_⟩
  intro x
  have hform : h x = x ⬝ᵥ b - β := by
    have : h x = ψ x + (-u) / (-t) := by
      simp [h, ψ, smul_eq_mul, add_comm, div_eq_mul_inv]
    calc
      h x = ψ x + (-u) / (-t) := this
      _ = (x ⬝ᵥ b) + (-u) / (-t) := by rw [hb x]
      _ = (x ⬝ᵥ b) - β := by simp [β, sub_eq_add_neg]
  have : ((x ⬝ᵥ b - β : Real) : EReal) ≤ f x := by
    simpa [hform] using (hh x)
  simpa [ge_iff_le] using this

/-- A real-valued function `g` (coerced to `EReal`) is pointwise below `indicatorFunction C`
iff `g x ≤ 0` for every `x ∈ C`. -/
lemma le_indicatorFunction_iff_forall_mem_le_zero {n : Nat} {C : Set (Fin n → Real)}
    {g : (Fin n → Real) → Real} :
    (fun x : Fin n → Real => ((g x : Real) : EReal)) ≤ indicatorFunction C ↔
      ∀ x, x ∈ C → g x ≤ 0 := by
  classical
  constructor
  · intro h x hx
    have hx' : ((g x : Real) : EReal) ≤ (0 : EReal) := by
      simpa [indicatorFunction, hx] using h x
    exact (EReal.coe_le_coe_iff.1 hx')
  · intro h x
    by_cases hx : x ∈ C
    · have : g x ≤ 0 := h x hx
      have : ((g x : Real) : EReal) ≤ (0 : EReal) := EReal.coe_le_coe_iff.2 this
      simpa [indicatorFunction, hx] using this
    · simp [indicatorFunction, hx]

/-- The inequality `x ⬝ᵥ b - β ≤ 0` on `C` is equivalent to the half-space containment
`C ⊆ {x | x ⬝ᵥ b ≤ β}`. -/
lemma forall_mem_sub_le_zero_iff_subset_halfspace {n : Nat} {C : Set (Fin n → Real)}
    (b : Fin n → Real) (β : Real) :
    (∀ x, x ∈ C → x ⬝ᵥ b - β ≤ 0) ↔ C ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  constructor
  · intro h x hx
    have : x ⬝ᵥ b - β ≤ 0 := h x hx
    have : x ⬝ᵥ b ≤ β := (sub_nonpos.1 this)
    simpa [Set.mem_setOf_eq] using this
  · intro h x hx
    have hx' : x ∈ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := h hx
    have : x ⬝ᵥ b ≤ β := by
      simpa [Set.mem_setOf_eq] using hx'
    exact (sub_nonpos.2 this)

/-- Text 12.1.1: If `f` is the indicator function of a convex set `C` and
`h x = ⟪x, b⟫ - β`, then `h ≤ f` if and only if `h x ≤ 0` for every `x ∈ C`,
i.e. if and only if `C ⊆ {x | ⟪x, b⟫ ≤ β}`. -/
theorem affine_le_indicatorFunction_iff_subset_halfspace {n : Nat} {C : Set (Fin n → Real)}
    (hC : Convex ℝ C) (b : Fin n → Real) (β : Real) :
    (fun x : Fin n → Real => ((x ⬝ᵥ b - β : Real) : EReal)) ≤ indicatorFunction C ↔
      C ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
  have _hC' : Convex ℝ C := hC
  have h1 :
      (fun x : Fin n → Real => ((x ⬝ᵥ b - β : Real) : EReal)) ≤ indicatorFunction C ↔
        ∀ x, x ∈ C → x ⬝ᵥ b - β ≤ 0 := by
    simpa using
      (le_indicatorFunction_iff_forall_mem_le_zero (C := C) (g := fun x => x ⬝ᵥ b - β))
  have h2 :
      (∀ x, x ∈ C → x ⬝ᵥ b - β ≤ 0) ↔ C ⊆ {x : Fin n → Real | x ⬝ᵥ b ≤ β} := by
    simpa using (forall_mem_sub_le_zero_iff_subset_halfspace (C := C) b β)
  exact h1.trans h2

/-- Rearranging `x ⬝ᵥ xStar - muStar ≤ f x` yields `x ⬝ᵥ xStar - f x ≤ muStar`. -/
lemma affine_majorized_iff_forall_dotSub_le_mu {n : Nat} (f : (Fin n → Real) → Real)
    (xStar : Fin n → Real) (muStar : Real) :
    (∀ x : Fin n → Real, x ⬝ᵥ xStar - muStar ≤ f x) ↔
      (∀ x : Fin n → Real, x ⬝ᵥ xStar - f x ≤ muStar) := by
  constructor <;> intro h x <;> have := h x <;> linarith

/-- A pointwise upper bound yields `BddAbove` for the range. -/
lemma bddAbove_range_of_forall_le {α β : Type*} [Preorder β] (g : α → β) (a : β)
    (h : ∀ x, g x ≤ a) : BddAbove (Set.range g) := by
  refine ⟨a, ?_⟩
  rintro y ⟨x, rfl⟩
  exact h x

/-- Text 12.1.2: Let `f` be a function on `ℝ^n` (contextually: closed convex), and let
`h x = ⟪x, x*⟫ - μ*` be an affine function. Then `h` is majorized by `f` (i.e. `h x ≤ f x` for
every `x`) if and only if
`μ* ≥ sup {⟪x, x*⟫ - f x | x ∈ ℝ^n}`. -/
theorem affine_majorized_iff_mu_ge_sSup (n : Nat) (f : (Fin n → Real) → Real)
    (xStar : Fin n → Real) (muStar : Real) :
    (∀ x : Fin n → Real, x ⬝ᵥ xStar - muStar ≤ f x) ↔
      BddAbove (Set.range (fun x : Fin n → Real => x ⬝ᵥ xStar - f x)) ∧
        muStar ≥ sSup (Set.range (fun x : Fin n → Real => x ⬝ᵥ xStar - f x)) := by
  classical
  let g : (Fin n → Real) → Real := fun x => x ⬝ᵥ xStar - f x
  have hrearr :
      (∀ x : Fin n → Real, x ⬝ᵥ xStar - muStar ≤ f x) ↔ ∀ x : Fin n → Real, g x ≤ muStar := by
    simpa [g] using (affine_majorized_iff_forall_dotSub_le_mu (f := f) xStar muStar)
  constructor
  · intro h
    have hg : ∀ x : Fin n → Real, g x ≤ muStar := (hrearr.1 h)
    have hb : BddAbove (Set.range g) := bddAbove_range_of_forall_le g muStar hg
    have hsSup : sSup (Set.range g) ≤ muStar := by
      refine csSup_le (s := Set.range g) (a := muStar) (h₁ := Set.range_nonempty g) ?_
      rintro y ⟨x, rfl⟩
      exact hg x
    refine ⟨?_, ?_⟩
    · simpa [g] using hb
    · simpa [ge_iff_le] using hsSup
  · rintro ⟨hb, hmu⟩
    have hsSup : sSup (Set.range g) ≤ muStar := by
      simpa [ge_iff_le] using hmu
    have hg : ∀ x : Fin n → Real, g x ≤ muStar := by
      have hrange : ∀ y ∈ Set.range g, y ≤ muStar :=
        (csSup_le_iff (s := Set.range g) (a := muStar) hb (Set.range_nonempty g)).1 hsSup
      intro x
      exact hrange (g x) ⟨x, rfl⟩
    exact (hrearr.2 hg)

end Section12
end Chap03
