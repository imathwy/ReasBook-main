import Mathlib
import SmoothManifolds_Lee_2012.Chap06.Sec06_45.Problem_6_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

section Problem617

-- Domain sampling pass: this counterexample lies in the stable-map-class / smooth-family domain.
-- Relevant owner declarations checked before refinement:
-- * `IsStableMapClass` from `Problem_6_16`
-- * `IsSmoothFamily` from `Definition_6_44_extra_2`
-- * the map-class owners `IsImmersion`, `IsSmoothSubmersion`, `IsSmoothEmbedding`,
--   `IsLocalDiffeomorph`, `IsTransverseToSubmanifold`, and `≃ₘ⟮I, I⟯`
-- Layer triage:
-- * source-facing: the explicit Lee family `problem_6_17_family`
-- * core/canonical: the family-smoothness owner `IsSmoothFamily I I I`
-- * derived API: pointwise evaluation and the specialized stability counterexamples

local notation "I" => 𝓘(ℝ, ℝ)

/-- The Problem 6-17 family is `F_s(x) = x φ (s x)`. -/
def problem_6_17_family (φ : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun x ↦ x * φ (s * x)

/-- The defining formula for the Problem 6-17 family. -/
@[simp] theorem problem_6_17_family_apply (φ : ℝ → ℝ) (s x : ℝ) :
    problem_6_17_family φ s x = x * φ (s * x) :=
  rfl

/-- The Problem 6-17 family is a smooth family of maps `ℝ → ℝ` whenever `φ` is smooth. -/
theorem problem_6_17_family_isSmoothFamily {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) :
    IsSmoothFamily I I I (problem_6_17_family φ) := sorry

/-- If `φ(0) = 1`, then the `s = 0` slice of the Problem 6-17 family is the identity map of `ℝ`.
-/
theorem problem_6_17_family_zero (φ : ℝ → ℝ) (hφ0 : φ 0 = 1) :
    problem_6_17_family φ 0 = id := by
  funext x
  simp [problem_6_17_family, hφ0]

/-- Compact support of `φ` forces each nonzero slice `F_s` to vanish outside a sufficiently large
compact interval. -/
theorem problem_6_17_family_eq_zero_outside_large_interval {φ : ℝ → ℝ} {s : ℝ}
    (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ |x| → problem_6_17_family φ s x = 0 := sorry

/-- Problem 6-17 (1): using the family `F_s(x) = x φ (s x)`, the class of immersions `ℝ → ℝ`
need not be stable when the source manifold is noncompact. -/
theorem immersions_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass I I {f : ℝ → ℝ | IsImmersion I I ∞ f} := sorry

/-- Problem 6-17 (2): using the same family, the class of smooth submersions `ℝ → ℝ` need not be
stable when the source manifold is noncompact. -/
theorem submersions_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass I I {f : ℝ → ℝ | IsSmoothSubmersion I I f} := sorry

/-- Problem 6-17 (3): using the same family, the class of smooth embeddings `ℝ → ℝ` need not be
stable when the source manifold is noncompact. -/
theorem embeddings_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass I I {f : ℝ → ℝ | IsSmoothEmbedding I I ∞ f} := sorry

/-- Problem 6-17 (4): using the same family, the class of smooth diffeomorphisms `ℝ → ℝ` need not
be stable when the source manifold is noncompact. -/
theorem diffeomorphisms_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass I I (range ((↑) : (ℝ ≃ₘ⟮I, I⟯ ℝ) → (ℝ → ℝ))) := sorry

/-- Problem 6-17 (5): using the same family, the class of local diffeomorphisms `ℝ → ℝ` need not
be stable when the source manifold is noncompact. -/
theorem local_diffeomorphisms_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass I I {f : ℝ → ℝ | IsLocalDiffeomorph I I ∞ f} := sorry

/-- Problem 6-17 (6): using the same family, the class of maps `ℝ → ℝ` transverse to the chosen
embedded submanifold structure on `{0}` need not be stable when the source manifold is
noncompact. -/
theorem transverse_maps_to_zero_need_not_be_stable_without_compact_source
    {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type*} [TopologicalSpace H0] {J0 : ModelWithCorners ℝ E0 H0}
    [ChartedSpace H0 ({(0 : ℝ)} : Set ℝ)] [IsManifold J0 ∞ ({(0 : ℝ)} : Set ℝ)]
    [IsEmbeddedSubmanifold I J0 ({(0 : ℝ)} : Set ℝ)]
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass I I
      {f : ℝ → ℝ |
        IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) f} := sorry

end Problem617
