import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Semantic search tool unavailable in this environment; the declarations below are aligned with
-- the local `IsSmoothSubmersion` API from `Proposition_4_28` and the existing `ContMDiff` notation
-- for Euclidean manifolds.

/-- The map `(x, y) ↦ xy` appearing in Problem 4-8. -/
def problem_4_8_pi : ℝ × ℝ → ℝ := fun p ↦ p.1 * p.2

/-- Companion lemma for `problem_4_8_pi`: its coordinate formula is multiplication. -/
theorem problem_4_8_pi_apply (x y : ℝ) :
    problem_4_8_pi (x, y) = x * y := sorry

/-- Problem 4-8 (1): the map `(x, y) ↦ xy` from `ℝ × ℝ` to `ℝ` is surjective. -/
theorem problem_4_8_pi_surjective :
    Function.Surjective problem_4_8_pi := sorry

/-- Problem 4-8 (2): the map `(x, y) ↦ xy` from `ℝ × ℝ` to `ℝ` is smooth. -/
theorem problem_4_8_pi_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) ∞ problem_4_8_pi := sorry

section

universe uE uH uP

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H P]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ P]

/-- Problem 4-8 (3): for every smooth manifold `P`, a map `F : ℝ → P` is smooth if and only if
`F ∘ problem_4_8_pi` is smooth. -/
theorem problem_4_8_contMDiff_iff_comp_pi {F : ℝ → P} :
    ContMDiff 𝓘(ℝ) I ∞ F ↔ ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (F ∘ problem_4_8_pi) := sorry

end

/-- Problem 4-8 (4): although `problem_4_8_pi` is surjective and has the smoothness-detection
property above, it is not a smooth submersion. -/
theorem problem_4_8_pi_not_isSmoothSubmersion :
    ¬ Manifold.IsSmoothSubmersion 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) problem_4_8_pi := sorry
