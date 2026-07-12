import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Example_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Torus

-- `lean_leansearch` is unavailable in this session, so the statement below follows the canonical
-- repository owners already used for the torus and complex exponential covering maps.

/-- Example 7.10 (1): the coordinatewise character `εⁿ : ℝⁿ → 𝕋ⁿ` is a universal smooth covering
map, so the additive Lie group `ℝⁿ` is the universal covering group of the torus `𝕋ⁿ`. -/
theorem torus_epsilon_add_char_isUniversalSmoothCoveringMap (n : ℕ) :
    Manifold.IsUniversalSmoothCoveringMap
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      (ε^{n}) := sorry

/-- Example 7.10 (2): the complex exponential `ℂ → ℂˣ`, realized by
`complex_exp_units_add_char`, is a universal smooth covering map, so `ℂ` is the universal
covering group of `ℂˣ`. -/
theorem complex_exp_units_add_char_isUniversalSmoothCoveringMap :
    Manifold.IsUniversalSmoothCoveringMap
      (𝓘(ℝ, ℂ))
      (𝓘(ℝ, ℂ))
      complex_exp_units_add_char := sorry
