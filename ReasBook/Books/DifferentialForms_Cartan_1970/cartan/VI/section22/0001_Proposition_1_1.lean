import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- Semantic search tool unavailable in this session; verified mathlib candidates:
-- `AnalyticAt.analyticAt_localInverse`,
-- `HasStrictDerivAt.eventually_left_inverse`,
-- `HasStrictDerivAt.eventually_right_inverse`.

/-- Proposition 1.1. If `f` is holomorphic near `z₀` and `deriv f z₀ ≠ 0`, then the canonical
local inverse of `f` at `z₀` is holomorphic near `f z₀`, sends `f z₀` to `z₀`, and is a local
inverse on both sides near these points. -/
theorem complex_holomorphic_local_inverse
    {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0) :
    let g := hf.hasStrictDerivAt.localInverse f (deriv f z₀) z₀ hf'
    AnalyticAt ℂ g (f z₀) ∧
      g (f z₀) = z₀ ∧
      (∀ᶠ z in 𝓝 z₀, g (f z) = z) ∧
      ∀ᶠ w in 𝓝 (f z₀), f (g w) = w := by
  let g := hf.hasStrictDerivAt.localInverse f (deriv f z₀) z₀ hf'
  change AnalyticAt ℂ g (f z₀) ∧
      g (f z₀) = z₀ ∧
      (∀ᶠ z in 𝓝 z₀, g (f z) = z) ∧
      ∀ᶠ w in 𝓝 (f z₀), f (g w) = w
  have hanalytic : AnalyticAt ℂ g (f z₀) := by
    simpa [g] using hf.analyticAt_localInverse hf'
  have hleft : ∀ᶠ z in 𝓝 z₀, g (f z) = z := by
    simpa [g] using hf.hasStrictDerivAt.eventually_left_inverse hf'
  have happly : g (f z₀) = z₀ :=
    hleft.self_of_nhds
  have hright : ∀ᶠ w in 𝓝 (f z₀), f (g w) = w := by
    simpa [g] using hf.hasStrictDerivAt.eventually_right_inverse hf'
  exact ⟨hanalytic, happly, hleft, hright⟩
