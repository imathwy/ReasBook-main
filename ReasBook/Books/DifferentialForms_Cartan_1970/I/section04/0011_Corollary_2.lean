import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology
open Set

universe u

-- Proof sketch: rewrite `𝓝[D] z₀` as `𝓝 z₀` using openness of `D`, then apply the canonical
-- identity principle `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
/-
Corollary 2 is a `bridge/view` item: the owner theorem is mathlib's
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, and this file keeps only the textbook
open-set formulation expressed with `𝓝[D] z₀`.
-/
/-- Corollary 2: principle of analytic continuation. If two analytic functions on a preconnected
open set `D` agree on a neighborhood of some point `z₀ ∈ D` within `D`, then they agree on all of
`D`. With `z₀ ∈ D`, this is equivalent to the usual connected-open-set formulation. -/
theorem analytic_continuation_principle
    {𝕜 : Type u} [RCLike 𝕜] {D : Set 𝕜} (hD_open : IsOpen D) (hD_preconnected : IsPreconnected D)
    {f g : 𝕜 → 𝕜} (hf : AnalyticOnNhd 𝕜 f D) (hg : AnalyticOnNhd 𝕜 g D) {z₀ : 𝕜}
    (hz₀ : z₀ ∈ D)
    (hfg : f =ᶠ[𝓝[D] z₀] g) :
    EqOn f g D := by
  have hfg' : f =ᶠ[𝓝 z₀] g := by
    simpa [hD_open.nhdsWithin_eq hz₀] using hfg
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hD_preconnected hz₀ hfg'
