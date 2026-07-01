import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the identity-principle API was verified directly in
-- `Mathlib/Analysis/Analytic/Uniqueness.lean`.

/-- Corollary 2: principle of analytic continuation. If two analytic functions on a connected set
`D` coincide on some open neighborhood of a point `z₀ ∈ D`, then they are identical on `D`. -/
theorem analytic_eqOn_of_eqOn_nhds
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set E}
    (hD_connected : IsConnected D) {f g : E → ℂ} (hf : AnalyticOnNhd ℂ f D)
    (hg : AnalyticOnNhd ℂ g D) {z₀ : E} (hz₀ : z₀ ∈ D) (U : Set E) (hU_open : IsOpen U)
    (hz₀U : z₀ ∈ U) (hfg : Set.EqOn f g U) :
    Set.EqOn f g D := by
  have hfg' : f =ᶠ[nhds z₀] g :=
    Filter.mem_of_superset (IsOpen.mem_nhds hU_open hz₀U) fun z hz ↦ hfg hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hD_connected.isPreconnected hz₀ hfg'
