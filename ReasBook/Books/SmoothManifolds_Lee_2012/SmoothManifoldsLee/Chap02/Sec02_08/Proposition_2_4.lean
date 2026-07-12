import Mathlib.Geometry.Manifold.ContMDiff.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I (∞ : ℕ∞ω) M] [IsManifold I' (∞ : ℕ∞ω) N]
  {F : M → N}

/- Proposition 2.4: Every `C^∞` map between smooth manifolds is continuous. This is the
canonical owner-level continuity theorem for `ContMDiff`, specialized to `n = ∞`. -/
#check (ContMDiff.continuous : ContMDiff I I' (∞ : ℕ∞ω) F → Continuous F)
