import Mathlib.Geometry.Manifold.ContMDiff.Defs
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u_𝕜 uE uH uM uE' uH' uN

variable
  {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
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

/- Proposition 2.5: a map between smooth manifolds is smooth exactly when it is continuous and
smooth in every pair of extended charts. This is the canonical chart criterion `contMDiff_iff`,
specialized to the smooth (`C^∞`) manifold context of this section. -/
#check
  (contMDiff_iff :
    ContMDiff I I' (∞ : ℕ∞ω) F ↔
      Continuous F ∧
        ∀ (x : M) (y : N),
          ContDiffOn 𝕜 (∞ : ℕ∞ω) (extChartAt I' y ∘ F ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' F ⁻¹' (extChartAt I' y).source))
