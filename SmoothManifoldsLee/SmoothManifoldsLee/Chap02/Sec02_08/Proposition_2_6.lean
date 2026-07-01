import Mathlib.Geometry.Manifold.ContMDiff.Defs

-- Declarations for this item will be appended below by the statement pipeline.

universe u_𝕜 uE uH uM uE' uH' uN

variable
  {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

/- Proposition 2.6 (1): smoothness is local on the source. If every point of `M` has an open
neighborhood on which `F` is smooth, then `F` is smooth. The canonical owner declaration is
`contMDiff_of_locally_contMDiffOn`. -/
#check contMDiff_of_locally_contMDiffOn

/- Proposition 2.6 (2): a smooth map is smooth on every subset of the source, hence in
particular on every open subset. The canonical derived API is `ContMDiff.contMDiffOn`. -/
#check ContMDiff.contMDiffOn
