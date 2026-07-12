import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (𝓘(𝕜, E)) ∞ G]

local notation "I" => 𝓘(𝕜, E)

/- Definition 7.46-extra-1: for a smooth manifold without boundary modeled on `E`, the canonical
mathlib notion of Lie group is `LieGroup I ∞ G`. Its fields encode smooth multiplication
and smooth inversion, and `topologicalGroup_of_lieGroup` gives the resulting topological-group
structure. -/
#check (LieGroup I ∞ G)
#check (contMDiff_mul I ∞)
#check (contMDiff_inv I ∞)
#check (topologicalGroup_of_lieGroup I ∞)
