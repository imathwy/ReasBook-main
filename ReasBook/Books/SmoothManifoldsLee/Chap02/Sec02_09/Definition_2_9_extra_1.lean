import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uF uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/- Definition 2.9-extra-1: a diffeomorphism from `M` to `N` is the canonical manifold notion
`M ≃ₘ⟮I, J⟯ N`, i.e. a smooth equivalence whose inverse is also smooth. -/
#check (M ≃ₘ⟮I, J⟯ N)

/- Two smooth manifolds are diffeomorphic precisely when the canonical type of diffeomorphisms
`M ≃ₘ⟮I, J⟯ N` is nonempty. -/
#check (Nonempty (M ≃ₘ⟮I, J⟯ N))
