import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced the generic mathlib construction
-- `AlgebraicGeometry.Proj.fromOfGlobalSections`, while local Chapter 28 precedent records
-- Situation 28.28.1 through the same `Proj` and section-ring owners.  The exact source-facing open
-- `W₁`, the projective twisting sheaves `𝒪_Y(n)`, their multiplication maps, and the comparison
-- maps `f^*𝒪_Y(n) → ℒ^{⊗ n}` are not yet packaged as concrete dependency-closed data.  The
-- Stacks source tag evidence is consistent with tag `01QI`.

/- Lemma 28.28.2: in Situation 28.28.1, the canonical morphism
`f : X ⟶ Y = Proj(Γ_*(X, \mathcal L))` maps `X` into the open subscheme
`W = W₁ ⊆ Y` where `\mathcal O_Y(1)` is invertible and where all multiplication maps
`\mathcal O_Y(n) ⊗_{\mathcal O_Y} \mathcal O_Y(m) ⟶ \mathcal O_Y(n + m)` are isomorphisms.
Moreover, all comparison maps `f^*\mathcal O_Y(n) ⟶ \mathcal L^{\otimes n}` are isomorphisms.

The currently available dependency-closed API exposes the ample invertible sheaf owner, the
graded section-ring owner, nonvanishing opens of tensor powers, and the generic
`Proj.fromOfGlobalSections` morphism in nearby Chapter 28 files.  It does not yet expose the
source's exact open `W₁` or the twisting/comparison map data as concrete declarations, so this item
is recorded as a labeled recall block rather than as a theorem over arbitrary replacement data. -/
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.basicOpen
#check AlgebraicGeometry.Proj.basicOpenIsoSpec
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
