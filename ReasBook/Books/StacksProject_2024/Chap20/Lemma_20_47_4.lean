import Mathlib
import StacksProject_2024.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: choose local strictly perfect approximations of `T.obj₁` in degree `m + 1` and
-- of `T.obj₂` in degree `m`, realize the first morphism of the distinguished triangle by an
-- actual map between those local models, and compare the cone triangle with `T` locally. The cone
-- stays strictly perfect, and the long exact cohomology sequence gives the required
-- cohomological bounds for `T.obj₃`, so Lemma `20.47.2` yields `m`-pseudo-coherence.
/-- Lemma 20.47.4 (1): in a distinguished triangle in `D(\mathcal O_X)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : IsMPseudoCoherent T.obj₁ (m + 1))
    (h₂ : IsMPseudoCoherent T.obj₂ m) :
    IsMPseudoCoherent T.obj₃ m := sorry

-- Proof sketch: rotate the distinguished triangle to put `T.obj₂` in the cone position covered
-- by part `(1)`. The hypotheses on `T.obj₁` and `T.obj₃` become the needed
-- `(m + 1)`-pseudo-coherence and `m`-pseudo-coherence assumptions for the rotated triangle.
/-- Lemma 20.47.4 (2): in a distinguished triangle in `D(\mathcal O_X)`, if the first and third
terms are `m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : IsMPseudoCoherent T.obj₁ m)
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₂ m := sorry

-- Proof sketch: rotate the distinguished triangle so that `T.obj₁` becomes the third vertex, and
-- apply part `(1)` to the rotated triangle. The shift in the first hypothesis matches the
-- `(m + 1)`-pseudo-coherence requirement exactly.
/-- Lemma 20.47.4 (3): in a distinguished triangle in `D(\mathcal O_X)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₂ : IsMPseudoCoherent T.obj₂ (m + 1))
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₁ (m + 1) := sorry

end AlgebraicGeometry.RingedSpace
