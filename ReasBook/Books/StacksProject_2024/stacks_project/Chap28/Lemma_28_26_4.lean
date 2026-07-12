import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable [MonoidalCategory X.Modules]

/- The source-facing owner here is the affine-open predicate on the intersection `U ∩ X_s`. The
local Chapter 28 owner is `Invertible.sectionNonvanishingOpen`, the source-facing bridge to the
canonical ringed-space nonvanishing open attached to a section of `L`. -/

/-- Lemma 28.26.4: if `U ⊆ X` is affine and `s` is a global section of an invertible
`\mathcal O_X`-module `L`, then the intersection `U ∩ X_s` is affine. In the Chapter 28 local
API, `X_s` is formalized as `hL.sectionNonvanishingOpen s`. -/
@[stacks 01PV]
theorem isAffineOpen_inf_sectionNonvanishingOpen
    {U : X.Opens} (hU : IsAffineOpen U)
    (L : X.Modules) [hL : Invertible L] (s : Γ(L, ⊤)) :
    IsAffineOpen (U ⊓ hL.sectionNonvanishingOpen s) := sorry

namespace IsAffineOpen

/-- Companion API for Lemma 28.26.4 in object-prefix form. -/
theorem inf_sectionNonvanishingOpen
    {U : X.Opens} (hU : IsAffineOpen U)
    (L : X.Modules) [hL : Invertible L] (s : Γ(L, ⊤)) :
    IsAffineOpen (U ⊓ hL.sectionNonvanishingOpen s) :=
  isAffineOpen_inf_sectionNonvanishingOpen hU L s

end IsAffineOpen

end AlgebraicGeometry.Scheme.Modules
