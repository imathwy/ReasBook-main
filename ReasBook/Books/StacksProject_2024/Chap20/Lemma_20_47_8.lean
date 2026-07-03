import StacksProject_2024.Chap15.Lemma_15_65_10
import StacksProject_2024.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open DerivedCategory.TStructure
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)

/-- A derived `\mathcal O_X`-module is locally bounded above if every point has an open
neighborhood on which its restriction lies in the bounded-above derived category. -/
def IsLocallyBoundedAbove (E : DModX) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    (t.minus : ObjectProperty (DerivedCategory (openSubspaceModuleCategory X U)))
      ((moduleRestrictionToOpenDerived X U).obj E)

-- Proof sketch: unfold `IsLocallyBoundedAbove`; this is exactly the neighborhoodwise bounded-above
-- condition on the derived restrictions to open subspaces.
/-- The local bounded-above condition is exactly bounded-above-ness after restricting to a
neighborhood of each point. -/
theorem isLocallyBoundedAbove_iff (E : DModX) :
    IsLocallyBoundedAbove E ↔
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
        (t.minus : ObjectProperty (DerivedCategory (openSubspaceModuleCategory X U)))
          ((moduleRestrictionToOpenDerived X U).obj E) := sorry

-- Proof sketch: work locally near each point. On a neighborhood where `E` becomes bounded above,
-- apply the bounded-above algebraic argument of Lemma `15.65.10` to the restricted object, using
-- the hypotheses on the cohomology sheaves `H^i(E)`. This yields local `m`-pseudo-coherence of
-- the restriction, and Lemma `20.47.2` upgrades the local strictly perfect approximations to
-- `IsMPseudoCoherent E m`.
/-- Lemma 20.47.8: if `E` is locally bounded above and every cohomology sheaf `H^i(E)` is
`(m - i)`-pseudo-coherent, then `E` is `m`-pseudo-coherent. This local formulation covers the
parenthetical bounded-above case as a special case. -/
theorem isMPseudoCoherent_of_locallyBoundedAbove_of_homology
    (E : DModX) (m : ℤ)
    (hbounded : IsLocallyBoundedAbove E)
    (hH :
      ∀ i : ℤ,
        IsMPseudoCoherent
          ((single0).obj ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) i).obj E))
          (m - i)) :
    IsMPseudoCoherent E m := sorry

end AlgebraicGeometry.RingedSpace
