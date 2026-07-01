import Mathlib
import stacks_project.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (openSubspaceModuleCategory X U))]
variable [MonoidalClosed (DerivedCategory (openSubspaceModuleCategory X U))]

-- Proof sketch: represent `K` by a K-injective complex `I`. By Lemma `20.32.1`, the restricted
-- complex `I|_U` is again K-injective, so both derived internal-Hom objects are computed by the
-- underived internal-Hom complexes of `I|_U` and the restriction of a representative of `L`.
-- The ordinary internal-Hom construction commutes with restriction to opens, giving the required
-- identification in the derived category on `U`.
/-- Lemma 20.42.3: for a ringed space `(X, \mathcal O_X)`, an open subset `U \subset X`, and
objects `K, L` of `D(\mathcal O_X)`, restricting `R\mathcal H\!\mathit{om}(K, L)` to `U` is
canonically isomorphic to the derived internal Hom of the restricted objects
`K|_U` and `L|_U`. -/
theorem ringedSpaceDerivedInternalHom_restrict_isomorphic
    (K L : DerivedCategory (RingedSpace.Modules X)) :
    IsIsomorphic
      ((moduleRestrictionToOpenDerived X U).obj ((ihom K).obj L))
      ((ihom ((moduleRestrictionToOpenDerived X U).obj K)).obj
        ((moduleRestrictionToOpenDerived X U).obj L)) := sorry

end

end AlgebraicGeometry.RingedSpace
