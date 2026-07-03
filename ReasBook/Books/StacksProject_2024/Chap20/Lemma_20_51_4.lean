import Mathlib
import StacksProject_2024.Chap06.Definition_6_27_1
import StacksProject_2024.Chap20.Lemma_20_51_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable (x : X)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (Modules (pointRingedSpace x))]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules (pointRingedSpace x)))]
variable [MonoidalClosed (DerivedCategory (Modules (pointRingedSpace x)))]
variable [(modulePullback (pointInclusion x)).Additive]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/-- The canonical pullback-to-internal-Hom comparison for the point inclusion
`i_x : ({x}, \mathcal O_{X, x}) ⟶ X`. This is the point-ringed-space avatar of the stalk map
`R\mathcal H\!\mathit{om}(K, M)_x \to R\mathrm{Hom}_{\mathcal O_{X, x}}(K_x, M_x)`. -/
noncomputable def stalkDerivedInternalHomComparison
    (K M : DModX) :
    (modulePullbackDerived (pointInclusion x)).obj ((ihom K).obj M) ⟶
      (ihom ((modulePullbackDerived (pointInclusion x)).obj K)).obj
        ((modulePullbackDerived (pointInclusion x)).obj M) :=
  pullbackDerivedInternalHomComparison (pointInclusion x) K M

-- Proof sketch: apply Lemma `20.51.3 (1)` to the point inclusion
-- `i_x : ({x}, \mathcal O_{X, x}) ⟶ X`. The resulting pullback comparison is exactly the
-- point-ringed-space form of the canonical stalk map
-- `R\mathcal H\!\mathit{om}(K, M)_x \to R\mathrm{Hom}_{\mathcal O_{X, x}}(K_x, M_x)`.
/-- Lemma 20.51.4 (1): if `K` is perfect, then the canonical map from the stalk of
`R\mathcal H\!\mathit{om}(K, M)` at `x` to the derived internal Hom over the stalk ring
`\mathcal O_{X, x}` is an isomorphism. -/
theorem stalkDerivedInternalHomComparison_isIso_of_isPerfect
    (K M : DModX) (hK : DerivedCategory.IsPerfect K) :
    IsIso (stalkDerivedInternalHomComparison x K M) := sorry

-- Proof sketch: the point inclusion `i_x : ({x}, \mathcal O_{X, x}) ⟶ X` is flat on stalks, so
-- Lemma `20.51.3 (2)` applies. Its pullback comparison is the point-ringed-space expression of
-- the canonical stalk map
-- `R\mathcal H\!\mathit{om}(K, M)_x \to R\mathrm{Hom}_{\mathcal O_{X, x}}(K_x, M_x)`.
/-- Lemma 20.51.4 (2): if `K` is pseudo-coherent and `M` is locally bounded below, then the
canonical map from the stalk of `R\mathcal H\!\mathit{om}(K, M)` at `x` to the derived internal
Hom over the stalk ring `\mathcal O_{X, x}` is an isomorphism. -/
theorem stalkDerivedInternalHomComparison_isIso_of_isPseudoCoherent_of_locallyBoundedBelow
    (K M : DModX) (hK : DerivedCategory.IsPseudoCoherent K)
    (hM : IsLocallyBoundedBelow M) :
    IsIso (stalkDerivedInternalHomComparison x K M) := sorry

end

end AlgebraicGeometry.RingedSpace
