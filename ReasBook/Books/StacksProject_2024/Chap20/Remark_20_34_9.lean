import Mathlib
import stacks_project.Chap20.Lemma_20_34_1

open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

local notation "DModX" => ringedSpaceModuleDerived X
local notation "DModZ" => closedSubsetModuleDerived X Z

variable (restrictionToClosedSubset : DModX ⥤ DModZ)
variable
    (pushforwardSectionsAdj :
      closedSubsetModulePushforwardDerived X Z ⊣
        closedSubsetModuleSectionsWithSupportDerived X hZ)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorZ : DModZ ⥤ DModZ ⥤ DModZ)
variable
    (pushforwardTensorToAmbient :
      ∀ (K : DModX) (L : DModZ),
        (closedSubsetModulePushforwardDerived X Z).obj
            ((derivedTensorZ.obj L).obj (restrictionToClosedSubset.obj K)) ⟶
          ((derivedTensorX.obj ((closedSubsetModulePushforwardDerived X Z).obj L)).obj K))

/-- The pushforward-side morphism whose adjoint transpose gives the closed-subset tensor map. -/
private noncomputable abbrev
    closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_adjoint
    (K M : DModX) :
    (closedSubsetModulePushforwardDerived X Z).obj
        ((derivedTensorZ.obj ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj M)).obj
          (restrictionToClosedSubset.obj K)) ⟶
      ((derivedTensorX.obj M).obj K) :=
  pushforwardTensorToAmbient K
      ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj M) ≫
    ((derivedTensorX.map (pushforwardSectionsAdj.counit.app M)).app K)

/-- Remark 20.34.9: for a ringed space `(X, \mathcal O_X)` and a closed subset `i : Z \hookrightarrow X`,
once `restrictionToClosedSubset` is a chosen model for the restriction functor `K \mapsto K|_Z`,
the adjunction `i_* ⊣ R\mathcal H_Z` and the canonical pushforward-side tensor map determine a
canonical morphism
`K|_Z \otimes_{\mathcal O_X|_Z}^{\mathbf L} R\mathcal H_Z(M) \to
  R\mathcal H_Z(K \otimes_{\mathcal O_X}^{\mathbf L} M)`
in `D(\mathcal O_X|_Z)`. -/
noncomputable def closedSubsetRestrictionTensor_sectionsWithSupportDerived_map
    (K M : DModX) :
    ((derivedTensorZ.obj ((closedSubsetModuleSectionsWithSupportDerived X hZ).obj M)).obj
      (restrictionToClosedSubset.obj K)) ⟶
      (closedSubsetModuleSectionsWithSupportDerived X hZ).obj
        ((derivedTensorX.obj M).obj K) :=
  pushforwardSectionsAdj.homEquiv _ _
    (closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_adjoint
      hZ restrictionToClosedSubset pushforwardSectionsAdj
      derivedTensorX derivedTensorZ pushforwardTensorToAmbient K M)

-- Proof sketch: unfold the definition. The displayed morphism is defined to be the adjoint
-- transpose, under `i_* ⊣ R\mathcal H_Z`, of the pushforward-side map
-- `i_*(K|_Z \otimes^{\mathbf L} R\mathcal H_Z(M)) \to K \otimes^{\mathbf L} M`, obtained by
-- composing the tensor comparison with the adjunction counit `i_* R\mathcal H_Z(M) \to M`.
/-- The canonical closed-subset tensor map is adjoint to the corresponding pushforward-side tensor
comparison followed by the counit map `i_* R\mathcal H_Z(M) \to M`. -/
theorem closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_homEquiv
    (K M : DModX) :
    (pushforwardSectionsAdj.homEquiv _ _).symm
        (closedSubsetRestrictionTensor_sectionsWithSupportDerived_map
          hZ restrictionToClosedSubset pushforwardSectionsAdj
          derivedTensorX derivedTensorZ pushforwardTensorToAmbient K M) =
      closedSubsetRestrictionTensor_sectionsWithSupportDerived_map_adjoint
        hZ restrictionToClosedSubset pushforwardSectionsAdj
        derivedTensorX derivedTensorZ pushforwardTensorToAmbient K M := sorry

end

end AlgebraicGeometry.RingedSpace
