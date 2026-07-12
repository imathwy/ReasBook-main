import StacksProject_2024.Chap20.«20_42_0_1»
import StacksProject_2024.Chap20.Lemma_20_42_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Remark 20.42.10:
- primary domain: tensor/internal-Hom comparison morphisms in the braided monoidal closed derived
  category `RingedSpaceDerived X`;
- inspected owner declarations:
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry`,
  `CategoryTheory.MonoidalClosed.internalHomTensorIso`,
  `CategoryTheory.MonoidalClosed.pre`;
- best owner abstraction: the source-facing comparison of the remark should be built directly from
  the ambient tensor/internal-Hom adjunction on `RingedSpaceDerived X`, together with the
  canonical currying isomorphism `internalHomTensorIso`, rather than by a bespoke tensor-side
  evaluation composite;
- primitive data: the braided monoidal closed structure on `RingedSpaceDerived X` and the four
  objects `K`, `K'`, `M`, `M'`;
- derived API: the canonical comparison
  `(K ⟹ K') ⊗ (M ⟹ M') ⟶ ((K ⊗ M) ⟹ (K' ⊗ M'))`
  factored through the ambient tensor/internal-Hom comparison and the internal-Hom currying
  isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks Project comparison morphism of Remark 20.42.10;
- `core/canonical`: `MonoidalClosed.curry`, `MonoidalClosed.uncurry`,
  `internalHomTensorIso`, and `MonoidalClosed.pre`;
- `bridge/view`: the right-tensor source-order bridge
  `(K ⟹ K') ⊗ M' ⟶ K ⟹ (K' ⊗ M')`, followed by the canonical currying identification from
  `M ⟹ (K ⟹ (K' ⊗ M'))` to `(K ⊗ M) ⟹ (K' ⊗ M')`.
-/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/-- The right-tensor comparison
`Rℋom(K, K') ⊗ M' ⟶ Rℋom(K, K' ⊗ M')` on `D(𝒪_X)`, obtained by braiding the tensor factor
`M'` to the left, applying the ringed-site comparison morphism of
`ringedSiteDerivedTensorInternalHomComparison`, and then transporting the target across the
braiding `M' ⊗ K' ≅ K' ⊗ M'`. -/
noncomputable def ringedSpaceDerivedRightTensorInternalHomComparison
    (K K' M' : DModX) :
    (K ⟹ K') ⊗ M' ⟶ K ⟹ (K' ⊗ M') :=
  (β_ (K ⟹ K') M').hom ≫
    ringedSiteDerivedTensorInternalHomComparison M' K' K ≫
    (ihom K).map (β_ M' K').hom

/-- The source-order bridge for Remark 20.42.10, landing in
`Rℋom(M ⊗ K, K' ⊗ M')` before transporting the internal-Hom variable across the braiding
`K ⊗ M ≅ M ⊗ K`. -/
noncomputable def ringedSpaceDerivedTensorInternalHomComparisonSourceOrder
    (K K' M M' : DModX) :
    (K ⟹ K') ⊗ (M ⟹ M') ⟶ ((M ⊗ K) ⟹ (K' ⊗ M')) :=
  ringedSiteDerivedTensorInternalHomComparison (K ⟹ K') M' M ≫
    (ihom M).map (ringedSpaceDerivedRightTensorInternalHomComparison K K' M') ≫
    (internalHomTensorIso M K (K' ⊗ M')).hom

/-- Remark 20.42.10: in `D(𝒪_X)`, there is a canonical morphism
`Rℋom(K, K') ⊗ Rℋom(M, M') ⟶ Rℋom(K ⊗ M, K' ⊗ M')`.
The refined owner surface builds this map from the chapter tensor/internal-Hom comparison
`ringedSiteDerivedTensorInternalHomComparison`, then applies the currying isomorphism
`internalHomTensorIso` and the source-order bridge
`ringedSpaceDerivedTensorInternalHomComparisonSourceOrder` on `K ⊗ M`. -/
@[stacks 0FXP]
noncomputable def ringedSpaceDerivedTensorInternalHomComparison
    (K K' M M' : DModX) :
    (K ⟹ K') ⊗ (M ⟹ M') ⟶ ((K ⊗ M) ⟹ (K' ⊗ M')) :=
  ringedSpaceDerivedTensorInternalHomComparisonSourceOrder K K' M M' ≫
    (MonoidalClosed.pre ((β_ K M).hom)).app (K' ⊗ M')

/-- The comparison of Remark 20.42.10 is obtained by first forming the source-order comparison
`Rℋom(K, K') ⊗ Rℋom(M, M') ⟶ Rℋom(M ⊗ K, K' ⊗ M')` from
`ringedSpaceDerivedTensorInternalHomComparisonSourceOrder`, then precomposing the internal-Hom
variable with the braiding `K ⊗ M ≅ M ⊗ K`. -/
theorem ringedSpaceDerivedTensorInternalHomComparison_sourceOrder
    (K K' M M' : DModX) :
    ringedSpaceDerivedTensorInternalHomComparison K K' M M' =
      ringedSpaceDerivedTensorInternalHomComparisonSourceOrder K K' M M' ≫
        (MonoidalClosed.pre ((β_ K M).hom)).app (K' ⊗ M') :=
  rfl

end

end AlgebraicGeometry.RingedSpace
