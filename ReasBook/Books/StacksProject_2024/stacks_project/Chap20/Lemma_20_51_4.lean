import StacksProject_2024.Chap17.Definition_17_20_1
import StacksProject_2024.Chap20.Lemma_20_51_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable (x : X)

open RingedSpace.Hom

local notation "ModX" => RingedSpace.Modules X
local notation "Modx" => RingedSpace.Modules (pointRingedSpace x)
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModx" => DerivedCategory (RingedSpace.Modules (pointRingedSpace x))
local notation "ix" => pointInclusion x

variable [((pointInclusion x)^*).Additive]

/- Domain-style sampling for Lemma 20.51.4:
- primary domain: derived internal Hom on ringed spaces, specialized to the point inclusion
  `i_x : pointRingedSpace x ⟶ X`;
- sampled owner declarations:
  `ModuleDerived`,
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`,
  `modulePullbackDerivedTensorIso`,
  `pullbackDerivedInternalHomComparison_isIso_of_isPerfect`,
  `pullbackDerivedInternalHomComparison_isIso_of_isFlat_of_isPseudoCoherent_of_locallyBoundedBelow`,
  `pointInclusion`;
- best owner abstraction: the Chapter 20 owner
  `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison`, with this file providing only
  the point-stalk specialization, and the canonical Chapter 20 tensor comparison is
  `fun A B ↦ (modulePullbackDerivedTensorIso ix B).app A`. This bridge nevertheless keeps a
  chosen pullback-tensor comparison as primitive data, because specializing to that canonical
  tensor isomorphism would force a strictly larger tensor-derived assumption layer than the source
  statement of this stalk lemma needs;
- primitive data: the point `x`, a chosen pullback-tensor comparison for `L(i_x)^*`, the
  objects `K`, `M`, and the source hypotheses on `K` and `M`;
- derived API: the two source-facing stalk comparison isomorphism statements below.

Source/core/bridge triage:
- `source-facing`: the stalk comparison isomorphism at a point;
- `core/canonical`: `SheafOfModules.RingedSite.pullbackDerivedInternalHomComparison` and its
  isomorphism theorems from Lemma `20.51.3`;
- `bridge/view`: specialization along `pointInclusion x`, interpreting the pullback comparison as
  the canonical stalk map for a chosen pullback-tensor comparison on `L(i_x)^*`. -/

-- Proof sketch: apply Lemma `20.51.3 (1)` to the point inclusion
-- `i_x : pointRingedSpace x ⟶ X`. The resulting pullback comparison is exactly the
-- point-ringed-space form of the canonical stalk map from the derived internal Hom of `K` and `M`
-- at `x` to the derived internal Hom over the stalk ring `𝒪_{X, x}`.
/-- Lemma 20.51.4 (1): if `K` is perfect, then the canonical map from the stalk of
the derived internal Hom of `K` and `M` at `x` to the derived internal Hom over the stalk ring
`𝒪_{X, x}`, formed using a chosen pullback-tensor comparison for `L(i_x)^*`, is an
isomorphism. -/
@[stacks 0GM8]
instance stalkDerivedInternalHomComparison_isIso_of_isPerfect
    [MonoidalCategory DModX] [BraidedCategory DModX] [MonoidalClosed DModX]
    [MonoidalCategory DModx] [BraidedCategory DModx] [MonoidalClosed DModx]
    (pullbackTensorIso :
      ∀ A B : DModX, (L(ix)^*).obj (A ⊗ B) ≅ ((L(ix)^*).obj A ⊗ (L(ix)^*).obj B))
    (K M : DModX) (hK : DerivedCategory.IsPerfect K) :
    IsIso (pullbackDerivedInternalHomComparison (L(ix)^*) pullbackTensorIso K M) := by
  letI : IsIso (pullbackDerivedInternalHomComparison (L(ix)^*) pullbackTensorIso K M) :=
    pullbackDerivedInternalHomComparison_isIso_of_isPerfect ix pullbackTensorIso K M hK
  infer_instance

-- Proof sketch: the point inclusion `i_x : pointRingedSpace x ⟶ X` is flat on stalks, so
-- Lemma `20.51.3 (2)` applies. Its pullback comparison is the point-ringed-space expression of
-- the canonical stalk map from the derived internal Hom of `K` and `M` at `x` to the derived
-- internal Hom over the stalk ring `𝒪_{X, x}`.
/-- Lemma 20.51.4 (2): if `K` is pseudo-coherent and `M` is locally bounded below, then the
canonical map from the stalk of the derived internal Hom of `K` and `M` at `x` to the derived
internal Hom over the stalk ring `𝒪_{X, x}`, formed using a chosen pullback-tensor comparison for
`L(i_x)^*`, is an isomorphism. -/
@[stacks 0GM8]
instance stalkDerivedInternalHomComparison_isIso_of_isPseudoCoherent_of_locallyBoundedBelow
    [MonoidalCategory DModX] [BraidedCategory DModX] [MonoidalClosed DModX]
    [MonoidalCategory DModx] [BraidedCategory DModx] [MonoidalClosed DModx]
    (pullbackTensorIso :
      ∀ A B : DModX, (L(ix)^*).obj (A ⊗ B) ≅ ((L(ix)^*).obj A ⊗ (L(ix)^*).obj B))
    (K M : DModX) (hK : ModuleDerived.IsPseudoCoherent K)
    (hM : ModuleDerived.IsLocallyBoundedBelow M) :
    IsIso (pullbackDerivedInternalHomComparison (L(ix)^*) pullbackTensorIso K M) := by
  letI : IsIso (pullbackDerivedInternalHomComparison (L(ix)^*) pullbackTensorIso K M) :=
    pullbackDerivedInternalHomComparison_isIso_of_isFlat_of_isPseudoCoherent_of_locallyBoundedBelow
      ix pullbackTensorIso K M hK hM
  infer_instance

end

end AlgebraicGeometry.RingedSpace
