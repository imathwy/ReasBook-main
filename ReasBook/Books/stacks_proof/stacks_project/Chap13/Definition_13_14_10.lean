import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_14_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open CategoryTheory.Limits

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂} [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
variable (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟)
variable [S.ContainsIdentities]

/- 
Domain-style sampling for Definition 13.14.10:
- primary domain: pointwise derived values at a fixed object and their canonical comparison maps;
- sampled owner declarations:
  `HasPointwiseRightDerivedFunctorAt`,
  `rightDerivedValueLeg`,
  `HasPointwiseLeftDerivedFunctorAt`,
  `leftDerivedValueProjection`,
  `leftKanExtensionObjIsoColimit`,
  `RightExtension.IsPointwiseRightKanExtensionAt.isoLimit`,
  `RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_π`,
  `HasRightDerivedFunctor`,
  `totalRightDerivedUnit`,
  `HasLeftDerivedFunctor`,
  `totalLeftDerivedCounit`;
- best owner abstraction: the source-facing notion here is the pointwise computation condition at
  `X`, so the owner should be a pointwise class extending the mathlib pointwise-derived owner and
  using the canonical identity-denominator comparison maps in the Chapter `13` owners
  `rightDerivedValueLeg` and `leftDerivedValueProjection`; the global total derived functor API is
  only a stronger bridge/view layer;
- primitive data: pointwise derived-definedness at `X` and invertibility of the canonical
  identity leg/projection in the pointwise colimit/limit presentation;
- derived API: the source-facing classes `ComputesRightDerivedAt` and `ComputesLeftDerivedAt`,
  the reusable object properties `computesRightDerivedObjectProperty` and
  `computesLeftDerivedObjectProperty`, together with bridge lemmas to the total derived
  unit/counit when those stronger global assumptions are available.

Source/core/bridge triage:
- `source-facing`: `Functor.ComputesRightDerivedAt` and `Functor.ComputesLeftDerivedAt`;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`, and the canonical identity-arrow maps in the
  pointwise colimit/limit presentations;
- `bridge/view`: the `_iff` lemmas below, which compare the source-facing classes with the
  stronger total derived unit/counit formulation when a global derived functor exists.
-/

section Right

/-- Definition 13.14.10 (1): an object `X` computes the right derived functor of `F` with
respect to `S` when the pointwise right derived value at `X` is defined and the canonical map
`F(X) ⟶ RF(X)` is an isomorphism. -/
@[stacks 05SX]
class ComputesRightDerivedAt : Prop extends F.HasPointwiseRightDerivedFunctorAt S X where
  /-- The identity-denominator leg `F.obj X ⟶ RF(X)` in the pointwise colimit presentation is an
  isomorphism. -/
  isIso_rightDerivedValueLeg : IsIso (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))

attribute [instance] ComputesRightDerivedAt.isIso_rightDerivedValueLeg

/-- The object property on `𝒟` consisting of those objects which compute the right derived
functor of `F` with respect to `S`. -/
abbrev computesRightDerivedObjectProperty : ObjectProperty 𝒟 :=
  fun X ↦ F.ComputesRightDerivedAt S X

variable [F.HasPointwiseRightDerivedFunctor S]

local instance hasPointwiseLeftKanExtension :
    S.Q.HasPointwiseLeftKanExtension F :=
  F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor S.Q S

/-- The source-facing identity leg in the pointwise right-derived colimit presentation agrees
with the total derived unit component, up to the canonical colimit comparison isomorphism. The
only public assumption is the owner-level pointwise existence hypothesis
`F.HasPointwiseRightDerivedFunctor S`, from which the needed Kan-extension data are derived
internally. -/
theorem rightDerivedValueLeg_id_eq_totalRightDerivedUnit :
    rightDerivedValueLeg S F (𝟙 X) (S.id_mem X) =
      ((F.totalRightDerivedUnit S.Q S).app X) ≫
        ((S.Q).leftKanExtensionObjIsoColimit F (S.Q.obj X)).hom := by
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  rw [rightDerivedValueLeg, Localization.isoOfHom_id_inv S.Q S X (S.id_mem X)]
  simpa [totalRightDerived, totalRightDerivedUnit] using
    (S.Q.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom F X).symm

/-- Under the stronger assumption that the pointwise right derived functor exists everywhere, the
source-facing condition that `X` computes the right derived functor is equivalent to invertibility
of the total derived unit component at `X`. This bridge lemma keeps only the canonical global
pointwise-existence assumption on the public surface. -/
theorem computesRightDerivedAt_iff :
    F.ComputesRightDerivedAt S X ↔
      IsIso ((F.totalRightDerivedUnit S.Q S).app X) :=
    by
  constructor
  · intro h
    -- Rewrite the source-facing identity leg to the total unit followed by the colimit
    -- comparison isomorphism, then transport `IsIso` across the right factor.
    letI : F.ComputesRightDerivedAt S X := h
    have hLeg : IsIso (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by infer_instance
    rw [rightDerivedValueLeg_id_eq_totalRightDerivedUnit (F := F) (S := S) (X := X)] at hLeg
    exact
      (isIso_comp_right_iff
        ((F.totalRightDerivedUnit S.Q S).app X)
        (((S.Q).leftKanExtensionObjIsoColimit F (S.Q.obj X)).hom)).1 hLeg
  · intro h
    -- Combine global pointwise existence with the transported invertibility of the identity leg.
    refine ⟨?_⟩
    rw [rightDerivedValueLeg_id_eq_totalRightDerivedUnit (F := F) (S := S) (X := X)]
    exact
      (isIso_comp_right_iff
        ((F.totalRightDerivedUnit S.Q S).app X)
        (((S.Q).leftKanExtensionObjIsoColimit F (S.Q.obj X)).hom)).2 h

end Right

section Left

/-- Definition 13.14.10 (2): an object `X` computes the left derived functor of `F` with
respect to `S` when the pointwise left derived value at `X` is defined and the canonical map
`LF(X) ⟶ F(X)` is an isomorphism. -/
@[stacks 05SX]
class ComputesLeftDerivedAt : Prop extends F.HasPointwiseLeftDerivedFunctorAt S X where
  /-- The identity-denominator projection `LF(X) ⟶ F.obj X` in the pointwise limit presentation
  is an isomorphism. -/
  isIso_leftDerivedValueProjection :
    IsIso (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X))

attribute [instance] ComputesLeftDerivedAt.isIso_leftDerivedValueProjection

/-- The object property on `𝒟` consisting of those objects which compute the left derived
functor of `F` with respect to `S`. -/
abbrev computesLeftDerivedObjectProperty : ObjectProperty 𝒟 :=
  fun X ↦ F.ComputesLeftDerivedAt S X

variable [F.HasPointwiseLeftDerivedFunctor S]

local instance hasLimitStructuredArrow :
    HasLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
  HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X

/-- The source-facing identity projection in the pointwise left-derived limit presentation agrees
with the total derived counit component, up to the canonical right-Kan-extension/limit comparison
for `S.Q` and `F`. The needed limit data are derived internally from the canonical owner
assumption `F.HasPointwiseLeftDerivedFunctor S`. -/
theorem leftDerivedValueProjection_id_eq_totalLeftDerivedCounit
    :
    leftDerivedValueProjection S F (𝟙 X) (S.id_mem X) =
      ((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
          (F.totalLeftDerived S.Q S) (F.totalLeftDerivedCounit S.Q S) S
          (S.Q.obj X)).isoLimit).inv ≫
        ((F.totalLeftDerivedCounit S.Q S).app X) := by
  simpa [leftDerivedValueProjection, totalLeftDerived, totalLeftDerivedCounit,
    Localization.isoOfHom_id_inv S.Q S X (S.id_mem X)] using
    ((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (F.totalLeftDerived S.Q S) (F.totalLeftDerivedCounit S.Q S) S
      (S.Q.obj X)).isoLimit_inv_π
        (StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv))).symm

/-- Under the stronger assumption that the pointwise left derived functor exists everywhere, the
source-facing condition that `X` computes the left derived functor is equivalent to invertibility
of the total derived counit component at `X`. -/
theorem computesLeftDerivedAt_iff :
    F.ComputesLeftDerivedAt S X ↔
      IsIso ((F.totalLeftDerivedCounit S.Q S).app X) :=
    by
  constructor
  · intro h
    -- Rewrite the source-facing identity projection to the limit comparison isomorphism
    -- followed by the total counit, then transport `IsIso` across the left factor.
    letI : F.ComputesLeftDerivedAt S X := h
    have hProjection : IsIso (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
      infer_instance
    rw [leftDerivedValueProjection_id_eq_totalLeftDerivedCounit (F := F) (S := S) (X := X)] at hProjection
    exact
      (isIso_comp_left_iff
        (((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
            (F.totalLeftDerived S.Q S) (F.totalLeftDerivedCounit S.Q S) S
            (S.Q.obj X)).isoLimit).inv)
        ((F.totalLeftDerivedCounit S.Q S).app X)).1 hProjection
  · intro h
    -- Combine global pointwise existence with the transported invertibility of the identity
    -- projection in the pointwise limit presentation.
    refine ⟨?_⟩
    rw [leftDerivedValueProjection_id_eq_totalLeftDerivedCounit (F := F) (S := S) (X := X)]
    exact
      (isIso_comp_left_iff
        (((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
            (F.totalLeftDerived S.Q S) (F.totalLeftDerivedCounit S.Q S) S
            (S.Q.obj X)).isoLimit).inv)
        ((F.totalLeftDerivedCounit S.Q S).app X)).2 h

end Left

end

end Functor

end CategoryTheory
