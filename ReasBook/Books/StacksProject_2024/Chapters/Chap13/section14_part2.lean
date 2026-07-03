import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_14_10 (from Chap13) -/
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

/-! ### Lemma_13_14_11 (from Chap13) -/
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.14.11:
- primary domain: shift compatibility for the source-facing computation conditions for pointwise
  left/right derived functors on a localization;
- inspected owner declarations:
  `ObjectProperty.IsStableUnderShift`,
  `ObjectProperty.prop_shift_iff_of_isStableUnderShift`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.computesRightDerivedObjectProperty`,
  `Functor.computesLeftDerivedObjectProperty`,
  `hasPointwiseRightDerivedFunctorAt_iff_shift`,
  `hasPointwiseLeftDerivedFunctorAt_iff_shift`;
- best owner abstraction: the canonical closure owner
  `ObjectProperty.IsStableUnderShift ℤ` applied to the Chapter `13` owner object properties
  `F.computesRightDerivedObjectProperty S` and `F.computesLeftDerivedObjectProperty S`;
- primitive data: the source-facing predicates `Functor.ComputesRightDerivedAt` and
  `Functor.ComputesLeftDerivedAt`, whose content is pointwise derived-definedness together with
  invertibility of the canonical unit/counit comparison map from `Definition_13_14_10`;
- derived API: the owner object properties from `Definition_13_14_10`, the closure instances
  below, and the source-facing `↔` lemmas whose proofs reuse that internal owner abstraction.

Source/core/bridge triage:
- `source-facing`: the textbook statements that `X` computes the derived functor if and only if
  `X⟦n⟧` does, under compatibility of `S` and `F` with shift;
- `core/canonical`: `ObjectProperty.IsStableUnderShift ℤ` for the owner object properties
  `F.computesRightDerivedObjectProperty S` and `F.computesLeftDerivedObjectProperty S`;
- `bridge/view`: the companion pointwise `↔` lemmas below, proved via the owner-level
  shift-stability API. -/

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
  {X : D} (n : ℤ)

/-- Objects which compute the right derived functor of `F` are closed under ambient
isomorphisms. -/
instance computesRightDerivedAt_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (F.computesRightDerivedObjectProperty S) := by
  sorry

/-- Objects which compute the left derived functor of `F` are closed under ambient
isomorphisms. -/
instance computesLeftDerivedAt_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (F.computesLeftDerivedObjectProperty S) := by
  sorry

/-- Objects which compute the right derived functor of `F` form a shift-stable object property. -/
instance computesRightDerivedAt_isStableUnderShift :
    IsStableUnderShift (F.computesRightDerivedObjectProperty S) ℤ := by
  sorry

/-- Objects which compute the left derived functor of `F` form a shift-stable object property. -/
instance computesLeftDerivedAt_isStableUnderShift :
    IsStableUnderShift (F.computesLeftDerivedObjectProperty S) ℤ := by
  sorry

end

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]
  {X : D} (n : ℤ)

-- Proof sketch: combine the shift invariance of pointwise right-derived existence from
-- `hasPointwiseRightDerivedFunctorAt_iff_shift` with the canonical shift comparison for the
-- pointwise derived values from `Lemma_13_14_5 (2)`, which transports invertibility of the unit
-- map `F.obj X ⟶ RF(X)` exactly to the unit map at `X⟦n⟧`.
/-- Lemma 13.14.11 (1): if the morphism property `S` and the functor `F` are compatible with
shifts, then `X` computes the right derived functor of `F` with respect to `S` if and only if
`X⟦n⟧` does. -/
theorem computesRightDerivedAt_iff_shift
    [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    : F.ComputesRightDerivedAt S X ↔
      F.ComputesRightDerivedAt S (X⟦n⟧) := by
  simpa using
    ((F.computesRightDerivedObjectProperty S).prop_shift_iff_of_isStableUnderShift X n).symm

-- Proof sketch: this is the dual argument, using
-- `hasPointwiseLeftDerivedFunctorAt_iff_shift` together with the shift comparison for the
-- pointwise left-derived values to transport invertibility of the canonical counit map.
/-- Lemma 13.14.11 (2): if the morphism property `S` and the functor `F` are compatible with
shifts, then `X` computes the left derived functor of `F` with respect to `S` if and only if
`X⟦n⟧` does. -/
theorem computesLeftDerivedAt_iff_shift
    [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    : F.ComputesLeftDerivedAt S X ↔
      F.ComputesLeftDerivedAt S (X⟦n⟧) := by
  simpa using
    ((F.computesLeftDerivedObjectProperty S).prop_shift_iff_of_isStableUnderShift X n).symm

end

end CategoryTheory

/-! ### Lemma_13_14_12 (from Chap13) -/
open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.14.12:
- primary domain: pointwise computation of right/left derived functors in a triangulated
  localization situation, with closure under distinguished triangles;
- sampled owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.computesRightDerivedObjectProperty`,
  `Functor.computesLeftDerivedObjectProperty`,
  `ObjectProperty.IsTriangulatedClosed₃`,
  `ObjectProperty.ext_of_isTriangulatedClosed₃`;
- best owner abstraction: the source-facing predicates
  `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt` are already organized by the
  Chapter 13 owner object properties `F.computesRightDerivedObjectProperty S` and
  `F.computesLeftDerivedObjectProperty S`; this file should therefore record the third-vertex
  distinguished-triangle closure first as the canonical owner instances
  `IsTriangulatedClosed₃` for those object properties, and only then keep the textbook `obj₃`
  statements as thin wrappers;
- primitive data: a distinguished triangle in `D` and computation hypotheses on its first two
  vertices, where `ComputesRightDerivedAt` / `ComputesLeftDerivedAt` already package the needed
  pointwise derived-definedness together with invertibility of the canonical identity
  leg/projection;
- derived API: the owner-level closure instances and the pointwise `obj₃` consequences.

Source/core/bridge triage:
- `source-facing`: the two textbook `obj₃` closure statements for objects computing the
  right/left derived functor in a distinguished triangle;
- `core/canonical`: the object-property owners
  `F.computesRightDerivedObjectProperty S` / `F.computesLeftDerivedObjectProperty S` together
  with `ObjectProperty.IsTriangulatedClosed₃`;
- `bridge/view`: the two theorem wrappers below, which simply restate the owner-level closure in
  the textbook pointwise form.
-/
variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [hasZeroObjectD' : Limits.HasZeroObject D']
  [HasShift D ℤ] [hasShiftD' : HasShift D' ℤ]
  [Preadditive D] [preadditiveD' : Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [shiftAdditiveD' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [pretriangulatedD' : Pretriangulated D']
  [triangulatedD' : IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [commShiftF : F.CommShift ℤ] [triangulatedF : F.IsTriangulated]
  [satS : IsSaturatedMultiplicativeSystem S] [compatS : S.IsCompatibleWithTriangulation]

section Right

include hasZeroObjectD' hasShiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  triangulatedD' commShiftF triangulatedF satS compatS

-- Proof sketch: the underlying pointwise right-derived-definedness already satisfies the
-- third-vertex closure by Lemma `13.14.6`. To upgrade from definedness to computation, compare
-- the `F`-image triangle with the induced triangle on pointwise right-derived values; the first
-- two vertical maps are isomorphisms by the hypotheses on `X` and `Y`, so
-- `Pretriangulated.isIso₃_of_isIso₁₂` gives the third one and hence the required unit
-- isomorphism at `Z`.
/-- Objects computing the right derived functor of `F` form an object property closed under the
third vertex of a distinguished triangle. -/
instance computesRightDerivedObjectProperty_isTriangulatedClosed₃
    : IsTriangulatedClosed₃ (F.computesRightDerivedObjectProperty S) := by
  refine .mk' ?_
  intro T hT h₁ h₂
  sorry

end Right

section Left

include hasZeroObjectD' hasShiftD' preadditiveD' shiftAdditiveD' pretriangulatedD'
  triangulatedD' commShiftF triangulatedF satS compatS

-- Proof sketch: this is the dual owner-level closure statement. Lemma `13.14.6` gives
-- pointwise left-derived existence at the third vertex, and the comparison morphism of
-- distinguished triangles has isomorphic first two components by the hypotheses that `X` and
-- `Y` compute `LF`; two-out-of-three gives the third component, i.e. the identity projection at
-- `Z`.
/-- Objects computing the left derived functor of `F` form an object property closed under the
third vertex of a distinguished triangle. -/
instance computesLeftDerivedObjectProperty_isTriangulatedClosed₃
    : IsTriangulatedClosed₃ (F.computesLeftDerivedObjectProperty S) := by
  refine .mk' ?_
  intro T hT h₁ h₂
  sorry

end Left

end

section SourceFacing

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [IsSaturatedMultiplicativeSystem S]

/-- Lemma 13.14.12 (1): if `T` is a distinguished triangle of `D` and its first two vertices
compute the right derived functor of `F` with respect to `S`, then so does its third vertex. -/
theorem computesRightDerivedAt_obj₃_of_distinguished_triangle
    [IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : F.ComputesRightDerivedAt S T.obj₁)
    (h₂ : F.ComputesRightDerivedAt S T.obj₂) :
    F.ComputesRightDerivedAt S T.obj₃ := by
  exact (F.computesRightDerivedObjectProperty S).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

/-- Lemma 13.14.12 (2): if `T` is a distinguished triangle of `D` and its first two vertices
compute the left derived functor of `F` with respect to `S`, then so does its third vertex. -/
theorem computesLeftDerivedAt_obj₃_of_distinguished_triangle
    [IsTriangulated D']
    [F.CommShift ℤ] [F.IsTriangulated]
    [S.IsCompatibleWithTriangulation]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : F.ComputesLeftDerivedAt S T.obj₁)
    (h₂ : F.ComputesLeftDerivedAt S T.obj₂) :
    F.ComputesLeftDerivedAt S T.obj₃ := by
  exact (F.computesLeftDerivedObjectProperty S).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

end SourceFacing

end CategoryTheory

/-! ### Lemma_13_14_13 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section Stability

/- Domain-style sampling for Lemma 13.14.13:
- primary domain: object properties on a triangulated category which are stable under retracts,
  applied to the source-facing predicates `Functor.ComputesRightDerivedAt` and
  `Functor.ComputesLeftDerivedAt`;
- inspected owner declarations:
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`,
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `rightDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `leftDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the core/canonical owner is
  `ObjectProperty.IsStableUnderRetracts`, first for the pointwise-definedness object properties
  from `Proposition_13_14_8`, then for the stronger source-facing computation predicates in the
  present file; the biproduct consequences should therefore be derived from the generic retract
  lemmas `of_biprod_left` and `of_biprod_right`, not stated only as ad hoc conjunction theorems;
- primitive data: the object properties `fun X ↦ F.ComputesRightDerivedAt S X` and
  `fun X ↦ F.ComputesLeftDerivedAt S X`;
- derived API: the left/right direct-summand consequences and the conjunction theorem packaging
  them together.

Source/core/bridge triage:
- `source-facing`: the textbook claim that if `X ⊞ Y` computes the right or left derived functor,
  then both summands do;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts` for the relevant object properties,
  together with `of_biprod_left` and `of_biprod_right`;
- `bridge/view`: the conjunction theorems `computesRightDerivedAt_of_biprod` and
  `computesLeftDerivedAt_of_biprod`, now demoted to thin wrappers around the owner-level API.
-/

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]
  {X Y : D}

-- Proof sketch: the source-facing computation predicate extends the pointwise-definedness
-- predicate, whose retract stability is already owned upstream. For the isomorphism part, the
-- identity leg
-- `F.obj X ⟶ rightDerivedValue S F X` is a retract, in the arrow category, of the corresponding
-- identity leg for any retract ambient object `Y`; retracts of isomorphisms are isomorphisms.
/-- Objects which compute the right derived functor of `F` form a retract-stable object
property. -/
instance computesRightDerivedAt_isStableUnderRetracts [IsIdempotentComplete D'] :
    (F.computesRightDerivedObjectProperty S).IsStableUnderRetracts := by
  refine ⟨?_⟩
  intro X Y r hY
  letI : F.ComputesRightDerivedAt S Y := hY
  have hX :
      rightDerivedDefinedObjectProperty F S X :=
    (rightDerivedDefinedObjectProperty F S).prop_of_retract r
      (show rightDerivedDefinedObjectProperty F S Y from inferInstance)
  letI : F.HasPointwiseRightDerivedFunctorAt S X := hX
  refine { isIso_rightDerivedValueLeg := ?_ }
  let X' : rightDerivedDefinedSubcategory F S := ⟨X, hX⟩
  let Y' : rightDerivedDefinedSubcategory F S :=
    ⟨Y, show rightDerivedDefinedObjectProperty F S Y from inferInstance⟩
  let i' : X' ⟶ Y' := ObjectProperty.homMk r.i
  let r' : Y' ⟶ X' := ObjectProperty.homMk r.r
  let uX : F.obj X ⟶ rightDerivedValue S F X :=
    rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)
  let uY : F.obj Y ⟶ rightDerivedValue S F Y :=
    rightDerivedValueLeg S F (𝟙 Y) (S.id_mem Y)
  let Ri : rightDerivedValue S F X ⟶ rightDerivedValue S F Y :=
    (rightDerivedDefinedFunctor F S).map i'
  let Rr : rightDerivedValue S F Y ⟶ rightDerivedValue S F X :=
    (rightDerivedDefinedFunctor F S).map r'
  have h_i :
      F.map r.i ≫ uY = uX ≫ Ri := by
    simpa [uX, uY, Ri, i'] using
      (show CommSq uX (F.map r.i) Ri uY from
        rightDerivedValueMap_comp_of_square S F r.i
          (𝟙 X) (𝟙 Y) (S.id_mem X) (S.id_mem Y) r.i
          ⟨by simp⟩).w.symm
  have h_r :
      F.map r.r ≫ uX = uY ≫ Rr := by
    simpa [uX, uY, Rr, r'] using
      (show CommSq uY (F.map r.r) Rr uX from
        rightDerivedValueMap_comp_of_square S F r.r
          (𝟙 Y) (𝟙 X) (S.id_mem Y) (S.id_mem X) r.r
          ⟨by simp⟩).w.symm
  have hR : Ri ≫ Rr = 𝟙 _ := by
    have hi' : i' ≫ r' = 𝟙 X' := by
      ext
      simpa [i', r'] using r.retract
    simpa [Ri, Rr, Functor.map_comp] using
      congrArg ((rightDerivedDefinedFunctor F S).map) hi'
  have hF : F.map r.i ≫ F.map r.r = 𝟙 _ := by
    rw [← F.map_comp, r.retract, F.map_id]
  let hArrow : RetractArrow uX uY :=
    { i := Arrow.homMk' (F.map r.i) Ri h_i
      r := Arrow.homMk' (F.map r.r) Rr h_r
      retract := by
        ext
        · exact hF
        · exact hR }
  exact MorphismProperty.of_retract hArrow inferInstance

-- Proof sketch: dually, pointwise left-derived-definedness already descends along retracts, and
-- the identity projection `leftDerivedValue S F X ⟶ F.obj X` is a retract of the corresponding
-- projection for `Y`; retracts of isomorphisms are isomorphisms.
/-- Objects which compute the left derived functor of `F` form a retract-stable object
property. -/
instance computesLeftDerivedAt_isStableUnderRetracts [IsIdempotentComplete D'] :
    (F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts := by
  refine ⟨?_⟩
  intro X Y r hY
  letI : F.ComputesLeftDerivedAt S Y := hY
  have hX :
      leftDerivedDefinedObjectProperty F S X :=
    (leftDerivedDefinedObjectProperty F S).prop_of_retract r
      (show leftDerivedDefinedObjectProperty F S Y from inferInstance)
  letI : F.HasPointwiseLeftDerivedFunctorAt S X := hX
  refine { isIso_leftDerivedValueProjection := ?_ }
  let X' : leftDerivedDefinedSubcategory F S := ⟨X, hX⟩
  let Y' : leftDerivedDefinedSubcategory F S :=
    ⟨Y, show leftDerivedDefinedObjectProperty F S Y from inferInstance⟩
  let i' : X' ⟶ Y' := ObjectProperty.homMk r.i
  let r' : Y' ⟶ X' := ObjectProperty.homMk r.r
  let uX : leftDerivedValue S F X ⟶ F.obj X :=
    leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)
  let uY : leftDerivedValue S F Y ⟶ F.obj Y :=
    leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y)
  let Li : leftDerivedValue S F X ⟶ leftDerivedValue S F Y :=
    (leftDerivedDefinedFunctor F S).map i'
  let Lr : leftDerivedValue S F Y ⟶ leftDerivedValue S F X :=
    (leftDerivedDefinedFunctor F S).map r'
  have h_i :
      Li ≫ uY = uX ≫ F.map r.i := by
    simpa [uX, uY, Li, i'] using
      (show CommSq Li uX uY (F.map r.i) from
        leftDerivedValueMap_comp_of_square S F r.i
          (𝟙 X) (𝟙 Y) (S.id_mem X) (S.id_mem Y) r.i
          ⟨by simp⟩).w
  have h_r :
      Lr ≫ uX = uY ≫ F.map r.r := by
    simpa [uX, uY, Lr, r'] using
      (show CommSq Lr uY uX (F.map r.r) from
        leftDerivedValueMap_comp_of_square S F r.r
          (𝟙 Y) (𝟙 X) (S.id_mem Y) (S.id_mem X) r.r
          ⟨by simp⟩).w
  have hL : Li ≫ Lr = 𝟙 _ := by
    have hi' : i' ≫ r' = 𝟙 X' := by
      ext
      simpa [i', r'] using r.retract
    simpa [Li, Lr, Functor.map_comp] using
      congrArg ((leftDerivedDefinedFunctor F S).map) hi'
  have hF : F.map r.i ≫ F.map r.r = 𝟙 _ := by
    rw [← F.map_comp, r.retract, F.map_id]
  let hArrow : RetractArrow uX uY :=
    { i := Arrow.homMk' Li (F.map r.i) h_i
      r := Arrow.homMk' Lr (F.map r.r) h_r
      retract := by
        ext
        · exact hL
        · exact hF }
  exact MorphismProperty.of_retract hArrow inferInstance

end Stability

section Biproduct

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroMorphisms D]
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.ContainsIdentities]
  {X Y : D}

/-- Lemma 13.14.13 (1): if `X ⊞ Y` computes the right derived functor of `F`, then `X` does. -/
theorem computesRightDerivedAt_left_of_biprod
    [(F.computesRightDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesRightDerivedAt S (X ⊞ Y)) :
    F.ComputesRightDerivedAt S X :=
  of_biprod_left (F.computesRightDerivedObjectProperty S) hXY

/-- Lemma 13.14.13 (2): if `X ⊞ Y` computes the right derived functor of `F`, then `Y` does. -/
theorem computesRightDerivedAt_right_of_biprod
    [(F.computesRightDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesRightDerivedAt S (X ⊞ Y)) :
    F.ComputesRightDerivedAt S Y :=
  of_biprod_right (F.computesRightDerivedObjectProperty S) hXY

/-- If `X ⊞ Y` computes the right derived functor of `F`, then both summands do. -/
theorem computesRightDerivedAt_of_biprod
    [(F.computesRightDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesRightDerivedAt S (X ⊞ Y)) :
    F.ComputesRightDerivedAt S X ∧
      F.ComputesRightDerivedAt S Y :=
  ⟨computesRightDerivedAt_left_of_biprod F S hXY,
    computesRightDerivedAt_right_of_biprod F S hXY⟩

/-- Lemma 13.14.13 (3): if `X ⊞ Y` computes the left derived functor of `F`, then `X` does. -/
theorem computesLeftDerivedAt_left_of_biprod
    [(F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesLeftDerivedAt S (X ⊞ Y)) :
    F.ComputesLeftDerivedAt S X :=
  of_biprod_left (F.computesLeftDerivedObjectProperty S) hXY

/-- Lemma 13.14.13 (4): if `X ⊞ Y` computes the left derived functor of `F`, then `Y` does. -/
theorem computesLeftDerivedAt_right_of_biprod
    [(F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesLeftDerivedAt S (X ⊞ Y)) :
    F.ComputesLeftDerivedAt S Y :=
  of_biprod_right (F.computesLeftDerivedObjectProperty S) hXY

/-- The left-derived analogue of `computesRightDerivedAt_of_biprod`. -/
theorem computesLeftDerivedAt_of_biprod
    [(F.computesLeftDerivedObjectProperty S).IsStableUnderRetracts]
    [HasBinaryBiproduct X Y]
    (hXY : F.ComputesLeftDerivedAt S (X ⊞ Y)) :
    F.ComputesLeftDerivedAt S X ∧
      F.ComputesLeftDerivedAt S Y :=
  ⟨computesLeftDerivedAt_left_of_biprod F S hXY,
    computesLeftDerivedAt_right_of_biprod F S hXY⟩

end Biproduct

end CategoryTheory

/-! ### Lemma_13_14_14 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']

/- Domain-style sampling for Lemma 13.14.14:
- primary domain: global pointwise existence of derived functors from source-facing computation
  objects connected by morphisms in the localization class;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the core/canonical owners are
  `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasPointwiseLeftDerivedFunctor`; the
  source-facing hypotheses use `ComputesRightDerivedAt` and `ComputesLeftDerivedAt`, whose only
  primitive data relevant here is the inherited pointwise-definedness owner at the chosen object,
  and transport along a morphism in `S` should therefore reuse the canonical owner theorems
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem` and
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem` rather than a chapter-local wrapper;
- primitive data: for each object `X`, an `S`-morphism connecting `X` to an object `X'` together
  with a proof that `X'` computes the corresponding derived functor;
- derived API: the everywhere-definedness predicates on `F`.

Source/core/bridge triage:
- `source-facing`: the Stacks existential hypotheses with objects computing the right or left
  derived functor;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`, and the owner transport equivalences
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem` and
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`;
- `bridge/view`: the two theorems in this file, which should remain thin existential-to-owner
  bridges.
-/

-- Proof sketch: for each `X`, choose `s : X ⟶ X'` in `S` with `X'` computing the right derived
-- functor. The computation hypothesis restricts to the core pointwise right-derived owner at `X'`,
-- and
-- `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem` transports this property along `s` back
-- to `X`.
/-- Lemma 13.14.14 (1): if every object admits a morphism in `S` to an object computing the
pointwise right derived functor of `F`, then the right derived functor is everywhere defined. -/
theorem hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) [S.ContainsIdentities]
    (h :
      ∀ X : 𝒟, ∃ (X' : 𝒟) (s : X ⟶ X'), S s ∧ F.ComputesRightDerivedAt S X') :
    F.HasPointwiseRightDerivedFunctor S := sorry

-- Proof sketch: for each `X`, choose `s : X' ⟶ X` in `S` with `X'` computing the left derived
-- functor. The computation hypothesis restricts to the core pointwise left-derived owner at `X'`,
-- and
-- `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem` transports this property along `s` to
-- `X`.
/-- Lemma 13.14.14 (2): if every object receives a morphism in `S` from an object computing the
pointwise left derived functor of `F`, then the left derived functor is everywhere defined. -/
theorem hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) [S.ContainsIdentities]
    (h :
      ∀ X : 𝒟, ∃ (X' : 𝒟) (s : X' ⟶ X), S s ∧ F.ComputesLeftDerivedAt S X') :
    F.HasPointwiseLeftDerivedFunctor S := sorry

end

end Functor

end CategoryTheory

/-! ### Lemma_13_14_15 (from Chap13) -/
open CategoryTheory.MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

/-
Domain-style sampling for Lemma 13.14.15:
- primary domain: pointwise existence of derived functors with respect to a localization class,
  using object-property/cofinality criteria;
- sampled owner declarations in the project:
  `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt`,
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt` /
  `Functor.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt`;
- best owner abstraction: the canonical ambient owner for the localization class is
  `S.IsSaturatedMultiplicativeSystem`, and the public targets of this file are the category-level
  owner predicates `Functor.ComputesRightDerivedAt`, `Functor.ComputesLeftDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctor`, and `Functor.HasPointwiseLeftDerivedFunctor`.
  The source-facing “subset of good objects” should therefore be represented by
  `ObjectProperty D`, the existing owner for predicates on objects.

Source/core/bridge triage:
- `source-facing`: the Stacks cofinality criteria using object properties `I` and `P`;
- `core/canonical`: `S.IsSaturatedMultiplicativeSystem` together with the derived-functor owner
  predicates `ComputesRightDerivedAt`, `ComputesLeftDerivedAt`,
  `HasPointwiseRightDerivedFunctor`, and `HasPointwiseLeftDerivedFunctor`;
- `bridge/view`: the four theorems in this file, which turn the source-facing subset hypotheses
  into those canonical owner predicates.

Primitive data:
- the functor `F`,
- the saturated multiplicative system structure on `S`,
- the source-facing reachability and isomorphism hypotheses on the chosen object properties.

Derived API:
- the localization transport lemmas on pointwise derivability,
- the pointwise and global derived-functor existence predicates for `F`.
-/

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [S.IsSaturatedMultiplicativeSystem]

section Right

variable (I : ObjectProperty D)
variable
  (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
  (hI_isIso :
    ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))

include hI_reaches hI_isIso

-- Proof sketch: for `X ∈ I`, the full subcategory of `X / S` consisting of denominators landing
-- in `I` contains the identity denominator of `X`, is cofinal in the full indexing category by
-- the same reachability argument, and all of its transition maps are sent to isomorphisms by
-- `hI_isIso`. Hence the pointwise right-derived diagram is essentially constant with value
-- `F.obj X`, so `X` computes the right derived functor directly, with no extra global
-- derivability hypothesis.
/-- Lemma 13.14.15 (2): under the same hypotheses, any object `X ∈ I` computes the right derived
functor of `F` with respect to `S`. -/
theorem computesRightDerivedAt_of_mem_subset
    {X : D} (hX : I X) :
    F.ComputesRightDerivedAt S X := sorry

-- Proof sketch: apply the canonical Chapter 13 bridge from existence of enough objects computing
-- the right derived functor. The source-facing content here is precisely that every `X` reaches
-- some `X' ∈ I`, and those `X'` compute `RF` by the previous theorem.
/-- Lemma 13.14.15 (1): if every object of `D` admits an arrow in `S` to an object of `I`, and
if `F` sends arrows of `S` between objects of `I` to isomorphisms, then the right derived
functor of `F` with respect to `S` is everywhere defined. -/
theorem hasPointwiseRightDerivedFunctor_of_subset :
    F.HasPointwiseRightDerivedFunctor S :=
  F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt S fun X ↦ by
    rcases hI_reaches X with ⟨X', s, hX', hs⟩
    exact ⟨X', s, hs,
      computesRightDerivedAt_of_mem_subset F S I hI_reaches hI_isIso hX'⟩

omit hI_reaches hI_isIso

end Right

section Left

variable (P : ObjectProperty D)
variable
  (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
  (hP_isIso :
    ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))

include hP_reaches hP_isIso

-- Proof sketch: for `X ∈ P`, the full subcategory of `S \ X` consisting of denominators with
-- source in `P` contains the identity denominator of `X`, is cofinal by `hP_reaches`, and all
-- of its transition maps are sent to isomorphisms by `hP_isIso`. Thus the pointwise left-derived
-- diagram is essentially constant with value `F.obj X`, so `X` computes the left derived
-- functor directly.
/-- Lemma 13.14.15 (4): under the dual hypotheses, any object `X ∈ P` computes the left derived
functor of `F` with respect to `S`. -/
theorem computesLeftDerivedAt_of_mem_subset
    {X : D} (hX : P X) :
    F.ComputesLeftDerivedAt S X := sorry

-- Proof sketch: this is the left-derived dual of part `(1)`, using the canonical bridge from
-- enough objects computing the left derived functor to everywhere-defined pointwise existence.
/-- Lemma 13.14.15 (3): dually, if every object of `D` receives an arrow in `S` from an object
of `P`, and if `F` sends arrows of `S` between objects of `P` to isomorphisms, then the left
derived functor of `F` with respect to `S` is everywhere defined. -/
theorem hasPointwiseLeftDerivedFunctor_of_subset :
    F.HasPointwiseLeftDerivedFunctor S :=
  F.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt S fun X ↦ by
    rcases hP_reaches X with ⟨X', s, hX', hs⟩
    exact ⟨X', s, hs,
      computesLeftDerivedAt_of_mem_subset F S P hP_reaches hP_isIso hX'⟩

omit hP_reaches hP_isIso

end Left

end

end Functor

end CategoryTheory

/-! ### Lemma_13_14_16 (from Chap13) -/
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open ComplexShape

section

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

/- Domain-style sampling for Lemma 13.14.16:
- primary domain: comparison morphisms for compositions of total left/right derived functors along
  localization functors;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `Functor.totalLeftDerived`,
  `Functor.rightDerivedDesc` / `Functor.rightDerived_fac`,
  `Functor.leftDerivedLift` / `Functor.leftDerived_fac`;
- best owner abstraction: the canonical owner is the comparison morphism itself in the
  `CategoryTheory.Functor` namespace, built from the universal property of the total derived
  functor. The localization classes are primitive owner parameters and should therefore be
  explicit in the public API instead of being hidden behind `@...` call sites.

Source/core/bridge triage:
- `source-facing`: the textbook comparison maps `R(G ∘ F) ⟶ RG ∘ RF'` and `LG ∘ LF' ⟶ L(G ∘ F)`;
- `core/canonical`: `Functor.totalRightDerived`, `Functor.totalLeftDerived`, and their universal
  morphisms `rightDerivedDesc` / `leftDerivedLift`;
- `bridge/view`: the two factorization lemmas, which expose the defining universal-property
  equations of the comparison morphisms.

Primitive data:
- the localization classes `S` on `A` and `S'` on `B`,
- the functors `F : A ⥤ B` and `G : B ⥤ C`,
- the three derived-functor existence instances needed to form the comparison.

Derived API:
- `rightDerivedCompComparison_fac`,
- `leftDerivedCompComparison_fac`.
-/

section Right

variable (S : MorphismProperty A) (S' : MorphismProperty B) (F : A ⥤ B) (G : B ⥤ C)
variable [(F ⋙ G).HasRightDerivedFunctor S]
variable [(F ⋙ S'.Q).HasRightDerivedFunctor S]
variable [G.HasRightDerivedFunctor S']

local notation "RF₁" => totalRightDerived (F ⋙ S'.Q) S.Q S
local notation "RG" => totalRightDerived G S'.Q S'
local notation "RGF" => totalRightDerived (F ⋙ G) S.Q S
local notation "α₁" => totalRightDerivedUnit (F ⋙ S'.Q) S.Q S
local notation "αG" => totalRightDerivedUnit G S'.Q S'
local notation "αGF" => totalRightDerivedUnit (F ⋙ G) S.Q S

/-- Lemma 13.14.16 (1): let `F' : A ⥤ S'⁻¹B` be the composite `F ⋙ S'.Q`. If the right derived
functors of `F'`, `G`, and `G ∘ F` are everywhere defined, then there is a canonical natural
transformation `R(G ∘ F) ⟶ RG ∘ RF'`. -/
noncomputable def rightDerivedCompComparison :
    RGF ⟶ RF₁ ⋙ RG :=
  rightDerivedDesc RGF αGF S (RF₁ ⋙ RG)
    (whiskerLeft F αG ≫
      (associator F S'.Q RG).hom ≫
      whiskerRight α₁ RG ≫
      (associator S.Q RF₁ RG).hom)

-- Proof sketch: this is the standard `rightDerived_fac` identity for the comparison morphism
-- defined via `rightDerivedDesc`.
/-- The right-derived comparison morphism factors the canonical unit of `R(G ∘ F)` through the
iterated right derived functor `RG ∘ RF'`. -/
@[reassoc]
theorem rightDerivedCompComparison_fac :
    αGF ≫ whiskerLeft S.Q (rightDerivedCompComparison S S' F G) =
      whiskerLeft F αG ≫
        (associator F S'.Q RG).hom ≫
        whiskerRight α₁ RG ≫
        (associator S.Q RF₁ RG).hom := by
  simpa [rightDerivedCompComparison] using
    (rightDerived_fac RGF αGF S (RF₁ ⋙ RG)
      (whiskerLeft F αG ≫
        (associator F S'.Q RG).hom ≫
        whiskerRight α₁ RG ≫
        (associator S.Q RF₁ RG).hom))

attribute [simp] rightDerivedCompComparison_fac rightDerivedCompComparison_fac_assoc

end Right

section Left

variable (S : MorphismProperty A) (S' : MorphismProperty B) (F : A ⥤ B) (G : B ⥤ C)
variable [(F ⋙ G).HasLeftDerivedFunctor S]
variable [(F ⋙ S'.Q).HasLeftDerivedFunctor S]
variable [G.HasLeftDerivedFunctor S']

local notation "LF₁" => totalLeftDerived (F ⋙ S'.Q) S.Q S
local notation "LG" => totalLeftDerived G S'.Q S'
local notation "LGF" => totalLeftDerived (F ⋙ G) S.Q S
local notation "β₁" => totalLeftDerivedCounit (F ⋙ S'.Q) S.Q S
local notation "βG" => totalLeftDerivedCounit G S'.Q S'
local notation "βGF" => totalLeftDerivedCounit (F ⋙ G) S.Q S

/-- Lemma 13.14.16 (2): let `F' : A ⥤ S'⁻¹B` be the composite `F ⋙ S'.Q`. If the left derived
functors of `F'`, `G`, and `G ∘ F` are everywhere defined, then there is a canonical natural
transformation `LG ∘ LF' ⟶ L(G ∘ F)`, written in Lean as
`LF' ⋙ LG ⟶ L(F ⋙ G)`. -/
noncomputable def leftDerivedCompComparison :
    LF₁ ⋙ LG ⟶ LGF :=
  leftDerivedLift LGF βGF S (LF₁ ⋙ LG)
    ((associator S.Q LF₁ LG).inv ≫
      whiskerRight β₁ LG ≫
      (associator F S'.Q LG).hom ≫
      whiskerLeft F βG)

-- Proof sketch: this is the standard `leftDerived_fac` identity for the comparison morphism
-- defined via `leftDerivedLift`.
/-- The left-derived comparison morphism factors the counit of the iterated left derived functor
through the canonical counit of `L(G ∘ F)`. -/
@[reassoc]
theorem leftDerivedCompComparison_fac :
    whiskerLeft S.Q (leftDerivedCompComparison S S' F G) ≫
      βGF =
        (associator S.Q LF₁ LG).inv ≫
          whiskerRight β₁ LG ≫
          (associator F S'.Q LG).hom ≫
          whiskerLeft F βG := by
  simpa [leftDerivedCompComparison] using
    (leftDerived_fac LGF βGF S (LF₁ ⋙ LG)
      ((associator S.Q LF₁ LG).inv ≫
        whiskerRight β₁ LG ≫
        (associator F S'.Q LG).hom ≫
        whiskerLeft F βG))

attribute [simp] leftDerivedCompComparison_fac leftDerivedCompComparison_fac_assoc

end Left

section Homotopy

variable [Preadditive A] [Preadditive B] [Preadditive C]

private theorem mapHomotopyCategoryComp_hom_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ := by
  sorry

private theorem mapHomotopyCategoryComp_inv_naturality
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    ∀ ⦃K L : HomotopyCategory A (up ℤ)⦄ (φ : K ⟶ L),
      (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)).map φ ≫
          𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj L) =
        𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K) ≫
          ((F ⋙ G).mapHomotopyCategory (up ℤ)).map φ := by
  sorry

private abbrev mapHomotopyCategoryCompHom
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (up ℤ) ⟶
      F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) :=
  NatTrans.mk
    (fun K ↦ 𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K))
    (mapHomotopyCategoryComp_hom_naturality F G)

private abbrev mapHomotopyCategoryCompInv
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) ⟶
      (F ⋙ G).mapHomotopyCategory (up ℤ) :=
  NatTrans.mk
    (fun K ↦ 𝟙 (((F ⋙ G).mapHomotopyCategory (up ℤ)).obj K))
    (mapHomotopyCategoryComp_inv_naturality F G)

private theorem mapHomotopyCategoryComp_hom_inv_id
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompHom F G ≫ mapHomotopyCategoryCompInv F G =
      𝟙 ((F ⋙ G).mapHomotopyCategory (up ℤ)) := by
  sorry

private theorem mapHomotopyCategoryComp_inv_hom_id
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapHomotopyCategoryCompInv F G ≫ mapHomotopyCategoryCompHom F G =
      𝟙 (F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ)) := by
  sorry

/-- Applying `mapHomotopyCategory` to a composite additive functor is canonically isomorphic to
composing the induced functors on homotopy categories. -/
noncomputable def mapHomotopyCategoryCompIso
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := mapHomotopyCategoryCompHom F G
  inv := mapHomotopyCategoryCompInv F G
  hom_inv_id := mapHomotopyCategoryComp_hom_inv_id F G
  inv_hom_id := mapHomotopyCategoryComp_inv_hom_id F G

/-- Applying `mapHomotopyCategory` to a natural isomorphism of additive functors yields the
corresponding isomorphism on homotopy categories. -/
noncomputable def mapHomotopyCategoryIso
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simpa using
      congrArg (fun α ↦ NatTrans.mapHomotopyCategory α (up ℤ)) (Iso.hom_inv_id e)
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp]
    simpa using
      congrArg (fun α ↦ NatTrans.mapHomotopyCategory α (up ℤ)) (Iso.inv_hom_id e)

end Homotopy

end

end Functor

end CategoryTheory
