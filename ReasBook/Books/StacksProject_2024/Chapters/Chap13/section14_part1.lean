import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_14_2 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂} [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
variable (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟)

/-
Domain-style sampling for Definition 13.14.2:
- primary domain: pointwise derived functors with respect to a localization morphism property;
- relevant owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff`;
- best owner abstraction: the pointwise derived-functor existence predicates already owned by
  mathlib, not a parallel local alias;
- primitive data: the Prop-valued owner saying the pointwise derived functor is defined at `X`;
- derived API: the upstream colimit/limit characterizations of the corresponding comma diagrams.

Source/core/bridge triage:
- `source-facing`: the source statement that the right or left derived functor is defined at `X`;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctorAt` and
  `Functor.HasPointwiseLeftDerivedFunctorAt`;
- `bridge/view`: `Functor.hasPointwiseRightDerivedFunctorAt_iff` and
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff`.
-/

/- Definition 13.14.2 (1): saying that the right derived functor of `F : 𝒟 ⥤ 𝒟'` with respect
to `S` is defined at `X` is exactly the canonical owner
`F.HasPointwiseRightDerivedFunctorAt S X`. -/
recall HasPointwiseRightDerivedFunctorAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟) : Prop

/- Definition 13.14.2 (2): saying that the left derived functor of `F : 𝒟 ⥤ 𝒟'` with respect
to `S` is defined at `X` is exactly the canonical owner
`F.HasPointwiseLeftDerivedFunctorAt S X`. -/
recall HasPointwiseLeftDerivedFunctorAt
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) (X : 𝒟) : Prop

end

end Functor

end CategoryTheory

/-! ### Lemma_13_14_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.Limits
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (S : MorphismProperty D) (F : D ⥤ D')

/- Domain-style sampling:
- primary domain: pointwise left/right derived values for a functor along a localization system,
  together with the canonical compatibility squares induced by morphisms and denominator choices;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.leftDerivedValue`;
- owner abstraction:
  `source-facing`: the local constructions `rightDerivedValue`, `leftDerivedValue`, and their
    induced maps for a fixed `S` and `F`;
  `core/canonical`: `CategoryTheory.CommSq` for any single square-shaped compatibility statement;
  `bridge/view`: the leg/projection descriptions relating the local derived-value maps to
    denominator squares in `D`.

Primitive data are the pointwise existence hypotheses and the canonical colimit/limit
presentations. The leg/projection compatibilities are derived API and should be stated through the
owner `CommSq`, not as standalone equalities of composites.
-/

private noncomputable abbrev rightDerivedDiagram (X : D) :=
  CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F

private noncomputable abbrev leftDerivedDiagram (X : D) :=
  StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F

/-- The pointwise right-derived value of `F` at `X`, computed as the colimit over the
costructured-arrow category of `S.Q` above `X`. -/
noncomputable abbrev rightDerivedValue (X : D)
    [F.HasPointwiseRightDerivedFunctorAt S X] : D' :=
  let _ : HasColimit (rightDerivedDiagram S F X) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  colimit (rightDerivedDiagram S F X)

/-- The canonical map from `F.obj X'` to the right-derived value at `X` associated to a
denominator `s : X ⟶ X'` in `S`. -/
noncomputable abbrev rightDerivedValueLeg {X X' : D} (s : X ⟶ X') (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X] : F.obj X' ⟶ rightDerivedValue S F X :=
  let _ : HasColimit (rightDerivedDiagram S F X) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  colimit.ι (rightDerivedDiagram S F X)
    (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))

/-- Lemma 13.14.3 (1): if the pointwise right-derived values of `F` are defined at `X` and `Y`,
then a morphism `f : X ⟶ Y` induces the canonical map `RF(f) : RF(X) ⟶ RF(Y)`. -/
noncomputable def rightDerivedValueMap {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y] :
    rightDerivedValue S F X ⟶ rightDerivedValue S F Y :=
  let _ : HasColimit (rightDerivedDiagram S F X) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let _ : HasColimit (rightDerivedDiagram S F Y) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y
  colimit.desc (rightDerivedDiagram S F X)
    (Cocone.mk (rightDerivedValue S F Y)
      { app := fun g ↦ colimit.ι (rightDerivedDiagram S F Y)
          ((CostructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa using colimit.w (rightDerivedDiagram S F Y)
            ((CostructuredArrow.map (S.Q.map f)).map φ) })

-- Proof sketch: rewrite the image of the denominator leg indexed by `s` under the defining
-- colimit descent as the leg indexed by the localized arrow `Q(s)⁻¹ ≫ Q(f)`. The commutative
-- square identifies this arrow with `Q(f') ≫ Q(s')⁻¹`, and the induced morphism in the
-- costructured-arrow category yields the required commuting square of colimit legs.
/-- The canonical map on right-derived values satisfies the commutative-square compatibility from
the textbook statement. -/
theorem rightDerivedValueMap_comp_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    {X' Y' : D} (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq f s s' f') :
    CommSq
      (rightDerivedValueLeg S F s hs)
      (F.map f')
      (rightDerivedValueMap S F f)
      (rightDerivedValueLeg S F s' hs') := sorry

-- Proof sketch: use the right calculus of fractions to represent any object of the indexing
-- category for `RF(X)` by a denominator `s : X ⟶ X'` in `S`; the assumed compatibility then
-- determines the image of each colimit leg. The colimit universal property gives existence and
-- uniqueness, and the Ore equalization axiom makes the result independent of the chosen square.
/-- Any morphism with the textbook compatibility on all denominator squares is the canonical map
between the right-derived values. -/
theorem rightDerivedValueMap_hom_ext {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y]
    [S.HasRightCalculusOfFractions]
    {φ : rightDerivedValue S F X ⟶ rightDerivedValue S F Y}
    (hφ : ∀ ⦃X' Y' : D⦄ (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq f s s' f'),
          CommSq
            (rightDerivedValueLeg S F s hs)
            (F.map f')
            φ
            (rightDerivedValueLeg S F s' hs')) :
    φ = rightDerivedValueMap S F f := sorry

/-- The pointwise left-derived value of `F` at `X`, computed as the limit over the
structured-arrow category of `S.Q` under `X`. -/
noncomputable abbrev leftDerivedValue (X : D)
    [F.HasPointwiseLeftDerivedFunctorAt S X] : D' :=
  let _ : HasLimit (leftDerivedDiagram S F X) :=
    HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  limit (leftDerivedDiagram S F X)

/-- The canonical projection from the left-derived value at `X` to `F.obj X'` associated to a
denominator `s : X' ⟶ X` in `S`. -/
noncomputable abbrev leftDerivedValueProjection {X X' : D} (s : X' ⟶ X) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S X] : leftDerivedValue S F X ⟶ F.obj X' :=
  let _ : HasLimit (leftDerivedDiagram S F X) :=
    HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  limit.π (leftDerivedDiagram S F X)
    (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))

/-- Lemma 13.14.3 (2): if the pointwise left-derived values of `F` are defined at `X` and `Y`,
then a morphism `f : X ⟶ Y` induces the canonical map `LF(f) : LF(X) ⟶ LF(Y)`. -/
noncomputable def leftDerivedValueMap {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    leftDerivedValue S F X ⟶ leftDerivedValue S F Y :=
  let _ : HasLimit (leftDerivedDiagram S F X) :=
    HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let _ : HasLimit (leftDerivedDiagram S F Y) :=
    HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  limit.lift (leftDerivedDiagram S F Y)
    (Cone.mk (leftDerivedValue S F X)
      { app := fun g ↦ limit.π (leftDerivedDiagram S F X)
          ((StructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa using (limit.w (leftDerivedDiagram S F X)
            ((StructuredArrow.map (S.Q.map f)).map φ)).symm })

-- Proof sketch: evaluate the defining limit lift on the denominator projection indexed by `s'`.
-- The commutative square identifies the structured-arrow object obtained from `s'` by
-- precomposition with `f` with the object coming from `s` followed by `f'`, and the induced
-- morphism in the structured-arrow category gives the desired commuting square of limit
-- projections.
/-- The canonical map on left-derived values satisfies the commutative-square compatibility from
the textbook statement. -/
theorem leftDerivedValueMap_comp_of_square {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    {X' Y' : D} (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq s f' f s') :
    CommSq
      (leftDerivedValueMap S F f)
      (leftDerivedValueProjection S F s hs)
      (leftDerivedValueProjection S F s' hs')
      (F.map f') := sorry

-- Proof sketch: use the left calculus of fractions to represent any object of the indexing
-- category for `LF(Y)` by a denominator `s' : Y' ⟶ Y` in `S`; the assumed compatibility then
-- determines the composite with each limit projection. The limit universal property gives the
-- unique morphism realizing these projections, and the Ore equalization axiom ensures
-- independence of the chosen square.
/-- Any morphism with the textbook compatibility on all denominator squares is the canonical map
between the left-derived values. -/
theorem leftDerivedValueMap_hom_ext {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [S.HasLeftCalculusOfFractions]
    {φ : leftDerivedValue S F X ⟶ leftDerivedValue S F Y}
    (hφ : ∀ ⦃X' Y' : D⦄ (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq s f' f s'),
          CommSq
            φ
            (leftDerivedValueProjection S F s hs)
            (leftDerivedValueProjection S F s' hs')
            (F.map f')) :
    φ = leftDerivedValueMap S F f := sorry

end

end CategoryTheory

/-! ### Lemma_13_14_4 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (S : MorphismProperty 𝒟) (F : 𝒟 ⥤ 𝒟')

/- Domain-style sampling for Lemma 13.14.4:
- primary domain: transport of pointwise left/right derived-definedness along morphisms in the
  localization class, together with the resulting isomorphism statements on the total derived
  functors;
- sampled owner declarations:
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `MorphismProperty.Q_inverts`,
  `MorphismProperty.IsInvertedBy.of_comp`,
  `Functor.totalRightDerived`,
  `Functor.totalLeftDerived`;
- best owner abstraction: the primitive owner data are the pointwise-definedness predicates
  `Functor.HasPointwiseRightDerivedFunctorAt` and `Functor.HasPointwiseLeftDerivedFunctorAt`, so
  the exact transport clauses should be direct recalls of the corresponding owner theorems; for
  the induced-isomorphism clauses, the owner-level abstraction is that the composite functors
  `S.Q ⋙ F.totalRightDerived S.Q S` and `S.Q ⋙ F.totalLeftDerived S.Q S` invert `S`, and the
  pointwise isomorphism statements should be thin companions derived from that owner fact;
- primitive data: a morphism `s` in `S` and the pointwise/global derived-functor existence
  owners;
- derived API: the owner-level inversion predicates for the composite total derived functors and
  the resulting isomorphism statements for the induced maps.

Source/core/bridge triage:
- `source-facing`: the four textbook clauses of Lemma 13.14.4;
- `core/canonical`: `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`, and the owner predicate
  `MorphismProperty.IsInvertedBy`;
- `bridge/view`: the two `Functor.total...Derived_map_isIso_of_mem` theorems below, which
  unpack the owner-level inversion statement into the source-facing pointwise isomorphism form.
-/

-- Proof sketch: this is exactly the invariance of pointwise right derived functors under
-- isomorphism in the localization, applied to the canonical isomorphism `Localization.isoOfHom`
-- attached to a morphism `s ∈ S`.
/- Lemma 13.14.4 (1): for a morphism `s : X ⟶ Y` in `S`, the right derived functor of `F`
is defined at `X` if and only if it is defined at `Y`. This is exactly the canonical owner
theorem for transport along a denominator. -/
recall hasPointwiseRightDerivedFunctorAt_iff_of_mem
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) {X Y : 𝒟} (s : X ⟶ Y) (hs : S s) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      F.HasPointwiseRightDerivedFunctorAt S Y

-- Proof sketch: a globally pointwise-defined right derived functor is a functor on the
-- localization `S.Localization`; since `S.Q.map s` is an isomorphism there, its image under the
-- total right derived functor is again an isomorphism.
/-- The composite `S.Q ⋙ RF` inverts every morphism of `S`. -/
theorem totalRightDerived_isInvertedBy [F.HasPointwiseRightDerivedFunctor S] :
    S.IsInvertedBy (S.Q ⋙ F.totalRightDerived S.Q S) :=
  MorphismProperty.IsInvertedBy.of_comp S S.Q S.Q_inverts (F.totalRightDerived S.Q S)

/-- Lemma 13.14.4 (2): if the right derived functor of `F` with respect to `S` is everywhere
defined, then the induced map on the values at `X` and `Y` coming from `s` is an isomorphism. -/
theorem totalRightDerived_map_isIso_of_mem {X Y : 𝒟} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseRightDerivedFunctor S] :
    IsIso ((F.totalRightDerived S.Q S).map (S.Q.map s)) := by
  simpa using totalRightDerived_isInvertedBy S F s hs

-- Proof sketch: this is the left-derived dual of the first clause, using the corresponding
-- invariance of pointwise left derived functors under isomorphism in the localization.
/- Lemma 13.14.4 (3): for a morphism `s : X ⟶ Y` in `S`, the left derived functor of `F`
is defined at `X` if and only if it is defined at `Y`. This is exactly the canonical owner
theorem for transport along a denominator. -/
recall hasPointwiseLeftDerivedFunctorAt_iff_of_mem
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) {X Y : 𝒟} (s : X ⟶ Y) (hs : S s) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      F.HasPointwiseLeftDerivedFunctorAt S Y

-- Proof sketch: a globally pointwise-defined left derived functor is a functor on the
-- localization `S.Localization`; the morphism `S.Q.map s` is an isomorphism, so its image under
-- the total left derived functor is an isomorphism as well.
/-- The composite `S.Q ⋙ LF` inverts every morphism of `S`. -/
theorem totalLeftDerived_isInvertedBy [F.HasPointwiseLeftDerivedFunctor S] :
    S.IsInvertedBy (S.Q ⋙ F.totalLeftDerived S.Q S) :=
  MorphismProperty.IsInvertedBy.of_comp S S.Q S.Q_inverts (F.totalLeftDerived S.Q S)

/-- Lemma 13.14.4 (4): if the left derived functor of `F` with respect to `S` is everywhere
defined, then the induced map on the values at `X` and `Y` coming from `s` is an isomorphism. -/
theorem totalLeftDerived_map_isIso_of_mem {X Y : 𝒟} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctor S] :
    IsIso ((F.totalLeftDerived S.Q S).map (S.Q.map s)) := by
  simpa using totalLeftDerived_isInvertedBy S F s hs

end

end Functor

end CategoryTheory

/-! ### Lemma_13_14_5 (from Chap13) -/
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The object property on `𝒟` consisting of those objects at which the pointwise right derived
functor of `F` with respect to `S` is defined. -/
abbrev rightDerivedDefinedObjectProperty : ObjectProperty 𝒟 :=
  fun X ↦ F.HasPointwiseRightDerivedFunctorAt S X

/-- The object property on `𝒟` consisting of those objects at which the pointwise left derived
functor of `F` with respect to `S` is defined. -/
abbrev leftDerivedDefinedObjectProperty : ObjectProperty 𝒟 :=
  fun X ↦ F.HasPointwiseLeftDerivedFunctorAt S X

end

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/- Domain-style sampling for Lemma 13.14.5:
- primary domain: pointwise left/right derived functors on a localization, together with shift
  compatibility;
- inspected owner declarations:
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.IsPointwiseLeftKanExtensionAt.isoColimit`,
  `Functor.IsPointwiseRightKanExtensionAt.isoLimit`;
- best owner abstraction: the source-facing pointwise derived values are already owned in this
  chapter by `rightDerivedValue`, `leftDerivedValue`, and the owner object properties
  `rightDerivedDefinedObjectProperty` / `leftDerivedDefinedObjectProperty`, built on top of the
  core/canonical mathlib predicates `Functor.HasPointwiseRightDerivedFunctorAt` and
  `Functor.HasPointwiseLeftDerivedFunctorAt`; the reusable closure API for those predicates should
  live at the owner level `ObjectProperty.IsClosedUnderIsomorphisms` and
  `ObjectProperty.IsStableUnderShift`;
- primitive data: the pointwise derived-definedness predicates at a fixed object;
- derived API: the owner-level closure instances, the shift-invariance equivalences for those
  predicates, and the canonical shift comparison isomorphisms for the pointwise derived values.

Source/core/bridge triage:
- `source-facing`: the four shift-compatibility statements in Lemma 13.14.5;
- `core/canonical`: `ObjectProperty.IsClosedUnderIsomorphisms`,
  `ObjectProperty.IsStableUnderShift`, `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`, `rightDerivedValue`, and `leftDerivedValue`;
- `bridge/view`: the direct typeclass transport instances from `X` to `X⟦n⟧`, derived from the
  owner-level object-property API. -/

/-- The predicate `X ↦ F.HasPointwiseRightDerivedFunctorAt S X` is invariant under isomorphism of
objects. -/
instance rightDerivedDefinedObjectProperty_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (rightDerivedDefinedObjectProperty F S) := by
  sorry

/-- The predicate `X ↦ F.HasPointwiseLeftDerivedFunctorAt S X` is invariant under isomorphism of
objects. -/
instance leftDerivedDefinedObjectProperty_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (leftDerivedDefinedObjectProperty F S) := by
  sorry

end

section RightShift

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The predicate `X ↦ F.HasPointwiseRightDerivedFunctorAt S X` is stable under shifts. -/
instance rightDerivedDefinedObjectProperty_isStableUnderShift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (rightDerivedDefinedObjectProperty F S) ℤ := by
  sorry

end RightShift

section RightShiftAPI

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: the localization functor `S.Q` commutes with shifts under
-- the shift-compatibility hypotheses from Situation 13.14.1. Packaging this as an
-- `ObjectProperty.IsStableUnderShift` instance gives the source-facing `↔` statement immediately.
/-- Lemma 13.14.5 (1): the right derived functor of `F` is defined at `X` if and only if it is
defined at the shifted object `X⟦n⟧`. -/
theorem hasPointwiseRightDerivedFunctorAt_iff_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := by
  simpa using
    ((rightDerivedDefinedObjectProperty F S).prop_shift_iff_of_isStableUnderShift X n).symm

instance pointwiseRightDerivedFunctorAt_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := by
  exact (hasPointwiseRightDerivedFunctorAt_iff_shift F S X n).mp inferInstance

end RightShiftAPI

section RightShiftIso

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: clause (1) already recovers the shifted pointwise right-derived value from the
-- single source-facing assumption at `X`; the shift-compatibility hypotheses then canonically
-- identify the diagrams computing `RF(X⟦n⟧)` and `RF(X)⟦n⟧`, and `isoColimit` packages the
-- resulting universal-property uniqueness as the comparison isomorphism.
/-- Lemma 13.14.5 (2): when the right derived functor of `F` is defined at `X`, the derived
value at `X⟦n⟧` is canonically isomorphic to the shift `RF(X)⟦n⟧`. -/
noncomputable def rightDerivedValueShiftIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    rightDerivedValue S F (X⟦n⟧) ≅ ((rightDerivedValue S F X)⟦n⟧) := by
  sorry

end RightShiftIso

section LeftShift

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The predicate `X ↦ F.HasPointwiseLeftDerivedFunctorAt S X` is stable under shifts. -/
instance leftDerivedDefinedObjectProperty_isStableUnderShift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (leftDerivedDefinedObjectProperty F S) ℤ := by
  sorry

end LeftShift

section LeftShiftAPI

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: this is the dual of the right-derived statement, again exposed first through the
-- owner-level shift-stability API on the underlying object property.
/-- Lemma 13.14.5 (3): the left derived functor of `F` is defined at `X` if and only if it is
defined at the shifted object `X⟦n⟧`. -/
theorem hasPointwiseLeftDerivedFunctorAt_iff_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := by
  simpa using
    ((leftDerivedDefinedObjectProperty F S).prop_shift_iff_of_isStableUnderShift X n).symm

instance pointwiseLeftDerivedFunctorAt_shift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := by
  exact (hasPointwiseLeftDerivedFunctorAt_iff_shift F S X n).mp inferInstance

end LeftShiftAPI

section LeftShiftIso

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: clause (3) supplies the shifted pointwise left-derived value from the single
-- source-facing assumption at `X`, and the localization-shift compatibility then identifies the
-- diagrams computing `LF(X⟦n⟧)` and `LF(X)⟦n⟧`, with `isoLimit` providing the canonical
-- uniqueness isomorphism.
/-- Lemma 13.14.5 (4): when the left derived functor of `F` is defined at `X`, the derived
value at `X⟦n⟧` is canonically isomorphic to the shift `LF(X)⟦n⟧`. -/
noncomputable def leftDerivedValueShiftIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    leftDerivedValue S F (X⟦n⟧) ≅ ((leftDerivedValue S F X)⟦n⟧) := by
  sorry

end LeftShiftIso

end CategoryTheory

/-! ### Lemma_13_14_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section RightTwoOutOfThree

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D'] (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

/- Domain-style sampling:
- primary domain: pointwise left/right derived functors in a triangulated localization situation;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.IsTriangulated`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `ObjectProperty.IsTriangulatedClosed₁`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `ObjectProperty.IsTriangulatedClosed₃`,
  `rightDerivedValueMap`,
  `leftDerivedValueMap`,
  `rightDerivedValueShiftIso`,
  `leftDerivedValueShiftIso`;
- best owner abstraction: the pointwise-definedness predicates should be treated as
  `ObjectProperty` owners on `D`, namely `rightDerivedDefinedObjectProperty F S` and
  `leftDerivedDefinedObjectProperty F S`; their distinguished-triangle closure belongs first in
  the canonical owner interfaces `IsTriangulatedClosed₁/₂/₃`, while the induced morphisms and
  shift comparison isomorphisms already belong to `Lemma_13_14_3` and `Lemma_13_14_5`.

Primitive data are a distinguished triangle in `D` and pointwise-definedness on two of its
vertices. The maps on derived values and the shift comparison are derived/canonical upstream API,
so they should be reused from their owner files rather than repeated here as parallel local
declarations.
-/

-- Proof sketch: choose the missing derived value by completing the image of the distinguished
-- triangle under `F` to a distinguished triangle in `D'`, then use the exactness of filtered
-- colimits on Hom groups together with the five lemma to show the third vertex computes the
-- remaining pointwise right-derived value.
/-- The pointwise right-derived-definedness property is closed under the third vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₃ :
    IsTriangulatedClosed₃ (rightDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle once, apply the previous clause to the rotated
-- triangle, and use Lemma `13.14.5` to move pointwise right-derived definedness from `X⟦1⟧`
-- back to `X`.
/-- The pointwise right-derived-definedness property is closed under the first vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₁ :
    IsTriangulatedClosed₁ (rightDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle twice and apply the main two-out-of-three
-- clause together with Lemma `13.14.5`.
/-- The pointwise right-derived-definedness property is closed under the middle vertex of a
distinguished triangle. -/
instance hasPointwiseRightDerivedFunctorAt_isTriangulatedClosed₂ :
    IsTriangulatedClosed₂ (rightDerivedDefinedObjectProperty F S) := by
  sorry

end RightTwoOutOfThree

section RightDistinguished

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

variable {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}

-- Proof sketch: after the two-out-of-three existence statement, the pointwise right-derived
-- values and their induced maps are defined on the whole triangle. The exactness of `F` and the
-- universal-property construction of the pointwise derived values show that the canonical shift
-- comparison from Lemma `13.14.5` makes the induced triangle distinguished.
/-- Lemma 13.14.6 (2): once the pointwise right derived values on a distinguished triangle are
defined, the induced triangle on right-derived values is distinguished in `D'`. -/
theorem right_derived_triangle_distinguished
    (hT : Triangle.mk f g h ∈ distTriang D)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S Z] :
    Triangle.mk (rightDerivedValueMap S F f) (rightDerivedValueMap S F g)
      (rightDerivedValueMap S F h ≫ (rightDerivedValueShiftIso F S X (1 : ℤ)).hom) ∈
        distTriang D' := sorry

end RightDistinguished

section LeftTwoOutOfThree

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D'] (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

-- Proof sketch: this is the dual two-out-of-three argument for pointwise left derived functors,
-- replacing filtered colimits by filtered limits and using the exactness criterion on Hom groups
-- against the completed distinguished triangle in `D'`.
/-- The pointwise left-derived-definedness property is closed under the third vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₃ :
    IsTriangulatedClosed₃ (leftDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle once, apply the preceding left-derived clause
-- to the rotated triangle, and use Lemma `13.14.5` to move pointwise left-derived definedness
-- from `X⟦1⟧` back to `X`.
/-- The pointwise left-derived-definedness property is closed under the first vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₁ :
    IsTriangulatedClosed₁ (leftDerivedDefinedObjectProperty F S) := by
  sorry

-- Proof sketch: rotate the distinguished triangle twice and apply the main left-derived
-- two-out-of-three clause together with Lemma `13.14.5`.
/-- The pointwise left-derived-definedness property is closed under the middle vertex of a
distinguished triangle. -/
instance hasPointwiseLeftDerivedFunctorAt_isTriangulatedClosed₂ :
    IsTriangulatedClosed₂ (leftDerivedDefinedObjectProperty F S) := by
  sorry

end LeftTwoOutOfThree

section LeftDistinguished

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [IsTriangulated D']
  (F : D ⥤ D') (S : MorphismProperty D)
  [F.CommShift ℤ] [F.IsTriangulated]
  [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]

variable {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}

-- Proof sketch: after the left-derived values are defined on the three objects, exactness of the
-- triangulated functor together with the pointwise left-Kan-extension construction shows that
-- the canonical shift comparison from Lemma `13.14.5` turns the induced sextuple into a
-- distinguished triangle.
/-- Lemma 13.14.6 (4): once the pointwise left derived values on a distinguished triangle are
defined, the induced triangle on left-derived values is distinguished in `D'`. -/
theorem left_derived_triangle_distinguished
    (hT : Triangle.mk f g h ∈ distTriang D)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S Z] :
    Triangle.mk (leftDerivedValueMap S F f) (leftDerivedValueMap S F g)
      (leftDerivedValueMap S F h ≫ (leftDerivedValueShiftIso F S X (1 : ℤ)).hom) ∈
        distTriang D' := sorry

end LeftDistinguished

end CategoryTheory

/-! ### Lemma_13_14_7 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section BiproductTriangles

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D']
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
  (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
  {X Y : D}

/- Domain-style sampling:
- primary domain: pointwise left/right derived functors in a localization situation,
  specialized to the split distinguished triangle attached to a binary biproduct and to the
  direct-summand consequences in a Karoubian target;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `rightDerivedDefinedObjectProperty`,
  `leftDerivedDefinedObjectProperty`,
  `right_derived_defined_at_all_three_of_two_of_three`,
  `left_derived_defined_at_all_three_of_two_of_three`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`,
  `CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- best owner abstraction: the primitive owners are the pointwise-definedness object properties
  `rightDerivedDefinedObjectProperty F S` and `leftDerivedDefinedObjectProperty F S`; the
  biproduct-closure clauses come from the canonical split triangle owner
  `binaryBiproductTriangle_distinguished`, while the Karoubian summand clauses are source-facing
  consequences of retract-stability plus the generic direct-summand API `of_biprod_left/right`.

Primitive data are the pointwise-definedness hypotheses at `X`, `Y`, and `X ⊞ Y`. The biproduct
closure statements, retract-stability owners, and canonical biproduct comparison morphisms are
derived API.

Source/core/bridge triage:
- `source-facing`: the eight biproduct clauses of Lemma `13.14.7`;
- `core/canonical`: the pointwise derived-definedness owners together with
  `binaryBiproductTriangle_distinguished` and `ObjectProperty.IsStableUnderRetracts`;
- `bridge/view`: the concluding `IsIso` statements for the canonical biproduct comparison maps,
  and the direct-summand clauses obtained from the owner API via the split-triangle criterion
  from Lemma `13.4.11`.
-/

-- Proof sketch: apply the two-out-of-three existence statement from Lemma `13.14.6` to the
-- distinguished split triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧` given by the binary biproduct triangle.
omit [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [IsTriangulated D']
  [F.CommShift ℤ] [F.IsTriangulated] [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation] in
/-- Lemma 13.14.7 (1): if the pointwise right derived functor of `F` is defined at `X` and `Y`,
then it is defined at `X ⊞ Y`. -/
theorem right_derived_defined_at_biprod
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    F.HasPointwiseRightDerivedFunctorAt S (X ⊞ Y) := by
  simpa using
    (rightDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₂
      (binaryBiproductTriangle X Y)
      (binaryBiproductTriangle_distinguished X Y)
      (inferInstance : rightDerivedDefinedObjectProperty F S X)
      (inferInstance : rightDerivedDefinedObjectProperty F S Y)

-- Proof sketch: apply the left-derived two-out-of-three statement from Lemma `13.14.6` to the
-- distinguished split triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧`.
omit [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D'] [IsTriangulated D']
  [F.CommShift ℤ] [F.IsTriangulated] [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation] in
/-- Lemma 13.14.7 (5): if the pointwise left derived functor of `F` is defined at `X` and `Y`,
then it is defined at `X ⊞ Y`. -/
theorem left_derived_defined_at_biprod
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    F.HasPointwiseLeftDerivedFunctorAt S (X ⊞ Y) := by
  simpa using
    (leftDerivedDefinedObjectProperty F S).ext_of_isTriangulatedClosed₂
      (binaryBiproductTriangle X Y)
      (binaryBiproductTriangle_distinguished X Y)
      (inferInstance : leftDerivedDefinedObjectProperty F S X)
      (inferInstance : leftDerivedDefinedObjectProperty F S Y)

-- Proof sketch: use the distinguished triangle on right-derived values produced from the split
-- triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧`; the second morphism has right inverse `RF(biprod.inr)`, so
-- Lemma `13.4.11` identifies the canonical map from
-- `RF(X) ⊞ RF(Y)` to `RF(X ⊞ Y)` as an isomorphism.
/-- Lemma 13.14.7 (4): whenever the pointwise right derived functor of `F` is defined at `X`,
`Y`, and `X ⊞ Y`, the canonical map `RF(X) ⊞ RF(Y) ⟶ RF(X ⊞ Y)` is an isomorphism. -/
theorem right_derived_biprod_desc_isIso
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S (X ⊞ Y)] :
    IsIso
      (biprod.desc
        (rightDerivedValueMap S F (biprod.inl : X ⟶ X ⊞ Y))
        (rightDerivedValueMap S F (biprod.inr : Y ⟶ X ⊞ Y))) := sorry

-- Proof sketch: use the distinguished triangle on left-derived values produced from the split
-- triangle `X ⟶ X ⊞ Y ⟶ Y ⟶ X⟦1⟧`; the second morphism has right inverse `LF(biprod.inr)`, so
-- Lemma `13.4.11` shows that the canonical map `LF(X) ⊞ LF(Y) ⟶ LF(X ⊞ Y)` is an isomorphism.
/-- Lemma 13.14.7 (8): whenever the pointwise left derived functor of `F` is defined at `X`,
`Y`, and `X ⊞ Y`, the canonical map `LF(X) ⊞ LF(Y) ⟶ LF(X ⊞ Y)` is an isomorphism. -/
theorem left_derived_biprod_desc_isIso
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [F.HasPointwiseLeftDerivedFunctorAt S (X ⊞ Y)] :
    IsIso
      (biprod.desc
        (leftDerivedValueMap S F (biprod.inl : X ⟶ X ⊞ Y))
        (leftDerivedValueMap S F (biprod.inr : Y ⟶ X ⊞ Y))) := sorry

end BiproductTriangles

section Retracts

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

-- Proof sketch: in an idempotent-complete target, retracts of pointwise colimit diagrams still
-- admit colimits, so the right-derived-definedness property descends along retracts. This is the
-- owner statement behind the Karoubian direct-summand clauses below.
/-- If `D'` is Karoubian, then the pointwise right-derived-definedness property is stable under
retracts. -/
instance rightDerivedDefinedObjectProperty_isStableUnderRetracts [IsIdempotentComplete D'] :
    (rightDerivedDefinedObjectProperty F S).IsStableUnderRetracts := by
  sorry

-- Proof sketch: dually, idempotent completeness lets one split the pointwise limit diagram
-- computing the left-derived value along retracts, so left-derived-definedness also descends
-- along retracts.
/-- If `D'` is Karoubian, then the pointwise left-derived-definedness property is stable under
retracts. -/
instance leftDerivedDefinedObjectProperty_isStableUnderRetracts [IsIdempotentComplete D'] :
    (leftDerivedDefinedObjectProperty F S).IsStableUnderRetracts := by
  sorry

end Retracts

section BiproductSummands

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroMorphisms D]
  (F : D ⥤ D') (S : MorphismProperty D)
  {X Y : D}
  [IsIdempotentComplete D'] [HasBinaryBiproduct X Y]

-- Proof sketch: this is the left direct-summand consequence of the retract-stability owner
-- `rightDerivedDefinedObjectProperty_isStableUnderRetracts`, via the generic biproduct API
-- `ObjectProperty.IsStableUnderRetracts.of_biprod_left`.
/-- Lemma 13.14.7 (2): if `D'` is Karoubian and the pointwise right derived functor of `F` is
defined at `X ⊞ Y`, then it is defined at `X`. -/
theorem right_derived_defined_at_left_of_biprod
    [F.HasPointwiseRightDerivedFunctorAt S (X ⊞ Y)] :
    F.HasPointwiseRightDerivedFunctorAt S X :=
  of_biprod_left (rightDerivedDefinedObjectProperty F S)
    (inferInstance : rightDerivedDefinedObjectProperty F S (X ⊞ Y))

-- Proof sketch: this is the right direct-summand consequence of the same retract-stability
-- owner.
/-- Lemma 13.14.7 (3): if `D'` is Karoubian and the pointwise right derived functor of `F` is
defined at `X ⊞ Y`, then it is defined at `Y`. -/
theorem right_derived_defined_at_right_of_biprod
    [F.HasPointwiseRightDerivedFunctorAt S (X ⊞ Y)] :
    F.HasPointwiseRightDerivedFunctorAt S Y :=
  of_biprod_right (rightDerivedDefinedObjectProperty F S)
    (inferInstance : rightDerivedDefinedObjectProperty F S (X ⊞ Y))

-- Proof sketch: this is the left direct-summand consequence of
-- `leftDerivedDefinedObjectProperty_isStableUnderRetracts`.
/-- Lemma 13.14.7 (6): if `D'` is Karoubian and the pointwise left derived functor of `F` is
defined at `X ⊞ Y`, then it is defined at `X`. -/
theorem left_derived_defined_at_left_of_biprod
    [F.HasPointwiseLeftDerivedFunctorAt S (X ⊞ Y)] :
    F.HasPointwiseLeftDerivedFunctorAt S X :=
  of_biprod_left (leftDerivedDefinedObjectProperty F S)
    (inferInstance : leftDerivedDefinedObjectProperty F S (X ⊞ Y))

-- Proof sketch: this is the right direct-summand consequence of the left-derived retract-stability
-- owner.
/-- Lemma 13.14.7 (7): if `D'` is Karoubian and the pointwise left derived functor of `F` is
defined at `X ⊞ Y`, then it is defined at `Y`. -/
theorem left_derived_defined_at_right_of_biprod
    [F.HasPointwiseLeftDerivedFunctorAt S (X ⊞ Y)] :
    F.HasPointwiseLeftDerivedFunctorAt S Y :=
  of_biprod_right (leftDerivedDefinedObjectProperty F S)
    (inferInstance : leftDerivedDefinedObjectProperty F S (X ⊞ Y))

end BiproductSummands

end CategoryTheory

/-! ### Proposition_13_14_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- 
Domain-style sampling:
- primary domain: pointwise right-derived functors on a localization, restricted to the full
  subcategory where the pointwise construction is defined, together with its left-derived dual;
- relevant owner declarations reused here:
  `ObjectProperty.FullSubcategory`,
  `fullSubcategoryLocalizationSystem`,
  `fullSubcategoryLocalizationFunctor`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `rightDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `leftDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `rightDerivedValueMap`,
  `leftDerivedValueMap`.

Source/core/bridge triage:
- `source-facing`: the full subcategory `𝓔` and the restricted multiplicative system `S_𝓔`;
- `core/canonical`: the upstream object-property owners `rightDerivedDefinedObjectProperty` and
  `leftDerivedDefinedObjectProperty` from `Lemma_13_14_5`, the transport owners
  `Functor.hasPointwise...DerivedFunctorAt_iff_of_mem`, the Karoubian retract-stability owners
  from `Lemma_13_14_7`, together with the chapter owner `fullSubcategoryLocalizationSystem`;
- `bridge/view`: the restricted functors and localizations obtained from `𝓔` and `S_𝓔`.

Primitive data are the object property saying where the pointwise right-derived functor is
defined, and its left-derived analogue. The subcategories and restricted localization systems are
derived owners built from those primitive predicates and reused throughout the proposition.
-/

section Basic

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- The full subcategory `𝓔 ⊆ D` consisting of objects at which the pointwise right derived
functor of `F` with respect to `S` is defined. -/
abbrev rightDerivedDefinedSubcategory (F : D ⥤ D') (S : MorphismProperty D) :=
  (rightDerivedDefinedObjectProperty F S).FullSubcategory

/-- The restricted multiplicative system `S_𝓔` on the full subcategory `𝓔`. -/
abbrev rightDerivedDefinedLocalizationSystem (F : D ⥤ D') (S : MorphismProperty D) :
    MorphismProperty (rightDerivedDefinedSubcategory F S) :=
  fullSubcategoryLocalizationSystem (rightDerivedDefinedObjectProperty F S) S

notation "𝓔[" F ", " S "]" => rightDerivedDefinedSubcategory F S
notation "S_𝓔[" F ", " S "]" => rightDerivedDefinedLocalizationSystem F S

/- Proposition 13.14.8 companion recall: for a denominator `s : X ⟶ Y` in `S`, the source and
target belong to `𝓔[F, S]` simultaneously. This is exactly the source-facing clause that any
`s ∈ S` whose source or target lies in `𝓔` is already a morphism of `𝓔`. -/
recall Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem

/-- An object of the full subcategory `𝓔` canonically carries the hypothesis that `RF` is
pointwise defined there. -/
instance rightDerivedDefinedSubcategory_hasPointwiseRightDerivedFunctorAt
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔[F, S]) :
    F.HasPointwiseRightDerivedFunctorAt S X.obj :=
  X.property

/-- The functor `RF : 𝓔 ⥤ D'` obtained by restricting the pointwise right derived construction to
the full subcategory where it is defined. -/
noncomputable def rightDerivedDefinedFunctor (F : D ⥤ D') (S : MorphismProperty D) :
    𝓔[F, S] ⥤ D' where
  obj X :=
    rightDerivedValue S F X.obj
  map f :=
    rightDerivedValueMap S F f.hom
  map_id X :=
    by
      sorry
  map_comp f g :=
    by
      sorry

-- Proof sketch: if a morphism of `S_𝓔` lies over an ambient arrow `s ∈ S`, then the two objects
-- of `𝓔` remain in the right-derived domain and Lemma `13.14.4` identifies the induced map on
-- pointwise right-derived values as an isomorphism.
/-- Every denominator in the restricted multiplicative system `S_𝓔` is sent to an isomorphism by
the restricted functor `RF : 𝓔 ⥤ D'`. -/
theorem rightDerivedDefinedFunctor_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔[F, S]).IsInvertedBy (rightDerivedDefinedFunctor F S) := sorry

/-- The localized right-derived functor `RF : S_𝓔^{-1}𝓔 ⥤ D'` induced by the restricted functor
`RF : 𝓔 ⥤ D'`. -/
noncomputable abbrev rightDerivedLocalizationFactorization
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔[F, S]).Localization ⥤ D' :=
  Localization.lift (rightDerivedDefinedFunctor F S)
    (rightDerivedDefinedFunctor_isInvertedBy F S) (S_𝓔[F, S]).Q

/-- The full subcategory `𝓔ₗ ⊆ D` consisting of objects at which the pointwise left derived
functor of `F` with respect to `S` is defined. -/
abbrev leftDerivedDefinedSubcategory (F : D ⥤ D') (S : MorphismProperty D) :=
  (leftDerivedDefinedObjectProperty F S).FullSubcategory

/-- The restricted multiplicative system `S_𝓔ₗ` on the full subcategory `𝓔ₗ`. -/
abbrev leftDerivedDefinedLocalizationSystem (F : D ⥤ D') (S : MorphismProperty D) :
    MorphismProperty (leftDerivedDefinedSubcategory F S) :=
  fullSubcategoryLocalizationSystem (leftDerivedDefinedObjectProperty F S) S

notation "𝓔ₗ[" F ", " S "]" => leftDerivedDefinedSubcategory F S
notation "S_𝓔ₗ[" F ", " S "]" => leftDerivedDefinedLocalizationSystem F S

/- Left-derived companion recall: a denominator `s : X ⟶ Y` in `S` has source in `𝓔ₗ[F, S]` if
and only if it has target in `𝓔ₗ[F, S]`. -/
recall Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem

/-- An object of the full subcategory `𝓔ₗ` canonically carries the hypothesis that `LF` is
pointwise defined there. -/
instance leftDerivedDefinedSubcategory_hasPointwiseLeftDerivedFunctorAt
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔ₗ[F, S]) :
    F.HasPointwiseLeftDerivedFunctorAt S X.obj :=
  X.property

/-- The functor `LF : 𝓔ₗ ⥤ D'` obtained by restricting the pointwise left derived construction to
the full subcategory where it is defined. -/
noncomputable def leftDerivedDefinedFunctor (F : D ⥤ D') (S : MorphismProperty D) :
    𝓔ₗ[F, S] ⥤ D' where
  obj X :=
    leftDerivedValue S F X.obj
  map f :=
    leftDerivedValueMap S F f.hom
  map_id X :=
    by
      sorry
  map_comp f g :=
    by
      sorry

-- Proof sketch: if a morphism of `S_𝓔ₗ` lies over an ambient arrow `s ∈ S`, then the two
-- objects of `𝓔ₗ` remain in the left-derived domain and Lemma `13.14.4` identifies the induced
-- map on pointwise left-derived values as an isomorphism.
/-- Every denominator in the restricted multiplicative system `S_𝓔ₗ` is sent to an isomorphism by
the restricted functor `LF : 𝓔ₗ ⥤ D'`. -/
theorem leftDerivedDefinedFunctor_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔ₗ[F, S]).IsInvertedBy (leftDerivedDefinedFunctor F S) := sorry

/-- The localized left-derived functor `LF : S_𝓔ₗ^{-1}𝓔ₗ ⥤ D'` induced by the restricted functor
`LF : 𝓔ₗ ⥤ D'`. -/
noncomputable abbrev leftDerivedLocalizationFactorization
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔ₗ[F, S]).Localization ⥤ D' :=
  Localization.lift (leftDerivedDefinedFunctor F S)
    (leftDerivedDefinedFunctor_isInvertedBy F S) (S_𝓔ₗ[F, S]).Q

end Basic

section RestrictedLocalization

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/- The restricted system `S_𝓔[F, S]` inherits saturation directly from the owner instance
`fullSubcategoryLocalizationSystem_isSaturatedMultiplicativeSystem`; no local reexport is needed.
-/

/- The restricted system `S_𝓔ₗ[F, S]` likewise inherits saturation from
`fullSubcategoryLocalizationSystem_isSaturatedMultiplicativeSystem`.
-/

end RestrictedLocalization

section Triangulated

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D]
  [HasShift D ℤ]
  [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  [IsTriangulated D]
  (F : D ⥤ D') (S : MorphismProperty D)

-- Proof sketch: apply Lemmas `13.14.4`, `13.14.6`, and `13.14.7` to show that the object
-- property “`RF` is defined” is closed under isomorphisms, shifts, cones, and the zero object;
-- this is exactly the canonical `ObjectProperty.IsTriangulated` interface.
/-- Proposition 13.14.8: the full subcategory `𝓔 ⊆ D` consisting of objects at which the
pointwise right derived functor of `F` with respect to `S` is defined is strictly full and
triangulated. The companion declarations below record the restricted functor `RF : 𝓔 ⥤ D'`, the
restricted multiplicative system `S_𝓔`, its localization factorization, and the Karoubian
saturation conclusion. -/
instance rightDerivedDefinedObjectProperty_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedObjectProperty F S).IsTriangulated := sorry

/-- The restricted right-derived functor `RF : 𝓔[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance rightDerivedDefinedFunctor_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedFunctor F S).CommShift ℤ := by
  sorry

/-- The restricted right-derived functor `RF : 𝓔[F, S] ⥤ D'` is exact. -/
instance rightDerivedDefinedFunctor_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedFunctor F S).IsTriangulated := by
  sorry

-- Strict fullness is already the owner instance
-- `rightDerivedDefinedObjectProperty_isClosedUnderIsomorphisms` from `Lemma_13_14_5`.

/- Once `rightDerivedDefinedObjectProperty F S` is triangulated, the restricted system `S_𝓔[F, S]`
inherits `IsCompatibleWithTriangulation` from the generic owner instance
`fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation`.
-/

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is fully faithful. -/
instance rightDerivedDefinedLocalizationFunctor_full
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).Full := by
  sorry

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is faithful. -/
instance rightDerivedDefinedLocalizationFunctor_faithful
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).Faithful := by
  sorry

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` commutes with shifts. -/
noncomputable instance rightDerivedDefinedLocalizationFunctor_commShift
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).CommShift ℤ := by
  sorry

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is exact. -/
noncomputable instance rightDerivedDefinedLocalizationFunctor_isTriangulated
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).IsTriangulated := by
  sorry

/-- The localized right-derived functor `RF : S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance rightDerivedLocalizationFactorization_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedLocalizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (S_𝓔[F, S]).Q (S_𝓔[F, S]) ℤ
    (rightDerivedDefinedFunctor F S) (rightDerivedLocalizationFactorization F S)

/-- The localized right-derived functor `RF : S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ D'` is exact. -/
instance rightDerivedLocalizationFactorization_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedLocalizationFactorization F S).IsTriangulated :=
  exact_factorization_isTriangulated (S_𝓔[F, S]) (rightDerivedDefinedFunctor F S)
    (rightDerivedDefinedFunctor_isInvertedBy F S)

-- Proof sketch: if `RF` is defined at a biproduct `X ⊞ Y`, Lemma `13.14.7` shows that in a
-- Karoubian target the two direct summands also lie in the domain. This is exactly stability
-- under retracts of the corresponding object property.
/- Proposition 13.14.8 companion recall: if `D'` is Karoubian, then the right-derived-defined
object property is stable under retracts. Together with
`rightDerivedDefinedObjectProperty_isTriangulated`, this is exactly the source-facing statement
that `𝓔[F, S]` is a saturated triangulated subcategory. -/
recall rightDerivedDefinedObjectProperty_isStableUnderRetracts

-- Proof sketch: apply the left-derived clauses of Lemmas `13.14.4`, `13.14.6`, and `13.14.7` to
-- show that the object property “`LF` is defined” is closed under isomorphisms, shifts, cones,
-- and the zero object; this is exactly the canonical `ObjectProperty.IsTriangulated` interface.
/-- The full subcategory `𝓔ₗ ⊆ D` consisting of objects at which the pointwise left derived
functor of `F` with respect to `S` is defined is strictly full and triangulated, with the same
localized-factorization companion picture as on the right-derived side. -/
instance leftDerivedDefinedObjectProperty_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedObjectProperty F S).IsTriangulated := sorry

/-- The restricted left-derived functor `LF : 𝓔ₗ[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance leftDerivedDefinedFunctor_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedFunctor F S).CommShift ℤ := by
  sorry

/-- The restricted left-derived functor `LF : 𝓔ₗ[F, S] ⥤ D'` is exact. -/
instance leftDerivedDefinedFunctor_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedFunctor F S).IsTriangulated := by
  sorry

-- Strict fullness is already the owner instance
-- `leftDerivedDefinedObjectProperty_isClosedUnderIsomorphisms` from `Lemma_13_14_5`.

/- Once `leftDerivedDefinedObjectProperty F S` is triangulated, the restricted system `S_𝓔ₗ[F, S]`
inherits `IsCompatibleWithTriangulation` from
`fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation`.
-/

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is fully faithful. -/
instance leftDerivedDefinedLocalizationFunctor_full
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).Full := by
  sorry

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is faithful. -/
instance leftDerivedDefinedLocalizationFunctor_faithful
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).Faithful := by
  sorry

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` commutes with shifts. -/
noncomputable instance leftDerivedDefinedLocalizationFunctor_commShift
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).CommShift ℤ := by
  sorry

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is exact. -/
noncomputable instance leftDerivedDefinedLocalizationFunctor_isTriangulated
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).IsTriangulated := by
  sorry

/-- The localized left-derived functor `LF : S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance leftDerivedLocalizationFactorization_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedLocalizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (S_𝓔ₗ[F, S]).Q (S_𝓔ₗ[F, S]) ℤ
    (leftDerivedDefinedFunctor F S) (leftDerivedLocalizationFactorization F S)

/-- The localized left-derived functor `LF : S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ D'` is exact. -/
instance leftDerivedLocalizationFactorization_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedLocalizationFactorization F S).IsTriangulated :=
  exact_factorization_isTriangulated (S_𝓔ₗ[F, S]) (leftDerivedDefinedFunctor F S)
    (leftDerivedDefinedFunctor_isInvertedBy F S)

-- Proof sketch: if `LF` is defined at a biproduct `X ⊞ Y`, Lemma `13.14.7` shows that in a
-- Karoubian target the two direct summands also lie in the domain. This is exactly stability
-- under retracts of the corresponding object property.
/- Left-derived companion recall: if `D'` is Karoubian, then the left-derived-defined object
property is stable under retracts, so `𝓔ₗ[F, S]` is saturated once it is triangulated. -/
recall leftDerivedDefinedObjectProperty_isStableUnderRetracts

end Triangulated

end CategoryTheory

/-! ### Definition_13_14_9 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂} [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
variable (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-
Domain-style sampling for Definition 13.14.9:
- primary domain: pointwise derived functors with respect to a localization morphism property;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `Functor.HasPointwiseRightDerivedFunctor`,
  `Functor.HasPointwiseLeftDerivedFunctor`;
- best owner abstraction: the mathlib pointwise-everywhere predicates
  `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasPointwiseLeftDerivedFunctor`;
- primitive data: the pointwise-at owners `Functor.HasPointwiseRightDerivedFunctorAt` and
  `Functor.HasPointwiseLeftDerivedFunctorAt`;
- derived API: the everywhere-defined predicates obtained by quantifying those pointwise-at
  owners over all objects.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertions that the right or left derived functor of `F`
  with respect to `S` is defined everywhere;
- `core/canonical`: `Functor.HasPointwiseRightDerivedFunctor` and
  `Functor.HasPointwiseLeftDerivedFunctor`;
- `bridge/view`: Definition 13.14.2, which records the corresponding pointwise-at owners.

This file should therefore stay as a direct recall of the canonical owner predicates rather than
introducing a parallel local alias or wrapper.
-/

/- Definition 13.14.9: for a functor `F : 𝒟 ⥤ 𝒟'` and a localization class `S`, saying that
`F` is right derivable, or that `RF` is everywhere defined, is the canonical pointwise-everywhere
predicate `F.HasPointwiseRightDerivedFunctor S`, meaning that the right derived functor is
defined at every object of `𝒟`. -/
recall HasPointwiseRightDerivedFunctor
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) : Prop

/- Companion recall: saying that `F` is left derivable, or that `LF` is everywhere defined, is
the canonical predicate `F.HasPointwiseLeftDerivedFunctor S`, meaning that the left derived
functor is defined at every object of `𝒟`. -/
recall HasPointwiseLeftDerivedFunctor
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) : Prop

end

end Functor

end CategoryTheory
