import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

-- Declarations for this item will be appended below by the statement pipeline.

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
  `Functor.HasPointwiseRightDerivedFunctorAt.hasColimit`,
  `Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit`;
- owner abstraction:
  `source-facing`: the local constructions `rightDerivedValue`, `leftDerivedValue`, and their
    induced maps for a fixed `S` and `F`;
  `core/canonical`: the canonical pointwise Kan-extension diagrams
    `CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F` and
    `StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F`, together with `CategoryTheory.CommSq` for
    square-shaped compatibility statements;
  `bridge/view`: the leg/projection descriptions relating the local derived-value maps to
    denominator squares in `D`.

Primitive data are the pointwise existence hypotheses and the canonical colimit/limit
presentations of those diagrams. The leg/projection compatibilities are derived API and should be
stated through the owner `CommSq`, not as standalone equalities of composites.
-/

/-- The pointwise right-derived value of `F` at `X`, computed as the colimit over the
costructured-arrow category of `S.Q` above `X`. -/
noncomputable abbrev rightDerivedValue (X : D)
    [F.HasPointwiseRightDerivedFunctorAt S X] : D' :=
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  colimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)

/-- The canonical map from `F.obj X'` to the right-derived value at `X` associated to a
denominator `s : X ⟶ X'` in `S`. -/
noncomputable abbrev rightDerivedValueLeg {X X' : D} (s : X ⟶ X') (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X] : F.obj X' ⟶ rightDerivedValue S F X :=
  let _ : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
    HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)
    (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))

/-- Lemma 13.14.3 (1): if the pointwise right-derived values of `F` are defined at `X` and `Y`,
then a morphism `f : X ⟶ Y` induces the canonical map `RF(f) : RF(X) ⟶ RF(Y)`. -/
noncomputable def rightDerivedValueMap {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y] :
    rightDerivedValue S F X ⟶ rightDerivedValue S F Y :=
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let RY := CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F
  let _ : HasColimit RX := HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let _ : HasColimit RY := HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y
  colimit.desc RX
    (Cocone.mk (rightDerivedValue S F Y)
      { app := fun g ↦ colimit.ι RY ((CostructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa [RX, RY] using
            colimit.w RY ((CostructuredArrow.map (S.Q.map f)).map φ) })

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
  let _ : HasLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
    HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  limit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)

/-- The canonical projection from the left-derived value at `X` to `F.obj X'` associated to a
denominator `s : X' ⟶ X` in `S`. -/
noncomputable abbrev leftDerivedValueProjection {X X' : D} (s : X' ⟶ X) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S X] : leftDerivedValue S F X ⟶ F.obj X' :=
  let _ : HasLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
    HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)
    (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))

/-- Lemma 13.14.3 (2): if the pointwise left-derived values of `F` are defined at `X` and `Y`,
then a morphism `f : X ⟶ Y` induces the canonical map `LF(f) : LF(X) ⟶ LF(Y)`. -/
noncomputable def leftDerivedValueMap {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    leftDerivedValue S F X ⟶ leftDerivedValue S F Y :=
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let _ : HasLimit LX := HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let _ : HasLimit LY := HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  limit.lift LY
    (Cone.mk (leftDerivedValue S F X)
      { app := fun g ↦ limit.π LX ((StructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa [LX, LY] using
            (limit.w LX ((StructuredArrow.map (S.Q.map f)).map φ)).symm })

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
