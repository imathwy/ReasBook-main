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

/-- Helper for Lemma 13.14.3: a commutative denominator square becomes the equality needed to
construct the corresponding morphism in the costructured-arrow indexing category. -/
private theorem costructuredArrow_hom_eq_of_commSq {X Y X' Y' : D} (f : X ⟶ Y)
    (s : X ⟶ X') (s' : Y ⟶ Y') (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq f s s' f') :
    S.Q.map f' ≫ (Localization.isoOfHom S.Q S s' hs').inv =
      (Localization.isoOfHom S.Q S s hs).inv ≫ S.Q.map f := by
  -- Proof comment: map the original square through the localization, then cancel the two
  -- denominator isomorphisms by whiskering with their inverses.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (sq.map S.Q).w
  simpa [Category.assoc, Localization.isoOfHom_hom] using hsq.symm

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
      (rightDerivedValueLeg S F s' hs') := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let RY := CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F
  let _ : HasColimit RX := HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let _ : HasColimit RY := HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y
  let c : Cocone RX :=
    Cocone.mk (rightDerivedValue S F Y)
      { app := fun g ↦ colimit.ι RY ((CostructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa [RX, RY] using
            colimit.w RY ((CostructuredArrow.map (S.Q.map f)).map φ) }
  let α :
      (CostructuredArrow.map (S.Q.map f)).obj
          (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ⟶
        CostructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv) :=
    CostructuredArrow.homMk f'
      (costructuredArrow_hom_eq_of_commSq (S := S) (f := f) s s' hs hs' f' sq)
  refine ⟨?_⟩
  -- Proof comment: evaluate the defining colimit descent on the denominator object `s`, then
  -- compare the resulting indexing object with the denominator object `s'` using the mapped
  -- square.
  have hα :
      colimit.ι RY
          ((CostructuredArrow.map (S.Q.map f)).obj
            (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))) =
        F.map f' ≫ rightDerivedValueLeg S F s' hs' := by
    simpa [RY, rightDerivedValueLeg] using (colimit.w RY α).symm
  have hdesc :
      rightDerivedValueLeg S F s hs ≫ rightDerivedValueMap S F f =
        colimit.ι RY
          ((CostructuredArrow.map (S.Q.map f)).obj
            (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))) := by
    simpa [RX, RY, c, rightDerivedValueLeg, rightDerivedValueMap] using
      colimit.ι_desc (F := RX) c
        (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv))
  exact hdesc.trans hα

-- Proof sketch: use the right calculus of fractions to represent any object of the indexing
-- category for `RF(X)` by a denominator `s : X ⟶ X'` in `S`; the assumed compatibility then
-- determines the image of each colimit leg. The colimit universal property gives existence and
-- uniqueness, and the Ore equalization axiom makes the result independent of the chosen square.
/-- Helper for Lemma 13.14.3: any right-indexing object receives a morphism from one coming from
an actual arrow into `X`. -/
private theorem costructuredArrow_exists_hom_from_plain_map {X : D}
    [S.HasRightCalculusOfFractions] (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X' ⟶ g.left) (_ : S s) (f : X' ⟶ X),
      Nonempty (CostructuredArrow.mk (S.Q.map f) ⟶ g) := by
  -- Proof comment: represent `g.hom` by a right fraction in the localization; its numerator gives
  -- the plain-map object and its denominator gives the required morphism into `g`.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ψ.f, ?_⟩
  refine ⟨CategoryTheory.CostructuredArrow.homMk ψ.s ?_⟩
  -- Proof comment: the defining right-fraction identity is exactly the triangle condition for
  -- the induced morphism of costructured arrows.
  simpa [hψ] using rfl

/-- Helper for Lemma 13.14.3: every right-indexing object should map to one coming from an actual
denominator out of `X`. -/
private theorem right_fraction_exists_target_denominator_square {A X : D}
    [S.HasLeftCalculusOfFractions] (ψ : S.RightFraction A X) :
    ∃ (X' : D) (s : X ⟶ X') (_ : S s) (f : A ⟶ X'),
      ψ.s ≫ f = ψ.f ≫ s := by
  -- Proof comment: in mathlib's conventions, a common-target denominator square is produced by
  -- converting the opposite left fraction `ψ.op` into a right fraction in `Dᵒᵖ`, then unop-ing
  -- the resulting data back to `D`.
  obtain ⟨φ, hφ⟩ := ψ.op.exists_rightFraction
  refine ⟨Opposite.unop φ.X', φ.s.unop, φ.hs, φ.f.unop, ?_⟩
  simpa using (congrArg Quiver.Hom.unop hφ).symm

/-- Helper for Lemma 13.14.3: every right-indexing object should map to one coming from an actual
denominator out of `X`. -/
private theorem costructuredArrow_exists_hom_to_denominator {X : D}
    [S.HasRightCalculusOfFractions] (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X ⟶ X') (hs : S s),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) := by
  -- Route correction: the source proof controls the denominator objects `X / S`, so the needed
  -- bridge is a morphism *to* a denominator object, not merely one *from* a plain-map object.
  -- TODO: the pure square lemma is now isolated below as
  -- `right_fraction_exists_target_denominator_square`, but mathlib exposes it from
  -- `HasLeftCalculusOfFractions` rather than `HasRightCalculusOfFractions`. The remaining bridge
  -- must therefore either recover the needed owner here from an earlier dependency, or show that
  -- this theorem should depend on the left-calculus owner in mathlib's naming.
  sorry

/-- Helper for Lemma 13.14.3: once every right-indexing object maps to a denominator object,
maps out of `RF(X)` are determined by the denominator legs. -/
private theorem rightDerivedValue_hom_ext_of_denominator_legs {X : D}
    [F.HasPointwiseRightDerivedFunctorAt S X]
    (hreach :
      ∀ g : CostructuredArrow S.Q (S.Q.obj X),
        ∃ (X' : D) (s : X ⟶ X') (hs : S s),
          Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)))
    {Z : D'} {ψ₁ ψ₂ : rightDerivedValue S F X ⟶ Z}
    (hψ : ∀ ⦃X' : D⦄ (s : X ⟶ X') (hs : S s),
      rightDerivedValueLeg S F s hs ≫ ψ₁ = rightDerivedValueLeg S F s hs ≫ ψ₂) :
    ψ₁ = ψ₂ := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let _ : HasColimit RX := HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  -- Proof comment: reduce equality of maps out of the colimit to each ambient indexing object,
  -- then move every object to a denominator object where the hypothesis applies.
  apply colimit.hom_ext
  intro g
  rcases hreach g with ⟨X', s, hs, ⟨α⟩⟩
  have hα₁ :
      colimit.ι RX g ≫ ψ₁ =
        RX.map α ≫ colimit.ι RX (CostructuredArrow.mk
          ((Localization.isoOfHom S.Q S s hs).inv)) ≫ ψ₁ := by
    -- Proof comment: whisker the colimit naturality relation for `α` by `ψ₁`.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ ψ₁) (colimit.w RX α)
  have hα₂ :
      colimit.ι RX g ≫ ψ₂ =
        RX.map α ≫ colimit.ι RX (CostructuredArrow.mk
          ((Localization.isoOfHom S.Q S s hs).inv)) ≫ ψ₂ := by
    -- Proof comment: the same whiskering identifies the second comparison composite.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ ψ₂) (colimit.w RX α)
  calc
    colimit.ι RX g ≫ ψ₁ =
        RX.map α ≫ colimit.ι RX (CostructuredArrow.mk
          ((Localization.isoOfHom S.Q S s hs).inv)) ≫ ψ₁ := hα₁
    _ = RX.map α ≫ colimit.ι RX (CostructuredArrow.mk
          ((Localization.isoOfHom S.Q S s hs).inv)) ≫ ψ₂ := by
      rw [show colimit.ι RX (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ≫ ψ₁ =
          colimit.ι RX (CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ≫ ψ₂ by
            simpa [RX, rightDerivedValueLeg] using hψ s hs]
    _ = colimit.ι RX g ≫ ψ₂ := hα₂.symm

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
    φ = rightDerivedValueMap S F f := by
  -- Route correction: the main theorem now factors through denominator-leg extensionality, so the
  -- remaining blocker is the source-faithful bridge sending an arbitrary indexing object to a
  -- denominator object of `X / S`.
  -- TODO: after `costructuredArrow_exists_hom_to_denominator` is proved, compare `φ` and the
  -- canonical map on one denominator leg at a time using the common-target denominator square
  -- supplied by `right_fraction_exists_target_denominator_square`.
  sorry

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

/-- Helper for Lemma 13.14.3: a commutative denominator square becomes the equality needed to
construct the corresponding morphism in the structured-arrow indexing category. -/
private theorem structuredArrow_hom_eq_of_commSq {X Y X' Y' : D} (f : X ⟶ Y)
    (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s') (f' : X' ⟶ Y')
    (sq : CommSq s f' f s') :
    (Localization.isoOfHom S.Q S s hs).inv ≫ S.Q.map f' =
      S.Q.map f ≫ (Localization.isoOfHom S.Q S s' hs').inv := by
  -- Proof comment: after localizing the commutative square, whisker by the inverse
  -- denominator isomorphisms to isolate the arrow needed in `StructuredArrow`.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (sq.map S.Q).w
  simpa [Category.assoc, Localization.isoOfHom_hom] using hsq.symm

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
      (F.map f') := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let _ : HasLimit LX := HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let _ : HasLimit LY := HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  let c : Cone LY :=
    Cone.mk (leftDerivedValue S F X)
      { app := fun g ↦ limit.π LX ((StructuredArrow.map (S.Q.map f)).obj g)
        naturality := fun g₁ g₂ φ ↦ by
          simpa [LX, LY] using
            (limit.w LX ((StructuredArrow.map (S.Q.map f)).map φ)).symm }
  let α :
      StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶
        (StructuredArrow.map (S.Q.map f)).obj
          (StructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv)) :=
    StructuredArrow.homMk f'
      (structuredArrow_hom_eq_of_commSq (S := S) (f := f) s s' hs hs' f' sq)
  refine ⟨?_⟩
  -- Proof comment: evaluate the defining limit lift on the denominator object `s'`, then use
  -- the mapped square to identify that projection with the one coming from `s`.
  have hα :
      limit.π LX
          ((StructuredArrow.map (S.Q.map f)).obj
            (StructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv))) =
        leftDerivedValueProjection S F s hs ≫ F.map f' := by
    simpa [LX, leftDerivedValueProjection] using (limit.w LX α).symm
  have hlift :
      leftDerivedValueMap S F f ≫ leftDerivedValueProjection S F s' hs' =
        limit.π LX
          ((StructuredArrow.map (S.Q.map f)).obj
            (StructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv))) := by
    simpa [LX, LY, c, leftDerivedValueProjection, leftDerivedValueMap] using
      limit.lift_π (F := LY) c
        (StructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv))
  exact hlift.trans hα

-- Proof sketch: use the left calculus of fractions to represent any object of the indexing
-- category for `LF(Y)` by a denominator `s' : Y' ⟶ Y` in `S`; the assumed compatibility then
-- determines the composite with each limit projection. The limit universal property gives the
-- unique morphism realizing these projections, and the Ore equalization axiom ensures
-- independence of the chosen square.
/-- Helper for Lemma 13.14.3: any left-indexing object maps to one coming from an actual arrow out
of `Y`. -/
private theorem structuredArrow_exists_hom_to_plain_map {Y : D}
    [S.HasLeftCalculusOfFractions] (g : StructuredArrow (S.Q.obj Y) S.Q) :
    ∃ (Y' : D) (f : Y ⟶ Y') (s : g.right ⟶ Y') (_ : S s),
      Nonempty (g ⟶ StructuredArrow.mk (S.Q.map f)) := by
  -- Proof comment: represent `g.hom` by a left fraction in the localization; its numerator gives
  -- the plain-map object and its denominator gives the comparison morphism out of `g`.
  obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction S.Q S g.hom
  refine ⟨ψ.Y', ψ.f, ψ.s, ψ.hs, ?_⟩
  refine ⟨CategoryTheory.StructuredArrow.homMk ψ.s ?_⟩
  -- Proof comment: the defining left-fraction identity is exactly the triangle condition for the
  -- induced morphism of structured arrows.
  simpa [hψ] using rfl

/-- Helper for Lemma 13.14.3: every left-indexing object should receive a morphism from one
coming from an actual denominator into `Y`. -/
private theorem left_fraction_exists_source_denominator_square {Y A : D}
    [S.HasRightCalculusOfFractions] (ψ : S.LeftFraction Y A) :
    ∃ (Y' : D) (s : Y' ⟶ Y) (_ : S s) (f : Y' ⟶ A),
      s ≫ ψ.f = f ≫ ψ.s := by
  -- Proof comment: dually, mathlib's `HasRightCalculusOfFractions` produces the common-source
  -- square by turning the opposite right fraction `ψ.op` into a left fraction and unop-ing the
  -- result.
  obtain ⟨φ, hφ⟩ := ψ.op.exists_leftFraction
  refine ⟨Opposite.unop φ.Y', φ.s.unop, φ.hs, φ.f.unop, ?_⟩
  simpa using congrArg Quiver.Hom.unop hφ

/-- Helper for Lemma 13.14.3: every left-indexing object should receive a morphism from one
coming from an actual denominator into `Y`. -/
private theorem structuredArrow_exists_hom_from_denominator {Y : D}
    [S.HasLeftCalculusOfFractions] (g : StructuredArrow (S.Q.obj Y) S.Q) :
    ∃ (Y' : D) (s : Y' ⟶ Y) (hs : S s),
      Nonempty (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶ g) := by
  -- Route correction: for the dual limit argument, the source proof again controls the genuine
  -- denominator objects `S \ Y`; plain-map objects have the wrong orientation.
  -- TODO: the pure square lemma is now isolated below as
  -- `left_fraction_exists_source_denominator_square`, but mathlib exposes it from
  -- `HasRightCalculusOfFractions` rather than `HasLeftCalculusOfFractions`. The remaining bridge
  -- must therefore recover that owner or explain the naming mismatch at the theorem boundary.
  sorry

/-- Helper for Lemma 13.14.3: once every left-indexing object receives a morphism from a
denominator object, maps into `LF(Y)` are determined by the denominator projections. -/
private theorem leftDerivedValue_hom_ext_of_denominator_projections {Y : D}
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [S.HasLeftCalculusOfFractions]
    (hreach :
      ∀ g : StructuredArrow (S.Q.obj Y) S.Q,
        ∃ (Y' : D) (s : Y' ⟶ Y) (hs : S s),
          Nonempty (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶ g))
    {Z : D'} {ψ₁ ψ₂ : Z ⟶ leftDerivedValue S F Y}
    (hψ : ∀ ⦃Y' : D⦄ (s : Y' ⟶ Y) (hs : S s),
      ψ₁ ≫ leftDerivedValueProjection S F s hs =
        ψ₂ ≫ leftDerivedValueProjection S F s hs) :
    ψ₁ = ψ₂ := by
  sorry

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
    φ = leftDerivedValueMap S F f := by
  -- Route correction: the dual theorem also factors through denominator-projection extensionality,
  -- so the only missing bridge is the source-faithful reachability from denominator objects in
  -- `S \ Y`.
  -- TODO: after `structuredArrow_exists_hom_from_denominator` is proved, compare `φ` and the
  -- canonical map on one denominator projection at a time using the common-source denominator
  -- square supplied by `left_fraction_exists_source_denominator_square`.
  sorry

end

end CategoryTheory
