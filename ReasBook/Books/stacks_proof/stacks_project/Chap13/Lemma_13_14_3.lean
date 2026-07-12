import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.StacksAttribute

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

/-- The first construction in Lemma 13.14.3: if the pointwise right-derived values of `F` are
defined at `X` and `Y`,
then a morphism `f : X ⟶ Y` induces the canonical map `RF(f) : RF(X) ⟶ RF(Y)`. -/
@[stacks 05SA]
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
      S.Q.map s ≫ g.hom = S.Q.map f := by
  -- Proof comment: represent `g.hom` by a right fraction in the localization; its numerator gives
  -- the plain-map object and its denominator gives the required morphism into `g`.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  -- Proof comment: the defining right-fraction identity is exactly the triangle condition for
  -- the induced morphism of costructured arrows.
  refine ⟨ψ.X', ψ.s, ψ.hs, ψ.f, ?_⟩
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
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
    (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X ⟶ X') (hs : S s),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) := by
  -- The source proof controls the denominator objects `X / S`, so the needed bridge is a morphism
  -- *to* a denominator object, not merely one *from* a plain-map object. In mathlib's naming this
  -- reachability uses both right fractions and the left-calculus common-target square.
  rcases costructuredArrow_exists_hom_from_plain_map (S := S) g with
    ⟨A, t, ht, u, hwα⟩
  rcases right_fraction_exists_target_denominator_square (S := S)
      (MorphismProperty.RightFraction.mk t ht u) with ⟨X', s, hs, f, hsq⟩
  refine ⟨X', s, hs, ⟨CostructuredArrow.homMk f ?_⟩⟩
  -- Proof comment: the plain-map presentation of `g` and the common-target denominator square
  -- identify `g.hom ≫ S.Q.map s` with `S.Q.map f`.
  have hcomp : g.hom ≫ S.Q.map s = S.Q.map f := by
    letI : IsIso (S.Q.map t) := Localization.inverts S.Q S t ht
    apply (cancel_epi (S.Q.map t)).1
    calc
      S.Q.map t ≫ (g.hom ≫ S.Q.map s) = (S.Q.map t ≫ g.hom) ≫ S.Q.map s := by
        simp [Category.assoc]
      _ = S.Q.map u ≫ S.Q.map s := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ S.Q.map s) hwα
      _ = S.Q.map (u ≫ s) := by
        simp [Functor.map_comp]
      _ = S.Q.map (t ≫ f) := by
        rw [hsq]
      _ = S.Q.map t ≫ S.Q.map f := by
        simp [Functor.map_comp]
  -- Proof comment: cancel the denominator isomorphism `S.Q.map s` on the right to rewrite
  -- `g.hom` in the form needed for a morphism to the denominator object indexed by `s`.
  letI : IsIso (S.Q.map s) := Localization.inverts S.Q S s hs
  apply (cancel_mono (S.Q.map s)).1
  calc
    (S.Q.map f ≫ (Localization.isoOfHom S.Q S s hs).inv) ≫ S.Q.map s =
        S.Q.map f := by
      simp [Category.assoc]
    _ = g.hom ≫ S.Q.map s := hcomp.symm

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
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
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
  refine rightDerivedValue_hom_ext_of_denominator_legs (S := S) (F := F)
    (hreach := costructuredArrow_exists_hom_to_denominator (S := S)) ?_
  intro X' s hs
  rcases right_fraction_exists_target_denominator_square (S := S)
      (MorphismProperty.RightFraction.mk s hs f) with ⟨Y', s', hs', f', hsq⟩
  let sq : CommSq f s s' f' := ⟨hsq.symm⟩
  -- Proof comment: both maps out of `RF(X)` satisfy the same denominator-square relation for the
  -- common-target square attached to `(s, f)`, so their composites with the leg indexed by `s`
  -- coincide.
  calc
    rightDerivedValueLeg S F s hs ≫ φ =
        F.map f' ≫ rightDerivedValueLeg S F s' hs' := (hφ s s' hs hs' f' sq).w
    _ = rightDerivedValueLeg S F s hs ≫ rightDerivedValueMap S F f := by
      symm
      exact (rightDerivedValueMap_comp_of_square (S := S) (F := F) (f := f)
        s s' hs hs' f' sq).w

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

/-- The second construction in Lemma 13.14.3: if the pointwise left-derived values of `F` are
defined at `X` and `Y`,
then a morphism `f : X ⟶ Y` induces the canonical map `LF(f) : LF(X) ⟶ LF(Y)`. -/
@[stacks 05SA]
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

/-- Helper for Lemma 13.14.3: the projection to a plain-map stage factors through the identity
denominator projection on `Y`. -/
private theorem leftDerivedValueProjection_plainMap {Y Y' : D} (k : Y ⟶ Y')
    [F.HasPointwiseLeftDerivedFunctorAt S Y] [S.HasLeftCalculusOfFractions]
    [HasLimit (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F)] :
    limit.π (StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F) (StructuredArrow.mk (S.Q.map k)) =
      leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y) ≫ F.map k := by
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let α :
      StructuredArrow.mk
          ((Localization.isoOfHom S.Q S (𝟙 Y) (S.id_mem Y)).inv) ⟶
        StructuredArrow.mk (S.Q.map k) :=
    StructuredArrow.homMk k (by
      simp [Localization.isoOfHom_id_inv])
  -- Proof comment: the identity denominator object maps to every plain-map object, so the
  -- universal property of the limit rewrites the plain-map projection through the identity stage.
  simpa [LY, leftDerivedValueProjection, Localization.isoOfHom_id_inv] using (limit.w LY α).symm

/-- Helper for Lemma 13.14.3: a denominator `s' : Y' ⟶ Y` can be completed with `f : X ⟶ Y` to a
common-source square `s ≫ f = f' ≫ s'`. -/
private theorem leftFraction_exists_source_denominator_square {X Y Y' : D} (f : X ⟶ Y)
    (s' : Y' ⟶ Y) (hs' : S s') [S.HasRightCalculusOfFractions] :
    ∃ (X' : D) (s : X' ⟶ X) (_ : S s) (f' : X' ⟶ Y'), s ≫ f = f' ≫ s' := by
  let φ : S.LeftFraction X Y' := MorphismProperty.LeftFraction.mk f s' hs'
  -- Proof comment: the right-calculus comparison for the left fraction `(f, s')` gives exactly
  -- the common-source denominator square required by the textbook argument.
  refine ⟨φ.rightFraction.X', φ.rightFraction.s, φ.rightFraction.hs, φ.rightFraction.f, ?_⟩
  simpa [φ] using φ.rightFraction_fac

/-- Helper for Lemma 13.14.3: every left-indexing object under `Y` receives a morphism from one
indexed by an actual denominator into `Y`. -/
private theorem structuredArrow_exists_hom_from_denominator {Y : D}
    [S.HasRightCalculusOfFractions] (g : StructuredArrow (S.Q.obj Y) S.Q) :
    ∃ (Y' : D) (s : Y' ⟶ Y) (hs : S s),
      Nonempty (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶ g) := by
  -- Proof comment: a right-fraction presentation of `g.hom` already has exactly the source
  -- denominator orientation needed for a morphism from a denominator object into `g`.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ?_⟩
  refine ⟨StructuredArrow.homMk ψ.f ?_⟩
  calc
    (Localization.isoOfHom S.Q S ψ.s ψ.hs).inv ≫ S.Q.map ψ.f =
        ψ.map S.Q (Localization.inverts S.Q S) := by
          rfl
    _ = g.hom := hψ.symm

/-- Helper for Lemma 13.14.3: maps into `LF(Y)` are determined by their composites with every
denominator projection. -/
private theorem leftDerivedValue_hom_ext_of_denominator_projections {Y : D}
    [F.HasPointwiseLeftDerivedFunctorAt S Y] [S.HasRightCalculusOfFractions]
    {Z : D'} {ψ₁ ψ₂ : Z ⟶ leftDerivedValue S F Y}
    (hψ : ∀ ⦃Y' : D⦄ (s : Y' ⟶ Y) (hs : S s),
      ψ₁ ≫ leftDerivedValueProjection S F s hs = ψ₂ ≫ leftDerivedValueProjection S F s hs) :
    ψ₁ = ψ₂ := by
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let _ : HasLimit LY := HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  -- Proof comment: reduce equality into the limit to each structured-arrow stage, then replace an
  -- arbitrary stage by a denominator stage using the reachability lemma above.
  apply limit.hom_ext
  intro g
  rcases structuredArrow_exists_hom_from_denominator (S := S) (Y := Y) g with
    ⟨Y', s, hs, ⟨α⟩⟩
  have hden :
      ψ₁ ≫ limit.π LY (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) =
        ψ₂ ≫ limit.π LY (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) := by
    -- Proof comment: denominator stages are exactly the projections controlled by the hypothesis.
    simpa [LY, leftDerivedValueProjection] using hψ s hs
  have hα₁ :
      ψ₁ ≫ limit.π LY g =
        ψ₁ ≫ limit.π LY (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ≫
          LY.map α := by
    -- Proof comment: `limit.w` transports the comparison from the denominator stage to `g`.
    simpa [Category.assoc] using
      (congrArg (fun k ↦ ψ₁ ≫ k) (limit.w LY α)).symm
  have hα₂ :
      ψ₂ ≫ limit.π LY g =
        ψ₂ ≫ limit.π LY (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ≫
          LY.map α := by
    -- Proof comment: the same transport formula applies to the second map into the limit.
    simpa [Category.assoc] using
      (congrArg (fun k ↦ ψ₂ ≫ k) (limit.w LY α)).symm
  calc
    ψ₁ ≫ limit.π LY g =
        ψ₁ ≫ limit.π LY (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ≫
          LY.map α := hα₁
    _ =
        ψ₂ ≫ limit.π LY (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) ≫
          LY.map α := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ LY.map α) hden
    _ = ψ₂ ≫ limit.π LY g := hα₂.symm

/-- Lemma 13.14.3: any morphism with the textbook compatibility on all denominator squares is the
canonical map between the left-derived values. -/
theorem leftDerivedValueMap_hom_ext {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y]
    [S.HasLeftCalculusOfFractions] [S.HasRightCalculusOfFractions]
    {φ : leftDerivedValue S F X ⟶ leftDerivedValue S F Y}
    (hφ : ∀ ⦃X' Y' : D⦄ (s : X' ⟶ X) (s' : Y' ⟶ Y) (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq s f' f s'),
          CommSq
            φ
            (leftDerivedValueProjection S F s hs)
            (leftDerivedValueProjection S F s' hs')
            (F.map f')) :
    φ = leftDerivedValueMap S F f := by
  -- Route correction: the failed plain-map route had the wrong orientation for `limit.w`. The
  -- correct uniqueness proof uses denominator objects that map *into* arbitrary stages of the
  -- structured-arrow indexing category.
  refine leftDerivedValue_hom_ext_of_denominator_projections (S := S) (F := F) ?_
  intro Y' s' hs'
  rcases leftFraction_exists_source_denominator_square (S := S) (f := f) s' hs' with
    ⟨X', s, hs, f', hsq⟩
  let sq : CommSq s f' f s' := ⟨hsq⟩
  -- Proof comment: both candidate maps satisfy the same compatibility with the denominator
  -- projection indexed by `s'`, so comparing them there suffices by the extensionality lemma.
  calc
    φ ≫ leftDerivedValueProjection S F s' hs' =
        leftDerivedValueProjection S F s hs ≫ F.map f' := (hφ s s' hs hs' f' sq).w
    _ = leftDerivedValueMap S F f ≫ leftDerivedValueProjection S F s' hs' := by
          simpa using
            (leftDerivedValueMap_comp_of_square (S := S) (F := F) (f := f)
              s s' hs hs' f' sq).w.symm

end

end CategoryTheory
