import StacksProject_2024.stacks_project.Chap13.Definition_13_14_10
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_5

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

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

/-- Helper for Lemma 13.14.11: transporting the right-derived colimit cocone across an ambient
isomorphism produces a comparison isomorphism between the pointwise right-derived values whose
effect on the identity leg is the expected conjugation by `F.map e.hom`. -/
lemma exists_rightDerivedValueIso_of_iso {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    ∃ i : rightDerivedValue S F X ≅ rightDerivedValue S F Y,
      rightDerivedValueLeg S F (𝟙 X) (S.id_mem X) ≫ i.hom =
        F.map e.hom ≫ rightDerivedValueLeg S F (𝟙 Y) (S.id_mem Y) := by
  -- Compare the canonical colimit cocone at `X` with the one obtained from the colimit cocone
  -- at `Y` by whiskering along `S.Q.mapIso e`.
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let RY := CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F
  let _ : HasColimit RX := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let _ : HasColimit RY := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y
  let eQ : S.Q.obj X ≅ S.Q.obj Y := S.Q.mapIso e
  let jX :
      CostructuredArrow S.Q (S.Q.obj X) :=
    CostructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let jY :
      CostructuredArrow S.Q (S.Q.obj Y) :=
    CostructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 Y) (S.id_mem Y)).inv)
  let transported : Cocone RX := (colimit.cocone RY).whisker (CostructuredArrow.mapIso eQ).functor
  have htransported : IsColimit transported := by
    simpa [RX, RY, transported] using
      (colimit.isColimit RY).whiskerEquivalence (CostructuredArrow.mapIso eQ)
  let i : rightDerivedValue S F X ≅ rightDerivedValue S F Y :=
    (colimit.isColimit RX).coconePointUniqueUpToIso htransported
  have hi :
      rightDerivedValueLeg S F (𝟙 X) (S.id_mem X) ≫ i.hom =
        transported.ι.app jX := by
    simpa [RX, i, transported, jX, rightDerivedValueLeg] using
      (colimit.isColimit RX).comp_coconePointUniqueUpToIso_hom htransported
        jX
  have hleg :
      transported.ι.app jX =
        F.map e.hom ≫ rightDerivedValueLeg S F (𝟙 Y) (S.id_mem Y) := by
    -- Naturality along `e.hom` identifies the transported identity leg with the identity leg
    -- at `Y`.
    let α : (CostructuredArrow.mapIso eQ).functor.obj jX ⟶ jY :=
      CostructuredArrow.homMk e.hom (by
        simp [jX, jY, eQ, Localization.isoOfHom_id_inv])
    simpa [RY, transported, jX, jY, rightDerivedValueLeg] using (colimit.w RY α).symm
  exact ⟨i, hi.trans hleg⟩

/-- Helper for Lemma 13.14.11: transporting the left-derived limit cone across an ambient
isomorphism produces a comparison isomorphism between the pointwise left-derived values whose
effect on the identity projection is the expected conjugation by `F.map e.hom`. -/
lemma exists_leftDerivedValueIso_of_iso {X Y : D} (e : X ≅ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    ∃ i : leftDerivedValue S F X ≅ leftDerivedValue S F Y,
      i.hom ≫ leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y) =
        leftDerivedValueProjection S F (𝟙 X) (S.id_mem X) ≫ F.map e.hom := by
  -- Compare the canonical limit cone at `Y` with the cone obtained from the limit cone at `X`
  -- by whiskering along `StructuredArrow.mapIso (S.Q.mapIso e)`.
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let _ : HasLimit LX := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let _ : HasLimit LY := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  let eQ : S.Q.obj X ≅ S.Q.obj Y := S.Q.mapIso e
  let jX :
      StructuredArrow (S.Q.obj X) S.Q :=
    StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let jY :
      StructuredArrow (S.Q.obj Y) S.Q :=
    StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 Y) (S.id_mem Y)).inv)
  let transported : Cone LY :=
    (limit.cone LX).whisker (StructuredArrow.mapIso eQ).symm.functor
  have htransported : IsLimit transported := by
    simpa [LX, LY, transported] using
      (limit.isLimit LX).whiskerEquivalence (StructuredArrow.mapIso eQ).symm
  let i₀ := htransported.conePointUniqueUpToIso (limit.isLimit LY)
  let i :
      leftDerivedValue S F X ≅ leftDerivedValue S F Y := by
    simpa [LX, transported, leftDerivedValue] using
      i₀
  have hi₀ :
      i₀.hom ≫ leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y) =
        transported.π.app jY := by
    simpa [LY, transported, jY, leftDerivedValueProjection] using
      htransported.conePointUniqueUpToIso_hom_comp (limit.isLimit LY) jY
  have hi :
      i.hom ≫ leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y) =
        transported.π.app jY := by
    simpa [i] using hi₀
  have hproj :
      transported.π.app jY =
        leftDerivedValueProjection S F (𝟙 X) (S.id_mem X) ≫ F.map e.hom := by
    -- Naturality along `e.hom` identifies the transported identity projection with the
    -- identity projection at `X`.
    let α : jX ⟶ (StructuredArrow.mapIso eQ).symm.functor.obj jY :=
      StructuredArrow.homMk e.hom (by
        simp [jX, jY, eQ, Localization.isoOfHom_id_inv])
    simpa [LX, transported, jX, jY, leftDerivedValueProjection] using (limit.w LX α).symm
  exact ⟨i, hi.trans hproj⟩

/-- Objects which compute the right derived functor of `F` are closed under ambient
isomorphisms. -/
instance computesRightDerivedAt_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (F.computesRightDerivedObjectProperty S) := by
  refine ⟨?_⟩
  intro X Y e hX
  letI : F.ComputesRightDerivedAt S X := hX
  have hY :
      rightDerivedDefinedObjectProperty F S Y :=
    (rightDerivedDefinedObjectProperty F S).prop_of_iso e
      (show rightDerivedDefinedObjectProperty F S X from inferInstance)
  letI : F.HasPointwiseRightDerivedFunctorAt S Y := hY
  obtain ⟨i, hi⟩ :=
    exists_rightDerivedValueIso_of_iso (F := F) (S := S) e.symm
  refine ⟨?_⟩
  -- The canonical identity leg at `Y` becomes the conjugate of the identity leg at `X`
  -- after transporting the colimit cocone along `e.symm`.
  have hcomp :
      IsIso (rightDerivedValueLeg S F (𝟙 Y) (S.id_mem Y) ≫ i.hom) := by
    rw [hi]
    infer_instance
  exact
    (isIso_comp_right_iff
      (rightDerivedValueLeg S F (𝟙 Y) (S.id_mem Y))
      i.hom).1 hcomp

/-- Objects which compute the left derived functor of `F` are closed under ambient
isomorphisms. -/
instance computesLeftDerivedAt_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (F.computesLeftDerivedObjectProperty S) := by
  refine ⟨?_⟩
  intro X Y e hX
  letI : F.ComputesLeftDerivedAt S X := hX
  have hY :
      leftDerivedDefinedObjectProperty F S Y :=
    (leftDerivedDefinedObjectProperty F S).prop_of_iso e
      (show leftDerivedDefinedObjectProperty F S X from inferInstance)
  letI : F.HasPointwiseLeftDerivedFunctorAt S Y := hY
  obtain ⟨i, hi⟩ :=
    exists_leftDerivedValueIso_of_iso (F := F) (S := S) e
  refine ⟨?_⟩
  -- The canonical identity projection at `Y` is the conjugate of the one at `X`
  -- through the comparison isomorphism produced above.
  have hcomp :
      IsIso (i.hom ≫ leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y)) := by
    rw [hi]
    infer_instance
  exact
    (isIso_comp_left_iff
      i.hom
      (leftDerivedValueProjection S F (𝟙 Y) (S.id_mem Y))).1 hcomp

/-- Helper for Lemma 13.14.11: the shifted identity leg obtained from the unshifted computing
object is an isomorphism after composing with `F.commShiftIso`. -/
lemma isIso_shifted_rightDerivedValueLeg
    [F.ComputesRightDerivedAt S X] :
    IsIso
      (((F.commShiftIso n).app X).hom ≫
        (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) := by
  -- Proof comment: both factors are canonical isomorphisms, so their composite is again an
  -- isomorphism.
  letI : IsIso (((F.commShiftIso n).app X).hom) := by infer_instance
  letI : IsIso (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by infer_instance
  have hmap :
      IsIso ((shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) :=
    Functor.map_isIso (shiftFunctor D' n) (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))
  exact IsIso.comp_isIso' inferInstance hmap

/-- Helper for Lemma 13.14.11: once the shifted identity-denominator leg is identified with the
shift of the unshifted leg through a comparison isomorphism, the shifted object computes the right
derived functor. -/
lemma computesRightDerivedAt_of_shift_leg_conjugation
    [F.ComputesRightDerivedAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧)]
    (h :
      ∃ i : rightDerivedValue S F (X⟦n⟧) ≅ ((rightDerivedValue S F X)⟦n⟧),
        rightDerivedValueLeg S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫ i.hom =
          ((F.commShiftIso n).app X).hom ≫
            (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) :
    F.ComputesRightDerivedAt S (X⟦n⟧) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨?_⟩
  -- Proof comment: the rewritten shifted identity leg is a composite of isomorphisms with the
  -- unshifted identity leg, so invertibility transports back across the comparison isomorphism.
  have hcomp :
      IsIso
        (rightDerivedValueLeg S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫ i.hom) := by
    rw [hi]
    exact isIso_shifted_rightDerivedValueLeg (F := F) (S := S) (X := X) (n := n)
  exact
    (isIso_comp_right_iff
      (rightDerivedValueLeg S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)))
      i.hom).1 hcomp

/-- Helper for Lemma 13.14.11: shifting preserves the invertibility of the identity projection of
an object computing the left derived functor. -/
lemma isIso_shifted_leftDerivedValueProjection
    [F.ComputesLeftDerivedAt S X] :
    IsIso ((shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X))) := by
  -- Proof comment: functors preserve isomorphisms, so shifting the identity projection preserves
  -- the computing condition.
  letI : IsIso (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by infer_instance
  exact
    Functor.map_isIso (shiftFunctor D' n) (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X))

/-- Helper for Lemma 13.14.11: once the shifted identity-denominator projection is identified
with the shift of the unshifted projection through a comparison isomorphism, the shifted object
computes the left derived functor. -/
lemma computesLeftDerivedAt_of_shift_projection_conjugation
    [F.ComputesLeftDerivedAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧)]
    (h :
      ∃ i : leftDerivedValue S F (X⟦n⟧) ≅ ((leftDerivedValue S F X)⟦n⟧),
        i.hom ≫ (shiftFunctor D' n).map
            (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) =
          leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
            ((F.commShiftIso n).app X).hom) :
    F.ComputesLeftDerivedAt S (X⟦n⟧) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨?_⟩
  -- Proof comment: after the conjugation rewrite, the shifted identity projection is a composite
  -- of the shifted unshifted projection with ambient comparison isomorphisms, hence invertible.
  have hcomp :
      IsIso
        (leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom) := by
    rw [← hi]
    letI : IsIso i.hom := by infer_instance
    have hmap :
        IsIso ((shiftFunctor D' n).map
          (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X))) :=
      isIso_shifted_leftDerivedValueProjection (F := F) (S := S) (X := X) (n := n)
    exact IsIso.comp_isIso' inferInstance hmap
  exact
    (isIso_comp_right_iff
      (leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)))
      ((F.commShiftIso n).app X).hom).1 hcomp

/-- Helper for Lemma 13.14.11: the canonical shift comparison for pointwise right-derived values
can be chosen so that it conjugates the identity-denominator leg by `F.commShiftIso`. -/
lemma exists_rightDerivedValueShiftIso_with_id_leg
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    ∃ i : rightDerivedValue S F (X⟦n⟧) ≅ ((rightDerivedValue S F X)⟦n⟧),
      rightDerivedValueLeg S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫ i.hom =
        ((F.commShiftIso n).app X).hom ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
  refine ⟨rightDerivedValueShiftIso F S X n, ?_⟩
  -- Route correction: the remaining issue is not existence of the shift comparison isomorphism,
  -- but the missing universal-property computation identifying its effect on the identity leg.
  -- TODO: rebuild this comparison locally from the shifted colimit cocone and read off the
  -- identity-denominator component through `IsColimit.comp_coconePointUniqueUpToIso_hom`.
  sorry

/-- Helper for Lemma 13.14.11: the canonical shift comparison for pointwise left-derived values
can be chosen so that it conjugates the identity-denominator projection by `F.commShiftIso`. -/
lemma exists_leftDerivedValueShiftIso_with_id_projection
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    ∃ i : leftDerivedValue S F (X⟦n⟧) ≅ ((leftDerivedValue S F X)⟦n⟧),
      i.hom ≫ (shiftFunctor D' n).map
          (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) =
        leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom := by
  refine ⟨leftDerivedValueShiftIso F S X n, ?_⟩
  -- Route correction: as on the right-derived side, the unresolved step is the explicit
  -- universal-property computation of the shifted identity projection, not the comparison
  -- isomorphism itself.
  -- TODO: reconstruct this comparison from the shifted limit cone and use
  -- `IsLimit.conePointUniqueUpToIso_hom_comp` at the identity-denominator object.
  sorry

/-- Objects which compute the right derived functor of `F` form a shift-stable object property. -/
instance computesRightDerivedAt_isStableUnderShift :
    IsStableUnderShift (F.computesRightDerivedObjectProperty S) ℤ where
  isStableUnderShiftBy := fun n ↦ by
    refine ⟨?_⟩
    intro X hX
    letI : F.ComputesRightDerivedAt S X := hX
    letI : F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) :=
      (hasPointwiseRightDerivedFunctorAt_iff_shift F S X n).mp inferInstance
    -- Proof comment: the owner-level stability proof now reduces to the source-faithful local
    -- conjugation formula for the shifted identity leg.
    exact computesRightDerivedAt_of_shift_leg_conjugation
      (F := F) (S := S) (X := X) (n := n)
      (exists_rightDerivedValueShiftIso_with_id_leg
        (F := F) (S := S) (X := X) (n := n))

/-- Objects which compute the left derived functor of `F` form a shift-stable object property. -/
instance computesLeftDerivedAt_isStableUnderShift :
    IsStableUnderShift (F.computesLeftDerivedObjectProperty S) ℤ where
  isStableUnderShiftBy := fun n ↦ by
    refine ⟨?_⟩
    intro X hX
    letI : F.ComputesLeftDerivedAt S X := hX
    letI : F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) :=
      (hasPointwiseLeftDerivedFunctorAt_iff_shift F S X n).mp inferInstance
    -- Proof comment: dually, stability is reduced to the local conjugation formula for the
    -- shifted identity projection.
    exact computesLeftDerivedAt_of_shift_projection_conjugation
      (F := F) (S := S) (X := X) (n := n)
      (exists_leftDerivedValueShiftIso_with_id_projection
        (F := F) (S := S) (X := X) (n := n))

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
