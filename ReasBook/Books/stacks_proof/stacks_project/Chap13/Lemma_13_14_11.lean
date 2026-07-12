import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Lemma_13_14_5
import Mathlib.Tactic.StacksAttribute

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

omit [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ] in
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

omit [HasShift D ℤ] [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ] in
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

omit [S.IsCompatibleWithShift ℤ] in
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

omit [S.IsCompatibleWithShift ℤ] in
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

omit [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ] in
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

omit [S.IsCompatibleWithShift ℤ] in
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

/-- Helper for Chap13 Lemma 13 14 11: in the forward right comma equivalence, the forward image
of the unshifted identity denominator object maps to the shifted identity denominator object by the
identity source morphism. -/
lemma rightDerivedShiftIdentityDenominatorForwardComm :
    let e := rightDerivedShiftForwardEquivalence (S := S) X n
    let j :
        CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let jX :
        CostructuredArrow S.Q (S.Q.obj X) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
    S.Q.map (𝟙 (X⟦n⟧)) ≫ (e.functor.obj jX).hom = j.hom := by
  -- Proof comment: after expanding the forward equivalence one layer, the only remaining
  -- comparison is the localization shift isomorphism composed with its inverse.
  dsimp
  simpa [rightDerivedShiftForwardEquivalence, Localization.isoOfHom_id_inv] using
    (S.Q.commShiftIso n).hom_inv_id_app X

/-- Helper for Chap13 Lemma 13 14 11: transport the shifted right identity denominator object back
across the inverse comma equivalence to the canonical unshifted identity denominator object. -/
noncomputable def rightDerivedShiftIdentityDenominatorHom :
    (rightDerivedShiftIndexFunctor (S := S) X n).obj
        (CostructuredArrow.mk
          ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)) ⟶
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv) :=
  let e := rightDerivedShiftForwardEquivalence (S := S) X n
  let j :
      CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  let jX :
      CostructuredArrow S.Q (S.Q.obj X) :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let β : j ⟶ e.functor.obj jX :=
    CostructuredArrow.homMk (𝟙 (X⟦n⟧))
      (rightDerivedShiftIdentityDenominatorForwardComm (S := S) (X := X) (n := n))
  -- Proof comment: map the forward identity comparison back along the inverse equivalence and
  -- then collapse `e.inverse.obj (e.functor.obj jX)` to `jX` using the unit isomorphism.
  e.inverse.map β ≫ (e.unitIso.app jX).inv

/-- Helper for Chap13 Lemma 13 14 11: the inverse app of the shifted right projection comparison
cancels with the shifted source morphism underlying `rightDerivedShiftIdentityDenominatorHom`. -/
lemma rightDerivedShiftIndexFunctorProjInvApp_shiftIdentityDenominator :
    let j :
        CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let α := rightDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
    ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
        (shiftFunctor D n).map α.left = 𝟙 (X⟦n⟧) := by
  let e := rightDerivedShiftForwardEquivalence (S := S) X n
  let j :
      CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  let jX :
      CostructuredArrow S.Q (S.Q.obj X) :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let β : j ⟶ e.functor.obj jX :=
    CostructuredArrow.homMk (𝟙 (X⟦n⟧))
      (rightDerivedShiftIdentityDenominatorForwardComm (S := S) (X := X) (n := n))
  let α := rightDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
  let α' : e.inverse.obj j ⟶ jX := e.inverse.map β ≫ (e.unitIso.app jX).inv
  have hα : α = α' := by
    rfl
  -- Proof comment: the transported comparison morphism is exactly `β` after cancelling the
  -- unit-counit composite of the comma equivalence.
  have hβ : e.counitIso.inv.app j ≫ e.functor.map α' = β := by
    ext
    simp [α', β, Category.assoc, e.fun_inv_map, e.counitIso_functor_comp]
  have hβα : e.counitIso.inv.app j ≫ e.functor.map α = β := by
    simpa [hα] using hβ
  -- Proof comment: taking source components turns the comma-morphism identity into the desired
  -- equality of source arrows.
  have hleft0 := congrArg (fun φ ↦ φ.left) hβα
  have hleft :
      ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
          (shiftFunctor D n).map α.left = β.left := by
    simpa [e, j, α, rightDerivedShiftIndexFunctor_proj, rightDerivedShiftForwardEquivalence_proj,
      rightDerivedShiftForwardEquivalence, ← Category.assoc] using hleft0
  simpa [β] using hleft

omit [HasShift D' ℤ] [F.CommShift ℤ] in
/-- Helper for Chap13 Lemma 13 14 11: after applying `F`, the right identity-denominator source
transport cancellation becomes the identity on `F.obj (X⟦n⟧)`. -/
lemma map_rightDerivedShiftIndexFunctorProjInvApp_shiftIdentityDenominator :
    let j :
        CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let α := rightDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
    F.map
        (((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
          (shiftFunctor D n).map α.left) = 𝟙 (F.obj (X⟦n⟧)) := by
  -- Proof comment: functoriality transports the source-side identity cancellation into `D'`.
  simpa [Functor.map_id] using
    congrArg
      (fun k ↦ F.map k)
      (rightDerivedShiftIndexFunctorProjInvApp_shiftIdentityDenominator
        (S := S) (X := X) (n := n))

/-- Helper for Chap13 Lemma 13 14 11: at the shifted identity denominator object, the inverse
comparison for the shifted right-derived diagram is the projection comparison followed by the
ambient shift-commutation isomorphism. -/
lemma rightDerivedShiftDiagramIsoInvApp_identityDenominator :
    let j :
        CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    ((rightDerived_shiftDiagramIso (F := F) (S := S) X n).inv.app j) =
      F.map ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
        ((F.commShiftIso n).app (((rightDerivedShiftIndexFunctor (S := S) X n).obj j).left)).hom := by
  -- Proof comment: unfold the composite diagram isomorphism once; objectwise, its inverse is the
  -- inverse projection comparison followed by the whiskered `commShiftIso` component.
  dsimp [rightDerived_shiftDiagramIso]

/-- Helper for Chap13 Lemma 13 14 11: the forward right identity-denominator comparison morphism
acts by the identity on the source object. -/
lemma rightDerivedShiftIdentityDenominatorComparison_left :
    let e := rightDerivedShiftForwardEquivalence (S := S) X n
    let j :
        CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let jX :
        CostructuredArrow S.Q (S.Q.obj X) :=
      CostructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
    let β : j ⟶ e.functor.obj jX :=
      CostructuredArrow.homMk (𝟙 (X⟦n⟧))
        (rightDerivedShiftIdentityDenominatorForwardComm (S := S) (X := X) (n := n))
    β.left = 𝟙 (X⟦n⟧) := by
  rfl

/-- Helper for Chap13 Lemma 13 14 11: the identity-denominator component of the shifted
right-derived cocone is the shifted original identity leg composed with `F.commShiftIso`. -/
lemma rightDerived_shifted_cocone_app_identityDenominator
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    (rightDerived_shifted_cocone (F := F) (S := S) X n).ι.app
        (CostructuredArrow.mk
          ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)) =
      ((F.commShiftIso n).app X).hom ≫
        (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let _ : HasColimit RX :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let j :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  let jX :
      CostructuredArrow S.Q (S.Q.obj X) :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let α := rightDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
  -- Route correction: the proof now normalizes the full transported component, not the bare
  -- bridge morphism `α`, so the remaining source transport cancels against the diagram iso.
  -- Proof comment: expand the shifted cocone one layer so the component is the diagram-iso
  -- transport followed by the shifted whiskered colimit leg.
  simp only [rightDerived_shifted_cocone, Cocone.precompose_obj_ι]
  rw [NatTrans.comp_app, Functor.mapCocone_ι_app, Cocone.whisker_ι, Functor.whiskerLeft_app]
  -- Proof comment: naturality of the original colimit cocone along `α` replaces the whiskered
  -- leg by the canonical identity leg at `X`.
  have hleg :
      (shiftFunctor D' n).map ((colimit.cocone RX).ι.app ((rightDerivedShiftIndexFunctor
          (S := S) X n).obj j)) =
        (shiftFunctor D' n).map (RX.map α) ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
    simpa [RX, jX, rightDerivedValueLeg, Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ (shiftFunctor D' n).map k) ((colimit.w RX α).symm)
  have hleg' :
      (shiftFunctor D' n).map
          ((colimit.cocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)).ι.app
            ((rightDerivedShiftIndexFunctor (S := S) X n).obj j)) =
        (shiftFunctor D' n).map ((CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F).map α) ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
    simpa [RX] using hleg
  have hstep :
      (rightDerived_shiftDiagramIso (F := F) (S := S) X n).inv.app j ≫
          (shiftFunctor D' n).map
            ((colimit.cocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)).ι.app
              ((rightDerivedShiftIndexFunctor (S := S) X n).obj j)) =
        (rightDerived_shiftDiagramIso (F := F) (S := S) X n).inv.app j ≫
          ((shiftFunctor D' n).map ((CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F).map α) ≫
            (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) := by
    exact congrArg
      (fun k ↦ (rightDerived_shiftDiagramIso (F := F) (S := S) X n).inv.app j ≫ k) hleg'
  -- TODO: normalize the residual factor in `D'` using the objectwise formula for
  -- `rightDerived_shiftDiagramIso.inv.app j`, `Functor.commShiftIso_hom_naturality`, and the
  -- mapped source-side cancellation lemma
  -- `map_rightDerivedShiftIndexFunctorProjInvApp_shiftIdentityDenominator`.
  have hcomm :
      ((F.commShiftIso n).app (((rightDerivedShiftIndexFunctor (S := S) X n).obj j).left)).hom ≫
          (shiftFunctor D' n).map (F.map α.left) =
        F.map ((shiftFunctor D n).map α.left) ≫ ((F.commShiftIso n).app X).hom := by
    -- Proof comment: this is exactly the naturality square for `F.commShiftIso` on `α.left`.
    simpa using (Functor.commShiftIso_hom_naturality (F := F) α.left n).symm
  have hcommExpanded := by
    simpa only [j] using hcomm
  have hstepExpanded := by
    simpa only [j] using hstep
  -- Proof comment: rewrite the diagram comparison, move the shifted map across
  -- `F.commShiftIso`, and collapse the mapped source-side transport to the identity.
  refine hstepExpanded.trans ?_
  rw [rightDerivedShiftDiagramIsoInvApp_identityDenominator (F := F) (S := S) (X := X) (n := n)]
  simp only [Functor.comp_obj, CostructuredArrow.proj_obj, CostructuredArrow.mk_left,
    colimit.cocone_x, Functor.const_obj_obj, Iso.app_hom, Functor.comp_map,
    CostructuredArrow.proj_map, Category.assoc]
  have htransport :
      F.map ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
          ((F.commShiftIso n).app (((rightDerivedShiftIndexFunctor (S := S) X n).obj j).left)).hom ≫
          (shiftFunctor D' n).map (F.map α.left) ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) =
        F.map
            (((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
              (shiftFunctor D n).map α.left) ≫
          ((F.commShiftIso n).app X).hom ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
    calc
      F.map ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
          ((F.commShiftIso n).app (((rightDerivedShiftIndexFunctor (S := S) X n).obj j).left)).hom ≫
          (shiftFunctor D' n).map (F.map α.left) ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) =
        F.map ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
          ((((F.commShiftIso n).app (((rightDerivedShiftIndexFunctor (S := S) X n).obj j).left)).hom ≫
              (shiftFunctor D' n).map (F.map α.left)) ≫
            (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) := by
        simp [Category.assoc]
      _ =
        F.map ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
          ((F.map ((shiftFunctor D n).map α.left) ≫ ((F.commShiftIso n).app X).hom) ≫
            (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ F.map ((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
              k ≫ (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))) hcomm
      _ =
        F.map
            (((rightDerivedShiftIndexFunctor_proj (S := S) X n).inv.app j) ≫
              (shiftFunctor D n).map α.left) ≫
          ((F.commShiftIso n).app X).hom ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
        simp [Functor.map_comp, Category.assoc]
  exact htransport.trans <| by
    rw [map_rightDerivedShiftIndexFunctorProjInvApp_shiftIdentityDenominator
      (F := F) (S := S) (X := X) (n := n)]
    exact
      Category.id_comp
        (((F.commShiftIso n).app X).hom ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)))

/-- Helper for Lemma 13.14.11: the canonical shift comparison for pointwise right-derived values
can be chosen so that it conjugates the identity-denominator leg by `F.commShiftIso`. -/
lemma exists_rightDerivedValueShiftIso_with_id_leg
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    ∃ i : rightDerivedValue S F (X⟦n⟧) ≅ ((rightDerivedValue S F X)⟦n⟧),
      rightDerivedValueLeg S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫ i.hom =
        ((F.commShiftIso n).app X).hom ≫
          (shiftFunctor D' n).map (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
  let i := rightDerivedValueShiftIso (F := F) (S := S) X n
  let shifted := rightDerived_shifted_cocone (F := F) (S := S) X n
  let RY := CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F
  let _ : HasColimit RY :=
    Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S (X⟦n⟧)
  let hc : IsColimit shifted :=
    rightDerived_shifted_cocone_isColimit (F := F) (S := S) X n
  let j :
      CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
    CostructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  refine ⟨i, ?_⟩
  -- Proof comment: the universal comparison identifies the canonical identity leg at `X⟦n⟧`
  -- with the identity component of the shifted cocone, and that shifted component is explicit.
  have hleg :
      rightDerivedValueLeg S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫ i.hom =
        shifted.ι.app j := by
    -- Proof comment: this is the canonical colimit comparison for the shifted cocone.
    simpa [i, rightDerivedValueShiftIso, shifted, RY, j, rightDerivedValueLeg,
      Localization.isoOfHom_id_inv] using
      (colimit.comp_coconePointUniqueUpToIso_inv (F := RY) (c := shifted) hc j)
  exact hleg.trans (rightDerived_shifted_cocone_app_identityDenominator
    (F := F) (S := S) (X := X) (n := n))

/-- Helper for Chap13 Lemma 13 14 11: in the forward left structured-arrow equivalence, the
forward image of the unshifted identity denominator object maps to the shifted identity
denominator object by the identity source morphism. -/
lemma leftDerivedShiftIdentityDenominatorForwardComm :
    let e := leftDerivedShiftForwardEquivalence (S := S) X n
    let j :
        StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let jX :
        StructuredArrow (S.Q.obj X) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
    (e.functor.obj jX).hom ≫ S.Q.map (𝟙 (X⟦n⟧)) = j.hom := by
  -- Proof comment: the structured-arrow side has the same forward normalization, again reducing
  -- to the localization shift isomorphism composed with its inverse.
  dsimp
  simpa [leftDerivedShiftForwardEquivalence, Localization.isoOfHom_id_inv] using
    (S.Q.commShiftIso n).hom_inv_id_app X

/-- Helper for Chap13 Lemma 13 14 11: transport the unshifted left identity denominator object
forward through the inverse structured-arrow equivalence to the shifted indexing object. -/
noncomputable def leftDerivedShiftIdentityDenominatorHom :
    StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv) ⟶
      (leftDerivedShiftIndexFunctor (S := S) X n).obj
        (StructuredArrow.mk
          ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)) :=
  let e := leftDerivedShiftForwardEquivalence (S := S) X n
  let j :
      StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  let jX :
      StructuredArrow (S.Q.obj X) S.Q :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let β : e.functor.obj jX ⟶ j :=
    StructuredArrow.homMk (𝟙 (X⟦n⟧))
      (leftDerivedShiftIdentityDenominatorForwardComm (S := S) (X := X) (n := n))
  -- Proof comment: move the forward identity comparison back across the inverse equivalence and
  -- then identify the resulting inverse-image object with `jX` through the unit isomorphism.
  (e.unitIso.app jX).hom ≫ e.inverse.map β

/-- Helper for Chap13 Lemma 13 14 11: the shifted source morphism underlying
`leftDerivedShiftIdentityDenominatorHom` cancels with the hom app of the left projection
comparison. -/
lemma leftDerivedShiftIndexFunctorProjHomApp_shiftIdentityDenominator :
    let j :
        StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let α := leftDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
    (shiftFunctor D n).map α.right ≫
        ((leftDerivedShiftIndexFunctor_proj (S := S) X n).hom.app j) = 𝟙 (X⟦n⟧) := by
  let e := leftDerivedShiftForwardEquivalence (S := S) X n
  let j :
      StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  let jX :
      StructuredArrow (S.Q.obj X) S.Q :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let β : e.functor.obj jX ⟶ j :=
    StructuredArrow.homMk (𝟙 (X⟦n⟧))
      (leftDerivedShiftIdentityDenominatorForwardComm (S := S) (X := X) (n := n))
  let α := leftDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
  let α' : jX ⟶ e.inverse.obj j := (e.unitIso.app jX).hom ≫ e.inverse.map β
  have hα : α = α' := by
    rfl
  -- Proof comment: dually, the transported comparison is `β` after cancelling the
  -- unit-counit composite of the structured-arrow equivalence.
  have hβ : e.functor.map α' ≫ e.counitIso.hom.app j = β := by
    ext
    simp [α', β, Category.assoc, e.fun_inv_map]
  have hβα : e.functor.map α ≫ e.counitIso.hom.app j = β := by
    simpa [hα] using hβ
  -- Proof comment: taking target components converts the structured-arrow equality into the
  -- required equality of shifted source arrows.
  have hright0 := congrArg (fun φ ↦ φ.right) hβα
  have hright :
      (shiftFunctor D n).map α.right ≫
          ((leftDerivedShiftIndexFunctor_proj (S := S) X n).hom.app j) = β.right := by
    simpa [e, j, α, leftDerivedShiftIndexFunctor_proj, leftDerivedShiftForwardEquivalence_proj,
      leftDerivedShiftForwardEquivalence, ← Category.assoc] using hright0
  simpa [β] using hright

omit [HasShift D' ℤ] [F.CommShift ℤ] in
/-- Helper for Chap13 Lemma 13 14 11: after applying `F`, the left identity-denominator source
transport cancellation becomes the identity on `F.obj (X⟦n⟧)`. -/
lemma map_leftDerivedShiftIndexFunctorProjHomApp_shiftIdentityDenominator :
    let j :
        StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let α := leftDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
    F.map
        ((shiftFunctor D n).map α.right ≫
          ((leftDerivedShiftIndexFunctor_proj (S := S) X n).hom.app j)) =
      𝟙 (F.obj (X⟦n⟧)) := by
  -- Proof comment: functoriality transports the dual source-side identity cancellation into `D'`.
  simpa [Functor.map_id] using
    congrArg
      (fun k ↦ F.map k)
      (leftDerivedShiftIndexFunctorProjHomApp_shiftIdentityDenominator
        (S := S) (X := X) (n := n))

/-- Helper for Chap13 Lemma 13 14 11: at the shifted identity denominator object, the forward
comparison for the shifted left-derived diagram is the ambient inverse `commShiftIso` component
followed by the projection comparison. -/
lemma leftDerivedShiftDiagramIsoHomApp_identityDenominator :
    let j :
        StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    ((leftDerived_shiftDiagramIso (F := F) (S := S) X n).hom.app j) =
      ((F.commShiftIso n).app (((leftDerivedShiftIndexFunctor (S := S) X n).obj j).right)).inv ≫
        F.map ((leftDerivedShiftIndexFunctor_proj (S := S) X n).hom.app j) := by
  -- Proof comment: unfold the composite diagram isomorphism once; objectwise, its forward map
  -- is the whiskered inverse `commShiftIso` component followed by the projection comparison.
  dsimp [leftDerived_shiftDiagramIso]

/-- Helper for Chap13 Lemma 13 14 11: the forward left identity-denominator comparison morphism
acts by the identity on the source object. -/
lemma leftDerivedShiftIdentityDenominatorComparison_right :
    let e := leftDerivedShiftForwardEquivalence (S := S) X n
    let j :
        StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
    let jX :
        StructuredArrow (S.Q.obj X) S.Q :=
      StructuredArrow.mk
        ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
    let β : e.functor.obj jX ⟶ j :=
      StructuredArrow.homMk (𝟙 (X⟦n⟧))
        (leftDerivedShiftIdentityDenominatorForwardComm (S := S) (X := X) (n := n))
    β.right = 𝟙 (X⟦n⟧) := by
  rfl

/-- Helper for Chap13 Lemma 13 14 11: the identity-denominator component of the shifted
left-derived cone is the shifted original identity projection followed by the inverse
`F.commShiftIso`. -/
lemma leftDerived_shifted_cone_app_identityDenominator
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    (leftDerived_shifted_cone (F := F) (S := S) X n).π.app
        (StructuredArrow.mk
          ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)) =
      (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
        ((F.commShiftIso n).app X).inv := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let _ : HasLimit LX :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let j :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  let jX :
      StructuredArrow (S.Q.obj X) S.Q :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)
  let α := leftDerivedShiftIdentityDenominatorHom (S := S) (X := X) (n := n)
  -- Route correction: the proof now rewrites the full transported projection composite, so the
  -- source-side transport cancels against `leftDerived_shiftDiagramIso.hom`.
  -- Proof comment: expand the shifted cone one layer so the component is the shifted whiskered
  -- limit projection followed by the diagram-iso transport.
  simp only [leftDerived_shifted_cone, Cone.postcompose_obj_π]
  rw [NatTrans.comp_app, Functor.mapCone_π_app, Cone.whisker_π, Functor.whiskerLeft_app]
  -- Proof comment: naturality of the original limit cone along `α` replaces the whiskered
  -- projection by the canonical identity projection at `X`.
  have hproj :
      (shiftFunctor D' n).map ((limit.cone LX).π.app ((leftDerivedShiftIndexFunctor
          (S := S) X n).obj j)) =
        (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
          (shiftFunctor D' n).map (LX.map α) := by
    simpa [LX, jX, leftDerivedValueProjection, Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ (shiftFunctor D' n).map k) ((limit.w LX α).symm)
  have hproj' :
      (shiftFunctor D' n).map
          ((limit.cone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)).π.app
            ((leftDerivedShiftIndexFunctor (S := S) X n).obj j)) =
        (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
          (shiftFunctor D' n).map ((StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F).map α) := by
    simpa [LX] using hproj
  have hstep :
      (shiftFunctor D' n).map
          ((limit.cone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)).π.app
            ((leftDerivedShiftIndexFunctor (S := S) X n).obj j)) ≫
          (leftDerived_shiftDiagramIso (F := F) (S := S) X n).hom.app j =
        ((shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
            (shiftFunctor D' n).map ((StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F).map α)) ≫
          (leftDerived_shiftDiagramIso (F := F) (S := S) X n).hom.app j := by
    exact congrArg
      (fun k ↦ k ≫ (leftDerived_shiftDiagramIso (F := F) (S := S) X n).hom.app j) hproj'
  -- TODO: normalize the residual factor in `D'` using the objectwise formula for
  -- `leftDerived_shiftDiagramIso.hom.app j`, `Functor.commShiftIso_inv_naturality`, and the
  -- mapped source-side cancellation lemma
  -- `map_leftDerivedShiftIndexFunctorProjHomApp_shiftIdentityDenominator`.
  have hcomm :
      (shiftFunctor D' n).map (F.map α.right) ≫
          ((F.commShiftIso n).app (((leftDerivedShiftIndexFunctor (S := S) X n).obj j).right)).inv =
        ((F.commShiftIso n).app X).inv ≫ F.map ((shiftFunctor D n).map α.right) := by
    -- Proof comment: this is the dual naturality square for `F.commShiftIso` on `α.right`.
    simpa using (Functor.commShiftIso_inv_naturality (F := F) α.right n)
  have hcommExpanded := by
    simpa only [j] using hcomm
  have hstepExpanded := by
    simpa only [j] using hstep
  -- Proof comment: rewrite the diagram comparison, commute the shifted map past
  -- `F.commShiftIso.inv`, and collapse the mapped source-side transport to the identity.
  refine hstepExpanded.trans ?_
  rw [leftDerivedShiftDiagramIsoHomApp_identityDenominator
    (F := F) (S := S) (X := X) (n := n)]
  simp only [limit.cone_x, Functor.const_obj_obj, Functor.comp_obj, StructuredArrow.proj_obj,
    StructuredArrow.mk_right, Functor.comp_map, StructuredArrow.proj_map, Iso.app_inv,
    Category.assoc, Functor.commShiftIso_inv_naturality_assoc]
  have hcancel :
      F.map
          ((shiftFunctor D n).map α.right ≫
            ((leftDerivedShiftIndexFunctor_proj (S := S) X n).hom.app j)) =
        𝟙 (F.obj (X⟦n⟧)) := by
    simpa only [α, j] using
      map_leftDerivedShiftIndexFunctorProjHomApp_shiftIdentityDenominator
        (F := F) (S := S) (X := X) (n := n)
  have hcancelExpanded := by
    simpa only [j] using hcancel
  rw [← Functor.map_comp]
  have hcancelPost :
      (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
          ((F.commShiftIso n).app X).inv ≫
          F.map
            ((shiftFunctor D n).map α.right ≫
              (leftDerivedShiftIndexFunctor_proj (S := S) X n).hom.app
                (StructuredArrow.mk
                  ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv))) =
        (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
          ((F.commShiftIso n).app X).inv ≫
          𝟙 (F.obj (X⟦n⟧)) := by
    exact
      congrArg
        (fun k ↦ (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
          ((F.commShiftIso n).app X).inv ≫ k)
        hcancelExpanded
  simpa [Category.assoc] using hcancelPost

/-- Helper for Lemma 13.14.11: the canonical shift comparison for pointwise left-derived values
can be chosen so that it conjugates the identity-denominator projection by `F.commShiftIso`. -/
lemma exists_leftDerivedValueShiftIso_with_id_projection
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    ∃ i : leftDerivedValue S F (X⟦n⟧) ≅ ((leftDerivedValue S F X)⟦n⟧),
      i.hom ≫ (shiftFunctor D' n).map
          (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) =
        leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom := by
  let i := leftDerivedValueShiftIso (F := F) (S := S) X n
  let shifted := leftDerived_shifted_cone (F := F) (S := S) X n
  let LY := StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F
  let _ : HasLimit LY :=
    Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S (X⟦n⟧)
  let hc : IsLimit shifted :=
    leftDerived_shifted_cone_isLimit (F := F) (S := S) X n
  let j :
      StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
    StructuredArrow.mk
      ((Localization.isoOfHom S.Q S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧))).inv)
  refine ⟨i, ?_⟩
  -- Proof comment: the universal comparison identifies `i.inv` with the shifted cone component
  -- at the identity denominator object, and the component formula above converts that component
  -- into the shifted original projection conjugated by `F.commShiftIso`.
  have hcomp :
      i.inv ≫ leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) =
        shifted.π.app j := by
    simpa [i, leftDerivedValueShiftIso, shifted, LY, j, leftDerivedValueProjection,
      Localization.isoOfHom_id_inv] using
      (hc.conePointUniqueUpToIso_hom_comp (limit.isLimit LY) j)
  have hproj :
      i.inv ≫ leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) =
        (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
          ((F.commShiftIso n).app X).inv := by
    exact hcomp.trans (leftDerived_shifted_cone_app_identityDenominator
      (F := F) (S := S) (X := X) (n := n))
  have hpost :
      i.inv ≫ leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom =
        (shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
    -- Proof comment: postcompose by `((F.commShiftIso n).app X).hom` to cancel the inverse
    -- shift comparison from the component formula.
    calc
      i.inv ≫ leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom =
          ((shiftFunctor D' n).map (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫
            ((F.commShiftIso n).app X).inv) ≫
              ((F.commShiftIso n).app X).hom := by
        rw [← Category.assoc, hproj]
        simp [Category.assoc]
      _ = (shiftFunctor D' n).map
          (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (shiftFunctor D' n).map
              (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) ≫ k)
            (((F.commShiftIso n).app X).inv_hom_id)
  have hfinal :
      leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom =
        i.hom ≫ (shiftFunctor D' n).map
          (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
    -- Proof comment: now precompose by `i.hom`, so the universal-comparison inverse cancels and
    -- the target conjugation appears with the requested orientation.
    calc
      leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
          ((F.commShiftIso n).app X).hom =
          i.hom ≫
            (i.inv ≫ leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
              ((F.commShiftIso n).app X).hom) := by
        simpa [Category.assoc] using
          i.hom_inv_id_assoc
            (leftDerivedValueProjection S F (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
              ((F.commShiftIso n).app X).hom)
      _ = i.hom ≫ (shiftFunctor D' n).map
          (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
        rw [hpost]
        rfl
  exact hfinal.symm

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
/-- Chap13 Lemma 13 14 11 (1): if the morphism property `S` and the functor `F` are compatible with
shifts, then `X` computes the right derived functor of `F` with respect to `S` if and only if
`X⟦n⟧` does. -/
@[stacks 05SY]
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
@[stacks 05SY]
theorem computesLeftDerivedAt_iff_shift
    [HasShift D' ℤ] [S.IsCompatibleWithShift ℤ] [F.CommShift ℤ]
    : F.ComputesLeftDerivedAt S X ↔
      F.ComputesLeftDerivedAt S (X⟦n⟧) := by
  simpa using
    ((F.computesLeftDerivedObjectProperty S).prop_shift_iff_of_isStableUnderShift X n).symm

end

end CategoryTheory
