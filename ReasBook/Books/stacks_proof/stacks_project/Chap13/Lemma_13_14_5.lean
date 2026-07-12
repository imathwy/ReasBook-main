import Mathlib
import StacksProject_2024.Chap13.Lemma_13_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

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
  refine ⟨?_⟩
  intro X Y e hX
  -- Proof comment: transport the defining colimit cocone along `S.Q.mapIso e`.
  letI : F.HasPointwiseRightDerivedFunctorAt S X := hX
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let RY := CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F
  letI : HasColimit RX := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let eQ : S.Q.obj X ≅ S.Q.obj Y := S.Q.mapIso e
  let transported : Cocone RY := (colimit.cocone RX).whisker (CostructuredArrow.mapIso eQ).symm.functor
  have htransported : IsColimit transported := by
    -- Proof comment: the whiskered cocone is still colimiting because `CostructuredArrow.mapIso`
    -- is an equivalence of indexing categories.
    simpa [RX, RY, transported] using
      (colimit.isColimit RX).whiskerEquivalence (CostructuredArrow.mapIso eQ).symm
  exact ⟨⟨transported, htransported⟩⟩

/-- The predicate `X ↦ F.HasPointwiseLeftDerivedFunctorAt S X` is invariant under isomorphism of
objects. -/
instance leftDerivedDefinedObjectProperty_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (leftDerivedDefinedObjectProperty F S) := by
  refine ⟨?_⟩
  intro X Y e hX
  -- Proof comment: transport the defining limit cone along `S.Q.mapIso e`.
  letI : F.HasPointwiseLeftDerivedFunctorAt S X := hX
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  letI : HasLimit LX := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let eQ : S.Q.obj X ≅ S.Q.obj Y := S.Q.mapIso e
  let transported : Cone LY := (limit.cone LX).whisker (StructuredArrow.mapIso eQ).symm.functor
  have htransported : IsLimit transported := by
    -- Proof comment: the whiskered cone is still limiting because `StructuredArrow.mapIso`
    -- is an equivalence of indexing categories.
    simpa [LX, LY, transported] using
      (limit.isLimit LX).whiskerEquivalence (StructuredArrow.mapIso eQ).symm
  exact ⟨⟨transported, htransported⟩⟩

end

section RightShift

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- Helper for Lemma 13.14.5: after shifting the source, the composite
`shiftFunctor 𝒟 n ⋙ S.Q` is still a localization functor for `S`. -/
noncomputable instance shiftCompLocalization_isLocalization
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (n : ℤ) :
    (shiftFunctor 𝒟 n ⋙ S.Q).IsLocalization S := by
  -- Proof comment: the localization functor also commutes with shifts, so shifting the source
  -- localization is isomorphic to postcomposing `S.Q` with the induced shift equivalence.
  letI : (S.Q ⋙ shiftFunctor S.Localization n).IsLocalization S := inferInstance
  exact Functor.IsLocalization.of_iso (W := S) (S.Q.commShiftIso n).symm

/-- Helper for Lemma 13.14.5: shifting the right comma diagram at `X` produces an equivalence with
the literal right comma diagram at `X⟦n⟧`. -/
noncomputable def rightDerivedShiftForwardEquivalence
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    CostructuredArrow S.Q (S.Q.obj X) ≌ CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
  -- Proof comment: shift the target of the comma diagram, rewrite the shifted localization by
  -- `S.Q.commShiftIso`, and then use the source shift equivalence to return to the original owner
  -- functor `S.Q`.
  (Functor.asEquivalence
      (CostructuredArrow.post S.Q (shiftFunctor S.Localization n) (S.Q.obj X))).trans
    ((CostructuredArrow.mapNatIso (S.Q.commShiftIso n).symm).trans
      ((CostructuredArrow.mapIso ((S.Q.commShiftIso n).app X).symm).trans
        (CostructuredArrow.pre (shiftFunctor 𝒟 n) S.Q (S.Q.obj (X⟦n⟧))).asEquivalence))

/-- Helper for Lemma 13.14.5: the inverse of the forward right comma equivalence is the
source-side reindexing functor used in the shifted colimit construction. -/
noncomputable def rightDerivedShiftIndexFunctor
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) ⥤ CostructuredArrow S.Q (S.Q.obj X) :=
  (rightDerivedShiftForwardEquivalence (S := S) X n).inverse

/-- Helper for Lemma 13.14.5: the forward right comma equivalence projects to the source shift. -/
noncomputable def rightDerivedShiftForwardEquivalence_proj
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    (rightDerivedShiftForwardEquivalence (S := S) X n).functor ⋙
        CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ≅
      CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ shiftFunctor 𝒟 n := by
  -- Proof comment: every step of the forward equivalence preserves the source object except for
  -- the final `pre`, which applies the shift functor to that source object.
  refine NatIso.ofComponents (fun g ↦ Iso.refl _) ?_
  intro g g' φ
  simp [rightDerivedShiftForwardEquivalence]

/-- Helper for Lemma 13.14.5: reindexing the right comma diagram for `X⟦n⟧` and then projecting
matches the literal projection after shifting the source. -/
noncomputable def rightDerivedShiftIndexFunctor_proj
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    rightDerivedShiftIndexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ shiftFunctor 𝒟 n ≅
      CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) := by
  let e := rightDerivedShiftForwardEquivalence (S := S) X n
  -- Proof comment: whisker the forward projection comparison by the inverse equivalence and then
  -- collapse the resulting `e.inverse ⋙ e.functor` using the counit.
  calc
    e.inverse ⋙ CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ shiftFunctor 𝒟 n ≅
        e.inverse ⋙ e.functor ⋙ CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) := by
      simpa [e, rightDerivedShiftIndexFunctor, Functor.associator] using
        Functor.isoWhiskerLeft e.inverse
          (rightDerivedShiftForwardEquivalence_proj (S := S) X n).symm
    _ ≅ CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) := by
      simpa [Functor.associator] using
        Functor.isoWhiskerRight e.counitIso (CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)))

/-- Helper for Lemma 13.14.5: after source reindexing and target shift, the right-derived
diagram for `X` identifies with the literal right-derived diagram for `X⟦n⟧`. -/
noncomputable def rightDerived_shiftDiagramIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) :
    rightDerivedShiftIndexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor 𝒟' n ≅
      CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F := by
  -- Proof comment: first rewrite the target shift across `F`, then collapse the source
  -- reindexing by the explicit comma-diagram projection comparison.
  calc
    rightDerivedShiftIndexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor 𝒟' n ≅
      rightDerivedShiftIndexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ shiftFunctor 𝒟 n ⋙ F := by
      simpa [Functor.associator] using
        Functor.isoWhiskerLeft
          (rightDerivedShiftIndexFunctor (S := S) X n ⋙
            CostructuredArrow.proj S.Q (S.Q.obj X))
          (F.commShiftIso n).symm
    _ ≅ CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F := by
      simpa [Functor.associator] using
        Functor.isoWhiskerRight (rightDerivedShiftIndexFunctor_proj (S := S) X n) F

/-- Helper for Lemma 13.14.5: transport the defining right-derived colimit cocone at `X`
through shift and the comma-diagram equivalence to a cocone on the literal diagram at `X⟦n⟧`. -/
noncomputable def rightDerived_shifted_cocone
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) [F.HasPointwiseRightDerivedFunctorAt S X] :
    Cocone (CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F) :=
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let hRX : HasColimit RX := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let c :
      Cocone
        (rightDerivedShiftIndexFunctor (S := S) X n ⋙
          CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor 𝒟' n) :=
    (shiftFunctor 𝒟' n).mapCocone
      ((@colimit.cocone _ _ _ _ RX hRX).whisker
        (rightDerivedShiftIndexFunctor (S := S) X n))
  (Cocone.precompose (rightDerived_shiftDiagramIso (F := F) (S := S) X n).inv).obj c

/-- Helper for Lemma 13.14.5: the shifted right-derived cocone on the literal diagram for
`X⟦n⟧` is colimiting. -/
noncomputable def rightDerived_shifted_cocone_isColimit
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) [F.HasPointwiseRightDerivedFunctorAt S X] :
    IsColimit (rightDerived_shifted_cocone (F := F) (S := S) X n) := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let e := rightDerivedShiftForwardEquivalence (S := S) X n
  let hRX : HasColimit RX := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S X
  let c : Cocone
      (rightDerivedShiftIndexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor 𝒟' n) :=
    (shiftFunctor 𝒟' n).mapCocone
      ((@colimit.cocone _ _ _ _ RX hRX).whisker (rightDerivedShiftIndexFunctor (S := S) X n))
  -- Proof comment: whisker the old colimit across the comma-category equivalence, then use that
  -- shifts preserve colimits, and finally transport along the literal diagram isomorphism.
  have hc₀ :
      IsColimit ((@colimit.cocone _ _ _ _ RX hRX).whisker (rightDerivedShiftIndexFunctor (S := S) X n)) := by
    simpa [e, rightDerivedShiftIndexFunctor] using
      (@colimit.isColimit _ _ _ _ RX hRX).whiskerEquivalence e.symm
  have hc : IsColimit c := by
    simpa [c] using isColimitOfPreserves (shiftFunctor 𝒟' n) hc₀
  change IsColimit
    ((Cocone.precompose (rightDerived_shiftDiagramIso (F := F) (S := S) X n).inv).obj c)
  exact
    (IsColimit.precomposeInvEquiv (rightDerived_shiftDiagramIso (F := F) (S := S) X n) c).symm hc

instance rightDerivedDefinedObjectProperty_isStableUnderShift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (rightDerivedDefinedObjectProperty F S) ℤ := by
  refine ⟨fun n ↦ ?_⟩
  refine ⟨?_⟩
  intro X hX
  let _ : F.HasPointwiseRightDerivedFunctorAt S X := hX
  -- Proof comment: the shifted right-derived cocone constructed above supplies the defining
  -- colimit datum for `X⟦n⟧`.
  exact ⟨⟨rightDerived_shifted_cocone (F := F) (S := S) X n,
    rightDerived_shifted_cocone_isColimit (F := F) (S := S) X n⟩⟩

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
@[stacks 05SU]
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
@[stacks 05SU]
noncomputable def rightDerivedValueShiftIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    rightDerivedValue S F (X⟦n⟧) ≅ ((rightDerivedValue S F X)⟦n⟧) := by
  let shifted := rightDerived_shifted_cocone (F := F) (S := S) X n
  let RY := CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F
  let hc : IsColimit shifted :=
    rightDerived_shifted_cocone_isColimit (F := F) (S := S) X n
  let hshifted : F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := ⟨⟨shifted, hc⟩⟩
  let _ : F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := hshifted
  let hRY : HasColimit RY := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S (X⟦n⟧)
  -- Proof comment: compare the explicit shifted colimit cocone with the canonical colimit cocone
  -- on the literal diagram for `X⟦n⟧`.
  exact (hc.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ RY hRY)).symm

end RightShiftIso

section LeftShift

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- Helper for Lemma 13.14.5: shifting the left comma diagram at `X` produces an equivalence with
the literal left comma diagram at `X⟦n⟧`. -/
noncomputable def leftDerivedShiftForwardEquivalence
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    StructuredArrow (S.Q.obj X) S.Q ≌ StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
  -- Proof comment: this is the dual structured-arrow version of the right-side reindexing
  -- equivalence above.
  (Functor.asEquivalence
      (StructuredArrow.post (S.Q.obj X) S.Q (shiftFunctor S.Localization n))).trans
    ((StructuredArrow.mapNatIso (S.Q.commShiftIso n).symm).trans
      ((StructuredArrow.mapIso ((S.Q.commShiftIso n).app X).symm).trans
        (StructuredArrow.pre (S.Q.obj (X⟦n⟧)) (shiftFunctor 𝒟 n) S.Q).asEquivalence))

/-- Helper for Lemma 13.14.5: the inverse of the forward left comma equivalence is the
source-side reindexing functor used in the shifted limit construction. -/
noncomputable def leftDerivedShiftIndexFunctor
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q ⥤ StructuredArrow (S.Q.obj X) S.Q :=
  (leftDerivedShiftForwardEquivalence (S := S) X n).inverse

/-- Helper for Lemma 13.14.5: the forward left comma equivalence projects to the source shift. -/
noncomputable def leftDerivedShiftForwardEquivalence_proj
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    (leftDerivedShiftForwardEquivalence (S := S) X n).functor ⋙
        StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ≅
      StructuredArrow.proj (S.Q.obj X) S.Q ⋙ shiftFunctor 𝒟 n := by
  -- Proof comment: on the left-derived side the source object is again shifted only by the final
  -- `pre`, so the projection comparison is objectwise the identity isomorphism.
  refine NatIso.ofComponents (fun g ↦ Iso.refl _) ?_
  intro g g' φ
  simp [leftDerivedShiftForwardEquivalence]

/-- Helper for Lemma 13.14.5: reindexing the left comma diagram for `X⟦n⟧` and then projecting
matches the literal projection after shifting the source. -/
noncomputable def leftDerivedShiftIndexFunctor_proj
    [HasShift 𝒟 ℤ] [S.IsCompatibleWithShift ℤ] (X : 𝒟) (n : ℤ) :
    leftDerivedShiftIndexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ shiftFunctor 𝒟 n ≅
      StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q := by
  let e := leftDerivedShiftForwardEquivalence (S := S) X n
  -- Proof comment: this is the dual counit reduction of the forward projection comparison.
  calc
    e.inverse ⋙ StructuredArrow.proj (S.Q.obj X) S.Q ⋙ shiftFunctor 𝒟 n ≅
        e.inverse ⋙ e.functor ⋙ StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q := by
      simpa [e, leftDerivedShiftIndexFunctor, Functor.associator] using
        Functor.isoWhiskerLeft e.inverse
          (leftDerivedShiftForwardEquivalence_proj (S := S) X n).symm
    _ ≅ StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q := by
      simpa [Functor.associator] using
        Functor.isoWhiskerRight e.counitIso (StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q)

/-- Helper for Lemma 13.14.5: after source reindexing and target shift, the left-derived diagram
for `X` identifies with the literal left-derived diagram for `X⟦n⟧`. -/
noncomputable def leftDerived_shiftDiagramIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) :
    leftDerivedShiftIndexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor 𝒟' n ≅
      StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F := by
  -- Proof comment: this is the dual of the right-derived diagram comparison above.
  calc
    leftDerivedShiftIndexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor 𝒟' n ≅
      leftDerivedShiftIndexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ shiftFunctor 𝒟 n ⋙ F := by
      simpa [Functor.associator] using
        Functor.isoWhiskerLeft
          (leftDerivedShiftIndexFunctor (S := S) X n ⋙
            StructuredArrow.proj (S.Q.obj X) S.Q)
          (F.commShiftIso n).symm
    _ ≅ StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F := by
      simpa [Functor.associator] using
        Functor.isoWhiskerRight (leftDerivedShiftIndexFunctor_proj (S := S) X n) F

/-- Helper for Lemma 13.14.5: transport the defining left-derived limit cone at `X`
through shift and the comma-diagram equivalence to a cone on the literal diagram at `X⟦n⟧`. -/
noncomputable def leftDerived_shifted_cone
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    Cone (StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F) :=
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let hLX : HasLimit LX := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let c :
      Cone
        (leftDerivedShiftIndexFunctor (S := S) X n ⋙
          StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor 𝒟' n) :=
    (shiftFunctor 𝒟' n).mapCone
      ((@limit.cone _ _ _ _ LX hLX).whisker
        (leftDerivedShiftIndexFunctor (S := S) X n))
  (Cone.postcompose (leftDerived_shiftDiagramIso (F := F) (S := S) X n).hom).obj c

/-- Helper for Lemma 13.14.5: the shifted left-derived cone on the literal diagram for `X⟦n⟧`
is limiting. -/
noncomputable def leftDerived_shifted_cone_isLimit
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    IsLimit (leftDerived_shifted_cone (F := F) (S := S) X n) := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let e := leftDerivedShiftForwardEquivalence (S := S) X n
  let hLX : HasLimit LX := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S X
  let c : Cone
      (leftDerivedShiftIndexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor 𝒟' n) :=
    (shiftFunctor 𝒟' n).mapCone
      ((@limit.cone _ _ _ _ LX hLX).whisker (leftDerivedShiftIndexFunctor (S := S) X n))
  -- Proof comment: whisker the old limit across the comma-category equivalence, then use that
  -- shifts preserve limits, and finally transport along the literal diagram isomorphism.
  have hc₀ :
      IsLimit ((@limit.cone _ _ _ _ LX hLX).whisker (leftDerivedShiftIndexFunctor (S := S) X n)) := by
    simpa [e, leftDerivedShiftIndexFunctor] using
      (@limit.isLimit _ _ _ _ LX hLX).whiskerEquivalence e.symm
  have hc : IsLimit c := by
    simpa [c] using isLimitOfPreserves (shiftFunctor 𝒟' n) hc₀
  change IsLimit
    ((Cone.postcompose (leftDerived_shiftDiagramIso (F := F) (S := S) X n).hom).obj c)
  exact
    (IsLimit.postcomposeHomEquiv (leftDerived_shiftDiagramIso (F := F) (S := S) X n) c).symm hc

instance leftDerivedDefinedObjectProperty_isStableUnderShift
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (leftDerivedDefinedObjectProperty F S) ℤ := by
  refine ⟨fun n ↦ ?_⟩
  refine ⟨?_⟩
  intro X hX
  let _ : F.HasPointwiseLeftDerivedFunctorAt S X := hX
  -- Proof comment: the shifted left-derived cone constructed above supplies the defining
  -- limit datum for `X⟦n⟧`.
  exact ⟨⟨leftDerived_shifted_cone (F := F) (S := S) X n,
    leftDerived_shifted_cone_isLimit (F := F) (S := S) X n⟩⟩

end LeftShift

section LeftShiftAPI

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

-- Proof sketch: this is the dual of the right-derived statement, again exposed first through the
-- owner-level shift-stability API on the underlying object property.
/-- Lemma 13.14.5 (3): the left derived functor of `F` is defined at `X` if and only if it is
defined at the shifted object `X⟦n⟧`. -/
@[stacks 05SU]
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
@[stacks 05SU]
noncomputable def leftDerivedValueShiftIso
    [HasShift 𝒟 ℤ] [HasShift 𝒟' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : 𝒟) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    leftDerivedValue S F (X⟦n⟧) ≅ ((leftDerivedValue S F X)⟦n⟧) := by
  let shifted := leftDerived_shifted_cone (F := F) (S := S) X n
  let LY := StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F
  let hc : IsLimit shifted :=
    leftDerived_shifted_cone_isLimit (F := F) (S := S) X n
  let hshifted : F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := ⟨⟨shifted, hc⟩⟩
  let _ : F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := hshifted
  let hLY : HasLimit LY := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S (X⟦n⟧)
  -- Proof comment: compare the explicit shifted limiting cone with the canonical limit cone on
  -- the literal diagram for `X⟦n⟧`.
  exact (hc.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ LY hLY)).symm

end LeftShiftIso

end CategoryTheory
