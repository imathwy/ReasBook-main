import StacksProject_2024.Chap13.Lemma_13_14_6

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Lemma 13.14.7: an identity denominator square identifies the corresponding
right-derived denominator legs. -/
theorem right_derived_leg_eq_of_id_square
    [F.HasPointwiseRightDerivedFunctorAt S Y]
    {Y₁ Y₂ : D} (s : Y ⟶ Y₁) (s' : Y ⟶ Y₂) (hs : S s) (hs' : S s') (f' : Y₁ ⟶ Y₂)
    (sq : CommSq (𝟙 Y) s s' f') :
    rightDerivedValueLeg S F s hs = F.map f' ≫ rightDerivedValueLeg S F s' hs' := by
  let RY := CostructuredArrow.proj S.Q (S.Q.obj Y) ⋙ F
  let _ : HasColimit RY := Functor.HasPointwiseRightDerivedFunctorAt.hasColimit F S.Q S Y
  let α :
      CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶
        CostructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv) :=
    CostructuredArrow.homMk f' (by
      -- Proof comment: localize the identity square and cancel the denominator isomorphisms.
      have hsq := congrArg
        (fun k ↦
          (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
            (Localization.isoOfHom S.Q S s' hs').inv)
        (sq.map S.Q).w
      simpa [Category.assoc, Localization.isoOfHom_hom] using hsq.symm)
  -- Proof comment: the resulting morphism in the costructured-arrow category compares the two
  -- colimit legs directly.
  simpa [RY, rightDerivedValueLeg] using (colimit.w RY α).symm

/-- Helper for Lemma 13.14.7: the right-derived value map of an identity morphism is the
identity. -/
theorem right_derived_valueMap_id
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    rightDerivedValueMap S F (𝟙 X) = 𝟙 (rightDerivedValue S F X) := by
  let φ : rightDerivedValue S F X ⟶ rightDerivedValue S F X := 𝟙 _
  have hφ :
      ∀ ⦃X' Y' : D⦄ (s : X ⟶ X') (s' : X ⟶ Y') (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq (𝟙 X) s s' f'),
          CommSq
            (rightDerivedValueLeg S F s hs)
            (F.map f')
            φ
            (rightDerivedValueLeg S F s' hs') := by
    intro X' Y' s s' hs hs' f' sq
    -- Proof comment: the identity map satisfies exactly the denominator-leg relation above.
    refine ⟨?_⟩
    simpa [φ] using right_derived_leg_eq_of_id_square
      (S := S) (F := F) s s' hs hs' f' sq
  -- Proof comment: the denominator-leg extensionality theorem identifies the canonical map with
  -- the identity candidate.
  simpa [φ] using
    (rightDerivedValueMap_hom_ext (S := S) (F := F) (f := 𝟙 X) (φ := φ) hφ).symm

/- Route correction: the split-triangle route is unchanged; the remaining local gap is the
composition input needed to show `RF(biprod.inr)` is a section of `RF(biprod.snd)`. -/
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
        (rightDerivedValueMap S F (biprod.inr : Y ⟶ X ⊞ Y))) := by
  -- TODO: prove
  -- `rightDerivedValueMap S F biprod.inr ≫ rightDerivedValueMap S F biprod.snd = 𝟙 _`
  -- using the denominator-square API plus the identity helper above, then apply
  -- `isIso_biprod_desc_of_distinguished_right_inverse` to the derived split triangle.
  sorry

/-- Helper for Lemma 13.14.7: an identity denominator square identifies the corresponding
left-derived denominator projections. -/
theorem left_derived_projection_eq_of_id_square
    [F.HasPointwiseLeftDerivedFunctorAt S Y]
    {Y₁ Y₂ : D} (s : Y₁ ⟶ Y) (s' : Y₂ ⟶ Y) (hs : S s) (hs' : S s') (f' : Y₁ ⟶ Y₂)
    (sq : CommSq s f' (𝟙 Y) s') :
    leftDerivedValueProjection S F s' hs' =
      leftDerivedValueProjection S F s hs ≫ F.map f' := by
  let LY := StructuredArrow.proj (S.Q.obj Y) S.Q ⋙ F
  let _ : HasLimit LY := Functor.HasPointwiseLeftDerivedFunctorAt.hasLimit F S.Q S Y
  let α :
      StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶
        StructuredArrow.mk ((Localization.isoOfHom S.Q S s' hs').inv) :=
    StructuredArrow.homMk f' (by
      -- Proof comment: localize the identity square and cancel the denominator isomorphisms.
      have hsq := congrArg
        (fun k ↦
          (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
            (Localization.isoOfHom S.Q S s' hs').inv)
        (sq.map S.Q).w
      simpa [Category.assoc, Localization.isoOfHom_hom] using hsq.symm)
  -- Proof comment: the induced structured-arrow morphism compares the two limit projections in
  -- the canonical orientation used by `leftDerivedValueMap_comp_of_square`.
  simpa [LY, leftDerivedValueProjection] using (limit.w LY α).symm

/-- Helper for Lemma 13.14.7: the left-derived value map of an identity morphism is the
identity. -/
theorem left_derived_valueMap_id
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    leftDerivedValueMap S F (𝟙 X) = 𝟙 (leftDerivedValue S F X) := by
  let φ : leftDerivedValue S F X ⟶ leftDerivedValue S F X := 𝟙 _
  have hφ :
      ∀ ⦃X' Y' : D⦄ (s : X' ⟶ X) (s' : Y' ⟶ X) (hs : S s) (hs' : S s')
        (f' : X' ⟶ Y') (_ : CommSq s f' (𝟙 X) s'),
          CommSq
            φ
            (leftDerivedValueProjection S F s hs)
            (leftDerivedValueProjection S F s' hs')
            (F.map f') := by
    intro X' Y' s s' hs hs' f' sq
    -- Proof comment: the identity map satisfies exactly the denominator-projection relation above.
    refine ⟨?_⟩
    simpa [φ] using left_derived_projection_eq_of_id_square
      (S := S) (F := F) s s' hs hs' f' sq
  -- Proof comment: the dual extensionality theorem identifies the canonical map with the
  -- identity candidate.
  simpa [φ] using
    (leftDerivedValueMap_hom_ext (S := S) (F := F) (f := 𝟙 X) (φ := φ) hφ).symm

/- Route correction: the left-derived clause is blocked by the same missing composition input as
the right-derived one. -/
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
        (leftDerivedValueMap S F (biprod.inr : Y ⟶ X ⊞ Y))) := by
  -- TODO: prove
  -- `leftDerivedValueMap S F biprod.inr ≫ leftDerivedValueMap S F biprod.snd = 𝟙 _`
  -- from the denominator-square API plus the identity helper above, then apply the split-triangle
  -- criterion to the derived distinguished triangle.
  sorry

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
  -- TODO: rewrite via `Functor.hasPointwiseRightDerivedFunctorAt_iff` and transfer the resulting
  -- pointwise left Kan-extension existence across the retract of `S.Q.obj X`.
  sorry

-- Proof sketch: dually, idempotent completeness lets one split the pointwise limit diagram
-- computing the left-derived value along retracts, so left-derived-definedness also descends
-- along retracts.
/-- If `D'` is Karoubian, then the pointwise left-derived-definedness property is stable under
retracts. -/
instance leftDerivedDefinedObjectProperty_isStableUnderRetracts [IsIdempotentComplete D'] :
    (leftDerivedDefinedObjectProperty F S).IsStableUnderRetracts := by
  -- TODO: rewrite via `Functor.hasPointwiseLeftDerivedFunctorAt_iff` and transfer the resulting
  -- pointwise right Kan-extension existence across the retract of `S.Q.obj X`.
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
