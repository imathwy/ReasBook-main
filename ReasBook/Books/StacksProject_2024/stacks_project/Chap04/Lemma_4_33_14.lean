import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_33_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Functor.IsHomLift
open scoped Bicategory

universe u v w

namespace CategoryTheory.FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver.{u, v, w, w} C}

noncomputable section

/- Domain-style sampling for Lemma 4.33.14:
- primary domain: fibred categories over a fixed base together with source-facing vertical
  factorizations of a morphism in the fibres;
- sampled owner declarations:
  `FibredCategoryOver`,
  `X ⟶ Y`,
  `Bicategory.Adjunction`,
  `Comma`,
  `ObjectProperty.FullSubcategory`,
  `StructuredArrow`,
  `Functor.Fiber`;
- best owner abstraction: globally, the factorization lives as the full subcategory of the comma
  category `Comma (𝟭 Y.S) (toFunctor F)` cut out by the verticality condition over the common
  base; over a
  fixed fibre `U`, its source-facing view is the structured-arrow owner
  `StructuredArrow y (fiberFunctor F U)`;
- primitive data: a base point `U : C`, a fibre object `y : Y_U`, an object `x : X_U`, and a
  vertical comparison morphism `y ⟶ F_U(x)`;
- derived API here: the bundled fibred factorization object, its projections to `X` and `Y`, the
  canonical source map `X ⟶ X'`, and the resulting fully-faithful / adjunction / fibred
  factorization statements.

Source/core/bridge triage:
- `source-facing`: `adjointFactorization`, `adjointFactorizationFromSource`,
  `adjointFactorizationToSource`, `adjointFactorizationToTarget`, and
  `exists_adjoint_fibred_factorization`;
- `core/canonical`: `FibredCategoryOver`, the ambient owner homs `X ⟶ Y`, `Comma`,
  `Bicategory.Adjunction`, `ObjectProperty.FullSubcategory`,
  `StructuredArrow`, and the fiber functors `fiberFunctor F U`;
- `bridge/view`: the fibrewise structured-arrow description of a fixed fiber of
  `adjointFactorization`, together with any comparison to the later iso-only explicit
  `2`-fibre-product model. -/

/-- The comma-object property cutting out the source-facing factorization of `F`: the comparison
arrow `y ⟶ F(x)` must be vertical over the identity of the common base object. -/
private abbrev adjointFactorizationObjectProperty
    (F : X ⟶ Y) :
    ObjectProperty (Comma (𝟭 Y.S) (toFunctor F)) :=
  fun P ↦ Y.p.IsHomLift (𝟙 (Y.p.obj P.left)) P.hom

/-- An object of the source-facing factorization of `F` is a vertical comma object
`y ⟶ F(x)`, organized as the full subcategory of `Comma (𝟭 Y.S) (toFunctor F)` cut out by the verticality
condition. -/
private abbrev AdjointFactorizationObject
    (F : X ⟶ Y) :=
  (adjointFactorizationObjectProperty F).FullSubcategory

/-- The projection from the source-facing factorization to the base category `C`. -/
private abbrev adjointFactorizationProjection
    (F : X ⟶ Y) :
    AdjointFactorizationObject F ⥤ C :=
  (adjointFactorizationObjectProperty F).ι ⋙ Comma.fst _ _ ⋙ Y.p

/-- The projection from the source-facing factorization to the total category of `X`. -/
private abbrev adjointFactorizationToSourceFunctor
    (F : X ⟶ Y) :
    AdjointFactorizationObject F ⥤ X.S :=
  (adjointFactorizationObjectProperty F).ι ⋙ Comma.snd _ _

private theorem adjointFactorizationToSourceFunctor_comm
    (F : X ⟶ Y) :
    adjointFactorizationToSourceFunctor F ⋙ X.p =
      adjointFactorizationProjection F := by
  sorry

/-- The projection from the source-facing factorization to the total category of `Y`. -/
private abbrev adjointFactorizationToTargetFunctor
    (F : X ⟶ Y) :
    AdjointFactorizationObject F ⥤ Y.S :=
  (adjointFactorizationObjectProperty F).ι ⋙ Comma.fst _ _

/-- The source-facing factorization projection is fibred over `C`. -/
private theorem adjointFactorizationProjection_isFibered
    (F : X ⟶ Y) :
    (adjointFactorizationProjection F).IsFibered := by
  sorry

/-- The source-facing factorization owner of `F`, namely the fibred category of
vertical arrows in the comma category `Comma (𝟭 Y.S) (toFunctor F)`. Over a fixed `U : C` and
`y : Y.p.Fiber U`, its fiber is the structured-arrow category `StructuredArrow y (fiberFunctor F U)`.
-/
noncomputable abbrev adjointFactorization
    (F : X ⟶ Y) :
    FibredCategoryOver C :=
  let p := adjointFactorizationProjection F
  letI : p.IsFibered := adjointFactorizationProjection_isFibered F
  FibredCategoryOver.ofFunctor p

/-- The projection `X' ⟶ X` from the source-facing factorization. -/
private noncomputable abbrev adjointFactorizationToSourceBased
    (F : X ⟶ Y) :
    (adjointFactorization F).toBasedCategory ⥤ᵇ X.toBasedCategory :=
  { toFunctor := adjointFactorizationToSourceFunctor F
    w := adjointFactorizationToSourceFunctor_comm F }

private theorem adjointFactorizationToSource_preservesStronglyCartesian
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian (adjointFactorizationToSourceBased F) := by
  sorry

/-- The projection from the source-facing factorization back to `X`. -/
noncomputable abbrev adjointFactorizationToSource
    (F : X ⟶ Y) :
    adjointFactorization F ⟶ X :=
  ofBasedFunctor
    (adjointFactorizationToSourceBased F)
    (adjointFactorizationToSource_preservesStronglyCartesian F)

/-- The projection `X' ⟶ Y` from the source-facing factorization. -/
private noncomputable abbrev adjointFactorizationToTargetBased
    (F : X ⟶ Y) :
    (adjointFactorization F).toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  { toFunctor := adjointFactorizationToTargetFunctor F
    w := rfl }

private theorem adjointFactorizationToTarget_preservesStronglyCartesian
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian (adjointFactorizationToTargetBased F) := by
  sorry

/-- The target projection in the source-facing factorization. -/
noncomputable abbrev adjointFactorizationToTarget
    (F : X ⟶ Y) :
    adjointFactorization F ⟶ Y :=
  ofBasedFunctor
    (adjointFactorizationToTargetBased F)
    (adjointFactorizationToTarget_preservesStronglyCartesian F)

/-- The canonical object `(x, F(x), id)` in the source-facing factorization. -/
private abbrev adjointFactorizationFromSourceObj
    (F : X ⟶ Y) (x : X.S) :
    AdjointFactorizationObject F :=
  ⟨{ left := (toFunctor F).obj x
     right := x
     hom := 𝟙 ((toFunctor F).obj x) }, by
    change Y.p.IsHomLift (𝟙 (Y.p.obj ((toFunctor F).obj x))) (𝟙 ((toFunctor F).obj x))
    simp [IsHomLift.id]⟩

/-- The underlying comma functor `x ↦ (F(x) ⟶ F(x))` used to build the canonical source map. -/
private def adjointFactorizationFromSourceComma
    (F : X ⟶ Y) :
    X.S ⥤ Comma (𝟭 Y.S) (toFunctor F) where
  obj := fun x ↦ (adjointFactorizationFromSourceObj F x).obj
  map := fun a ↦
    { left := (toFunctor F).map a
      right := a
      w := by simp }
  map_id := by
    intro x
    apply Comma.hom_ext <;> simp
  map_comp := by
    intro x y z a b
    apply Comma.hom_ext <;> simp

private abbrev adjointFactorizationFromSourceFunctor
    (F : X ⟶ Y) :
    X.S ⥤ AdjointFactorizationObject F :=
  (adjointFactorizationObjectProperty F).lift
    (adjointFactorizationFromSourceComma F)
    fun x ↦ (adjointFactorizationFromSourceObj F x).property

private def adjointFactorizationToSourceFunctorUnit
    (F : X ⟶ Y) :
    𝟭 (AdjointFactorizationObject F) ⟶
      adjointFactorizationToSourceFunctor F ⋙ adjointFactorizationFromSourceFunctor F where
  app P :=
    ObjectProperty.homMk
      { left := P.obj.hom
        right := 𝟙 P.obj.right
        w := by simp [adjointFactorizationFromSourceComma] }
  naturality {P Q} φ := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp [adjointFactorizationFromSourceComma]
    simpa [adjointFactorizationFromSourceComma] using φ.hom.w

private def adjointFactorizationToSourceFunctorCounitIso
    (F : X ⟶ Y) :
    adjointFactorizationFromSourceFunctor F ⋙ adjointFactorizationToSourceFunctor F ≅ 𝟭 X.S where
  hom :=
    { app := fun x ↦ 𝟙 x
      naturality := by intro x x' f; simp [adjointFactorizationFromSourceComma] }
  inv :=
    { app := fun x ↦ 𝟙 x
      naturality := by intro x x' f; simp [adjointFactorizationFromSourceComma] }
  hom_inv_id := by
    ext x
    simp [adjointFactorizationFromSourceComma]
  inv_hom_id := by
    ext x
    simp [adjointFactorizationFromSourceComma]

private noncomputable def adjointFactorizationToSourceFunctorAdjunction
    (F : X ⟶ Y) :
    adjointFactorizationToSourceFunctor F ⊣ adjointFactorizationFromSourceFunctor F :=
  Adjunction.mkOfUnitCounit
    { unit := adjointFactorizationToSourceFunctorUnit F
      counit := (adjointFactorizationToSourceFunctorCounitIso F).hom
      left_triangle := by
        ext P
        simp [adjointFactorizationToSourceFunctorUnit, adjointFactorizationToSourceFunctorCounitIso,
          adjointFactorizationFromSourceComma]
      right_triangle := by
        ext x <;> simp [adjointFactorizationToSourceFunctorUnit,
          adjointFactorizationToSourceFunctorCounitIso, adjointFactorizationFromSourceComma] }

/-- The canonical map `X ⟶ X'` given by `x ↦ (x, F(x), id)`. -/
private noncomputable abbrev adjointFactorizationFromSourceBased
    (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ (adjointFactorization F).toBasedCategory :=
  { toFunctor := adjointFactorizationFromSourceFunctor F
    w := by
      sorry }

private theorem adjointFactorizationFromSourceFunctor_base_eq
    (F : X ⟶ Y) (P : AdjointFactorizationObject F) :
    (adjointFactorization F).toBasedCategory.p.obj
        ((adjointFactorizationFromSourceFunctor F).obj P.obj.right) =
      (adjointFactorization F).toBasedCategory.p.obj P := by
  let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
  change Y.p.obj ((toFunctor F).obj P.obj.right) = Y.p.obj P.obj.left
  exact IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom

private def adjointFactorizationToSourceBasedUnit
    (F : X ⟶ Y) :
    BasedNatTrans (BasedFunctor.id (adjointFactorization F).toBasedCategory)
      (BasedFunctor.comp (adjointFactorizationToSourceBased F)
        (adjointFactorizationFromSourceBased F)) where
  toNatTrans := adjointFactorizationToSourceFunctorUnit F
  isHomLift' := fun P ↦ by
    let _ : Y.p.IsHomLift (𝟙 (Y.p.obj P.obj.left)) P.obj.hom := P.property
    refine IsHomLift.of_fac'
      ((adjointFactorization F).toBasedCategory.p)
      (𝟙 (((adjointFactorization F).toBasedCategory.p).obj P))
      ((adjointFactorizationToSourceFunctorUnit F).app P) rfl ?_ ?_
    · exact adjointFactorizationFromSourceFunctor_base_eq F P
    · simpa [adjointFactorization, FibredCategoryOver.ofFunctor, adjointFactorizationProjection,
        adjointFactorizationToSourceFunctorUnit] using
        (IsHomLift.fac' Y.p (𝟙 (Y.p.obj P.obj.left)) P.obj.hom)

private def adjointFactorizationFromSourceBasedCounit
    (F : X ⟶ Y) :
    BasedNatTrans (BasedFunctor.comp (adjointFactorizationFromSourceBased F)
        (adjointFactorizationToSourceBased F))
      (BasedFunctor.id X.toBasedCategory) where
  toNatTrans := (adjointFactorizationToSourceFunctorCounitIso F).hom
  isHomLift' := fun x ↦ by
    simpa using
      (show X.p.IsHomLift (𝟙 (X.p.obj x))
          ((adjointFactorizationToSourceFunctorCounitIso F).hom.app x) from
        IsHomLift.id (rfl : X.p.obj x = X.p.obj x))

private abbrev fibredCategoryMorHomOfBasedNatTrans
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    F ⟶ G :=
  ⟨ObjectProperty.homMk η, trivial⟩

@[simp] private theorem fibredCategoryMorHomOfBasedNatTrans_hom_hom
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    (fibredCategoryMorHomOfBasedNatTrans η).hom.hom = η :=
  rfl

private theorem adjointFactorizationFromSource_preservesStronglyCartesian
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian (adjointFactorizationFromSourceBased F) := by
  sorry

/-- The canonical source map into the source-facing factorization. -/
noncomputable abbrev adjointFactorizationFromSource
    (F : X ⟶ Y) :
    X ⟶ adjointFactorization F :=
  ofBasedFunctor
    (adjointFactorizationFromSourceBased F)
    (adjointFactorizationFromSource_preservesStronglyCartesian F)

/-- The canonical source map `X ⟶ X'` into the source-facing factorization is fully faithful. -/
noncomputable def adjointFactorizationFromSource_fullyFaithful
    (F : X ⟶ Y) :
    (toFunctor (adjointFactorizationFromSource F)).FullyFaithful := by
  let adj := adjointFactorizationToSourceFunctorAdjunction F
  letI : IsIso adj.counit := by
    change IsIso (adjointFactorizationToSourceFunctorCounitIso F).hom
    infer_instance
  change (adjointFactorizationFromSourceFunctor F).FullyFaithful
  exact adj.fullyFaithfulROfIsIsoCounit

/-- The projection `X' ⟶ X` is left adjoint over `C` to the canonical source map `X ⟶ X'`. -/
noncomputable def adjointFactorizationToSource_adjunction
    (F : X ⟶ Y) :
    adjointFactorizationToSource F ⊣ adjointFactorizationFromSource F where
  unit := fibredCategoryMorHomOfBasedNatTrans (adjointFactorizationToSourceBasedUnit F)
  counit := fibredCategoryMorHomOfBasedNatTrans (adjointFactorizationFromSourceBasedCounit F)
  left_triangle := by
    sorry
  right_triangle := by
    sorry

/-- The target projection `X' ⟶ Y` is fibred on the underlying total categories. -/
theorem adjointFactorizationToTarget_isFibered
    (F : X ⟶ Y) :
    (toFunctor (adjointFactorizationToTarget F)).IsFibered := by
  sorry

/-- The canonical source map followed by the target projection recovers `F`. -/
theorem adjointFactorization_comp
    (F : X ⟶ Y) :
    adjointFactorizationFromSource F ≫ adjointFactorizationToTarget F = F := by
  sorry

-- Proof sketch: use the vertical full subcategory of `Comma (𝟭 Y.S) (toFunctor F)`. Its
-- projection to `X` is left adjoint over `C` to the canonical source map
-- `x ↦ (F(x) ⟶ F(x))`, that source map is fully faithful, and the projection to `Y` is fibred and
-- composes with it to recover `F` in the category of fibred categories over `C`.
/-- Lemma 4.33.14: every `1`-morphism of fibred categories over `C` factors through a fully
faithful `1`-morphism admitting a left adjoint over `C`, followed by a fibred functor to the
target. -/
theorem exists_adjoint_fibred_factorization
    (F : X ⟶ Y) :
    ∃ X' : FibredCategoryOver C,
      ∃ u : X ⟶ X',
              ∃ v : X' ⟶ Y,
            ∃ w : X' ⟶ X,
              ∃ _ : (toFunctor u).FullyFaithful,
              ∃ _ : w ⊣ u,
                ∃ _ : (toFunctor v).IsFibered,
                  (u ≫ v : X ⟶ Y) = F := by
  show ∃ X' : FibredCategoryOver C,
      ∃ u : X ⟶ X',
        ∃ v : X' ⟶ Y,
          ∃ w : X' ⟶ X,
            ∃ _ : (toFunctor u).FullyFaithful,
              ∃ _ : w ⊣ u,
                ∃ _ : (toFunctor v).IsFibered,
                  (u ≫ v : X ⟶ Y) = F
  refine ⟨adjointFactorization F, adjointFactorizationFromSource F, adjointFactorizationToTarget F,
    adjointFactorizationToSource F, ?_, ?_, ?_, ?_⟩
  · simpa using adjointFactorizationFromSource_fullyFaithful F
  · simpa using adjointFactorizationToSource_adjunction F
  · simpa using adjointFactorizationToTarget_isFibered F
  · simpa using adjointFactorization_comp F

end

end CategoryTheory.FibredCategoryMor
