import Mathlib
import stacks_project.Chap04.Example_4_3_4
import stacks_project.Chap04.Definition_4_29_6
import stacks_project.Chap04.Definition_4_42_3
import stacks_project.Chap08.Definition_8_4_5
import stacks_project.Chap08.Lemma_8_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.BasedFunctor
open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂ u v vDesc

namespace CategoryTheory

open Bicategory
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

private abbrev toFibredCategoryMor
    {J : GrothendieckTopology C} {X Y : StackOver J} (F : X ⟶ Y) :=
  InducedCategory.Hom.toFibredCategoryMor F

private abbrev toBasedFunctor
    {J : GrothendieckTopology C} {X Y : StackOver J} (F : X ⟶ Y) :=
  InducedCategory.Hom.toBasedFunctor F

private abbrev stackTwoHomToFibredCategoryMorTwoHom
    {J : GrothendieckTopology C} {X Y : StackOver J} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    toFibredCategoryMor F ⟶ toFibredCategoryMor G :=
  η.hom.hom

private abbrev stackTwoHomToNatTrans
    {J : GrothendieckTopology C} {X Y : StackOver J} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    (toBasedFunctor F).toFunctor ⟶ (toBasedFunctor G).toFunctor :=
  (stackTwoHomToFibredCategoryMorTwoHom η).hom.hom.toNatTrans

section

variable (J : GrothendieckTopology C)

variable (U : C)

/- Domain-style sampling for Lemma 8.13.2:
- primary domain: stacks over a site, localization of a site at `U`, and the slice strict
  `2`-category over the representable stack `C/U`.
- inspected owner-level declarations:
  `StackOver`,
  `StackOver.ofProjection`,
  `SliceTwoCategory`,
  `FibredCategoryMor.ofBasedFunctor`,
  `StrictPseudofunctor.IsInverse`.
- best owner abstraction: the localized side should use the chapter owner `StackOver (J.over U)`
  directly, and the two source constructions should be packaged as strict pseudofunctors between
  `StackOver (J.over U)` and `SliceTwoCategory (sliceStackOver J U hU)`.
- primitive data: the projection functors produced by Constructions A and B together with the
  stack-on-site proofs for those projections.
- derived API: the bundled `StackOver` objects, their induced slice morphisms, and the inverse
  package `StrictPseudofunctor.IsInverse`.

Source/core/bridge triage:
- `source-facing`: `localizedStacksToSlice`, `sliceToLocalizedStacks`,
  `localizedStacks_equivalent_to_stacks_with_map_to_slice`.
- `core/canonical`: `StackOver`, `StackOver.ofProjection`, `SliceTwoCategory`,
  `FibredCategoryMor.ofBasedFunctor`, `StrictPseudofunctor.IsInverse`.
- `bridge/view`: the representable stack `sliceStackOver` and the private bundled object
  conversions used by Constructions A and B. -/

/-- If the representable presheaf `h_U` is a sheaf on `(C, J)`, then the slice fibred category
`C/U` defines the corresponding representable stack over `(C, J)`. -/
abbrev sliceStackOver
    (hU : Presheaf.IsSheaf J h[U]) : StackOver J :=
  let p : Over U ⥤ C := Over.forget U
  letI : IsStackOnSite J p := by
    simpa [p] using (over_forget_isStackOnSite_iff_representable_isSheaf J U).2 hU
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

private abbrev sliceTwoHomToNatTrans
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)} {F G : X ⟶ Y}
    (η : F ⟶ G) :
    (toBasedFunctor F.hom).toFunctor ⟶ (toBasedFunctor G.hom).toFunctor :=
  stackTwoHomToNatTrans η.hom

/-- Construction A on objects: a stack over the localized site `(C/U, J.over U)` defines a stack
over `(C, J)` by composing its projection with `Over.forget U`. -/
private abbrev localizedStackAsStackOver
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) : StackOver J :=
  let p : X.S ⥤ C := X.p ⋙ Over.forget U
  letI : IsStackOnSite J p := by
    change IsStackOnSite J (X.p ⋙ Over.forget U)
    sorry
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

/-- The based functor over `C` underlying Construction A on the map to `C/U`. -/
private abbrev localizedStackToSliceBasedFunctor
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    (localizedStackAsStackOver J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (sliceStackOver J U hU).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.S ⥤ Over U from X.p
  w := by
    rfl

private theorem localizedStackToSlice_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    BasedFunctor.PreservesStronglyCartesian
      (localizedStackToSliceBasedFunctor J U hU X) := by
  intro a b φ hφ
  simpa [localizedStackToSliceBasedFunctor, sliceStackOver, FibredCategoryOver.p,
      FibredCategoryOver.ofFunctor] using
    (inferInstance : IsFibredInGroupoids (Over.forget U)).isStronglyCartesian_map
      (X.p.map φ)

/-- Construction A on objects: the canonical morphism from the induced stack over `(C, J)` to the
representable stack `C/U`. -/
private abbrev localizedStackToSliceMorphism
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    FibredCategoryMor
      (localizedStackAsStackOver J U hU X).toFibredCategoryOver
      (sliceStackOver J U hU).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (localizedStackToSliceBasedFunctor J U hU X)
    (localizedStackToSlice_preservesStronglyCartesian J U hU X)

/-- Construction A on `1`-morphisms, forgetting that the source and target lie over `Over U` and
viewing the same functor as a morphism over `C`. -/
private abbrev localizedStackMapAsStackBasedFunctor
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    (localizedStackAsStackOver J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (localizedStackAsStackOver J U hU Y).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.S ⥤ Y.S from (toBasedFunctor F).toFunctor
  w := by
    sorry

private theorem localizedStackMapAsStack_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (localizedStackMapAsStackBasedFunctor J U hU F) := by
  intro a b φ hφ
  sorry

private abbrev localizedStackMapAsStackMorphism
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    FibredCategoryMor
      (localizedStackAsStackOver J U hU X).toFibredCategoryOver
      (localizedStackAsStackOver J U hU Y).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (localizedStackMapAsStackBasedFunctor J U hU F)
    (localizedStackMapAsStack_preservesStronglyCartesian J U hU F)

private abbrev localizedStackMapAsStackTwoHom
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} {F G : X ⟶ Y} (η : F ⟶ G) :
    localizedStackMapAsStackMorphism J U hU F ⟶
      localizedStackMapAsStackMorphism J U hU G :=
  let τ := stackTwoHomToNatTrans η
  ⟨ObjectProperty.homMk <|
      { toNatTrans := τ
        isHomLift' := by
          intro a
          sorry },
    trivial⟩

private abbrev localizedStackToSliceHom
    (hU : Presheaf.IsSheaf J h[U])
    (X : StackOver (J.over U)) :
    localizedStackAsStackOver J U hU X ⟶
      sliceStackOver J U hU :=
  InducedCategory.Hom.ofFibredCategoryMor (localizedStackToSliceMorphism J U hU X)

private theorem localizedStackToSlice_map_comm
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : StackOver (J.over U)} (F : X ⟶ Y) :
    InducedCategory.Hom.ofFibredCategoryMor (localizedStackMapAsStackMorphism J U hU F) ≫
        localizedStackToSliceHom J U hU Y =
      localizedStackToSliceHom J U hU X := by
  sorry

/-- Construction A of Lemma 8.13.2: a localized stack defines a stack over `(C, J)` equipped with
its canonical map to the representable stack `C/U`. -/
private def localizedStacksToSlicePreCore
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctorPreCore
      (StackOver (J.over U))
      (SliceTwoCategory (sliceStackOver J U hU)) :=
  {
    obj := fun X ↦
      { obj := localizedStackAsStackOver J U hU X
        hom := localizedStackToSliceHom J U hU X }
    map := fun F ↦
      { hom := InducedCategory.Hom.ofFibredCategoryMor (localizedStackMapAsStackMorphism J U hU F)
        comm := localizedStackToSlice_map_comm J U hU F }
    map₂ := fun η ↦
      { hom := InducedCategory.Hom.homMk (localizedStackMapAsStackTwoHom J U hU η)
        comm := by
          sorry
      }
    map_id := by
      intro X
      sorry
    map_comp := by
      intro X Y Z F G
      sorry
    map₂_id := by
      intro X Y F
      sorry
    map₂_comp := by
      intro X Y F G H η θ
      sorry
    map₂_whisker_left := by
      intro a b c f g g' η
      sorry
    map₂_whisker_right := by
      intro a b c f f' η g
      sorry
  }

/-- Construction A of Lemma 8.13.2: a localized stack defines a stack over `(C, J)` equipped with
its canonical map to the representable stack `C/U`. -/
noncomputable def localizedStacksToSlice
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctor
      (StackOver (J.over U))
      (SliceTwoCategory (sliceStackOver J U hU)) :=
  StrictPseudofunctor.mk'' (localizedStacksToSlicePreCore J U hU)

/-- Construction B on objects: a stack over `(C, J)` with a map to `C/U` is viewed as a stack
over the localized site `(C/U, J.over U)` via that map. -/
private abbrev sliceObjectAsLocalizedStack
    (hU : Presheaf.IsSheaf J h[U])
    (X : SliceTwoCategory (sliceStackOver J U hU)) :
    StackOver (J.over U) :=
  let p : X.obj.S ⥤ Over U := (toBasedFunctor X.hom).toFunctor
  letI : IsStackOnSite (J.over U) p := by
    change IsStackOnSite (J.over U) (toBasedFunctor X.hom).toFunctor
    sorry
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite (J.over U) p)⟩

private abbrev sliceHomToLocalizedStackBasedFunctor
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    (sliceObjectAsLocalizedStack J U hU X).toFibredCategoryOver.toBasedCategory ⥤ᵇ
      (sliceObjectAsLocalizedStack J U hU Y).toFibredCategoryOver.toBasedCategory where
  toFunctor := show X.obj.S ⥤ Y.obj.S from (toBasedFunctor F.hom).toFunctor
  w := by
    sorry

private theorem sliceHomToLocalizedStack_preservesStronglyCartesian
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (sliceHomToLocalizedStackBasedFunctor J U hU F) := by
  intro a b φ hφ
  sorry

/-- Construction B on `1`-morphisms: a triangle over `C/U` induces a morphism over the localized
site `(C/U, J.over U)`. -/
private abbrev sliceHomToLocalizedStackMorphism
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    (F : X ⟶ Y) :
    FibredCategoryMor
      (sliceObjectAsLocalizedStack J U hU X).toFibredCategoryOver
      (sliceObjectAsLocalizedStack J U hU Y).toFibredCategoryOver :=
  FibredCategoryMor.ofBasedFunctor
    (sliceHomToLocalizedStackBasedFunctor J U hU F)
    (sliceHomToLocalizedStack_preservesStronglyCartesian J U hU F)

private abbrev sliceHomToLocalizedStackTwoHom
    (hU : Presheaf.IsSheaf J h[U])
    {X Y : SliceTwoCategory (sliceStackOver J U hU)}
    {F G : X ⟶ Y} (η : F ⟶ G) :
    sliceHomToLocalizedStackMorphism J U hU F ⟶
      sliceHomToLocalizedStackMorphism J U hU G :=
  let τ := sliceTwoHomToNatTrans J U hU η
  ⟨ObjectProperty.homMk <|
      { toNatTrans := τ
        isHomLift' := by
          intro a
          sorry },
    trivial⟩

/-- Construction B of Lemma 8.13.2: a stack over `(C, J)` equipped with a map to `C/U` defines a
stack over the localized site `(C/U, J.over U)`. -/
private def sliceToLocalizedStacksPreCore
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctorPreCore
      (SliceTwoCategory (sliceStackOver J U hU))
      (StackOver (J.over U)) :=
  {
    obj := fun X ↦ sliceObjectAsLocalizedStack J U hU X
    map := fun F ↦
      InducedCategory.Hom.ofFibredCategoryMor (sliceHomToLocalizedStackMorphism J U hU F)
    map₂ := fun η ↦
      InducedCategory.Hom.homMk (sliceHomToLocalizedStackTwoHom J U hU η)
    map_id := by
      intro X
      sorry
    map_comp := by
      intro X Y Z F G
      sorry
    map₂_id := by
      intro X Y F
      sorry
    map₂_comp := by
      intro X Y F G H η θ
      sorry
    map₂_whisker_left := by
      intro a b c f g g' η
      sorry
    map₂_whisker_right := by
      intro a b c f f' η g
      sorry
  }

/-- Construction B of Lemma 8.13.2: a stack over `(C, J)` equipped with a map to `C/U` defines a
stack over the localized site `(C/U, J.over U)`. -/
noncomputable def sliceToLocalizedStacks
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctor
      (SliceTwoCategory (sliceStackOver J U hU))
      (StackOver (J.over U)) :=
  StrictPseudofunctor.mk'' (sliceToLocalizedStacksPreCore J U hU)

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on objects. -/
@[simp] private theorem sliceToLocalizedStacks_obj_localizedStacksToSlice_obj
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ X : StackOver (J.over U),
      (sliceToLocalizedStacks J U hU).obj ((localizedStacksToSlice J U hU).obj X) = X := by
  intro X
  sorry

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on `1`-morphisms. -/
@[simp] private theorem sliceToLocalizedStacks_map_localizedStacksToSlice_map
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : StackOver (J.over U)⦄ (F : X ⟶ Y),
      HEq ((sliceToLocalizedStacks J U hU).map ((localizedStacksToSlice J U hU).map F)) F := by
  intro X Y F
  sorry

/-- Construction A followed by Construction B is the identity on the strict `2`-category of
stacks over the localized site `(C/U, J.over U)` on `2`-morphisms. -/
@[simp] private theorem sliceToLocalizedStacks_map₂_localizedStacksToSlice_map₂
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : StackOver (J.over U)⦄ {F G : X ⟶ Y} (η : F ⟶ G),
      HEq ((sliceToLocalizedStacks J U hU).map₂ ((localizedStacksToSlice J U hU).map₂ η)) η := by
  intro X Y F G η
  sorry

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on objects. -/
@[simp] private theorem localizedStacksToSlice_obj_sliceToLocalizedStacks_obj
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ X : SliceTwoCategory (sliceStackOver J U hU),
      (localizedStacksToSlice J U hU).obj ((sliceToLocalizedStacks J U hU).obj X) = X := by
  intro X
  sorry

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on `1`-morphisms, up to transport along
the object equalities from `localizedStacksToSlice_obj_sliceToLocalizedStacks_obj`. -/
private theorem localizedStacksToSlice_map_sliceToLocalizedStacks_map
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : SliceTwoCategory (sliceStackOver J U hU)⦄ (F : X ⟶ Y),
      HEq ((localizedStacksToSlice J U hU).map ((sliceToLocalizedStacks J U hU).map F)) F := by
  intro X Y F
  sorry

/-- Construction B followed by Construction A is the identity on the slice strict `2`-category of
stacks over `(C, J)` above the representable stack `C/U` on `2`-morphisms, up to transport along
the object equalities from `localizedStacksToSlice_obj_sliceToLocalizedStacks_obj`. -/
private theorem localizedStacksToSlice_map₂_sliceToLocalizedStacks_map₂
    (hU : Presheaf.IsSheaf J h[U]) :
    ∀ ⦃X Y : SliceTwoCategory (sliceStackOver J U hU)⦄
      {F G : X ⟶ Y} (η : F ⟶ G),
      HEq ((localizedStacksToSlice J U hU).map₂ ((sliceToLocalizedStacks J U hU).map₂ η)) η := by
  intro X Y F G η
  sorry

/-- Lemma 8.13.2: if the representable presheaf `h[U]` is a sheaf on `(C, J)`, then Construction A
`localizedStacksToSlice` and Construction B `sliceToLocalizedStacks` are inverse strict
`2`-functors between stacks over the localized site `(C/U, J.over U)` and stacks over `(C, J)`
above the representable stack `C/U`. This packages the source statement in the canonical Lean
form `StrictPseudofunctor.IsInverse`. -/
theorem localizedStacks_equivalent_to_stacks_with_map_to_slice
    (hU : Presheaf.IsSheaf J h[U]) :
    StrictPseudofunctor.IsInverse
      (localizedStacksToSlice J U hU)
      (sliceToLocalizedStacks J U hU) := by
  refine
    { left_obj := sliceToLocalizedStacks_obj_localizedStacksToSlice_obj J U hU
      left_map := sliceToLocalizedStacks_map_localizedStacksToSlice_map J U hU
      left_map₂ := sliceToLocalizedStacks_map₂_localizedStacksToSlice_map₂ J U hU
      right_obj := localizedStacksToSlice_obj_sliceToLocalizedStacks_obj J U hU
      right_map := localizedStacksToSlice_map_sliceToLocalizedStacks_map J U hU
      right_map₂ := localizedStacksToSlice_map₂_sliceToLocalizedStacks_map₂ J U hU }

end

end CategoryTheory
