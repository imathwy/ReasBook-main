import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens
open CategoryTheory.Limits
open scoped Classical ZeroObject

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe w v u

section

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- The topological space underlying the open subspace `U ⊆ X`. -/
abbrev extensionByZeroOpenSubsetSpace (U : Opens X) : TopCat.{w} :=
  (Opens.toTopCat X).obj U

/-- The inclusion of the open subspace `U ⊆ X` into the ambient space `X`. -/
abbrev extensionByZeroOpenSubsetInclusion (U : Opens X) : extensionByZeroOpenSubsetSpace U ⟶ X :=
  Opens.inclusion' U

/-- The pullback of an ambient open subset of `X` to the open subspace `U`. -/
abbrev openSubsetPreimageOpen (U : Opens X) (V : Opens X) :
    Opens (extensionByZeroOpenSubsetSpace U) :=
  (Opens.map (extensionByZeroOpenSubsetInclusion U)).obj V

/-- The value of the presheaf-level extension-by-initial-object construction on an ambient open. -/
private abbrev openSubsetPresheafExtensionByInitialObjectValue
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) (V : (Opens X)ᵒᵖ) : C :=
  if _h : unop V ≤ U then
    ℱ.obj (op (openSubsetPreimageOpen U (unop V)))
  else
    ⊥_ C

/-- The restriction map in the presheaf-level extension-by-initial-object construction. -/
private noncomputable def openSubsetPresheafExtensionByInitialObjectMap
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    openSubsetPresheafExtensionByInitialObjectValue U ℱ V ⟶
      openSubsetPresheafExtensionByInitialObjectValue U ℱ W := by
  classical
  by_cases hV : unop V ≤ U
  · by_cases hW : unop W ≤ U
    · simpa [openSubsetPresheafExtensionByInitialObjectValue, hV, hW] using
        ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op
    · exact False.elim (hW (le_trans i.unop.le hV))
  · by_cases hW : unop W ≤ U
    · simpa [openSubsetPresheafExtensionByInitialObjectValue, hV, hW] using
        (initial.to (openSubsetPresheafExtensionByInitialObjectValue U ℱ W))
    · simpa [openSubsetPresheafExtensionByInitialObjectValue, hV, hW] using
        (initial.to (openSubsetPresheafExtensionByInitialObjectValue U ℱ W))

-- Proof sketch: split into the cases `V ⊆ U` and `V ⊈ U`; on the inside branch this reduces to
-- `ℱ.map_id`, while on the outside branch it is the identity on the initial object.
/-- The restriction maps in presheaf extension by the initial object satisfy the identity law. -/
private theorem openSubsetPresheafExtensionByInitialObject_map_id
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) (V : (Opens X)ᵒᵖ) :
    openSubsetPresheafExtensionByInitialObjectMap U ℱ (𝟙 V) =
      𝟙 (openSubsetPresheafExtensionByInitialObjectValue U ℱ V) := sorry

-- Proof sketch: split into the inside/outside cases for the three opens. The inside branch is
-- exactly `ℱ.map_comp`, and the outside branches are forced by uniqueness of maps from the initial
-- object.
/-- The restriction maps in presheaf extension by the initial object satisfy the composition law.
-/
private theorem openSubsetPresheafExtensionByInitialObject_map_comp
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W Z : (Opens X)ᵒᵖ} (i : V ⟶ W) (j : W ⟶ Z) :
    openSubsetPresheafExtensionByInitialObjectMap U ℱ (i ≫ j) =
      openSubsetPresheafExtensionByInitialObjectMap U ℱ i ≫
        openSubsetPresheafExtensionByInitialObjectMap U ℱ j := sorry

/-- The ambient presheaf underlying extension by the initial object along `U ↪ X`. -/
noncomputable def openSubsetPresheafExtensionByInitialObjectOnAmbient
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) : X.Presheaf C where
  obj := openSubsetPresheafExtensionByInitialObjectValue U ℱ
  map := fun i ↦ openSubsetPresheafExtensionByInitialObjectMap U ℱ i
  map_id := openSubsetPresheafExtensionByInitialObject_map_id U ℱ
  map_comp := openSubsetPresheafExtensionByInitialObject_map_comp U ℱ

-- Proof sketch: unfold the defining `if` and evaluate the inside branch `V ⊆ U`.
/-- Over an ambient open contained in `U`, extension by the initial object recovers the original
section object on the corresponding open of the subspace. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (h : unop V ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj V =
      ℱ.obj (op (openSubsetPreimageOpen U (unop V))) := sorry

-- Proof sketch: unfold the defining `if` and evaluate the outside branch `V ⊈ U`.
/-- Over an ambient open not contained in `U`, extension by the initial object takes the initial
value. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (h : ¬ unop V ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj V = ⊥_ C := sorry

/-- On opens `W ⊆ V ⊆ U`, the restriction map of extension by the initial object is the original
restriction map of `ℱ`, up to the canonical identifications of the section objects. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : unop V ≤ U) (hW : unop W ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
        ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := by
  sorry

/-- If `V` is not contained in `U`, then the restriction map out of `V` in extension by the
initial object is the unique map from the initial object. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : ¬ unop V ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
        initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj W) := by
  sorry

/-- The objectwise map induced by a morphism of presheaves under extension by the initial object.
-/
private noncomputable def openSubsetPresheafExtensionByInitialObjectHomApp
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj V ⟶
      (openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V := by
  classical
  by_cases hV : unop V ≤ U
  · simpa [openSubsetPresheafExtensionByInitialObjectOnAmbient,
      openSubsetPresheafExtensionByInitialObjectValue, hV] using
        η.app (op (openSubsetPreimageOpen U (unop V)))
  · simpa [openSubsetPresheafExtensionByInitialObjectOnAmbient,
      openSubsetPresheafExtensionByInitialObjectValue, hV] using
        (initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V))

/-- On opens contained in `U`, a morphism of presheaves acts through the original component of
the morphism. -/
theorem openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) (hV : unop V ≤ U) :
    openSubsetPresheafExtensionByInitialObjectHomApp U η V =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
        η.app (op (openSubsetPreimageOpen U (unop V))) ≫
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
  sorry

/-- Outside `U`, the component of a morphism of extension-by-initial-object presheaves is the
unique map from the initial object. -/
theorem openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_not_le
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) (hV : ¬ unop V ≤ U) :
    openSubsetPresheafExtensionByInitialObjectHomApp U η V =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
        initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V) := by
  sorry

-- Proof sketch: on the inside branch this is the naturality square for `η` after pulling the
-- inclusion back to `U`; on the outside branch all maps factor uniquely through the initial
-- object.
/-- The objectwise maps induced by presheaf extension by the initial object are natural in the
ambient open. -/
private theorem openSubsetPresheafExtensionByInitialObjectHomApp_naturality
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i ≫
        openSubsetPresheafExtensionByInitialObjectHomApp U η W =
      openSubsetPresheafExtensionByInitialObjectHomApp U η V ≫
        (openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).map i := sorry

/-- The morphism of ambient presheaves induced by a morphism on the open subspace `U`. -/
private noncomputable def openSubsetPresheafExtensionByInitialObjectHom
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢) :
    openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ ⟶
      openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢 where
  app := openSubsetPresheafExtensionByInitialObjectHomApp U η
  naturality := by
    intro V W i
    exact openSubsetPresheafExtensionByInitialObjectHomApp_naturality U η i

-- Proof sketch: check objectwise that on each ambient open the induced morphism is the identity
-- on the original section object or on the initial object.
/-- Extension by the initial object preserves identity morphisms of presheaves. -/
private theorem openSubsetPresheafExtensionByInitialObject_functor_map_id
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    openSubsetPresheafExtensionByInitialObjectHom U (𝟙 ℱ) =
      𝟙 (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ) := sorry

-- Proof sketch: verify the claim objectwise; on opens contained in `U` this is functoriality of
-- the original natural transformations, while outside `U` all components are the unique maps out
-- of the initial object.
/-- Extension by the initial object preserves composition of presheaf morphisms. -/
private theorem openSubsetPresheafExtensionByInitialObject_functor_map_comp
    (U : Opens X) {ℱ 𝒢 ℋ : (extensionByZeroOpenSubsetSpace U).Presheaf C}
    (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    openSubsetPresheafExtensionByInitialObjectHom U (η ≫ θ) =
      openSubsetPresheafExtensionByInitialObjectHom U η ≫
        openSubsetPresheafExtensionByInitialObjectHom U θ := sorry

/-- Extension by zero / by the initial object: for an open immersion `j : U ↪ X`, the presheaf
functor `j_{p!}` sends an ambient open `V` to the original section object on `V` when `V ⊆ U`,
and otherwise to the initial object of `C`. -/
noncomputable def openSubsetPresheafExtensionByInitialObject
    (U : Opens X) : (extensionByZeroOpenSubsetSpace U).Presheaf C ⥤ X.Presheaf C where
  obj := openSubsetPresheafExtensionByInitialObjectOnAmbient U
  map := fun η ↦ openSubsetPresheafExtensionByInitialObjectHom U η
  map_id := openSubsetPresheafExtensionByInitialObject_functor_map_id U
  map_comp := openSubsetPresheafExtensionByInitialObject_functor_map_comp U

variable [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- Sheaf-level extension by the initial object along `U ↪ X`, obtained by sheafifying the
presheaf-level construction. -/
noncomputable def openSubsetSheafExtensionByInitialObject
    (U : Opens X) : (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C :=
  TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U) ⋙
    openSubsetPresheafExtensionByInitialObject U ⋙
    CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C

end

notation:max "jₚ! " U:max =>
  openSubsetPresheafExtensionByInitialObject U

notation:max "j! " U:max =>
  openSubsetSheafExtensionByInitialObject U

section Modules

variable {X : TopCat.{u}}

private abbrev openSubsetAbelianPresheafExtensionByZero
    (U : Opens X) :
    (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u} ⥤
      X.Presheaf AddCommGrpCat.{u} :=
  openSubsetPresheafExtensionByInitialObject U

private theorem openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj V =
      ℱ.obj (op (openSubsetPreimageOpen U V.unop)) := by
  simpa [openSubsetAbelianPresheafExtensionByZero] using
    openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV

private theorem openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : ¬ V.unop ≤ U) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj V = ⊥_ AddCommGrpCat.{u} := by
  simpa [openSubsetAbelianPresheafExtensionByZero] using
    openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV

private theorem openSubsetAbelianPresheafExtensionByZero_isSheaf
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.1)) := by
  sorry

private instance : Subsingleton (⊥_ AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero initialIsInitial.isZero

private instance : Subsingleton (0 : AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero (isZero_zero _)

private noncomputable instance openSubsetModuleExtensionByZeroObj_module
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) (V : (Opens X)ᵒᵖ) :
    Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) := by
  classical
  by_cases hV : V.unop ≤ U
  · let αV : 𝒪X.obj V ⟶ 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) := by
      simpa using α.app V
    letI : Module (𝒪X.obj V) (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :=
      Module.compHom (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) αV.hom
    rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV]
    infer_instance
  · rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ.presheaf hV]
    exact
      { smul := fun _ _ ↦ 0
        one_smul := fun _ ↦ Subsingleton.elim _ _
        mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        smul_zero := fun _ ↦ Subsingleton.elim _ _
        smul_add := fun _ _ _ ↦ Subsingleton.elim _ _
        add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        zero_smul := fun _ ↦ Subsingleton.elim _ _ }

private noncomputable def openSubsetModuleExtensionByZeroObj
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) :
    PresheafOfModules 𝒪X :=
  letI : ∀ V : (Opens X)ᵒᵖ,
      Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :=
    fun V ↦ openSubsetModuleExtensionByZeroObj_module U α ℱ V
  PresheafOfModules.ofPresheaf
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf)
    (by
      intro V W i r m
      sorry)

private noncomputable def openSubsetModuleExtensionByZeroHomApp
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V ⟶
      ((openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf).obj V := by
  let _ := α
  classical
  by_cases hV : V.unop ≤ U
  · exact
      eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV) ≫
        ((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)) ≫
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm
  · exact
      eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ.presheaf hV) ≫
        0 ≫
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U 𝒢.presheaf hV).symm

private theorem openSubsetModuleExtensionByZeroHomApp_naturality
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).map i ≫
        openSubsetModuleExtensionByZeroHomApp U α η W =
      openSubsetModuleExtensionByZeroHomApp U α η V ≫
        ((openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf).map i := sorry

private noncomputable def openSubsetModuleExtensionByZeroHom
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) :
    openSubsetModuleExtensionByZeroObj U α ℱ ⟶
      openSubsetModuleExtensionByZeroObj U α 𝒢 :=
  let φ :
      (openSubsetModuleExtensionByZeroObj U α ℱ).presheaf ⟶
        (openSubsetModuleExtensionByZeroObj U α 𝒢).presheaf := by
    simpa [openSubsetModuleExtensionByZeroObj] using
      ({ app := openSubsetModuleExtensionByZeroHomApp U α η
         naturality := fun {_ _} i ↦
           openSubsetModuleExtensionByZeroHomApp_naturality U α η i } :
        (openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf ⟶
          (openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf)
  PresheafOfModules.homMk φ
    (by
      intro V r m
      sorry)

private theorem openSubsetModuleExtensionByZero_functor_map_id
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) :
    openSubsetModuleExtensionByZeroHom U α (𝟙 ℱ) =
      𝟙 (openSubsetModuleExtensionByZeroObj U α ℱ) := sorry

private theorem openSubsetModuleExtensionByZero_functor_map_comp
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 ℋ : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    openSubsetModuleExtensionByZeroHom U α (η ≫ θ) =
      openSubsetModuleExtensionByZeroHom U α η ≫
        openSubsetModuleExtensionByZeroHom U α θ := sorry

private noncomputable def openSubsetModuleExtensionByZero
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U) :
    PresheafOfModules 𝒪U ⥤ PresheafOfModules 𝒪X where
  obj := openSubsetModuleExtensionByZeroObj U α
  map := fun η ↦ openSubsetModuleExtensionByZeroHom U α η
  map_id := openSubsetModuleExtensionByZero_functor_map_id U α
  map_comp := openSubsetModuleExtensionByZero_functor_map_comp U α

/-- The presheaf-level extension-by-zero functor on modules along the open inclusion `U ↪ X`. -/
noncomputable abbrev openSubsetModulePresheafExtensionByZero
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{u}) :
    PresheafOfModules ((TopCat.Presheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      PresheafOfModules 𝒪 :=
  openSubsetModuleExtensionByZero U
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
      (extensionByZeroOpenSubsetInclusion U)).unit.app 𝒪)

/-- The sheaf-level extension-by-zero functor on modules along the open inclusion `U ↪ X`. -/
noncomputable abbrev openSubsetModuleSheafExtensionByZero
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{u}) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      SheafOfModules 𝒪 where
  obj ℱ :=
    { val := (openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
          (extensionByZeroOpenSubsetInclusion U)).unit.app 𝒪).hom).obj ℱ.val
      isSheaf := by
        simpa [openSubsetModuleExtensionByZero, openSubsetModuleExtensionByZeroObj,
          PresheafOfModules.ofPresheaf_presheaf] using
          openSubsetAbelianPresheafExtensionByZero_isSheaf U
            ((SheafOfModules.toSheaf
              ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪)).obj ℱ) }
  map η :=
    { val := (openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
          (extensionByZeroOpenSubsetInclusion U)).unit.app 𝒪).hom).map η.val }

end Modules
