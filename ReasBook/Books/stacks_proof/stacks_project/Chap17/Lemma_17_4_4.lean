import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks
import stacks_proof.stacks_project.Chap06.Lemma_6_15_4
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4
import stacks_proof.stacks_project.Chap06.Lemma_6_17_6
import stacks_proof.stacks_project.Chap06.Lemma_6_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace PresheafOfModules
open AlgebraicGeometry

universe u

/- Domain-style sampling for subsheaf generation by local sections:
- primary domain: subobjects of `\mathcal O_X`-module sheaves on a ringed space;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `CategoryTheory.Subobject.arrow`,
  `CategoryTheory.Subobject.sInf`,
  `CategoryTheory.Subobject.sInf_le`,
  `CategoryTheory.Subobject.le_sInf`,
  `RingedSpace.Modules`,
  `subsheaf_contains_local_sections`;
- source-facing layer: existence and uniqueness of the smallest subsheaf containing prescribed
  local sections;
- core/canonical owner abstraction: the complete lattice `Subobject ℱ`, with the generated
  subsheaf defined in the next item as the infimum of all subsheaves containing the prescribed
  local sections;
- bridge/view layer here: the direct source-facing existence/uniqueness theorem.

Primitive-vs-derived split:
- primitive data: a ringed space `X`, an `\mathcal O_X`-module sheaf `ℱ`, opens `U i`, and
  sections `s i`;
- derived API: the containment predicate and the unique-minimality theorem below.
-/

namespace AlgebraicGeometry

noncomputable section

variable {X : RingedSpace.{u}}
variable {I : Type u}

local notation "ModX" => RingedSpace.Modules X

/-- Helper for Lemma 17.4.4: the structure sheaf of rings on the underlying topological space of
`X`, viewed in `RingCat`. -/
private abbrev structureRingSheaf (X : RingedSpace.{u}) :=
  (RingedSpace.ringCatSheaf X).obj

/-- Helper for Lemma 17.4.4: the structure sheaf of rings on `X` as a sheaf object. -/
private abbrev structureRingSheafObj (X : RingedSpace.{u}) :=
  RingedSpace.ringCatSheaf X

/-- A subsheaf contains the indexed local sections `s i` when each `s i` lifts to a section of that
subsheaf over `U i`. -/
def subsheaf_contains_local_sections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (G : Subobject ℱ) : Prop :=
  let ι := G.arrow.val
  ∀ i, s i ∈ Set.range (ι.app (op (U i)))

/-- Helper for Lemma 17.4.4: the objectwise generating set consists of the prescribed sections
restricted to the current open. -/
private def generated_local_sections_set
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X) : Set (ℱ.val.obj (op W)) :=
  { x | ∃ i, ∃ h : W ≤ U i, x = ℱ.val.map (homOfLE h).op (s i) }

/-- Helper for Lemma 17.4.4: objectwise we take the `𝒪_X(W)`-submodule spanned by the restricted
generators. -/
private def generated_local_sections_submodule
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X) : Submodule ((structureRingSheaf X).obj (op W)) (ℱ.val.obj (op W)) :=
  Submodule.span ((structureRingSheaf X).obj (op W)) (generated_local_sections_set ℱ U s W)

/-- Helper for Lemma 17.4.4: restricting a section from a larger open preserves membership in the
generated span. -/
private theorem generated_local_sections_map_mem
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (x : generated_local_sections_submodule ℱ U s V.unop) :
    ℱ.val.map f x.1 ∈ generated_local_sections_submodule ℱ U s W.unop := by
  -- Proof comment: this is the source-faithful span-stability lemma for the generated presheaf.
  refine Submodule.span_induction
      (p := fun y _ ↦ ℱ.val.map f y ∈ generated_local_sections_submodule ℱ U s W.unop)
      ?_ ?_ ?_ ?_ x.2
  · intro y hy
    rcases hy with ⟨i, hi, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨i, le_trans (leOfHom f.unop) hi, ?_⟩
    -- Proof comment: restriction along `f` simply composes the two inclusion maps of opens.
    have hcomp :
        (homOfLE (le_trans (leOfHom f.unop) hi)).op = (homOfLE hi).op ≫ f := by
      apply congrArg Opposite.op
      simpa [homOfLE_comp] using
        (Subsingleton.elim
          (homOfLE (le_trans (leOfHom f.unop) hi))
          (f.unop ≫ homOfLE hi))
    rw [hcomp]
    simpa using congrArg (fun g ↦ g.hom (s i)) (ℱ.val.map_comp (homOfLE hi).op f).symm
  · simpa using
      (show (ℱ.val.map f).hom (0 : ℱ.val.obj V) ∈
          generated_local_sections_submodule ℱ U s W.unop from by
        rw [(ℱ.val.map f).hom.map_zero]
        exact Submodule.zero_mem _)
  · intro y z hy hz hy' hz'
    rw [(ℱ.val.map f).hom.map_add]
    exact Submodule.add_mem _ hy' hz'
  · intro a y hy hy'
    rw [(ℱ.val.map f).hom.map_smulₛₗ]
    exact Submodule.smul_mem (generated_local_sections_submodule ℱ U s W.unop)
      (((structureRingSheaf X).map f).hom a) hy'

/-- Helper for Lemma 17.4.4: the canonical generator over `U i` belongs to the generated
submodule. -/
private theorem generated_local_sections_generator_mem
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) (i : I) :
    ℱ.val.map (homOfLE (show U i ≤ U i from le_rfl)).op (s i) ∈
      generated_local_sections_submodule ℱ U s (U i) := by
  exact Submodule.subset_span
    (show
      ℱ.val.map (homOfLE (show U i ≤ U i from le_rfl)).op (s i) ∈
        generated_local_sections_set ℱ U s (U i) from
      ⟨i, le_rfl, rfl⟩)

/-- Helper for Lemma 17.4.4: the object of the generated presheaf over an open `W`. -/
private abbrev generated_local_sections_presheaf_obj
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : (Opens X)ᵒᵖ) :
    ModuleCat ((structureRingSheaf X).obj W) :=
  ModuleCat.of ((structureRingSheaf X).obj W) (generated_local_sections_submodule ℱ U s W.unop)

/-- Helper for Lemma 17.4.4: the generated spans form a restriction-stable presheaf of
`\mathcal O_X`-modules. -/
private noncomputable def generated_local_sections_presheafMap
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    generated_local_sections_presheaf_obj ℱ U s V ⟶
      (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).obj
        (generated_local_sections_presheaf_obj ℱ U s W) := by
  -- Proof comment: restrict an element of the objectwise span and keep the target membership by
  -- `generated_local_sections_map_mem`.
  letI : Module ((structureRingSheaf X).obj V) (ℱ.val.obj W) :=
    Module.compHom (ℱ.val.obj W) ((structureRingSheaf X).map f).hom
  letI : Module ((structureRingSheaf X).obj V) ↥(generated_local_sections_submodule ℱ U s W.unop) :=
    Module.compHom ↥(generated_local_sections_submodule ℱ U s W.unop)
      ((structureRingSheaf X).map f).hom
  change
    ModuleCat.of ((structureRingSheaf X).obj V)
        (generated_local_sections_submodule ℱ U s V.unop) ⟶
      ModuleCat.of ((structureRingSheaf X).obj V)
        (generated_local_sections_submodule ℱ U s W.unop)
  refine ModuleCat.ofHom
    { toFun := fun x ↦ ⟨(ℱ.val.map f).hom x.1, generated_local_sections_map_mem ℱ U s f x⟩
      map_add' := fun x y ↦ by
        apply Subtype.ext
        simpa using (ℱ.val.map f).hom.map_add x.1 y.1
      map_smul' := fun a x ↦ by
        apply Subtype.ext
        simpa using (ℱ.val.map f).hom.map_smulₛₗ a x.1 }

/-- Helper for Lemma 17.4.4: the generated-span restriction map is the identity on identity
inclusions of opens. -/
private theorem generated_local_sections_presheafMap_id
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : (Opens X)ᵒᵖ) :
    generated_local_sections_presheafMap ℱ U s (𝟙 W) =
      (ModuleCat.restrictScalarsId' ((structureRingSheaf X).map (𝟙 W)).hom
        (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_id W))).inv.app
        (generated_local_sections_presheaf_obj ℱ U s W) := by
  -- Proof comment: both sides are induced by the identity restriction on `ℱ`.
  refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  apply Subtype.ext
  change (ℱ.val.map (𝟙 W)).hom x.1 =
      ((ModuleCat.restrictScalarsId' ((structureRingSheaf X).map (𝟙 W)).hom
        (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_id W))).inv.app
        (ℱ.val.obj W)).hom x.1
  exact congrArg (fun g ↦ g x.1) (congrArg ModuleCat.Hom.hom (ℱ.val.map_id W))

/-- Helper for Lemma 17.4.4: the generated-span restriction maps compose functorially. -/
private theorem generated_local_sections_presheafMap_comp
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) :
    generated_local_sections_presheafMap ℱ U s (f ≫ g) =
      generated_local_sections_presheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          (generated_local_sections_presheafMap ℱ U s g) ≫
        (ModuleCat.restrictScalarsComp' ((structureRingSheaf X).map f).hom
          ((structureRingSheaf X).map g).hom ((structureRingSheaf X).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_comp f g))).inv.app
          (generated_local_sections_presheaf_obj ℱ U s Z) := by
  -- Proof comment: this is functoriality of restriction for the generated-span presheaf.
  refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  apply Subtype.ext
  change (ℱ.val.map (f ≫ g)).hom x.1 =
      ((ℱ.val.map f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map (ℱ.val.map g) ≫
        (ModuleCat.restrictScalarsComp' ((structureRingSheaf X).map f).hom
          ((structureRingSheaf X).map g).hom ((structureRingSheaf X).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_comp f g))).inv.app
          (ℱ.val.obj Z)).hom x.1)
  simpa using congrArg (fun h ↦ h.hom x.1) (ℱ.val.map_comp f g)

/-- Helper for Lemma 17.4.4: the presheaf whose sections are finite `\mathcal O_X`-linear
combinations of the restricted generators. -/
private noncomputable def generated_local_sections_presheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    PresheafOfModules (structureRingSheaf X) where
  obj := generated_local_sections_presheaf_obj ℱ U s
  map := generated_local_sections_presheafMap ℱ U s
  map_id := generated_local_sections_presheafMap_id ℱ U s
  map_comp := generated_local_sections_presheafMap_comp ℱ U s

/-- Helper for Lemma 17.4.4: the generated presheaf includes objectwise into the ambient sheaf
`\mathcal F`. -/
private noncomputable def generated_local_sections_presheaf_inclusion
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    generated_local_sections_presheaf ℱ U s ⟶ ℱ.val where
  app W := ModuleCat.ofHom (generated_local_sections_submodule ℱ U s W.unop).subtype
  naturality f := by
    -- Proof comment: both composites are the ambient restriction map on `ℱ` followed by the
    -- obvious subtype projection.
    refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
    rfl

/-- Helper for Lemma 17.4.4: the generated-presheaf inclusion is objectwise the subtype inclusion,
so it is injective on every open. -/
private theorem generated_local_sections_presheaf_inclusion_app_injective
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X) :
    Function.Injective (((generated_local_sections_presheaf_inclusion ℱ U s).app (op W)).hom) := by
  -- Proof comment: objectwise the inclusion forgets only the submodule proof, so equality in
  -- `ℱ(W)` already forces equality in the subtype.
  intro x y hxy
  apply Subtype.ext
  exact hxy

/-- Helper for Lemma 17.4.4: the explicit generated-presheaf inclusion is monic. -/
private theorem generated_local_sections_presheaf_inclusion_mono
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Mono (generated_local_sections_presheaf_inclusion ℱ U s) := by
  -- Proof comment: monicity is checked objectwise because presheaves of modules form a functor
  -- category and the inclusion is injective on each open set.
  refine ⟨?_⟩
  intro P g h hgh
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  apply generated_local_sections_presheaf_inclusion_app_injective ℱ U s W.unop
  exact congrArg (fun k ↦ ((k.app W).hom) x) hgh

/-- Helper for Lemma 17.4.4: the module sheafification functor over the structure sheaf of `X`. -/
private noncomputable abbrev modSheafification (X : RingedSpace.{u}) :=
  PresheafOfModules.sheafification (𝟙 (structureRingSheaf X))

/-- Helper for Lemma 17.4.4: the canonical comparison from the sheafification of the explicit
generated presheaf into the ambient sheaf `ℱ`. -/
private noncomputable def generated_local_sections_sheafification_comparison
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    (modSheafification X).obj (generated_local_sections_presheaf ℱ U s) ⟶ ℱ :=
  (modSheafification X).map (generated_local_sections_presheaf_inclusion ℱ U s) ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).counit.app ℱ

/-- Helper for Lemma 17.4.4: the sheafification unit followed by the constructive comparison map
recovers the explicit presheaf inclusion. -/
private theorem generated_local_sections_unit_comp_comparison
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
        (generated_local_sections_presheaf ℱ U s)) ≫
      ((SheafOfModules.forget (structureRingSheafObj X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureRingSheaf X))).map
        (generated_local_sections_sheafification_comparison ℱ U s)) =
      generated_local_sections_presheaf_inclusion ℱ U s := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))
  have hcomparison :
      (adj.homEquiv (generated_local_sections_presheaf ℱ U s) ℱ).symm
          (generated_local_sections_presheaf_inclusion ℱ U s) =
        generated_local_sections_sheafification_comparison ℱ U s := by
    -- Proof comment: the comparison map is defined to be the adjoint transpose of the inclusion.
    simpa [adj, generated_local_sections_sheafification_comparison] using
      (Adjunction.homEquiv_counit adj
        (generated_local_sections_presheaf ℱ U s) ℱ
        (generated_local_sections_presheaf_inclusion ℱ U s))
  rw [← hcomparison]
  have hunit :
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
          (generated_local_sections_presheaf ℱ U s)) ≫
        (PresheafOfModules.restrictScalars (𝟙 (structureRingSheaf X))).map
          ((adj.homEquiv (generated_local_sections_presheaf ℱ U s) ℱ).symm
            (generated_local_sections_presheaf_inclusion ℱ U s)).val =
      (adj.homEquiv (generated_local_sections_presheaf ℱ U s) ℱ)
        ((adj.homEquiv (generated_local_sections_presheaf ℱ U s) ℱ).symm
          (generated_local_sections_presheaf_inclusion ℱ U s)) := by
    -- Proof comment: this is exactly the adjunction unit identity specialized to the inclusion.
    exact (Adjunction.homEquiv_unit adj
      (generated_local_sections_presheaf ℱ U s) ℱ
      ((adj.homEquiv (generated_local_sections_presheaf ℱ U s) ℱ).symm
        (generated_local_sections_presheaf_inclusion ℱ U s))).symm
  exact hunit.trans
    ((adj.homEquiv (generated_local_sections_presheaf ℱ U s) ℱ).apply_symm_apply
      (generated_local_sections_presheaf_inclusion ℱ U s))

/-- Helper for Lemma 17.4.4: the ordinary stalk map induced by a morphism of module presheaves. -/
private noncomputable def presheafStalkMap
    {P Q : PresheafOfModules (structureRingSheaf X)} (x : X) (φ : P ⟶ Q) :
    TopCat.Presheaf.stalk P.presheaf x ⟶ TopCat.Presheaf.stalk Q.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf (structureRingSheaf X)).map φ)

/-- Helper for Lemma 17.4.4: the sheafification unit is bijective on stalks of module
presheaves. -/
private theorem sheafification_unit_stalk_map_bijective
    (P : PresheafOfModules (structureRingSheaf X)) (x : X) :
    Function.Bijective
      (presheafStalkMap (X := X) x
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app P)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf (structureRingSheaf X)).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: forgetting the module structure turns the module sheafification unit into
    -- the additive sheafification unit.
    simpa [η] using
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (structureRingSheaf X)) P
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (structureRingSheaf X)).map η)) := by
    -- Proof comment: additive sheafification preserves stalks.
    rw [hη]
    simpa using
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf
  let fη :
      TopCat.Presheaf.stalk P.presheaf x ⟶
        TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X))).obj P).val.presheaf) x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf (structureRingSheaf X)).map η)
  have hη_iso' : IsIso fη := by
    simpa [fη] using hη_iso
  have hη_bijective : Function.Bijective (ConcreteCategory.hom fη) :=
    (CategoryTheory.isIso_iff_bijective fη).1 hη_iso'
  simpa [presheafStalkMap, η, fη] using hη_bijective

/-- Helper for Lemma 17.4.4: a morphism of `\mathcal O_X`-modules is monic once all of its stalk
maps are injective. -/
private theorem mono_of_stalkwise_injective
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X, Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    Mono φ := by
  let toAbelianSheaf : ModX ⥤ TopCat.Sheaf AddCommGrpCat X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  have hmonoUnderlying : Mono (toAbelianSheaf.map φ) := by
    refine (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map φ)).2 ?_
    intro x
    -- Proof comment: injectivity of the module stalk map is exactly injectivity of the underlying
    -- additive stalk map after forgetting scalars.
    exact (AddCommGrpCat.mono_iff_injective _).2 <| by
      simpa [RingedSpace.moduleStalkMap, toAbelianSheaf] using hφ x
  let _ : Mono (toAbelianSheaf.map φ) := hmonoUnderlying
  refine ⟨?_⟩
  intro Z g h hcomp
  have hmapEq : toAbelianSheaf.map g = toAbelianSheaf.map h :=
    (cancel_mono (toAbelianSheaf.map φ)).1 <| by
      simpa using congrArg (fun k ↦ toAbelianSheaf.map k) hcomp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext t
  simpa [toAbelianSheaf, PresheafOfModules.toPresheaf] using
    congrArg (fun k ↦ (k.hom.app U) t) hmapEq

/-- Helper for Lemma 17.4.4: the comparison from the sheafified explicit generated presheaf into
`\mathcal F` is monic. -/
private theorem generated_local_sections_sheafification_comparison_mono
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Mono (generated_local_sections_sheafification_comparison ℱ U s) := by
  -- Proof comment: the sheafification unit is surjective on stalks, and the unit-comparison
  -- triangle reduces injectivity of the comparison stalk map to injectivity of the explicit
  -- generated-presheaf inclusion on stalks.
  apply mono_of_stalkwise_injective
  intro x
  let P := generated_local_sections_presheaf ℱ U s
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app P)
  have hηsurj : Function.Surjective (presheafStalkMap (X := X) x η) :=
    (sheafification_unit_stalk_map_bijective (X := X) P x).2
  have hιinj :
      Function.Injective
        (presheafStalkMap (X := X) x (generated_local_sections_presheaf_inclusion ℱ U s)) := by
    have hmonoPresheaf :
        Mono ((PresheafOfModules.toPresheaf (structureRingSheaf X)).map
          (generated_local_sections_presheaf_inclusion ℱ U s)) := by
      exact Functor.map_mono (PresheafOfModules.toPresheaf (structureRingSheaf X))
        (generated_local_sections_presheaf_inclusion ℱ U s)
    have hmonoStalk :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (structureRingSheaf X)).map
            (generated_local_sections_presheaf_inclusion ℱ U s))) :=
      (TopCat.Presheaf.mono_iff_stalk_mono
        ((PresheafOfModules.toPresheaf (structureRingSheaf X)).map
          (generated_local_sections_presheaf_inclusion ℱ U s))).1 hmonoPresheaf x
    exact (AddCommGrpCat.mono_iff_injective _).1 hmonoStalk
  intro z z' hz
  rcases hηsurj z with ⟨y, rfl⟩
  rcases hηsurj z' with ⟨y', rfl⟩
  apply hιinj
  have htriangle :
      presheafStalkMap (X := X) x η ≫
          RingedSpace.moduleStalkMap x
            (generated_local_sections_sheafification_comparison ℱ U s) =
        presheafStalkMap (X := X) x (generated_local_sections_presheaf_inclusion ℱ U s) := by
    -- Proof comment: apply the stalk functor to the unit-comparison triangle and identify the
    -- right factor with the module stalk map of the comparison morphism.
    simpa [P, η, presheafStalkMap, RingedSpace.moduleStalkMap] using
      congrArg (presheafStalkMap (X := X) x)
        (generated_local_sections_unit_comp_comparison ℱ U s)
  have hy :
      presheafStalkMap (X := X) x (generated_local_sections_presheaf_inclusion ℱ U s) y =
        presheafStalkMap (X := X) x (generated_local_sections_presheaf_inclusion ℱ U s) y' := by
    calc
      presheafStalkMap (X := X) x (generated_local_sections_presheaf_inclusion ℱ U s) y =
          RingedSpace.moduleStalkMap x
            (generated_local_sections_sheafification_comparison ℱ U s)
            (presheafStalkMap (X := X) x η y) := by
              symm
              exact congrArg (fun k ↦ k y) htriangle
      _ =
          RingedSpace.moduleStalkMap x
            (generated_local_sections_sheafification_comparison ℱ U s)
            (presheafStalkMap (X := X) x η y') := by
              simpa using hz
      _ =
          presheafStalkMap (X := X) x (generated_local_sections_presheaf_inclusion ℱ U s) y' := by
              exact congrArg (fun k ↦ k y') htriangle
  exact hy

/-- Helper for Lemma 17.4.4: use the comparison mono theorem as the local instance needed by
`Subobject.mk` and `Subobject.underlyingIso`. -/
private instance generated_local_sections_sheafification_comparison_mono_inst
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Mono (generated_local_sections_sheafification_comparison ℱ U s) :=
  generated_local_sections_sheafification_comparison_mono ℱ U s

/-- Helper for Lemma 17.4.4: after packaging the sheafified comparison as a subobject, transport
through `Subobject.underlyingIso` recovers the raw comparison on sections. -/
private theorem generated_local_sections_subsheaf_arrow_inv_app_apply
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X)
    (t : ((modSheafification X).obj (generated_local_sections_presheaf ℱ U s)).val.obj (op W)) :
    (((Subobject.mk
        (generated_local_sections_sheafification_comparison ℱ U s)).arrow).val.app (op W))
        (((Subobject.underlyingIso
            (generated_local_sections_sheafification_comparison ℱ U s)).inv.val.app
            (op W)) t) =
      ((generated_local_sections_sheafification_comparison ℱ U s).val.app (op W)) t := by
  -- Proof comment: `generated_local_sections_subsheaf` is `Subobject.mk` of the comparison, so
  -- `Subobject.underlyingIso_arrow` rewrites the packaged arrow back to the original comparison.
  change
    (((Subobject.underlyingIso
          (generated_local_sections_sheafification_comparison ℱ U s)).inv ≫
        (Subobject.mk
          (generated_local_sections_sheafification_comparison ℱ U s)).arrow).val.app
          (op W)).hom t =
      ((generated_local_sections_sheafification_comparison ℱ U s).val.app (op W)).hom t
  simpa using
    congrArg (fun η ↦ (η.val.app (op W)).hom t)
      (Subobject.underlyingIso_arrow
        (generated_local_sections_sheafification_comparison ℱ U s))

/-- Helper for Lemma 17.4.4: if a subsheaf contains the chosen generators, then every explicit
generated section lands in the range of its sectionwise inclusion map. -/
private theorem generated_local_sections_submodule_le_arrow_range_of_contains
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : Opens X) :
    generated_local_sections_submodule ℱ U s W ≤
      LinearMap.range ((H.arrow.val.app (op W)).hom) := by
  -- Proof comment: each restricted generator lifts along `H.arrow`, so the entire span lies in
  -- the range by linearity.
  rw [generated_local_sections_submodule, Submodule.span_le]
  intro x hx
  rcases hx with ⟨i, hWUi, rfl⟩
  rcases hH i with ⟨t, ht⟩
  refine ⟨((Subobject.underlying.obj H).val.map (homOfLE hWUi).op) t, ?_⟩
  change
    ((H.arrow.val.app (op W)).hom
      ((((Subobject.underlying.obj H).val.map (homOfLE hWUi).op).hom t))) =
      ((ℱ.val.map (homOfLE hWUi).op).hom (s i))
  rw [← ht]
  simpa using congrArg (fun g ↦ g.hom t) (H.arrow.val.naturality (homOfLE hWUi).op)

/-- Helper for Lemma 17.4.4: on each open, the section map of a subobject is injective because it
is a component of a monomorphism. -/
private theorem subobject_arrow_app_injective
    (ℱ : ModX) {H : Subobject ℱ} (W : (Opens X)ᵒᵖ) :
    Function.Injective ((H.arrow.val.app W).hom) := by
  -- Proof comment: componentwise monicity of a natural transformation gives injectivity in
  -- `ModuleCat`.
  have hmonoArrow : Mono H.arrow := inferInstance
  have hmonoVal : Mono H.arrow.val := by
    simpa using hmonoArrow
  have hmonoApp : Mono (H.arrow.val.app W) :=
    (NatTrans.mono_iff_mono_app H.arrow.val).1 hmonoVal W
  exact (ModuleCat.mono_iff_injective _).1 hmonoApp

/-- Helper for Lemma 17.4.4: on each open, the explicit generated-presheaf inclusion factors
through the section map of any containing subsheaf. -/
private theorem generated_local_sections_to_subsheaf_app_exists
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : (Opens X)ᵒᵖ) :
    ∃ t : generated_local_sections_presheaf_obj ℱ U s W ⟶ (Subobject.underlying.obj H).val.obj W,
      t ≫ H.arrow.val.app W = (generated_local_sections_presheaf_inclusion ℱ U s).app W := by
  -- Proof comment: the generated-span inclusion lands in the range of `H.arrow` on every open,
  -- so Chapter 6 factors it through that injective section map.
  have hsubset :
      Set.range (((generated_local_sections_presheaf_inclusion ℱ U s).app W).hom) ⊆
        Set.range ((H.arrow.val.app W).hom) := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact generated_local_sections_submodule_le_arrow_range_of_contains ℱ U s hH W x.2
  obtain ⟨t, ht⟩ :=
    morphism_factors_through_of_range_subset_of_injective
      (F := forget (ModuleCat ((structureRingSheaf X).obj W)))
      ((generated_local_sections_presheaf_inclusion ℱ U s).app W)
      (H.arrow.val.app W)
      (subobject_arrow_app_injective (ℱ := ℱ) (H := H) W)
      hsubset
  exact ⟨t, ht.symm⟩

/-- Helper for Lemma 17.4.4: on each open, the explicit generated presheaf factors through any
subsheaf containing the chosen local sections. -/
private noncomputable def generated_local_sections_to_subsheaf_app
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : (Opens X)ᵒᵖ) :
    generated_local_sections_presheaf_obj ℱ U s W ⟶ (Subobject.underlying.obj H).val.obj W :=
  Classical.choose (generated_local_sections_to_subsheaf_app_exists ℱ U s hH W)

/-- Helper for Lemma 17.4.4: the sectionwise factor map into a containing subsheaf composes with
the subobject arrow to the obvious inclusion into `\mathcal F`. -/
private theorem generated_local_sections_to_subsheaf_app_comp_arrow
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : (Opens X)ᵒᵖ) :
    generated_local_sections_to_subsheaf_app ℱ U s hH W ≫ H.arrow.val.app W =
      (generated_local_sections_presheaf_inclusion ℱ U s).app W := by
  -- Proof comment: the app-level factor was chosen exactly to satisfy this commuting relation.
  exact Classical.choose_spec (generated_local_sections_to_subsheaf_app_exists ℱ U s hH W)

/-- Helper for Lemma 17.4.4: the chosen sectionwise factor maps are natural in the open set once
we postcompose with the mono subobject arrow and cancel. -/
private theorem generated_local_sections_to_subsheaf_naturality
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    generated_local_sections_presheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          (generated_local_sections_to_subsheaf_app ℱ U s hH W) =
      generated_local_sections_to_subsheaf_app ℱ U s hH V ≫
        (Subobject.underlying.obj H).val.map f := by
  -- Proof comment: after postcomposing with the restricted section map of `H`, both sides reduce
  -- to the naturality square for the explicit inclusion into `ℱ`.
  let g :=
    (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map (H.arrow.val.app W)
  have hg : Mono g := by
    exact Functor.map_mono (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom)
      (H.arrow.val.app W)
  apply (cancel_mono g).1
  calc
    generated_local_sections_presheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          (generated_local_sections_to_subsheaf_app ℱ U s hH W) ≫
        g
        =
      generated_local_sections_presheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          ((generated_local_sections_to_subsheaf_app ℱ U s hH W) ≫ H.arrow.val.app W) := by
            simp [g, Category.assoc, Functor.map_comp]
    _ =
      generated_local_sections_presheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          ((generated_local_sections_presheaf_inclusion ℱ U s).app W) := by
            rw [generated_local_sections_to_subsheaf_app_comp_arrow]
    _ =
      (generated_local_sections_presheaf_inclusion ℱ U s).app V ≫ ℱ.val.map f := by
        simpa [generated_local_sections_presheaf_inclusion] using
          (generated_local_sections_presheaf_inclusion ℱ U s).naturality f
    _ =
      generated_local_sections_to_subsheaf_app ℱ U s hH V ≫
        H.arrow.val.app V ≫ ℱ.val.map f := by
          rw [generated_local_sections_to_subsheaf_app_comp_arrow]
    _ =
      generated_local_sections_to_subsheaf_app ℱ U s hH V ≫
        (Subobject.underlying.obj H).val.map f ≫ g := by
          rw [Category.assoc]
          congr 1
          simpa [g, Category.assoc] using (H.arrow.val.naturality f).symm

/-- Helper for Lemma 17.4.4: the explicit generated presheaf factors through any subsheaf that
contains the chosen generators. -/
private noncomputable def generated_local_sections_to_subsheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generated_local_sections_presheaf ℱ U s ⟶ (Subobject.underlying.obj H).val :=
  { app := generated_local_sections_to_subsheaf_app ℱ U s hH
    naturality := generated_local_sections_to_subsheaf_naturality ℱ U s hH }

/-- Helper for Lemma 17.4.4: after factoring the explicit generated presheaf through a containing
subsheaf, postcomposing with the subobject arrow recovers the original inclusion. -/
private theorem generated_local_sections_to_subsheaf_comp_arrow
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generated_local_sections_to_subsheaf ℱ U s hH ≫ H.arrow.val =
      generated_local_sections_presheaf_inclusion ℱ U s := by
  -- Proof comment: the presheaf-level factorization is determined objectwise by the chosen app
  -- maps, so `PresheafOfModules.hom_ext` reduces the claim to the app-level comparison above.
  apply PresheafOfModules.hom_ext
  intro W
  exact generated_local_sections_to_subsheaf_app_comp_arrow ℱ U s hH W

/-- Helper for Lemma 17.4.4: sheafifying the sectionwise factorization into a containing subsheaf
produces a morphism from the constructive generated subsheaf candidate into that subsheaf. -/
private noncomputable def generated_local_sections_comparison_to_subsheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    (modSheafification X).obj (generated_local_sections_presheaf ℱ U s) ⟶ H :=
  (modSheafification X).map (generated_local_sections_to_subsheaf ℱ U s hH) ≫
    ((asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureRingSheaf X))).counit).app H).hom

/-- Helper for Lemma 17.4.4: the sheafified factorization into a containing subsheaf composes back
to the raw comparison map into `\mathcal F`. -/
private theorem generated_local_sections_comparison_to_subsheaf_comp_arrow
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generated_local_sections_comparison_to_subsheaf ℱ U s hH ≫ H.arrow =
      generated_local_sections_sheafification_comparison ℱ U s := by
  -- Proof comment: sheafify the presheaf-level factorization and then use counit naturality to
  -- move from the sheafified underlying object of `H` back to `H` itself.
  let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).counit
  calc
    generated_local_sections_comparison_to_subsheaf ℱ U s hH ≫ H.arrow
        =
      (modSheafification X).map (generated_local_sections_to_subsheaf ℱ U s hH) ≫
        (e.app H).hom ≫ H.arrow := by
          simp [generated_local_sections_comparison_to_subsheaf, e, Category.assoc]
    _ =
      (modSheafification X).map (generated_local_sections_to_subsheaf ℱ U s hH) ≫
        (modSheafification X).map H.arrow.val ≫ (e.app ℱ).hom := by
          rw [← Category.assoc]
          simpa [e, Category.assoc] using
            (PresheafOfModules.sheafificationAdjunction
              (𝟙 (structureRingSheaf X))).counit.naturality H.arrow
    _ =
      (modSheafification X).map
          (generated_local_sections_to_subsheaf ℱ U s hH ≫ H.arrow.val) ≫
        (e.app ℱ).hom := by
          rw [Functor.map_comp, Category.assoc]
    _ =
      (modSheafification X).map (generated_local_sections_presheaf_inclusion ℱ U s) ≫
        (e.app ℱ).hom := by
          rw [generated_local_sections_to_subsheaf_comp_arrow]
    _ = generated_local_sections_sheafification_comparison ℱ U s := by
          rfl

/-- Helper for Lemma 17.4.4: the constructive generated subsheaf built from the explicit
generated-presheaf and sheafification comparison. -/
private noncomputable abbrev generated_local_sections_subsheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    : Subobject ℱ :=
  -- Proof comment: package the sheafified comparison map as a subobject, using the local mono
  -- instance proved by the stalk-triangle argument above.
  Subobject.mk (generated_local_sections_sheafification_comparison ℱ U s)

/-- Helper for Lemma 17.4.4: the constructive generated subsheaf contains the prescribed local
sections. -/
private lemma generated_local_sections_contains_local_sections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    subsheaf_contains_local_sections ℱ U s (generated_local_sections_subsheaf ℱ U s) := by
  intro i
  let t : (generated_local_sections_presheaf ℱ U s).obj (op (U i)) :=
    ⟨ℱ.val.map (homOfLE (show U i ≤ U i from le_rfl)).op (s i),
      generated_local_sections_generator_mem ℱ U s i⟩
  refine ⟨((Subobject.underlyingIso
      (generated_local_sections_sheafification_comparison ℱ U s)).inv.val.app
      (op (U i)))
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
          (generated_local_sections_presheaf ℱ U s)).app (op (U i))) t), ?_⟩
  -- Proof comment: after unpacking the subobject arrow, the unit-comparison triangle identifies
  -- the image of the tautological generator with the original chosen section `s i`.
  have harrow :
      ((generated_local_sections_subsheaf ℱ U s).arrow.val.app (op (U i)))
          (((Subobject.underlyingIso
              (generated_local_sections_sheafification_comparison ℱ U s)).inv.val.app
              (op (U i)))
            ((((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
                (generated_local_sections_presheaf ℱ U s)).app (op (U i))) t)) =
        ((generated_local_sections_sheafification_comparison ℱ U s).val.app (op (U i)))
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
              (generated_local_sections_presheaf ℱ U s)).app (op (U i))) t) := by
    simpa [generated_local_sections_subsheaf] using
      (generated_local_sections_subsheaf_arrow_inv_app_apply ℱ U s (U i)
        ((((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
            (generated_local_sections_presheaf ℱ U s)).app (op (U i))) t))
  rw [harrow]
  have hsection :
      ((((SheafOfModules.forget (structureRingSheafObj X) ⋙
            PresheafOfModules.restrictScalars (𝟙 (structureRingSheaf X))).map
          (generated_local_sections_sheafification_comparison ℱ U s)).app (op (U i))).hom)
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X))).unit.app
              (generated_local_sections_presheaf ℱ U s)).app (op (U i))) t) =
        (((generated_local_sections_presheaf_inclusion ℱ U s).app (op (U i))).hom) t := by
    exact congrArg (fun η ↦ (η.app (op (U i))).hom t)
      (generated_local_sections_unit_comp_comparison ℱ U s)
  simpa [t] using hsection

/-- Helper for Lemma 17.4.4: any subsheaf containing the prescribed local sections also contains
the constructive generated subsheaf. -/
private lemma generated_local_sections_le_of_contains
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generated_local_sections_subsheaf ℱ U s ≤ H := by
  let γ := generated_local_sections_comparison_to_subsheaf ℱ U s hH
  have hγ : γ ≫ H.arrow = generated_local_sections_sheafification_comparison ℱ U s :=
    generated_local_sections_comparison_to_subsheaf_comp_arrow ℱ U s hH
  -- Proof comment: once the sheafified comparison factors through `H`, `Subobject.mk_le_of_comm`
  -- packages the factorization as an inequality of subobjects.
  exact Subobject.mk_le_of_comm γ hγ

/-- Lemma 17.4.4: for a ringed space `X`, an `\mathcal O_X`-module sheaf `ℱ`, and local sections
`s i ∈ ℱ(U i)`, there exists a unique smallest subsheaf of `ℱ` containing all the `s i`. -/
@[stacks 01AP]
theorem existsUnique_subsheaf_generated_by_local_sections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    ∃! G : Subobject ℱ,
      IsLeast { H : Subobject ℱ | subsheaf_contains_local_sections ℱ U s H } G := by
  -- Route correction: the order-theoretic `sInf` proof needs extra `WellPowered` infrastructure
  -- that is not part of the current theorem statement, so we isolate the intended sheafification
  -- candidate and the two source-faithful properties it must satisfy.
  let G : Subobject ℱ := generated_local_sections_subsheaf ℱ U s
  refine ⟨G, ?_, ?_⟩
  · refine ⟨generated_local_sections_contains_local_sections ℱ U s, ?_⟩
    intro H hH
    exact generated_local_sections_le_of_contains ℱ U s hH
  · intro H hH
    apply le_antisymm
    · exact hH.2 (generated_local_sections_contains_local_sections ℱ U s)
    · exact generated_local_sections_le_of_contains ℱ U s hH.1

end

end AlgebraicGeometry
