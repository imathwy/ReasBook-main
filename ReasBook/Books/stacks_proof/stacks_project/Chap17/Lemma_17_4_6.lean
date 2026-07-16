import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap06.Lemma_6_15_4
import stacks_proof.stacks_project.Chap06.Lemma_6_17_6
import stacks_proof.stacks_project.Chap06.Lemma_6_20_1
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4
import stacks_proof.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace PresheafOfModules
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}}
variable {I : Type u}

local notation "ModX" => RingedSpace.Modules X

/-- Helper for Chap17 Lemma 17 4 6: a subsheaf contains the indexed local sections `s i` when
each `s i` lifts to a section of that subsheaf over `U i`. -/
def subsheaf_contains_local_sections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (G : Subobject ℱ) : Prop :=
  let ι := G.arrow.val
  ∀ i, s i ∈ Set.range (ι.app (op (U i)))

/-- Helper for Lemma 17.4.6: the structure sheaf of rings on the underlying space of `X`, viewed
in `RingCat`. -/
private abbrev structureRingSheaf (X : RingedSpace.{u}) :=
  (RingedSpace.ringCatSheaf X).obj

/-- Helper for Lemma 17.4.6: the structure sheaf of rings on `X` as a sheaf object. -/
private abbrev structureRingSheafObj (X : RingedSpace.{u}) :=
  RingedSpace.ringCatSheaf X

/-- Helper for Lemma 17.4.6: the explicit objectwise span used by the constructive generated
subsheaf model from Lemma 17.4.4. -/
private def generatedLocalSectionsSet
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X) : Set (ℱ.val.obj (op W)) :=
  { x | ∃ i, ∃ h : W ≤ U i, x = ℱ.val.map (homOfLE h).op (s i) }

/-- Helper for Lemma 17.4.6: the explicit objectwise span used by the constructive generated
subsheaf model from Lemma 17.4.4. -/
private def generatedLocalSectionsSubmodule
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X) : Submodule ((structureRingSheaf X).obj (op W)) (ℱ.val.obj (op W)) :=
  Submodule.span ((structureRingSheaf X).obj (op W)) (generatedLocalSectionsSet ℱ U s W)

/-- Helper for Lemma 17.4.6: restriction preserves membership in the explicit generated
submodules. -/
private theorem generatedLocalSectionsMapMem
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (x : generatedLocalSectionsSubmodule ℱ U s V.unop) :
    ℱ.val.map f x.1 ∈ generatedLocalSectionsSubmodule ℱ U s W.unop := by
  -- Proof comment: restriction of a generator remains a generator on the smaller open, so the
  -- span is stable under all presheaf restriction maps.
  refine Submodule.span_induction
      (p := fun y _ ↦ ℱ.val.map f y ∈ generatedLocalSectionsSubmodule ℱ U s W.unop)
      ?_ ?_ ?_ ?_ x.2
  · intro y hy
    rcases hy with ⟨i, hi, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨i, le_trans (leOfHom f.unop) hi, ?_⟩
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
      (show (ℱ.val.map f).hom (0 : ℱ.val.obj V) ∈ generatedLocalSectionsSubmodule ℱ U s W.unop
        from by
          rw [(ℱ.val.map f).hom.map_zero]
          exact Submodule.zero_mem _)
  · intro y z hy hz hy' hz'
    rw [(ℱ.val.map f).hom.map_add]
    exact Submodule.add_mem _ hy' hz'
  · intro a y hy hy'
    rw [(ℱ.val.map f).hom.map_smulₛₗ]
    exact Submodule.smul_mem (generatedLocalSectionsSubmodule ℱ U s W.unop)
      (((structureRingSheaf X).map f).hom a) hy'

/-- Helper for Lemma 17.4.6: the presheaf of explicit finite linear combinations of the prescribed
local sections from Lemma 17.4.4. -/
private noncomputable abbrev generatedLocalSectionsPresheafObj
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : (Opens X)ᵒᵖ) :
    ModuleCat ((structureRingSheaf X).obj W) :=
  ModuleCat.of ((structureRingSheaf X).obj W) (generatedLocalSectionsSubmodule ℱ U s W.unop)

/-- Helper for Lemma 17.4.6: the restriction maps for the explicit generated presheaf. -/
private noncomputable def generatedLocalSectionsPresheafMap
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    generatedLocalSectionsPresheafObj ℱ U s V ⟶
      (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).obj
        (generatedLocalSectionsPresheafObj ℱ U s W) := by
  -- Proof comment: the objectwise restriction map is the ambient restriction map, with target
  -- membership supplied by `generatedLocalSectionsMapMem`.
  letI : Module ((structureRingSheaf X).obj V) (ℱ.val.obj W) :=
    Module.compHom (ℱ.val.obj W) ((structureRingSheaf X).map f).hom
  letI : Module ((structureRingSheaf X).obj V) ↥(generatedLocalSectionsSubmodule ℱ U s W.unop) :=
    Module.compHom ↥(generatedLocalSectionsSubmodule ℱ U s W.unop)
      ((structureRingSheaf X).map f).hom
  change
    ModuleCat.of ((structureRingSheaf X).obj V)
        (generatedLocalSectionsSubmodule ℱ U s V.unop) ⟶
      ModuleCat.of ((structureRingSheaf X).obj V)
        (generatedLocalSectionsSubmodule ℱ U s W.unop)
  refine ModuleCat.ofHom
    { toFun := fun x ↦ ⟨(ℱ.val.map f).hom x.1, generatedLocalSectionsMapMem ℱ U s f x⟩
      map_add' := fun x y ↦ by
        apply Subtype.ext
        simpa using (ℱ.val.map f).hom.map_add x.1 y.1
      map_smul' := fun a x ↦ by
        apply Subtype.ext
        simpa using (ℱ.val.map f).hom.map_smulₛₗ a x.1 }

/-- Helper for Lemma 17.4.6: the explicit generated presheaf respects identity restrictions. -/
private theorem generatedLocalSectionsPresheafMap_id
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : (Opens X)ᵒᵖ) :
    generatedLocalSectionsPresheafMap ℱ U s (𝟙 W) =
      (ModuleCat.restrictScalarsId' ((structureRingSheaf X).map (𝟙 W)).hom
        (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_id W))).inv.app
        (generatedLocalSectionsPresheafObj ℱ U s W) := by
  -- Proof comment: both sides are induced by the identity endomorphism on the ambient section
  -- module `ℱ(W)`.
  refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  apply Subtype.ext
  change (ℱ.val.map (𝟙 W)).hom x.1 =
      ((ModuleCat.restrictScalarsId' ((structureRingSheaf X).map (𝟙 W)).hom
        (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_id W))).inv.app
        (ℱ.val.obj W)).hom x.1
  exact congrArg (fun g ↦ g x.1) (congrArg ModuleCat.Hom.hom (ℱ.val.map_id W))

/-- Helper for Lemma 17.4.6: the explicit generated presheaf respects composite restrictions. -/
private theorem generatedLocalSectionsPresheafMap_comp
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) :
    generatedLocalSectionsPresheafMap ℱ U s (f ≫ g) =
      generatedLocalSectionsPresheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          (generatedLocalSectionsPresheafMap ℱ U s g) ≫
        (ModuleCat.restrictScalarsComp' ((structureRingSheaf X).map f).hom
          ((structureRingSheaf X).map g).hom ((structureRingSheaf X).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((structureRingSheaf X).map_comp f g))).inv.app
          (generatedLocalSectionsPresheafObj ℱ U s Z) := by
  -- Proof comment: this is just the functoriality of the ambient restriction maps on `ℱ`.
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

/-- Helper for Lemma 17.4.6: the presheaf whose sections are finite `\mathcal O_X`-linear
combinations of the chosen generators. -/
private noncomputable def generatedLocalSectionsPresheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    PresheafOfModules (structureRingSheaf X) where
  obj := generatedLocalSectionsPresheafObj ℱ U s
  map := generatedLocalSectionsPresheafMap ℱ U s
  map_id := generatedLocalSectionsPresheafMap_id ℱ U s
  map_comp := generatedLocalSectionsPresheafMap_comp ℱ U s

/-- Helper for Lemma 17.4.6: the canonical presheaf inclusion of the explicit generated-span
presheaf into the ambient sheaf. -/
private noncomputable def generatedLocalSectionsPresheafInclusion
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    generatedLocalSectionsPresheaf ℱ U s ⟶ ℱ.val where
  app W := ModuleCat.ofHom (generatedLocalSectionsSubmodule ℱ U s W.unop).subtype
  naturality f := by
    -- Proof comment: both sides are the ambient restriction map on `ℱ`, followed by forgetting
    -- the submodule proof.
    refine ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
    rfl

/-- Helper for Lemma 17.4.6: the generated-presheaf inclusion is objectwise injective. -/
private theorem generatedLocalSectionsPresheafInclusionAppInjective
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X) :
    Function.Injective (((generatedLocalSectionsPresheafInclusion ℱ U s).app (op W)).hom) := by
  -- Proof comment: the inclusion only forgets the membership proof in the generated submodule.
  intro x y hxy
  exact Subtype.ext hxy

/-- Helper for Lemma 17.4.6: the explicit generated-presheaf inclusion is monic. -/
private theorem generatedLocalSectionsPresheafInclusion_mono
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Mono (generatedLocalSectionsPresheafInclusion ℱ U s) := by
  -- Proof comment: monicity is checked objectwise because presheaves of modules form a functor
  -- category and the inclusion is injective on each open set.
  refine ⟨?_⟩
  intro P g h hgh
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext t
  apply generatedLocalSectionsPresheafInclusionAppInjective ℱ U s W.unop
  exact congrArg (fun k ↦ ((k.app W).hom) t) hgh

/-- Helper for Chap17 Lemma 17 4 6: the generated subsheaf is the sheafified-span object
associated to the explicit generated presheaf. -/
noncomputable def subsheaf_generated_by_local_sections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Subobject ℱ := sorry

/-- Helper for Chap17 Lemma 17 4 6: the generated subsheaf contains the prescribed local
sections. -/
theorem subsheaf_generated_by_local_sections_contains_local_sections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    subsheaf_contains_local_sections ℱ U s (subsheaf_generated_by_local_sections ℱ U s) := sorry

/-- Helper for Chap17 Lemma 17 4 6: the generated subsheaf is minimal among subsheaves containing
the prescribed local sections. -/
theorem subsheaf_generated_by_local_sections_le
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {G : Subobject ℱ} (hG : subsheaf_contains_local_sections ℱ U s G) :
    subsheaf_generated_by_local_sections ℱ U s ≤ G := sorry

/- Domain-style sampling for Lemma 17.4.6:
- primary domain: stalks of sheaves of modules on a ringed space and subsheaves generated by local
  sections;
- sampled owner declarations:
  `RingedSpace.moduleStalkHom`,
  `RingedSpace.moduleStalkMap_germ`,
  `subsheaf_generated_by_local_sections`,
  `TopCat.Presheaf.germ`;
- best owner abstraction: the canonical stalk morphism
  `RingedSpace.moduleStalkHom x (subsheaf_generated_by_local_sections ℱ U s).arrow`;
- primitive data: the family of opens `U`, the local sections `s`, and the point `x`;
- derived API: the explicit family of germs
  `fun i : { i // x ∈ U i } ↦ germ ℱ.val.presheaf (U i) x i.2 (s i)`.

Source/core/bridge triage:
- `source-facing`: the stalk image equals the submodule generated by the germs of the chosen local
  sections;
- `core/canonical`: `subsheaf_generated_by_local_sections` together with
  `RingedSpace.moduleStalkHom`;
- `bridge/view`: the explicit germ family indexed by `{ i // x ∈ U i }`. -/

-- Proof sketch: the image of the canonical stalk morphism from the generated subsheaf contains
-- the germs of all local generators, because each generator lifts to a local section of that
-- subsheaf. The reverse inclusion uses the minimality of the generated subsheaf.
/-- Lemma 17.4.6: the image of the canonical stalk morphism from
`subsheaf_generated_by_local_sections ℱ U s` is the `\mathcal O_{X, x}`-submodule of `ℱ_x`
generated by the germs `s_{i, x}` for those `i` with `x ∈ U i`. -/
@[stacks 01AR]
theorem subsheaf_generated_by_local_sections_stalk_eq_span
    (ℱ : ModX) (U : I → Opens X)
    (s : ∀ i, ℱ.val.obj (op (U i))) (x : X) :
    (moduleStalkHom x (subsheaf_generated_by_local_sections ℱ U s).arrow).hom.range =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i : { i // x ∈ U i } ↦
          germ ℱ.val.presheaf (U i) x i.2 (s i)) := sorry

end AlgebraicGeometry
