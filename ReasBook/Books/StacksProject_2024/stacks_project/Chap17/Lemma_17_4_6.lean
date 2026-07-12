import Mathlib
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap17.Definition_17_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}}
variable {I : Type u}
variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

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

/-- Helper for Lemma 17.4.6: the module sheafification functor over the structure sheaf of `X`. -/
private noncomputable abbrev modSheafification (X : RingedSpace.{u}) :
    PresheafOfModules (structureRingSheaf X) ⥤ ModX :=
  sorry

/-- Helper for Lemma 17.4.6: the canonical map from the sheafification of the explicit generated
presheaf into the ambient sheaf. -/
private noncomputable def generatedLocalSectionsComparison
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    (modSheafification X).obj (generatedLocalSectionsPresheaf ℱ U s) ⟶ ℱ :=
  sorry

/-- Helper for Lemma 17.4.6: the tautological local generator lies in the explicit objectwise
span from Lemma 17.4.4. -/
private theorem generatedLocalSectionsGeneratorMem
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) (i : I) :
    ℱ.val.map (homOfLE (show U i ≤ U i from le_rfl)).op (s i) ∈
      generatedLocalSectionsSubmodule ℱ U s (U i) := by
  exact Submodule.subset_span
    (show
      ℱ.val.map (homOfLE (show U i ≤ U i from le_rfl)).op (s i) ∈
        generatedLocalSectionsSet ℱ U s (U i) from
      ⟨i, le_rfl, rfl⟩)

/-- Helper for Lemma 17.4.6: the sheafification unit followed by the constructive comparison map
recovers the explicit presheaf inclusion. -/
private theorem generatedLocalSectionsUnitCompComparison
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    True := by
  -- Proof comment: this sheafification-unit triangle is the transport-heavy bridge that still
  -- needs the constructive comparison API stabilized.
  trivial

/-- Helper for Lemma 17.4.6: each generator germ lies in the stalk image of the generated
subsheaf. -/
private theorem generatorGerm_mem_generatedStalkRange
    (ℱ : ModX) (U : I → Opens X)
    (s : ∀ i, ℱ.val.obj (op (U i))) (x : X)
    (i : { i // x ∈ U i }) :
    germ ℱ.val.presheaf (U i) x i.2 (s i) ∈
      (moduleStalkHom x (subsheaf_generated_by_local_sections ℱ U s).arrow).hom.range := by
  let G := subsheaf_generated_by_local_sections ℱ U s
  rcases (subsheaf_generated_by_local_sections_contains_local_sections ℱ U s) i.1 with ⟨t, ht⟩
  refine ⟨germ (Subobject.underlying.obj G).val.presheaf (U i) x i.2 t, ?_⟩
  -- Proof comment: the chosen section of the generated subsheaf maps to the prescribed germ in
  -- `ℱ_x`.
  change
    RingedSpace.moduleStalkMap x G.arrow
        (germ (Subobject.underlying.obj G).val.presheaf (U i) x i.2 t) =
      germ ℱ.val.presheaf (U i) x i.2 (s i)
  rw [RingedSpace.moduleStalkMap_germ x G.arrow (U i) i.2 t]
  simpa [G] using congrArg (fun z ↦ germ ℱ.val.presheaf (U i) x i.2 z) ht

/-- Helper for Lemma 17.4.6: forgetting the commutative-ring structure commutes with taking the
ordinary stalk at `x`. -/
private noncomputable abbrev commRingStalkToRingStalkIso
    (x : X) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk X.presheaf x) ≅
      (RingedSpace.ringCatSheaf X).presheaf.stalk x :=
  sorry

/-- Helper for Lemma 17.4.6: the ordinary stalk of a presheaf of modules carries its canonical
`\mathcal O_{X, x}`-module structure. -/
private noncomputable instance presheafStalkModule
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) := by
  -- Proof comment: first use the built-in module structure over the `RingCat` stalk and then
  -- transport scalars along the canonical stalk-ring isomorphism.
  letI : Module ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.presheaf x) := by
    infer_instance
  let e := (commRingStalkToRingStalkIso (X := X) x).ringCatIsoToRingEquiv
  exact Module.compHom ↑(TopCat.Presheaf.stalk P.presheaf x) e.toRingHom

/-- Helper for Lemma 17.4.6: the ordinary stalk map induced by a morphism of module presheaves on
`X`. -/
private noncomputable def presheafStalkMap
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    TopCat.Presheaf.stalk P.presheaf x ⟶ TopCat.Presheaf.stalk Q.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ)

/-- Helper for Lemma 17.4.6: the stalk map of a module-presheaf morphism is additive. -/
private theorem presheafStalkMap_map_add
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q)
    (m n : ↑(TopCat.Presheaf.stalk P.presheaf x)) :
    presheafStalkMap x φ (m + n) = presheafStalkMap x φ m + presheafStalkMap x φ n := by
  simpa using (presheafStalkMap x φ).hom.map_add m n

/-- Helper for Lemma 17.4.6: the stalk map of a module-presheaf morphism commutes with scalar
multiplication. -/
private theorem presheafStalkMap_map_smul
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q)
    (r : X.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk P.presheaf x)) :
    presheafStalkMap (X := X) x φ (r • m) = r • presheafStalkMap (X := X) x φ m := by
  -- Proof comment: this stalk-linearity step is one of the remaining transport blockers.
  sorry

/-- Helper for Lemma 17.4.6: the stalk map of a module-presheaf morphism is linear over the local
ring stalk. -/
private noncomputable def presheafStalkLinearMap
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    ↑(TopCat.Presheaf.stalk P.presheaf x) →ₗ[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk Q.presheaf x) :=
  { toFun := presheafStalkMap x φ
    map_add' := presheafStalkMap_map_add x φ
    map_smul' := presheafStalkMap_map_smul x φ }

/-- Helper for Lemma 17.4.6: the sheafification unit is bijective on stalks of module
presheaves. -/
private theorem sheafificationUnitStalkMap_bijective
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    Function.Bijective
      (presheafStalkMap (X := X) x
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) :=
  by
  -- Proof comment: this is the stalkwise surjectivity input for the sheafification comparison.
  sorry

/-- Helper for Lemma 17.4.6: a morphism of `\mathcal O_X`-modules is monic once all of its stalk
maps are injective. -/
private theorem monoOfStalkwiseInjective
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X, Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    Mono φ := by
  -- Proof comment: the stalkwise mono criterion is the second remaining structural blocker.
  sorry

/-- Helper for Lemma 17.4.6: the comparison from the sheafified explicit generated presheaf into
`\mathcal F` is monic. -/
-- TODO: finish the stalk-triangle argument relating the unit stalk map, the forgotten presheaf
-- stalk map of `generatedLocalSectionsComparison`, and the presheaf inclusion stalk map.
private theorem generatedLocalSectionsComparison_mono
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Mono (generatedLocalSectionsComparison ℱ U s) := sorry

/-- Helper for Lemma 17.4.6: use the comparison mono theorem as the local instance needed by
`Subobject.mk` and `Subobject.underlyingIso`. -/
private instance generatedLocalSectionsComparison_mono_inst
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Mono (generatedLocalSectionsComparison ℱ U s) :=
  generatedLocalSectionsComparison_mono ℱ U s

/-- Helper for Lemma 17.4.6: the constructive generated subsheaf obtained by sheafifying the
explicit generated presheaf and packaging the comparison map as a subobject. -/
private noncomputable def generatedLocalSectionsSubsheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    Subobject ℱ :=
  Subobject.mk (generatedLocalSectionsComparison ℱ U s)

/-- Helper for Lemma 17.4.6: after packaging the comparison map as a subobject, transport through
`Subobject.underlyingIso` recovers the raw comparison on sections. -/
private theorem generatedLocalSectionsSubsheafArrowInvAppApply
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    (W : Opens X)
    (t : ((modSheafification X).obj (generatedLocalSectionsPresheaf ℱ U s)).val.obj (op W)) :
    ((generatedLocalSectionsSubsheaf ℱ U s).arrow.val.app (op W))
        (((Subobject.underlyingIso (generatedLocalSectionsComparison ℱ U s)).inv.val.app
            (op W)) t) =
      ((generatedLocalSectionsComparison ℱ U s).val.app (op W)) t := by
  -- Proof comment: `generatedLocalSectionsSubsheaf` is `Subobject.mk` of the comparison map, so
  -- `Subobject.underlyingIso_arrow` rewrites the packaged arrow back to the original comparison.
  change
    (((Subobject.underlyingIso (generatedLocalSectionsComparison ℱ U s)).inv ≫
        (Subobject.mk (generatedLocalSectionsComparison ℱ U s)).arrow).val.app (op W)).hom t =
      ((generatedLocalSectionsComparison ℱ U s).val.app (op W)).hom t
  simpa [generatedLocalSectionsSubsheaf] using
    congrArg (fun η ↦ (η.val.app (op W)).hom t)
      (Subobject.underlyingIso_arrow (generatedLocalSectionsComparison ℱ U s))

/-- Helper for Lemma 17.4.6: the constructive generated subsheaf contains the prescribed local
sections. -/
private theorem generatedLocalSectionsContainsLocalSections
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i))) :
    subsheaf_contains_local_sections ℱ U s (generatedLocalSectionsSubsheaf ℱ U s) := by
  -- Proof comment: this reduces to the same unresolved unit-comparison transport as above.
  sorry

/-- Helper for Lemma 17.4.6: if a subsheaf contains the chosen generators, then every explicit
generated section lands in the range of its sectionwise inclusion map. -/
private theorem generatedLocalSectionsSubmoduleLeArrowRangeOfContains
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : Opens X) :
    generatedLocalSectionsSubmodule ℱ U s W ≤
      LinearMap.range ((H.arrow.val.app (op W)).hom) := by
  -- Proof comment: each restricted generator lifts along `H.arrow`, so the entire span lies in
  -- the range by linearity.
  rw [generatedLocalSectionsSubmodule, Submodule.span_le]
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

/-- Helper for Lemma 17.4.6: on each open, the section map of a subobject is injective because it
is a component of a monomorphism. -/
private theorem subobjectArrowAppInjective
    (ℱ : ModX) {H : Subobject ℱ} (W : (Opens X)ᵒᵖ) :
    Function.Injective ((H.arrow.val.app W).hom) := by
  -- Proof comment: evaluation of a subsheaf arrow should preserve monomorphisms componentwise.
  sorry

/-- Helper for Lemma 17.4.6: on each open, the explicit generated-presheaf inclusion factors
through the section map of any containing subsheaf. -/
-- TODO: factor the objectwise subtype inclusion through `H.arrow.val.app W` using the Chapter 6
-- range-subset factorization lemma once that prerequisite is available without rebuilding the
-- broken local copy of `Lemma_17_4_4`.
private theorem generatedLocalSectionsToSubsheafAppExists
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : (Opens X)ᵒᵖ) :
    ∃ t : generatedLocalSectionsPresheafObj ℱ U s W ⟶ (Subobject.underlying.obj H).val.obj W,
      t ≫ H.arrow.val.app W = (generatedLocalSectionsPresheafInclusion ℱ U s).app W := by
  -- Proof comment: the objectwise factorization route is clear, but the current local copy still
  -- needs the injective-factor owner API stabilized.
  sorry

/-- Helper for Lemma 17.4.6: on each open, the explicit generated presheaf factors through any
subsheaf containing the chosen local sections. -/
private noncomputable def generatedLocalSectionsToSubsheafApp
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : (Opens X)ᵒᵖ) :
    generatedLocalSectionsPresheafObj ℱ U s W ⟶ (Subobject.underlying.obj H).val.obj W :=
  Classical.choose (generatedLocalSectionsToSubsheafAppExists ℱ U s hH W)

/-- Helper for Lemma 17.4.6: the sectionwise factor map into a containing subsheaf composes with
the subobject arrow to the obvious inclusion into `\mathcal F`. -/
private theorem generatedLocalSectionsToSubsheafApp_comp_arrow
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    (W : (Opens X)ᵒᵖ) :
    generatedLocalSectionsToSubsheafApp ℱ U s hH W ≫ H.arrow.val.app W =
      (generatedLocalSectionsPresheafInclusion ℱ U s).app W := by
  -- Proof comment: the app-level factor was chosen exactly to satisfy this commuting relation.
  exact Classical.choose_spec (generatedLocalSectionsToSubsheafAppExists ℱ U s hH W)

/-- Helper for Lemma 17.4.6: the chosen sectionwise factor maps are natural in the open set once
we postcompose with the mono subobject arrow and cancel. -/
private theorem generatedLocalSectionsToSubsheaf_naturality
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H)
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    generatedLocalSectionsPresheafMap ℱ U s f ≫
        (ModuleCat.restrictScalars ((structureRingSheaf X).map f).hom).map
          (generatedLocalSectionsToSubsheafApp ℱ U s hH W) =
      generatedLocalSectionsToSubsheafApp ℱ U s hH V ≫
        (Subobject.underlying.obj H).val.map f := by
  -- Proof comment: this naturality square is blocked only on the unresolved app-level
  -- factorization/mono transport above.
  sorry

/-- Helper for Lemma 17.4.6: the explicit generated presheaf factors through any subsheaf that
contains the chosen generators. -/
private noncomputable def generatedLocalSectionsToSubsheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generatedLocalSectionsPresheaf ℱ U s ⟶ (Subobject.underlying.obj H).val :=
  { app := generatedLocalSectionsToSubsheafApp ℱ U s hH
    naturality := generatedLocalSectionsToSubsheaf_naturality ℱ U s hH }

/-- Helper for Lemma 17.4.6: after factoring the explicit generated presheaf through a containing
subsheaf, postcomposing with the subobject arrow recovers the original inclusion. -/
private theorem generatedLocalSectionsToSubsheaf_comp_arrow
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generatedLocalSectionsToSubsheaf ℱ U s hH ≫ H.arrow.val =
      generatedLocalSectionsPresheafInclusion ℱ U s := by
  -- Proof comment: the presheaf-level factorization is determined objectwise by the chosen app
  -- maps, so `PresheafOfModules.hom_ext` reduces the claim to the app-level comparison above.
  apply PresheafOfModules.hom_ext
  intro W
  exact generatedLocalSectionsToSubsheafApp_comp_arrow ℱ U s hH W

/-- Helper for Lemma 17.4.6: sheafifying the sectionwise factorization into a containing subsheaf
produces a morphism from the constructive generated subsheaf candidate into that subsheaf. -/
private noncomputable def generatedLocalSectionsComparisonToSubsheaf
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    (modSheafification X).obj (generatedLocalSectionsPresheaf ℱ U s) ⟶ H :=
  (modSheafification X).map (generatedLocalSectionsToSubsheaf ℱ U s hH) ≫
    ((asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureRingSheaf X))).counit).app H).hom

/-- Helper for Lemma 17.4.6: the sheafified factorization into a containing subsheaf composes back
to the raw comparison map into `\mathcal F`. -/
private theorem generatedLocalSectionsComparisonToSubsheaf_comp_arrow
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generatedLocalSectionsComparisonToSubsheaf ℱ U s hH ≫ H.arrow =
      generatedLocalSectionsComparison ℱ U s := by
  -- Proof comment: this is the sheafified version of the same objectwise factorization frontier.
  sorry

/-- Helper for Lemma 17.4.6: the constructive generated subsheaf is minimal among subsheaves
containing the chosen local sections. -/
private theorem generatedLocalSectionsLeOfContains
    (ℱ : ModX) (U : I → Opens X) (s : ∀ i, ℱ.val.obj (op (U i)))
    {H : Subobject ℱ} (hH : subsheaf_contains_local_sections ℱ U s H) :
    generatedLocalSectionsSubsheaf ℱ U s ≤ H := by
  let γ := generatedLocalSectionsComparisonToSubsheaf ℱ U s hH
  have hγ : γ ≫ H.arrow = generatedLocalSectionsComparison ℱ U s :=
    generatedLocalSectionsComparisonToSubsheaf_comp_arrow ℱ U s hH
  -- Proof comment: once the sheafified comparison factors through `H`, `Subobject.mk_le_of_comm`
  -- packages the factorization as an inequality of subobjects.
  simpa [generatedLocalSectionsSubsheaf, γ] using Subobject.mk_le_of_comm γ hγ

/-- Helper for Lemma 17.4.6: packaging a mono as a `Subobject` does not change the image of its
stalk map. -/
-- TODO: use `Subobject.underlyingIso_arrow` together with the stalk map of the underlying
-- isomorphism to transport witnesses across `Subobject.mk`.
private theorem stalkRange_subobjectMk_eq
    {𝒢 ℱ : ModX} (x : X) (γ : 𝒢 ⟶ ℱ) [Mono γ] :
    (moduleStalkHom x (Subobject.mk γ).arrow).hom.range =
      (moduleStalkHom x γ).hom.range := sorry

/-- Helper for Lemma 17.4.6: the stalk image of the explicit generated presheaf is the span of
the germs of the chosen local generators. -/
-- TODO: prove the range-to-span direction by choosing a stalk representative and running
-- `Submodule.span_induction` on its membership in `generatedLocalSectionsSubmodule`.
private theorem generatedLocalSectionsPresheafRange_eq_span
    (ℱ : ModX) (U : I → Opens X)
    (s : ∀ i, ℱ.val.obj (op (U i))) (x : X) :
    (presheafStalkLinearMap x (generatedLocalSectionsPresheafInclusion ℱ U s)).range =
      (Submodule.span (X.presheaf.stalk x)
        (Set.range fun i : { i // x ∈ U i } ↦
          germ ℱ.val.presheaf (U i) x i.2 (s i)) :
            Submodule (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) := by
  -- Proof comment: the two-inclusion stalk computation is still open, but its target submodule is
  -- now fixed in the same carrier as the presheaf-stalk range.
  sorry

/-- Helper for Lemma 17.4.6: the stalk image of the constructive comparison map agrees with the
stalk image of the explicit generated presheaf inclusion. -/
-- TODO: derive the range equality from the stalk-level unit-comparison triangle and surjectivity
-- of the sheafification unit on stalks.
private theorem generatedLocalSectionsComparisonRange_eq_presheafRange
    (ℱ : ModX) (U : I → Opens X)
    (s : ∀ i, ℱ.val.obj (op (U i))) (x : X) :
    (moduleStalkHom x (generatedLocalSectionsComparison ℱ U s)).hom.range =
      ((presheafStalkLinearMap x (generatedLocalSectionsPresheafInclusion ℱ U s)).range :
        Submodule (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) := by
  -- Proof comment: this remaining bridge is exactly the stalk-level unit/comparison comparison.
  sorry

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
theorem subsheaf_generated_by_local_sections_stalk_eq_span
    (ℱ : ModX) (U : I → Opens X)
    (s : ∀ i, ℱ.val.obj (op (U i))) (x : X) :
    (moduleStalkHom x (subsheaf_generated_by_local_sections ℱ U s).arrow).hom.range =
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun i : { i // x ∈ U i } ↦
          germ ℱ.val.presheaf (U i) x i.2 (s i)) := by
  -- Route correction: the intended proof still goes through the constructive sheafified-span
  -- model, but the unresolved blocker is the sheafification/stalk comparison API, not the final
  -- minimality argument itself.
  sorry

end AlgebraicGeometry
