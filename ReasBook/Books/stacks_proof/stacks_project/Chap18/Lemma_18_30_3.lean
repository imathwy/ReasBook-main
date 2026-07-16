import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import stacks_proof.stacks_project.Chap07.Definition_7_17_1
import stacks_proof.stacks_project.Chap18.Lemma_18_3_1
import stacks_proof.stacks_project.Chap07.Lemma_7_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Limits.CoproductsFromFiniteFiltered

noncomputable section

universe w v u

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 18.30.3: the transition maps in the finite-subcoproduct diagram of
set-valued sheaves are monomorphisms. -/
private lemma finiteSubcoproductsSheafTransition_mono
    {ι : Type w} (F : ι → Sheaf J (Type (max u v)))
    {s t : Finset (Discrete ι)} (h : s ⟶ t) :
    Mono ((liftToFinsetObj (Discrete.functor F)).map h) := by
  -- Route correction: work directly on sections and identify the component map with the explicit
  -- finite-coproduct inclusion coming from `leOfHom h`.
  refine CategoryTheory.Sheaf.mono_of_injective
    (φ := ((liftToFinsetObj (Discrete.functor F)).map h)) ?_
  intro U
  let ιst : s → t := fun y ↦ ⟨y.1, (leOfHom h) y.2⟩
  have hmono :
      Mono (Limits.Sigma.desc fun y : s ↦
        Limits.Sigma.ι (fun x : t ↦ (F x.1.as).1.obj U) (ιst y)) :=
    CategoryTheory.Limits.MonoCoprod.mono_of_injective'
      (fun x : t ↦ (F x.1.as).1.obj U) ιst (by
        intro a b hab
        exact Subtype.ext <| congrArg Subtype.val hab)
  letI := hmono
  -- Convert the categorical mono statement in `Type` into injectivity of the section map.
  simpa [liftToFinsetObj, Discrete.functor, ιst] using
    (CategoryTheory.injective_of_mono
      (Limits.Sigma.desc fun y : s ↦
        Limits.Sigma.ι (fun x : t ↦ (F x.1.as).1.obj U) (ιst y)))

/-- Helper for Lemma 18.30.3: monicity of the underlying additive-sheaf map reflects back to
monicity of the original morphism of `𝒪`-module sheaves. -/
private lemma monoOfToSheafMapMono
    (𝒪 : Sheaf J RingCat.{u}) {𝒢 ℋ : SheafOfModules 𝒪} (φ : 𝒢 ⟶ ℋ)
    [Mono ((SheafOfModules.toSheaf 𝒪).map φ)] :
    Mono φ := by
  -- Faithfulness of `toSheaf` lets us reflect left-cancellation from additive sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (SheafOfModules.toSheaf 𝒪).map_injective
  apply (cancel_mono ((SheafOfModules.toSheaf 𝒪).map φ)).1
  simpa using congrArg ((SheafOfModules.toSheaf 𝒪).map) hgh

/-- Helper for Lemma 18.30.3: the transition maps in the finite-subcoproduct diagram of
`\mathcal O`-modules are monomorphisms. -/
private lemma finiteSubcoproductsModuleTransition_mono
    (𝒪 : Sheaf J RingCat.{u}) [HasFiniteCoproducts (SheafOfModules 𝒪)]
    {ι : Type w} (F : ι → SheafOfModules 𝒪)
    {s t : Finset (Discrete ι)} (h : s ⟶ t) :
    Mono ((liftToFinsetObj (Discrete.functor F)).map h) := by
  let φ := ((liftToFinsetObj (Discrete.functor F)).map h)
  have htoSheafMono : Mono ((SheafOfModules.toSheaf 𝒪).map φ) := by
    -- Route correction: prove monicity after forgetting to additive sheaves, where the section map
    -- is still the explicit finite direct-sum inclusion.
    refine CategoryTheory.Sheaf.mono_of_injective
      (φ := (SheafOfModules.toSheaf 𝒪).map φ) ?_
    intro U
    let ιst : s → t := fun y ↦ ⟨y.1, (leOfHom h) y.2⟩
    have hmono :
        Mono (Limits.Sigma.desc fun y : s ↦
          Limits.Sigma.ι (fun x : t ↦ (F x.1.as).1.obj (op U)) (ιst y)) :=
      CategoryTheory.Limits.MonoCoprod.mono_of_injective'
        (fun x : t ↦ (F x.1.as).1.obj (op U)) ιst (by
          intro a b hab
          exact Subtype.ext <| congrArg Subtype.val hab)
    letI := hmono
    -- The underlying additive-sheaf component is the same function as the module component.
    simpa [φ, liftToFinsetObj, Discrete.functor, ιst] using
      ((ModuleCat.mono_iff_injective
          (Limits.Sigma.desc fun y : s ↦
            Limits.Sigma.ι (fun x : t ↦ (F x.1.as).1.obj (op U)) (ιst y))).1 inferInstance)
  letI : Mono ((SheafOfModules.toSheaf 𝒪).map φ) := htoSheafMono
  -- Reflect monicity back from additive sheaves to sheaves of `𝒪`-modules.
  exact monoOfToSheafMapMono (𝒪 := 𝒪) φ

/- Domain-style sampling for Lemma 18.30.3:
- primary domain: sections functors on sheaves and sheaves of modules over a Grothendieck site,
  with quasi-compactness controlling preservation of arbitrary coproducts/direct sums;
- sampled owner declarations:
  `sheafSections`,
  `SheafOfModules.evaluation`,
  `SheafOfModules.toSheaf`,
  `forget₂`;
- best owner abstraction: the canonical owner for sections of set-valued sheaves is
  `(sheafSections J (Type (max u v))).obj (op W)`, while the module-valued sections owner is
  `SheafOfModules.evaluation 𝒪 (op W)`, and the source-facing additive-sections functor is its
  abelian-group bridge
  `SheafOfModules.evaluation 𝒪 (op W) ⋙
    forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}`;
- primitive-vs-derived split:
  primitive data are only the site `(C, J)`, the quasi-compact object `W`, and the index type `ι`;
  the module-valued evaluation functor is the core owner, while the textbook `Ab`-valued sections
  functor is derived by forgetting scalars from that owner;
- source/core/bridge triage:
  `source-facing`: preservation of coproducts/direct sums by sections over a quasi-compact object;
  `core/canonical`: `sheafSections` and `SheafOfModules.evaluation`;
  `bridge/view`: passage from module-valued sections to abelian-group-valued sections by
  `forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat`. -/

local instance (ι : Type w) :
    HasColimitsOfShape (Finset (Discrete ι)) (Sheaf J (Type (max u v))) := by
  -- The sheaf category already has all small colimits, so finite-support diagrams are available.
  infer_instance

local instance (ι : Type w) [Finite ι] :
    HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) := by
  -- Finite discrete diagrams admit colimits because the sheaf category has finite coproducts.
  infer_instance

local instance (ι : Type w) :
    HasColimitsOfShape (Finset (Discrete ι)) (Type (max u v)) := by
  -- `Type` has all small colimits, so the finite-support target diagram is available automatically.
  infer_instance

local instance (𝒪 : Sheaf J RingCat.{u}) (ι : Type w) :
    HasColimitsOfShape (Finset (Discrete ι)) (SheafOfModules 𝒪) := by
  -- The module-sheaf category has all small colimits, so the finite-support diagram is available.
  infer_instance

local instance (ι : Type w) [Finite ι] :
    HasColimitsOfShape (Discrete ι) (Type (max u v)) := by
  -- In particular, finite discrete coproducts of section types exist.
  infer_instance

/-- Helper for Chap18 Lemma 18 30 3: in any category with the required coproducts and colimits,
the ambient discrete coproduct is the colimit of the finite-support diagram. -/
private noncomputable def finiteSubcoproductsColimitIso
    {D : Type*} [Category D] [HasFiniteCoproducts D]
    {ι : Type w} [HasColimitsOfShape (Finset (Discrete ι)) D]
    [HasColimitsOfShape (Discrete ι) D] (F : ι → D) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) := by
  -- Compare the standard discrete coproduct cocone with the finite-support colimit cocone.
  exact (isColimitFiniteSubproductsCocone F).coconePointUniqueUpToIso
    (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))

/-- Helper for Chap18 Lemma 18 30 3: the `hom` of the generic finite-support comparison sends a
finite-stage inclusion to the corresponding colimit leg. -/
private lemma finiteSubcoproductsColimitIso_hom_app
    {D : Type*} [Category D] [HasFiniteCoproducts D]
    {ι : Type w} [HasColimitsOfShape (Finset (Discrete ι)) D]
    [HasColimitsOfShape (Discrete ι) D] (F : ι → D) (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finiteSubcoproductsColimitIso F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- The generic comparison isomorphism is characterized by the finite-support cocone legs.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finiteSubcoproductsColimitIso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitFiniteSubproductsCocone F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Chap18 Lemma 18 30 3: on a singleton support, the generic finite-support
comparison identifies the discrete coproduct injection with the singleton stage leg. -/
private lemma finiteSubcoproductsColimitIso_hom_singleton
    {D : Type*} [Category D] [HasFiniteCoproducts D]
    {ι : Type w} [HasColimitsOfShape (Finset (Discrete ι)) D]
    [HasColimitsOfShape (Discrete ι) D] (F : ι → D) (i : Discrete ι) :
    colimit.ι (Discrete.functor F) i ≫ (finiteSubcoproductsColimitIso F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) ({i} : Finset (Discrete ι)) := by
  -- The singleton finite support recovers the original coproduct injection.
  simpa using finiteSubcoproductsColimitIso_hom_app (F := F) ({i} : Finset (Discrete ι))

/-- Helper for Chap18 Lemma 18 30 3: the inverse of the generic finite-support comparison sends a
colimit leg back to the corresponding finite-stage inclusion. -/
private lemma finiteSubcoproductsColimitIso_inv_app
    {D : Type*} [Category D] [HasFiniteCoproducts D]
    {ι : Type w} [HasColimitsOfShape (Finset (Discrete ι)) D]
    [HasColimitsOfShape (Discrete ι) D] (F : ι → D) (s : Finset (Discrete ι)) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) s ≫
        (finiteSubcoproductsColimitIso F).inv =
      Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) := by
  -- This is the inverse cocone-leg identity for the same generic comparison isomorphism.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finiteSubcoproductsColimitIso] using
    (IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitFiniteSubproductsCocone F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Chap18 Lemma 18 30 3: on a singleton support, the inverse generic finite-support
comparison recovers the original coproduct injection. -/
private lemma finiteSubcoproductsColimitIso_inv_singleton
    {D : Type*} [Category D] [HasFiniteCoproducts D]
    {ι : Type w} [HasColimitsOfShape (Finset (Discrete ι)) D]
    [HasColimitsOfShape (Discrete ι) D] (F : ι → D) (i : Discrete ι) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) ({i} : Finset (Discrete ι)) ≫
        (finiteSubcoproductsColimitIso F).inv =
      colimit.ι (Discrete.functor F) i := by
  -- The singleton finite stage is exactly the original summand of the discrete coproduct.
  simpa using finiteSubcoproductsColimitIso_inv_app (F := F) ({i} : Finset (Discrete ι))

/-- Helper for Lemma 18.30.3: the finite-support cocone of a sheaf family is a colimit cocone. -/
private noncomputable def finiteSubcoproductsSheafCoconeIsColimit
    {ι : Type w} (F : ι → Sheaf J (Type (max u v))) :
    IsColimit (finiteSubcoproductsCocone F) :=
  isColimitFiniteSubproductsCocone F

/-- Helper for Lemma 18.30.3: the ambient coproduct of a sheaf family identifies with the colimit
of its finite-support diagram. -/
private noncomputable def finiteSubcoproductsSheafColimitIso
    {ι : Type w} (F : ι → Sheaf J (Type (max u v))) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) :=
  finiteSubcoproductsColimitIso F

/-- Helper for Lemma 18.30.3: the `hom` of the finite-support colimit comparison sends each
finite-stage inclusion to the corresponding colimit leg. -/
private lemma finiteSubcoproductsSheafColimitIso_hom_app
    {ι : Type w} (F : ι → Sheaf J (Type (max u v))) (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finiteSubcoproductsSheafColimitIso (J := J) F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- This is the generic finite-support comparison specialized to sheaves.
  simpa [finiteSubcoproductsSheafColimitIso] using
    finiteSubcoproductsColimitIso_hom_app
      (D := Sheaf J (Type (max u v))) F s

/-- Helper for Lemma 18.30.3: the inverse finite-support comparison sends each colimit leg back
to the corresponding finite-stage inclusion. -/
private lemma finiteSubcoproductsSheafColimitIso_inv_app
    {ι : Type w} (F : ι → Sheaf J (Type (max u v))) (s : Finset (Discrete ι)) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) s ≫
        (finiteSubcoproductsSheafColimitIso (J := J) F).inv =
      Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) := by
  -- This is the generic inverse finite-support comparison specialized to sheaves.
  simpa [finiteSubcoproductsSheafColimitIso] using
    finiteSubcoproductsColimitIso_inv_app
      (D := Sheaf J (Type (max u v))) F s

/-- Helper for Chap18 Lemma 18 30 3: on a singleton support, the inverse finite-support
comparison recovers the original coproduct injection. -/
private lemma finiteSubcoproductsSheafColimitIso_inv_singleton
    {ι : Type w} (F : ι → Sheaf J (Type (max u v))) (i : Discrete ι) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) ({i} : Finset (Discrete ι)) ≫
        (finiteSubcoproductsSheafColimitIso (J := J) F).inv =
      colimit.ι (Discrete.functor F) i := by
  -- The singleton finite stage is exactly the original summand of the discrete coproduct.
  simpa using finiteSubcoproductsSheafColimitIso_inv_app (J := J) F ({i} : Finset (Discrete ι))

/-- Helper for Lemma 18.30.3: the finite-support cocone of a module-sheaf family is a colimit
cocone. -/
private noncomputable def finiteSubcoproductsModuleCoconeIsColimit
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (F : ι → SheafOfModules 𝒪) :
    IsColimit (finiteSubcoproductsCocone F) :=
  isColimitFiniteSubproductsCocone F

/-- Helper for Lemma 18.30.3: the ambient coproduct of a module-sheaf family identifies with the
colimit of its finite-support diagram. -/
private noncomputable def finiteSubcoproductsModuleColimitIso
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (F : ι → SheafOfModules 𝒪) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) :=
  finiteSubcoproductsColimitIso F

/-- Helper for Lemma 18.30.3: the `hom` of the module finite-support comparison sends each
finite-stage inclusion to the corresponding colimit leg. -/
private lemma finiteSubcoproductsModuleColimitIso_hom_app
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (F : ι → SheafOfModules 𝒪)
    (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finiteSubcoproductsModuleColimitIso (J := J) 𝒪 F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- This is the generic finite-support comparison specialized to module sheaves.
  simpa [finiteSubcoproductsModuleColimitIso] using
    finiteSubcoproductsColimitIso_hom_app
      (D := SheafOfModules 𝒪) F s

/-- Helper for Chap18 Lemma 18 30 3: the inverse module finite-support comparison sends each
colimit leg back to the corresponding finite-stage inclusion. -/
private lemma finiteSubcoproductsModuleColimitIso_inv_app
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (F : ι → SheafOfModules 𝒪)
    (s : Finset (Discrete ι)) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) s ≫
        (finiteSubcoproductsModuleColimitIso (J := J) 𝒪 F).inv =
      Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) := by
  -- This is the generic inverse finite-support comparison specialized to module sheaves.
  simpa [finiteSubcoproductsModuleColimitIso] using
    finiteSubcoproductsColimitIso_inv_app
      (D := SheafOfModules 𝒪) F s

/-- Helper for Chap18 Lemma 18 30 3: on a singleton support, the inverse module finite-support
comparison recovers the original coproduct injection. -/
private lemma finiteSubcoproductsModuleColimitIso_inv_singleton
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (F : ι → SheafOfModules 𝒪) (i : Discrete ι) :
    colimit.ι (liftToFinsetObj (Discrete.functor F)) ({i} : Finset (Discrete ι)) ≫
        (finiteSubcoproductsModuleColimitIso (J := J) 𝒪 F).inv =
      colimit.ι (Discrete.functor F) i := by
  -- The singleton finite stage is exactly the original module summand.
  simpa using
    finiteSubcoproductsModuleColimitIso_inv_app (J := J) 𝒪 F ({i} : Finset (Discrete ι))

/-- Helper for Lemma 18.30.3: sections over `W` commute with each finite-support coproduct stage
through the canonical coproduct comparison. -/
private noncomputable def finiteSubcoproductsSheafSectionsNatIso
    {ι : Type w} (W : C) (F : ι → Sheaf J (Type (max u v))) :
    liftToFinsetObj (Discrete.functor F) ⋙ ((sheafSections J (Type (max u v))).obj (op W)) ≅
      liftToFinsetObj
        (Discrete.functor (fun i ↦ ((sheafSections J (Type (max u v))).obj (op W)).obj (F i))) := by
  classical
  refine NatIso.ofComponents
    (fun s ↦
      (PreservesCoproduct.iso
        ((sheafSections J (Type (max u v))).obj (op W))
        (fun i : s ↦ F i.1.as)).symm)
    ?_
  intro s t h
  -- Compare the transition maps after precomposing with each coproduct injection of the source
  -- finite stage.
  apply Limits.Sigma.hom_ext
  intro i
  simp [liftToFinsetObj, Category.assoc, Limits.map_ι_comp_inv_sigmaComparison]

/-- Helper for Lemma 18.30.3: after forgetting scalars, evaluation over `W` commutes with each
finite-support coproduct stage through the canonical coproduct comparison. -/
private noncomputable def finiteSubcoproductsModuleSectionsNatIso
    {ι : Type w} (𝒪 : Sheaf J RingCat.{u}) (W : C) (F : ι → SheafOfModules 𝒪) :
    liftToFinsetObj (Discrete.functor F) ⋙
        (SheafOfModules.evaluation 𝒪 (op W) ⋙
          forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}) ≅
      liftToFinsetObj
        (Discrete.functor
          (fun i ↦
            ((SheafOfModules.evaluation 𝒪 (op W) ⋙
              forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}).obj (F i)))) := by
  classical
  refine NatIso.ofComponents
    (fun s ↦
      (PreservesCoproduct.iso
        (SheafOfModules.evaluation 𝒪 (op W) ⋙
          forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v})
        (fun i : s ↦ F i.1.as)).symm)
    ?_
  intro s t h
  -- The additive-group comparison has the same summandwise normal form.
  apply Limits.Sigma.hom_ext
  intro i
  simp [liftToFinsetObj, Category.assoc, Limits.map_ι_comp_inv_sigmaComparison]

/-- Helper for Chap18 Lemma 18 30 3: the discrete sections comparison factors through the
finite-support filtered comparison for set-valued sheaves. -/
private lemma sheafSectionsDiscreteComparison_factorization
    {ι : Type w} (W : C) (F : ι → Sheaf J (Type (max u v))) :
    colimit.post (Discrete.functor F) ((sheafSections J (Type (max u v))).obj (op W)) =
        (finiteSubcoproductsColimitIso
          (fun i ↦ ((sheafSections J (Type (max u v))).obj (op W)).obj (F i))).hom ≫
          (HasColimit.isoOfNatIso
            (finiteSubcoproductsSheafSectionsNatIso (J := J) W F)).inv ≫
          colimit.post (liftToFinsetObj (Discrete.functor F))
            ((sheafSections J (Type (max u v))).obj (op W)) ≫
          ((sheafSections J (Type (max u v))).obj (op W)).map
            (finiteSubcoproductsSheafColimitIso (J := J) F).inv := by
  let ΓW := ((sheafSections J (Type (max u v))).obj (op W))
  let S : ι → Type (max u v) := fun i ↦ ΓW.obj (F i)
  -- Compare the two maps on each summand of the discrete coproduct of sections.
  apply colimit.hom_ext
  intro i
  calc
    colimit.ι (Discrete.functor S) i ≫ colimit.post (Discrete.functor F) ΓW =
      ΓW.map (colimit.ι (Discrete.functor F) i) := by
      rw [colimit.ι_post]
    _ = colimit.ι (Discrete.functor S) i ≫
          (finiteSubcoproductsColimitIso S).hom ≫
            (HasColimit.isoOfNatIso (finiteSubcoproductsSheafSectionsNatIso (J := J) W F)).inv ≫
            colimit.post (liftToFinsetObj (Discrete.functor F)) ΓW ≫
            ΓW.map (finiteSubcoproductsSheafColimitIso (J := J) F).inv := by
        -- Normalize through the singleton finite stage, then apply the finite-support comparison.
        rw [Category.assoc]
        rw [finiteSubcoproductsColimitIso_hom_singleton]
        rw [HasColimit.isoOfNatIso_ι_inv_assoc]
        rw [Category.assoc]
        rw [colimit.ι_post]
        rw [Functor.map_comp]
        rw [finiteSubcoproductsSheafColimitIso_inv_singleton]
        simp [ΓW, S, finiteSubcoproductsSheafSectionsNatIso, liftToFinsetObj, Category.assoc,
          Limits.map_ι_comp_inv_sigmaComparison]

/-- Helper for Chap18 Lemma 18 30 3: the quasi-compact additive sections comparison factors
through the finite-support filtered comparison for sheaves of modules. -/
private lemma moduleSectionsDiscreteComparison_isIsoOfQuasiCompact
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (W : C) (hW : J.QuasiCompactObject W)
    (F : ι → SheafOfModules 𝒪) :
    IsIso
      (colimit.post (Discrete.functor F)
        (SheafOfModules.evaluation 𝒪 (op W) ⋙
          forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v})) := by
  let ΓW :=
    (SheafOfModules.evaluation 𝒪 (op W) ⋙
      forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v})
  let D : Finset (Discrete ι) ⥤ SheafOfModules 𝒪 :=
    liftToFinsetObj (Discrete.functor F)
  have hFiltered : IsIso (colimit.post D ΓW) := by
    -- The finite-support module diagram is filtered and its transition maps are monomorphisms.
    refine sheafFilteredColimitSectionsComparison_isIso_of_quasiCompactObject_of_transitionMonomorphisms
      (J := J) D W hW ?_
    intro s t h
    simpa [D, ΓW] using finiteSubcoproductsModuleTransition_mono (J := J) 𝒪 F h
  letI : IsIso (colimit.post D ΓW) := hFiltered
  letI : PreservesColimit D ΓW :=
    preservesColimit_of_isIso_post (F := D) (G := ΓW)
  let S : ι → AddCommGrpCat.{max u v} := fun i ↦ ΓW.obj (F i)
  have hFactor :
      colimit.post (Discrete.functor F) ΓW =
        (finiteSubcoproductsColimitIso S).hom ≫
          (HasColimit.isoOfNatIso
            (finiteSubcoproductsModuleSectionsNatIso (J := J) 𝒪 W F)).inv ≫
          colimit.post D ΓW ≫
          ΓW.map (finiteSubcoproductsModuleColimitIso (J := J) 𝒪 F).inv := by
    -- Compare the two maps on each summand of the discrete coproduct of module sections.
    apply colimit.hom_ext
    intro i
    calc
      colimit.ι (Discrete.functor S) i ≫ colimit.post (Discrete.functor F) ΓW =
        ΓW.map (colimit.ι (Discrete.functor F) i) := by
        rw [colimit.ι_post]
      _ =
        colimit.ι (Discrete.functor S) i ≫
          (finiteSubcoproductsColimitIso S).hom ≫
            (HasColimit.isoOfNatIso
              (finiteSubcoproductsModuleSectionsNatIso (J := J) 𝒪 W F)).inv ≫
            colimit.post D ΓW ≫
            ΓW.map (finiteSubcoproductsModuleColimitIso (J := J) 𝒪 F).inv := by
          -- Normalize through the singleton finite stage, then use the finite-support comparison.
          rw [Category.assoc]
          rw [finiteSubcoproductsColimitIso_hom_singleton]
          rw [HasColimit.isoOfNatIso_ι_inv_assoc]
          rw [Category.assoc]
          rw [colimit.ι_post]
          rw [Functor.map_comp]
          rw [finiteSubcoproductsModuleColimitIso_inv_singleton (J := J) 𝒪 F]
          simp [ΓW, S, finiteSubcoproductsModuleSectionsNatIso, liftToFinsetObj, Category.assoc,
            Limits.map_ι_comp_inv_sigmaComparison]
  -- The factorization writes the additive comparison as a composition of isomorphisms.
  rw [← hFactor]
  infer_instance

/-- Helper for Chap18 Lemma 18 30 3: forgetting scalars transports the module-valued comparison
map to the additive comparison map by the standard `colimit.post_post` formula. -/
private lemma moduleEvaluationComparison_post_forget
    (𝒪 : Sheaf J RingCat.{u}) {ι : Type w} (W : C) (F : ι → SheafOfModules 𝒪) :
    colimit.post
        (Discrete.functor F ⋙ SheafOfModules.evaluation 𝒪 (op W))
        (forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}) ≫
      (forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}).map
        (colimit.post (Discrete.functor F) (SheafOfModules.evaluation 𝒪 (op W))) =
      colimit.post (Discrete.functor F)
        (SheafOfModules.evaluation 𝒪 (op W) ⋙
          forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}) := by
  -- This is the standard transport of a colimit comparison through a composite functor.
  simpa using
    (colimit.post_post
      (F := Discrete.functor F)
      (G := SheafOfModules.evaluation 𝒪 (op W))
      (H := forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}))

/-- Helper for Lemma 18.30.3: quasi-compact sections identify the discrete coproduct comparison
with the filtered finite-support comparison. -/
private lemma sheafSectionsDiscreteComparison_isIsoOfQuasiCompact
    {ι : Type w} (W : C) (hW : J.QuasiCompactObject W)
    (F : ι → Sheaf J (Type (max u v))) :
    IsIso (colimit.post (Discrete.functor F) ((sheafSections J (Type (max u v))).obj (op W))) := by
  let D : Finset (Discrete ι) ⥤ Sheaf J (Type (max u v)) :=
    liftToFinsetObj (Discrete.functor F)
  have hFiltered :
      IsIso (colimit.post D ((sheafSections J (Type (max u v))).obj (op W))) := by
    -- The finite-support diagram is filtered and its transition maps are monomorphisms.
    refine sheafFilteredColimitSectionsComparison_isIso_of_quasiCompactObject_of_transitionMonomorphisms
      (J := J) D W hW ?_
    intro s t h
    simpa [D] using finiteSubcoproductsSheafTransition_mono (J := J) F h
  letI : IsIso (colimit.post D ((sheafSections J (Type (max u v))).obj (op W))) := hFiltered
  letI :
      PreservesColimit D ((sheafSections J (Type (max u v))).obj (op W)) :=
    preservesColimit_of_isIso_post
      (F := D) (G := ((sheafSections J (Type (max u v))).obj (op W)))
  -- The discrete comparison is the finite-support comparison conjugated by the bridge isomorphisms.
  rw [← sheafSectionsDiscreteComparison_factorization (J := J) W F]
  infer_instance


-- Proof sketch: write an arbitrary coproduct of sheaves as the filtered colimit over its finite
-- subcoproducts; the transition maps are monomorphisms, so Lemma 7.17.7 identifies sections over a
-- quasi-compact object `W` with the corresponding colimit of sections.
/-- Lemma 18.30.3 (1): if `W` is quasi-compact, then taking sections over `W` defines a functor
`Sh(\mathcal{C}) \to \mathrm{Sets}` that preserves coproducts. -/
@[stacks 0935]
theorem quasiCompactObject_sheaf_sections_preserves_coproducts
    (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) ((sheafSections J (Type (max u v))).obj (op W)) := by
  refine ⟨fun F ↦ ?_⟩
  -- Each discrete comparison map is an isomorphism by the finite-support bridge above.
  let _ : IsIso (colimit.post (Discrete.functor F) ((sheafSections J (Type (max u v))).obj (op W))) :=
    sheafSectionsDiscreteComparison_isIsoOfQuasiCompact (J := J) W hW F
  exact preservesColimit_of_isIso_post
    (F := Discrete.functor F)
    (G := ((sheafSections J (Type (max u v))).obj (op W)))

-- Proof sketch: forget the `𝒪(W)`-module structure on sections from the stronger owner-level
-- module-valued statement below. This gives the source-facing additive-sections functor
-- `Mod(𝒪) ⥤ AddCommGrpCat`. The stronger module-valued statement for
-- `SheafOfModules.evaluation 𝒪 (op W)` is a companion owner-level refinement.
/-- Companion owner-level form of Lemma 18.30.3 (2): for quasi-compact `W`, the stronger
module-valued sections functor `Mod(\mathcal{O}) \to \mathrm{Mod}(\mathcal{O}(W))` also preserves
direct sums. -/
theorem quasiCompactObject_module_evaluation_preserves_direct_sums
    (𝒪 : Sheaf J RingCat.{u}) (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (SheafOfModules.evaluation 𝒪 (op W)) := by
  refine ⟨fun F ↦ ?_⟩
  let G :=
    (forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v})
  let α := colimit.post (Discrete.functor F) (SheafOfModules.evaluation 𝒪 (op W))
  let β := colimit.post (Discrete.functor F ⋙ SheafOfModules.evaluation 𝒪 (op W)) G
  have hAdditive :
      IsIso (colimit.post (Discrete.functor F) (SheafOfModules.evaluation 𝒪 (op W) ⋙ G)) :=
    moduleSectionsDiscreteComparison_isIsoOfQuasiCompact (J := J) 𝒪 W hW F
  let _ : IsIso β := by
    infer_instance
  let _ : IsIso (G.map α) := by
    have hComposite : IsIso (β ≫ G.map α) := by
      -- The forgotten comparison map is the standard `post_post` composite.
      dsimp [α, β]
      rw [moduleEvaluationComparison_post_forget (J := J) 𝒪 W F]
      exact hAdditive
    let _ : IsIso (β ≫ G.map α) := hComposite
    exact IsIso.of_isIso_comp_left β (G.map α)
  let _ : IsIso α := isIso_of_reflects_iso α G
  -- Reflect the forgotten additive comparison back to the module-valued comparison.
  exact preservesColimit_of_isIso_post
    (F := Discrete.functor F)
    (G := SheafOfModules.evaluation 𝒪 (op W))

/-- Helper for Lemma 18.30.3: a morphism in the finite-support index category is exactly an
inclusion of the smaller finite support into the larger one. -/
private lemma mem_of_finiteSubcoproductHom
    {ι : Type w} {s t : Finset (Discrete ι)} (h : s ⟶ t) (y : s) :
    y.1 ∈ t :=
  (leOfHom h) y.2

-- Proof sketch: forget the `𝒪(W)`-module structure on sections from the stronger owner-level
-- module-valued statement above. This gives the source-facing additive-sections functor
-- `Mod(𝒪) ⥤ AddCommGrpCat`. The stronger module-valued statement for
-- `SheafOfModules.evaluation 𝒪 (op W)` is a companion owner-level refinement.
/-- Lemma 18.30.3 (2): if `W` is quasi-compact, then for any sheaf of rings `𝒪` the functor
`Mod(\mathcal{O}) \to \mathrm{Ab}` given by sections over `W` preserves direct sums. -/
@[stacks 0935]
theorem quasiCompactObject_module_sections_preserves_direct_sums
    (𝒪 : Sheaf J RingCat.{u}) (W : C) (hW : J.QuasiCompactObject W) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.evaluation 𝒪 (op W) ⋙
        forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}) := by
  -- The owner-level module-evaluation theorem supplies the direct-sum preservation on modules.
  let _ : PreservesColimitsOfShape (Discrete ι) (SheafOfModules.evaluation 𝒪 (op W)) :=
    quasiCompactObject_module_evaluation_preserves_direct_sums (J := J) 𝒪 W hW ι
  -- Forgetting scalars from `𝒪(W)`-modules to abelian groups preserves all colimits.
  let _ :
      PreservesColimitsOfShape (Discrete ι)
        (forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v}) := by
    infer_instance
  -- Compose the two preservation statements to obtain the source-facing additive-sections functor.
  exact CategoryTheory.Limits.comp_preservesColimitsOfShape
    (SheafOfModules.evaluation 𝒪 (op W))
    (forget₂ (ModuleCat (𝒪.1.obj (op W))) AddCommGrpCat.{max u v})

end
