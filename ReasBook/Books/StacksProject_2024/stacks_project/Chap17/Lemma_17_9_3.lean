import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap07.Lemma_7_41_2
import StacksProject_2024.stacks_project.Chap17.Definition_17_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open CategoryTheory.ObjectProperty

noncomputable section

universe u v u'

/- Domain-style sampling for Lemma 17.9.3:
- primary domain: finite-type sheaves of modules over a sheaf of rings on a site;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `CategoryTheory.ObjectProperty.IsClosedUnderQuotients`,
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`,
  `SheafOfModules.finiteTypeModuleProperty_isClosedUnderIsomorphisms`,
  `Abelian.factorThruImage`;
- owner abstraction: the canonical owner predicate `SheafOfModules.IsFiniteType`, used directly
  through its `ObjectProperty` view;
- primitive data: local finite generating families, as provided by
  `SheafOfModules.IsFiniteType.exists_localGeneratorsData`;
- derived API: closure under quotients, images, and short exact extensions.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claims that finite-type modules are stable under images and
  extensions;
- `core/canonical`: the owner predicate `SheafOfModules.IsFiniteType` and its object-property
  packaging;
- `bridge/view`: the ringed-space specialization obtained by taking `R = (RingedSpace.ringCatSheaf X)`.

The file should therefore state the closure facts at the generic `SheafOfModules` owner layer,
with ringed spaces only as a specialization, rather than as parallel ringed-space-specific global
theorems. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {ℱ 𝒢 : SheafOfModules R}

/-- Helper for Lemma 17.9.3: restricting an `R`-module sheaf to the slice site `J.over X` is the
canonical pushforward functor along the identity comparison morphism of sheaves of rings. -/
abbrev overRestrictionFunctor (X : C) : SheafOfModules R ⥤ SheafOfModules (R.over X) :=
  SheafOfModules.pushforward
    (CategoryTheory.CategoryStruct.id
      (((CategoryTheory.Over.forget X).sheafPushforwardContinuous RingCat (J.over X) J).obj R))

namespace GeneratingSections

omit [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Helper for Lemma 17.9.3: pushing a finite generating family through an epimorphism preserves
finiteness of the indexing type. -/
lemma isFiniteType_ofEpi {M N : SheafOfModules R} (σ : M.GeneratingSections)
    [σ.IsFiniteType] (p : M ⟶ N) [Epi p] :
    (σ.ofEpi p).IsFiniteType := by
  -- `GeneratingSections.ofEpi` keeps the same index type, so only the original finiteness matters.
  refine ⟨?_⟩
  simpa [SheafOfModules.GeneratingSections.ofEpi] using (inferInstance : Finite σ.I)

end GeneratingSections

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Helper for Lemma 17.9.3: if the underlying additive-sheaf map is epi, then the original
module-sheaf map is epi. -/
lemma epi_of_toSheaf_map_epi {M N : SheafOfModules R} (p : M ⟶ N)
    [Epi ((SheafOfModules.toSheaf R).map p)] : Epi p := by
  -- Faithfulness of `toSheaf` reflects the right-cancellation property from additive sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (SheafOfModules.toSheaf R).map_injective
  apply (cancel_epi ((SheafOfModules.toSheaf R).map p)).1
  simpa using congrArg ((SheafOfModules.toSheaf R).map) hgh

/-- Helper for Lemma 17.9.3: a morphism of sheaves of abelian groups is epic exactly when the
underlying morphism of set-valued sheaves is epic. -/
private theorem sheafAddCommGrp_epi_iff_forget_epi
    {X Y : Sheaf J AddCommGrpCat.{u}} (φ : X ⟶ Y) :
    Epi φ ↔ Epi ((sheafCompose J (forget AddCommGrpCat.{u})).map φ) := by
  constructor
  · intro hφ
    -- Proof comment: the forgetful sheaf functor preserves epimorphisms.
    letI : Epi φ := hφ
    exact (sheafCompose J (forget AddCommGrpCat.{u})).map_epi φ
  · intro hφ
    -- Proof comment: the same forgetful functor is faithful, so it reflects epimorphisms.
    exact (sheafCompose J (forget AddCommGrpCat.{u})).epi_of_epi_map hφ

/-- Helper for Lemma 17.9.3: the inverse terminal-evaluation section is compatible with
restriction maps in the slice category. -/
private theorem over_sections_equiv_terminal_inv_naturality
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    ∀ V Y : (Over U)ᵒᵖ, ∀ f : V ⟶ Y,
      M.val.map f (M.val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        M.val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of `Over U` has a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 17.9.3: rebuild a section on the slice from its value at the terminal
object. -/
private noncomputable def over_sections_from_terminal
    {U : C} (M : SheafOfModules (R.over U))
    (m : M.val.obj (op (Over.mk (𝟙 U)))) : M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (over_sections_equiv_terminal_inv_naturality (M := M) m)

/-- Helper for Lemma 17.9.3: a slice section is recovered from its value at the terminal object by
restricting along the unique terminal maps. -/
private theorem over_sections_equiv_terminal_left_inv
    {U : C} {M : SheafOfModules (R.over U)} (s : M.sections) :
    over_sections_from_terminal M (s.1 (op (Over.mk (𝟙 U)))) = s := by
  -- Proof comment: a section on the slice is determined by its restrictions from the terminal
  -- object.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 17.9.3: evaluating the reconstructed slice section at the terminal object
returns the original value. -/
private theorem over_sections_equiv_terminal_right_inv
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    (over_sections_from_terminal M m).1 (op (Over.mk (𝟙 U))) = m := by
  -- Proof comment: the unique endomorphism of the terminal object is the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.9.3: terminal evaluation identifies sections on a slice with the value at
the terminal object. -/
private noncomputable def over_sections_equiv_terminal
    {U : C} (M : SheafOfModules (R.over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
    invFun := over_sections_from_terminal M
    left_inv := over_sections_equiv_terminal_left_inv (M := M)
    right_inv := over_sections_equiv_terminal_right_inv (M := M) }

/-- Helper for Lemma 17.9.3: under terminal evaluation, `sectionsMap` is exactly the terminal
component of the underlying sheaf morphism on the slice site. -/
private theorem over_sections_equiv_terminal_sectionsMap
    {U : C} {M N : SheafOfModules (R.over U)} (ψ : M ⟶ N) (s : M.sections) :
    over_sections_equiv_terminal N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (op (Over.mk (𝟙 U)))) (over_sections_equiv_terminal M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Lemma 17.9.3: the inverse terminal-evaluation equivalence is natural in module-sheaf
morphisms on the slice site. -/
private theorem sectionsMap_over_sections_equiv_terminal_symm
    {U : C} {M N : SheafOfModules (R.over U)} (ψ : M ⟶ N)
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((over_sections_equiv_terminal M).symm m) =
      (over_sections_equiv_terminal N).symm ((ψ.val.app (op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation.
  apply (over_sections_equiv_terminal N).injective
  rw [over_sections_equiv_terminal_sectionsMap]
  simp

/-- Helper for Lemma 17.9.3: an epimorphism of `R`-module sheaves remains epic after forgetting to
the underlying sheaf of abelian groups. -/
private theorem underlying_epi_of_module_epi
    {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] :
    Epi ((SheafOfModules.toSheaf R).map p) := by
  -- Route correction: the source proof needs local lifting only for the ambient underlying
  -- additive sheaf, so the next step is to prove that `toSheaf` preserves epimorphisms in the
  -- current universe range instead of chasing slice-restriction functors.
  let F : SheafOfModules R ⥤ Sheaf J AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf R
  let _ : PreservesFiniteColimits F :=
    ((exactFunctor_iff F).1 (ExactFunctor.of F).property).2
  -- Proof comment: exact functors preserve finite colimits, hence epimorphisms.
  exact Functor.map_epi F p

/-- Helper for Lemma 17.9.3: restricting an epic module-sheaf morphism to a slice site keeps it
epic. -/
private theorem overRestrictionFunctor_map_epi
    {U : C} {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] :
    Epi ((overRestrictionFunctor (R := R) U).map p) := by
  let F : SheafOfModules R ⥤ SheafOfModules (R.over U) :=
    overRestrictionFunctor (R := R) U
  have hToSheaf :
      Epi ((SheafOfModules.toSheaf (R.over U)).map (F.map p)) := by
    let u : Over U ⥤ C := Over.forget U
    let GJ : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
      sheafCompose J (forget AddCommGrpCat.{u})
    let GK : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf (J.over U) (Type u) :=
      sheafCompose (J.over U) (forget AddCommGrpCat.{u})
    have hGJ : Epi (GJ.map ((SheafOfModules.toSheaf R).map p)) :=
      (sheafAddCommGrp_epi_iff_forget_epi (J := J)
        ((SheafOfModules.toSheaf R).map p)).1
          (underlying_epi_of_module_epi (R := R) p)
    letI : Epi (GJ.map ((SheafOfModules.toSheaf R).map p)) := hGJ
    have hGK :
        Epi (GK.map ((SheafOfModules.toSheaf (R.over U)).map (F.map p))) := by
      -- Proof comment: on underlying set-valued sheaves, slice restriction is the sheaf
      -- pushforward along `Over.forget U`, and Chapter 7 shows that this pushforward preserves
      -- epimorphisms.
      change Epi ((GJ ⋙ u.sheafPushforwardContinuous (Type u) (J.over U) J).map
        ((SheafOfModules.toSheaf R).map p))
      infer_instance
    exact GK.epi_of_epi_map hGK
  letI : Epi ((SheafOfModules.toSheaf (R.over U)).map (F.map p)) := hToSheaf
  -- Proof comment: `toSheaf` reflects epimorphisms back to sheaves of modules.
  exact epi_of_toSheaf_map_epi (R := R.over U) (F.map p)

/-- Helper for Lemma 17.9.3: an epic module-sheaf morphism admits local lifts of ambient
sections. -/
private theorem exists_cover_lift_of_locallySurjective_section
    {M N : SheafOfModules R} (p : M ⟶ N)
    [Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p)]
    (U : C) (s : N.val.obj (op U)) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ t : M.val.obj (op I.Y),
        (p.val.app (op I.Y)) t = N.val.map I.f.op s := by
  -- Proof comment: once local surjectivity of the underlying additive-sheaf map is available,
  -- the source proof chooses the canonical image-sieve cover and its built-in local preimages.
  let T : J.Cover U :=
    ⟨Presheaf.imageSieve (((SheafOfModules.toSheaf R).map p).hom) s,
      Presheaf.imageSieve_mem (J := J) (((SheafOfModules.toSheaf R).map p).hom) s⟩
  refine ⟨T, ?_⟩
  intro I
  refine ⟨Presheaf.localPreimage (((SheafOfModules.toSheaf R).map p).hom) s I.f I.hf, ?_⟩
  -- The chosen local preimage maps to the requested restricted section by construction.
  simpa using Presheaf.app_localPreimage (((SheafOfModules.toSheaf R).map p).hom) s I.f I.hf

/-- Helper for Lemma 17.9.3: an epic module-sheaf morphism admits local lifts of ambient
sections. -/
private theorem exists_cover_lift_of_epi_section
    {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] (U : C)
    (s : N.val.obj (op U)) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ t : M.val.obj (op I.Y),
        (p.val.app (op I.Y)) t = N.val.map I.f.op s := by
  -- Proof comment: after forgetting to abelian sheaves, the source proof packages the image sieve
  -- of `s` as a cover and then chooses the canonical local preimages on that cover.
  have hp : Epi ((SheafOfModules.toSheaf R).map p) :=
    underlying_epi_of_module_epi (R := R) p
  letI : Epi ((SheafOfModules.toSheaf R).map p) := hp
  letI : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf R).map p)).2 hp
  -- Proof comment: `Sheaf.isLocallySurjective_iff_epi'` converts the ambient epi into the local
  -- lifting predicate used by the image-sieve cover helper.
  exact exists_cover_lift_of_locallySurjective_section (R := R) p U s

/-- Helper for Lemma 17.9.3: sections of the restriction of a module sheaf to `W : Over U` are
canonically identified with the value of the ambient sheaf on `W`. -/
private theorem over_sections_equiv_obj_inv_property
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U)
    (m : M.val.obj (op W)) :
    ∀ ⦃V Y : (Over W)ᵒᵖ⦄ (f : V ⟶ Y),
      (M.over W).val.map f ((M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        (M.over W).val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of `Over W` has a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 17.9.3: a section of `M.over W` is determined by its value on the terminal
object of `Over W`. -/
private theorem over_sections_equiv_obj_left_inv
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U)
    (s : (M.over W).sections) :
    (M.over W).val.sectionsMk
        (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op)
          (s.1 (op (Over.mk (𝟙 W)))))
        (over_sections_equiv_obj_inv_property (R := R) M W
          (s.1 (op (Over.mk (𝟙 W))))) = s := by
  -- Proof comment: a section of the localized sheaf is recovered from its terminal value.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 17.9.3: evaluating the section induced by `m` at the terminal object gives
back `m`. -/
private theorem over_sections_equiv_obj_right_inv
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U)
    (m : M.val.obj (op W)) :
    ((M.over W).val.sectionsMk
        (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m)
        (over_sections_equiv_obj_inv_property (R := R) M W m)).1
      (op (Over.mk (𝟙 W))) = m := by
  -- Proof comment: the terminal restriction of the reconstructed section is the original value.
  change (M.over W).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 W))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 W)) = 𝟙 (Over.mk (𝟙 W)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using (M.over W).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.9.3: sections of the restriction to `W : Over U` are canonically
identified with the ambient value on `W`. -/
private noncomputable def over_sections_equiv_obj
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U) :
    (M.over W).sections ≃ M.val.obj (op W) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 W)))
    invFun := fun m ↦
      (M.over W).val.sectionsMk
        (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m)
        (over_sections_equiv_obj_inv_property (R := R) M W m)
    left_inv := over_sections_equiv_obj_left_inv (R := R) M W
    right_inv := over_sections_equiv_obj_right_inv (R := R) M W }

/-- Helper for Lemma 17.9.3: under the canonical section equivalence, restriction of a morphism
to `W` acts by the ambient component map on `W`. -/
private theorem overRestrictionFunctor_map_app_terminal
    {U : C} {M N : SheafOfModules (R.over U)}
    (ψ : M ⟶ N) (W : Over U) :
    ((overRestrictionFunctor (R := R.over U) W).map ψ).val.app (op (Over.mk (𝟙 W))) =
      ψ.val.app (op W) := by
  ext m
  rfl

/-- Helper for Lemma 17.9.3: under the canonical section equivalence, the restricted morphism
acts on sections by the ambient component map on `W`. -/
private theorem over_sections_equiv_obj_sectionsMap
    {U : C} {M N : SheafOfModules (R.over U)}
    (ψ : M ⟶ N) (W : Over U) (s : (M.over W).sections) :
    (over_sections_equiv_obj (R := R) N W)
      (SheafOfModules.sectionsMap ((overRestrictionFunctor (R := R.over U) W).map ψ) s) =
        (ψ.val.app (op W)) ((over_sections_equiv_obj (R := R) M W) s) := by
  -- Proof comment: evaluating both sides at the terminal object produces the same formula.
  change (((overRestrictionFunctor (R := R.over U) W).map ψ).val.app
      (op (Over.mk (𝟙 W)))) (s.1 (op (Over.mk (𝟙 W)))) =
    (ψ.val.app (op W)) (s.1 (op (Over.mk (𝟙 W))))
  exact congrArg
    (fun f : M.val.obj (op W) ⟶ N.val.obj (op W) ↦ f (s.1 (op (Over.mk (𝟙 W)))))
    (overRestrictionFunctor_map_app_terminal (R := R) ψ W)

/-- Helper for Lemma 17.9.3: the inverse of the section equivalence is natural in the sheaf
morphism. -/
private theorem sectionsMap_over_sections_equiv_obj_symm
    {U : C} {M N : SheafOfModules (R.over U)}
    (ψ : M ⟶ N) (W : Over U) (m : M.val.obj (op W)) :
    SheafOfModules.sectionsMap ((overRestrictionFunctor (R := R.over U) W).map ψ)
        ((over_sections_equiv_obj (R := R) M W).symm m) =
      (over_sections_equiv_obj (R := R) N W).symm ((ψ.val.app (op W)) m) := by
  -- Proof comment: compare the two sections after evaluating on the terminal object of `Over W`.
  apply (over_sections_equiv_obj (R := R) N W).injective
  rw [over_sections_equiv_obj_sectionsMap]
  simp

/-- Helper for Lemma 17.9.3: restricting the generating epimorphism of a generating family keeps
it epic on the slice. -/
private theorem restrictedGeneratingPiEpi
    {U : C} {M : SheafOfModules (R.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    Epi ((overRestrictionFunctor (R := R.over U) W).map σ.π) := by
  let F : SheafOfModules (R.over U) ⥤ SheafOfModules ((R.over U).over W) :=
    overRestrictionFunctor (R := R.over U) W
  letI : Functor.PreservesEpimorphisms F :=
    Functor.preservesEpimorphisms_of_adjunction
      (SheafOfModules.overPushforwardOverAdj (R := R.over U) W)
  change Epi (F.map σ.π)
  infer_instance

/-- Helper for Lemma 17.9.3: `mapFree` identifies restriction of the ambient free sheaf with the
canonical free sheaf on the slice over `W`. -/
private abbrev overRestrictionFreeIso
    {U : C} (W : Over U) (I : Type u) :
    (overRestrictionFunctor (R := R.over U) W).obj
        (SheafOfModules.free.{u} I : SheafOfModules (R.over U)) ≅
      (SheafOfModules.free.{u} I : SheafOfModules ((R.over U).over W)) :=
  SheafOfModules.mapFree
    (overRestrictionFunctor (R := R.over U) W)
    (Iso.refl (SheafOfModules.unit ((R.over U).over W)))
    I

/-- Helper for Lemma 17.9.3: transporting the free basis through `mapFree` gives the restricted
ambient basis section on the slice over `W`. -/
private theorem restrictedFreeBasisTransport
    {U : C} (I : Type u) (W : Over U) (i : I) :
    SheafOfModules.sectionsMap
        ((overRestrictionFreeIso (R := R) W I).inv)
        (SheafOfModules.freeSection (R := (R.over U).over W) i) =
      (over_sections_equiv_obj (R := R)
          (SheafOfModules.free.{u} I : SheafOfModules (R.over U)) W).symm
        ((SheafOfModules.freeSection (R := R.over U) i).1 (op W)) := by
  let F := overRestrictionFunctor (R := R.over U) W
  let m := overRestrictionFreeIso (R := R) W I
  have hiota :
      F.map (SheafOfModules.ιFree (R := R.over U) i) =
        SheafOfModules.ιFree (R := (R.over U).over W) i ≫ m.inv := by
    -- Proof comment: compare the basis morphisms through `mapFree.hom` and cancel the isomorphism.
    calc
      F.map (SheafOfModules.ιFree (R := R.over U) i) =
          F.map (SheafOfModules.ιFree (R := R.over U) i) ≫ m.hom ≫ m.inv := by
            symm
            rw [IsIso.hom_inv_id_assoc]
      _ =
          (Iso.refl (SheafOfModules.unit ((R.over U).over W))).hom ≫
            SheafOfModules.ιFree (R := (R.over U).over W) i ≫ m.inv := by
            rw [SheafOfModules.map_ιFree_mapFree_hom]
      _ = SheafOfModules.ιFree (R := (R.over U).over W) i ≫ m.inv := by
            simp
  calc
    SheafOfModules.sectionsMap m.inv
        (SheafOfModules.freeSection (R := (R.over U).over W) i) =
      SheafOfModules.unitHomEquiv
        (((SheafOfModules.free.{u} I : SheafOfModules (R.over U)).over W))
        (SheafOfModules.ιFree (R := (R.over U).over W) i ≫ m.inv) := by
          rfl
    _ =
      SheafOfModules.unitHomEquiv
        (((SheafOfModules.free.{u} I : SheafOfModules (R.over U)).over W))
        (F.map (SheafOfModules.ιFree (R := R.over U) i)) := by
          rw [hiota]
  apply (over_sections_equiv_obj (R := R)
      (SheafOfModules.free.{u} I : SheafOfModules (R.over U)) W).injective
  -- Proof comment: evaluating the restricted ambient basis morphism at the terminal object
  -- recovers the ambient basis section over `W`.
  rfl

/-- Helper for Lemma 17.9.3: restricting a generating family to `W` identifies the restricted
generating map with the free morphism attached to the restricted sections. -/
private theorem restrictedGeneratingPiEqFreeHom
    {U : C} {M : SheafOfModules (R.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    (overRestrictionFreeIso (R := R) W σ.I).inv ≫
      (overRestrictionFunctor (R := R.over U) W).map σ.π =
      (((M.over W).freeHomEquiv).symm
        (fun i ↦ (over_sections_equiv_obj (R := R) M W).symm ((σ.s i).1 (op W)))) := by
  -- Proof comment: both morphisms are determined by their values on the free basis sections.
  apply ((M.over W).freeHomEquiv).injective
  funext i
  calc
    (M.over W).freeHomEquiv
        ((overRestrictionFreeIso (R := R) W σ.I).inv ≫
          (overRestrictionFunctor (R := R.over U) W).map σ.π) i =
      SheafOfModules.sectionsMap
        ((overRestrictionFunctor (R := R.over U) W).map σ.π)
        ((((SheafOfModules.free.{u} σ.I :
            SheafOfModules (R.over U)).over W).freeHomEquiv)
          ((overRestrictionFreeIso (R := R) W σ.I).inv) i) := by
            simpa using
              (SheafOfModules.freeHomEquiv_comp_apply
                (f := (overRestrictionFreeIso (R := R) W σ.I).inv)
                (p := (overRestrictionFunctor (R := R.over U) W).map σ.π)
                (i := i))
    _ = SheafOfModules.sectionsMap
        ((overRestrictionFunctor (R := R.over U) W).map σ.π)
        (SheafOfModules.sectionsMap
          ((overRestrictionFreeIso (R := R) W σ.I).inv)
          (SheafOfModules.freeSection (R := (R.over U).over W) i)) := by
            rw [SheafOfModules.freeHomEquiv_apply]
    _ = SheafOfModules.sectionsMap
        ((overRestrictionFunctor (R := R.over U) W).map σ.π)
        ((over_sections_equiv_obj (R := R)
            (SheafOfModules.free.{u} σ.I : SheafOfModules (R.over U)) W).symm
          ((SheafOfModules.freeSection (R := R.over U) i).1 (op W))) := by
            rw [restrictedFreeBasisTransport]
  apply (over_sections_equiv_obj (R := R) M W).injective
  rw [over_sections_equiv_obj_sectionsMap]
  have hσ :
      SheafOfModules.sectionsMap σ.π
          (show ((SheafOfModules.free.{u} σ.I :
              SheafOfModules (R.over U)).sections) from
            SheafOfModules.freeSection (R := R.over U) i) =
        σ.s i := by
    -- Proof comment: the defining property of `σ.π` identifies the `i`th basis section.
    simpa [SheafOfModules.GeneratingSections.π] using
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
        (R := R.over U) (f := σ.s) i)
  have hσW :
      (SheafOfModules.sectionsMap σ.π
          (show ((SheafOfModules.free.{u} σ.I :
              SheafOfModules (R.over U)).sections) from
            SheafOfModules.freeSection (R := R.over U) i)).1 (op W) =
        (σ.s i).1 (op W) := by
    exact congrArg (fun s : M.sections ↦ s.1 (op W)) hσ
  simpa [SheafOfModules.sectionsMap] using hσW

/-- Helper for Lemma 17.9.3: restricting a generating family along `W : Over U` yields a
generating family on the iterated slice. -/
private noncomputable def restrictedGeneratingSections
    {U : C} {M : SheafOfModules (R.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    (M.over W).GeneratingSections where
  I := σ.I
  s i := (over_sections_equiv_obj (R := R) M W).symm ((σ.s i).1 (op W))
  epi := by
    let e := overRestrictionFreeIso (R := R) W σ.I
    have hπ :
        e.inv ≫ (overRestrictionFunctor (R := R.over U) W).map σ.π =
          (((M.over W).freeHomEquiv).symm
            (fun i ↦ (over_sections_equiv_obj (R := R) M W).symm ((σ.s i).1 (op W)))) :=
      restrictedGeneratingPiEqFreeHom (R := R) σ W
    -- Proof comment: the restricted generating map is an isomorphic transport of the restricted
    -- ambient generating epimorphism.
    rw [← hπ]
    apply epi_comp

/-- Helper for Lemma 17.9.3: the terminal maps in `Over U` compose functorially. -/
private theorem mkIdTerminal_from_comp
    {U : C} {V W : Over U} (g : W ⟶ V) :
    g ≫ Over.mkIdTerminal.from V = Over.mkIdTerminal.from W := by
  -- Proof comment: `Over.mk (𝟙 U)` is terminal in the slice category.
  exact Over.mkIdTerminal.hom_ext _ _

/-- Helper for Lemma 17.9.3: after passing to opposites, the terminal maps in `Over U` still
compose functorially. -/
private theorem op_mkIdTerminal_from_comp
    {U : C} {V W : Over U} (g : W ⟶ V) :
    (Over.mkIdTerminal.from V).op ≫ g.op = (Over.mkIdTerminal.from W).op := by
  exact congrArg Quiver.Hom.op (mkIdTerminal_from_comp (g := g))

/-- Helper for Lemma 17.9.3: a local lift on a slice chart restricts along any further slice arrow
to the corresponding lift on the refinement. -/
private theorem local_lift_restricts_along_slice_arrow
    {U : C} {M N : SheafOfModules (R.over U)} (p : M ⟶ N)
    {V W : Over U} (g : W ⟶ V)
    {s : N.val.obj (op (Over.mk (𝟙 U)))} {t : M.val.obj (op V)}
    (ht : (p.val.app (op V)) t = N.val.map (Over.mkIdTerminal.from V).op s) :
    (p.val.app (op W)) (M.val.map g.op t) =
      N.val.map (Over.mkIdTerminal.from W).op s := by
  -- Proof comment: move the lift equation across `g` by naturality and then collapse the
  -- terminal maps.
  have h := congrArg (fun h => h t) (p.val.naturality g.op)
  rw [ht] at h
  simpa [FunctorToTypes.map_comp_apply, op_mkIdTerminal_from_comp (g := g)] using h

/-- Helper for Lemma 17.9.3: the sieve generated by a family of slice objects is the sieve
generated by the corresponding underlying arrows in the ambient site. -/
private theorem over_sieve_of_objects_eq_of_arrows
    {U : C} {ι : Type*} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  ext W g
  constructor
  · intro hg
    -- Proof comment: a factorization in the slice category forgets to the same factorization in
    -- the ambient site.
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    -- Proof comment: conversely, any underlying factorization lifts uniquely to the slice.
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 17.9.3: the cover arrows of a slice cover of `V` form a top cover on the
slice over `V.left`. -/
private theorem cover_arrow_family_coversTop_left
    {U : C} {V : Over U} (T : (J.over U).Cover V) :
    (J.over V.left).CoversTop (fun A : T.Arrow ↦ Over.mk A.f.left) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over V.left) (X := Over.mk (𝟙 V.left)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows]
  have hT : (Sieve.overEquiv V) T.1 ∈ J V.left := by
    -- Proof comment: a covering sieve in the slice forgets to a covering sieve in the base site.
    have hT' : T.1 ∈ (J.over U) V := T.2
    rw [GrothendieckTopology.mem_over_iff] at hT'
    exact hT'
  have hCoverSieve :
      (Sieve.overEquiv V) T.1 =
        Sieve.ofArrows (fun A : T.Arrow ↦ A.Y.left) (fun A : T.Arrow ↦ A.f.left) := by
    ext W g
    constructor
    · intro hg
      rw [Sieve.overEquiv_iff] at hg
      rw [Sieve.mem_ofArrows_iff]
      refine ⟨⟨Over.mk (g ≫ V.hom), Over.homMk g (by simp), ?_⟩, 𝟙 _, ?_⟩
      · simpa using hg
      · simp
    · intro hg
      rw [Sieve.overEquiv_iff]
      rw [Sieve.mem_ofArrows_iff] at hg
      rcases hg with ⟨A, a, ha⟩
      have hcomp : a ≫ A.f.left ≫ V.hom = g ≫ V.hom := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ V.hom) ha.symm
      have hcomp' : a ≫ A.Y.hom = g ≫ V.hom := by
        calc
          a ≫ A.Y.hom = a ≫ (A.f.left ≫ V.hom) := by rw [← A.f.w]
          _ = g ≫ V.hom := by simpa [Category.assoc] using hcomp
      let gOver : Over.mk (g ≫ V.hom) ⟶ V := Over.homMk g (by simp)
      let aOver : Over.mk (g ≫ V.hom) ⟶ A.Y := Over.homMk a hcomp'
      have hOver : aOver ≫ A.f = gOver := by
        ext
        simpa using ha.symm
      simpa [aOver, hOver] using T.1.downward_closed A.hf aOver
  have hCover :
      Sieve.ofArrows (fun A : T.Arrow ↦ A.Y.left) (fun A : T.Arrow ↦ A.f.left) ∈ J V.left := by
    rwa [← hCoverSieve]
  simpa using hCover

/-- Helper for Lemma 17.9.3: composing a covering family of `U` with covering families on each
member yields a sigma-indexed covering family of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {I : Type (max u v)} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    {K : I → Type (max u v)} {Y : ∀ i : I, K i → Over (X i).left}
    (hY : ∀ i : I, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Σ i : I, K i ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Proof comment: reduce the slice `CoversTop` condition to ordinary covering sieves on the
  -- terminal object `Over.mk (𝟙 U)`, then compose the two stages with
  -- `GrothendieckTopology.bindOfArrows`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)).1 hX
    rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows] at hXTerminal
    exact hXTerminal
  have hY' :
      ∀ i : I,
        Sieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom) ∈ J (X i).left := by
    intro i
    have hYTerminal :
        Sieve.ofObjects (Y i) (Over.mk (𝟙 (X i).left)) ∈
          (J.over (X i).left) (Over.mk (𝟙 (X i).left)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over (X i).left) (X := Over.mk (𝟙 (X i).left))
        (hX := Over.mkIdTerminal)).1 (hY i)
    rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows] at hYTerminal
    exact hYTerminal
  simpa [Presieve.bindOfArrows_ofArrows] using
    J.bindOfArrows
      (h := hX')
      (R := fun i ↦
        Presieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom))
      (fun i ↦ by simpa using hY' i)

/-- Helper for Lemma 17.9.3: a finite family of sections over the terminal object of the slice
site admits a common refinement on which all sections lift simultaneously. -/
private theorem liftedGeneratingFamilyCover
    {U : C} {M N : SheafOfModules (R.over U)}
    (σ : N.GeneratingSections) [σ.IsFiniteType] (p : M ⟶ N) [Epi p] :
    ∃ (κ : Type (max u v)) (cover : κ → Over U), (J.over U).CoversTop cover ∧
      ∀ k : κ, ∀ i : σ.I,
        ∃ t : M.val.obj (op (cover k)),
          (p.val.app (op (cover k))) t =
            N.val.map (Over.mkIdTerminal.from (cover k)).op
              ((σ.s i).1 (op (Over.mk (𝟙 U)))) := by
  classical
  induction σ.I using Finite.induction_empty_option with
  | @of_equiv I₁ I₂ e IH =>
      obtain ⟨κ, cover, hcover, hs⟩ := IH (σ.s ∘ e)
      refine ⟨κ, cover, hcover, ?_⟩
      intro k i
      simpa using hs k (e.symm i)
  | h_empty =>
      refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), ?_, ?_⟩
      · -- Proof comment: with no generators, the singleton identity cover is enough.
        rw [GrothendieckTopology.coversTop_iff_of_isTerminal
          (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
        rw [GrothendieckTopology.mem_over_iff]
        have htop :
            (Sieve.overEquiv (Over.mk (𝟙 U)))
              (Sieve.ofObjects (fun _ : PUnit => Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
          ext Z g
          constructor
          · intro _
            trivial
          · intro _
            rw [Sieve.overEquiv_iff]
            exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
        rw [htop]
        exact (J.over U).top_mem (Over.mk (𝟙 U))
      · intro k i
        exact PEmpty.elim i
  | @h_option I _ IH =>
      obtain ⟨κ, cover, hcover, hs⟩ := IH (σ.s ∘ Option.some)
      have hnone :
          ∀ k : κ,
            ∃ T : (J.over U).Cover (cover k), ∀ A : T.Arrow,
              ∃ t : M.val.obj (op A.Y),
                (p.val.app (op A.Y)) t =
                  N.val.map A.f.op
                    (N.val.map (Over.mkIdTerminal.from (cover k)).op
                      ((σ.s none).1 (op (Over.mk (𝟙 U))))) := by
        intro k
        exact exists_cover_lift_of_epi_section (R := R.over U) p (cover k)
          (N.val.map (Over.mkIdTerminal.from (cover k)).op
            ((σ.s none).1 (op (Over.mk (𝟙 U)))))
      choose T hT using hnone
      refine ⟨Σ k : κ, (T k).Arrow, fun a ↦ a.2.Y, ?_, ?_⟩
      · -- Proof comment: refine `cover` by the cover arrows chosen for the remaining generator.
        intro Z
        let X : κ → Over U := cover
        let Y : ∀ k : κ, (T k).Arrow → Over (cover k).left := fun k A ↦ Over.mk A.f.left
        have hXY :
            (fun a : Σ k : κ, (T k).Arrow ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) =
              fun a : Σ k : κ, (T k).Arrow ↦ a.2.Y := by
          funext a
          cases a with
          | mk k A =>
              cases A
              rfl
        rw [← hXY]
        exact coversTopSigmaComp (J := J) hcover
          (fun k ↦ cover_arrow_family_coversTop_left (J := J) (T k)) Z
      · intro a i
        cases i with
        | none =>
            rcases hT a.1 a.2 with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc
              (p.val.app (op a.2.Y)) t =
                  N.val.map a.2.f.op
                    (N.val.map (Over.mkIdTerminal.from (cover a.1)).op
                      ((σ.s none).1 (op (Over.mk (𝟙 U))))) := ht
              _ =
                  N.val.map ((Over.mkIdTerminal.from (cover a.1)).op ≫ a.2.f.op)
                    ((σ.s none).1 (op (Over.mk (𝟙 U)))) := by
                      simpa [FunctorToTypes.map_comp_apply]
              _ =
                  N.val.map (Over.mkIdTerminal.from a.2.Y).op
                    ((σ.s none).1 (op (Over.mk (𝟙 U)))) := by
                      rw [op_mkIdTerminal_from_comp (g := a.2.f)]
        | some i =>
            rcases hs a.1 i with ⟨t, ht⟩
            refine ⟨M.val.map a.2.f.op t, ?_⟩
            simpa using
              local_lift_restricts_along_slice_arrow (R := R) (p := p)
                (g := a.2.f) (s := (σ.s (Option.some i)).1 (op (Over.mk (𝟙 U)))) ht

/-- Helper for Lemma 17.9.3: a quotient of a finite-type module sheaf is finite type. -/
theorem isFiniteType_of_epi
    {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] [M.IsFiniteType] :
    N.IsFiniteType := by
  -- Route correction: the old slice-epi proof drifted away from the source. The intended proof is
  -- to keep the same cover and push each local finite generating family through the restricted
  -- epimorphism on the corresponding slice.
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let τ : N.LocalGeneratorsData :=
    { I := σ.I
      X := σ.X
      coversTop := σ.coversTop
      generators := fun i ↦
        let F : SheafOfModules.{u, v, u', u} R ⥤
            SheafOfModules.{u, v, max u' v, u} (R.over (σ.X i)) :=
          overRestrictionFunctor (R := R) (σ.X i)
        letI : Epi (F.map p) :=
          overRestrictionFunctor_map_epi (R := R) (U := σ.X i) p
        (σ.generators i).ofEpi (F.map p) }
  have hτ : τ.IsFiniteType := by
    refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk ?_
    intro i
    -- Proof comment: each restricted generating family keeps the same finite index type after
    -- passing through the restricted epimorphism.
    let F : SheafOfModules.{u, v, u', u} R ⥤
        SheafOfModules.{u, v, max u' v, u} (R.over (σ.X i)) :=
      overRestrictionFunctor (R := R) (σ.X i)
    letI : Epi (F.map p) :=
      overRestrictionFunctor_map_epi (R := R) (U := σ.X i) p
    exact SheafOfModules.GeneratingSections.isFiniteType_ofEpi
      (σ := σ.generators i) (p := F.map p)
  exact ⟨τ, hτ⟩

/-- Finite-type sheaves of modules are closed under quotients. -/
instance isFiniteType_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) := by
  refine ⟨?_⟩
  intro M N p _ hM
  -- Proof comment: quotient-closure is the public `ObjectProperty` packaging of
  -- `isFiniteType_of_epi`.
  letI : M.IsFiniteType := hM
  exact isFiniteType_of_epi (R := R) p

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Helper for Lemma 17.9.3: finite-type sheaves of modules remain finite type after transport
across an isomorphism. -/
lemma finite_type_closed_under_isomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) where
  of_iso := by
    intro M N e hM
    rcases hM.exists_localGeneratorsData with ⟨σ, hσ⟩
    let τ : N.LocalGeneratorsData :=
      { I := σ.I
        X := σ.X
        coversTop := σ.coversTop
        generators := fun i ↦
          let F : SheafOfModules.{u, v, u', u} R ⥤
              SheafOfModules.{u, v, max u' v, u} (R.over (σ.X i)) :=
            overRestrictionFunctor (R := R) (σ.X i)
          (σ.generators i).ofEpi (Functor.mapIso F e).hom }
    have hτ : τ.IsFiniteType := by
      refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk ?_
      intro i
      -- Each restricted generating family keeps its finite index set under the restricted
      -- isomorphism.
      let F : SheafOfModules.{u, v, u', u} R ⥤
          SheafOfModules.{u, v, max u' v, u} (R.over (σ.X i)) :=
        overRestrictionFunctor (R := R) (σ.X i)
      refine SheafOfModules.GeneratingSections.IsFiniteType.mk ?_
      simpa [SheafOfModules.GeneratingSections.ofEpi, F] using
        ((hσ.isFiniteType i).finite : Finite (σ.generators i).I)
    exact ⟨τ, hτ⟩

/-- Helper for Lemma 17.9.3: a morphism out of a sheaf generated by `σ` is zero once it kills
all generators in `σ`. -/
private theorem hom_eq_zero_of_vanishing_on_generators
    {M N : SheafOfModules R} (σ : M.GeneratingSections) (φ : M ⟶ N)
    (hφ : ∀ i : σ.I, SheafOfModules.sectionsMap φ (σ.s i) = 0) :
    φ = 0 := by
  -- Proof comment: compose `φ` with the epi from the free sheaf determined by `σ` and check the
  -- resulting family of sections pointwise on the chosen generators.
  apply (cancel_epi σ.π).1
  apply N.freeHomEquiv.injective
  ext i
  simpa [SheafOfModules.GeneratingSections.π, SheafOfModules.freeHomEquiv_comp_apply] using hφ i

/-- Helper for Lemma 17.9.3: once quotient generators are lifted to the middle term of a short
exact sequence, adjoining them to generators of the kernel gives a generating family of the middle
term. -/
private theorem epi_sumGeneratingSections_of_shortExact
    {U : C} {S : ShortComplex (SheafOfModules (R.over U))} (hS : S.ShortExact)
    (σ₁ : S.X₁.GeneratingSections) (σ₃ : S.X₃.GeneratingSections)
    (lift : σ₃.I → S.X₂.sections)
    (hlift : ∀ i : σ₃.I, SheafOfModules.sectionsMap S.g (lift i) = σ₃.s i) :
    let σ₂ : S.X₂.GeneratingSections :=
      { I := Sum σ₁.I σ₃.I
        s := fun x ↦ Sum.elim (fun i ↦ SheafOfModules.sectionsMap S.f (σ₁.s i)) lift x }
    Epi σ₂.π := by
  classical
  let σ₂ : S.X₂.GeneratingSections :=
    { I := Sum σ₁.I σ₃.I
      s := fun x ↦ Sum.elim (fun i ↦ SheafOfModules.sectionsMap S.f (σ₁.s i)) lift x }
  let q : S.X₂ ⟶ cokernel σ₂.π := cokernel.π σ₂.π
  have hσ₂q : σ₂.π ≫ q = 0 := cokernel.condition σ₂.π
  have hqf : S.f ≫ q = 0 := by
    -- Proof comment: the cokernel map vanishes on the kernel generators because they are among
    -- the generators of `σ₂`.
    apply hom_eq_zero_of_vanishing_on_generators (σ := σ₁)
    intro i
    have h :=
      congrArg
        (fun z ↦ (cokernel σ₂.π).freeHomEquiv z (Sum.inl i))
        hσ₂q
    simpa [σ₂, q, SheafOfModules.freeHomEquiv_comp_apply] using h
  obtain ⟨l, hl⟩ := hS.exact.desc' q hqf
  have hl_zero : l = 0 := by
    -- Proof comment: after descending through `g`, the quotient generators of `S.X₃` also land in
    -- zero because their chosen lifts already lie in the image of `σ₂.π`.
    apply hom_eq_zero_of_vanishing_on_generators (σ := σ₃)
    intro i
    have h :=
      congrArg
        (fun z ↦ (cokernel σ₂.π).freeHomEquiv z (Sum.inr i))
        hσ₂q
    have hqi : SheafOfModules.sectionsMap q (lift i) = 0 := by
      simpa [σ₂, q, SheafOfModules.freeHomEquiv_comp_apply] using h
    calc
      SheafOfModules.sectionsMap l (σ₃.s i)
          = SheafOfModules.sectionsMap l (SheafOfModules.sectionsMap S.g (lift i)) := by
              rw [hlift i]
      _ = SheafOfModules.sectionsMap (S.g ≫ l) (lift i) := rfl
      _ = SheafOfModules.sectionsMap q (lift i) := by simpa [hl]
      _ = 0 := hqi
  -- Proof comment: the cokernel of `σ₂.π` is zero, so `σ₂.π` is epic.
  refine epi_of_cokernel_π_eq_zero ?_
  simpa [q, hl_zero] using hl

/-- Helper for Lemma 17.9.3: the combined generating family has finite index type whenever both
the kernel generators and quotient generators do. -/
private theorem isFiniteType_sumGeneratingSections
    {U : C} {S : ShortComplex (SheafOfModules (R.over U))}
    (σ₁ : S.X₁.GeneratingSections) (σ₃ : S.X₃.GeneratingSections)
    (lift : σ₃.I → S.X₂.sections)
    [σ₁.IsFiniteType] [σ₃.IsFiniteType] :
    let σ₂ : S.X₂.GeneratingSections :=
      { I := Sum σ₁.I σ₃.I
        s := fun x ↦ Sum.elim (fun i ↦ SheafOfModules.sectionsMap S.f (σ₁.s i)) lift x }
    σ₂.IsFiniteType := by
  -- Proof comment: the index type is the finite sum of the two finite index types.
  let σ₂ : S.X₂.GeneratingSections :=
    { I := Sum σ₁.I σ₃.I
      s := fun x ↦ Sum.elim (fun i ↦ SheafOfModules.sectionsMap S.f (σ₁.s i)) lift x }
  refine SheafOfModules.GeneratingSections.IsFiniteType.mk ?_
  infer_instance

-- Proof sketch: in a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`, locally lift finite generators
-- of `ℱ₃` along the epimorphism and adjoin finite generators of `ℱ₁`; these jointly generate
-- `ℱ₂`.
/-- Finite-type sheaves of modules are closed under extensions. -/
instance isFiniteType_isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) := by
  -- TODO for Lemma 17.9.3: refine the cover of `S.X₃` so its finite generators lift locally
  -- along the epimorphism, adjoin restricted finite generators of `S.X₁`, and conclude by
  -- exactness on each refined slice.
  sorry

/-- Helper for Lemma 17.9.3: once quotients are known to preserve finite type, the coimage of a
map from a finite-type module sheaf is finite type. -/
private theorem isFiniteType_coimage_of_finiteType
    {M N : SheafOfModules R} (φ : M ⟶ N) [M.IsFiniteType] :
    (Abelian.coimage φ).IsFiniteType := by
  -- Proof comment: `Abelian.coimage.π φ` is epic, so the quotient-closure instance applies
  -- directly to the source object `M`.
  exact isFiniteType_of_epi (R := R) (Abelian.coimage.π φ)

/-- Lemma 17.9.3 (1): the image of a morphism from a finite-type sheaf of modules is again of
finite type. -/
theorem isFiniteType_image (φ : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] :
    (Abelian.image φ).IsFiniteType := by
  -- Proof comment: the source proof factors through the coimage, which is a quotient of `ℱ`, and
  -- then transports finite type across the canonical coimage-image isomorphism.
  let P : ObjectProperty (SheafOfModules R) := SheafOfModules.IsFiniteType
  have hcoim : (Abelian.coimage φ).IsFiniteType :=
    isFiniteType_coimage_of_finiteType (R := R) φ
  -- Proof comment: `Abelian.coimageIsoImage φ` transfers the finite-type witness to the image.
  exact P.prop_of_iso (Abelian.coimageIsoImage φ) hcoim

-- Proof sketch: this is exactly the extension-closure statement for the object property
-- attached to `SheafOfModules.IsFiniteType`.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.9.3 (2): in a short exact sequence of sheaves of modules, if the left and right terms
are of finite type, then the middle term is of finite type. -/
theorem isFiniteType_of_shortExact
    {ℱ₁ ℱ₂ ℱ₃ : SheafOfModules R}
    (f : ℱ₁ ⟶ ℱ₂) (g : ℱ₂ ⟶ ℱ₃) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [ℱ₁.IsFiniteType] [ℱ₃.IsFiniteType] :
    ℱ₂.IsFiniteType := by
  let P : ObjectProperty (SheafOfModules R) := SheafOfModules.IsFiniteType
  exact P.prop_X₂_of_shortExact hS inferInstance inferInstance

end SheafOfModules
