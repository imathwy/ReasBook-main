import Mathlib
import StacksProject_2024.Chap15.Lemma_15_90_1
import StacksProject_2024.Chap18.IdealQuotientSheaf
import StacksProject_2024.Chap18.Lemma_18_25_1
import StacksProject_2024.Chap18.Lemma_18_28_6
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SheafOfModules
open scoped TensorProduct

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.28.16:
- primary domain: same-site change of rings for sheaves of modules on a ringed site, together
  with quotient ring sheaves by ideal sheaves;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlatHom`,
  `ringedSiteStructureMap`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `quotientRingSheaf`,
  `quotientRingSheafMap`,
  `IsAnnihilatedByIdealPower`;
- best owner abstraction: the quotient side should be consumed through the shared owner
  `quotientRingSheaf I` and its canonical map `quotientRingSheafMap α I`, while the theorem
  itself remains the source-facing `IsIso` statement for the base-change unit at `ℱ`;
- primitive data: a morphism `α : 𝒪 ⟶ 𝒪'`, an ideal sheaf
  `I : Subobject (unitModule J 𝒪)`, and an `\mathcal O`-module `ℱ`;
- derived API: the quotient ring sheaves, their canonical comparison map, and the source-facing
  annihilation-by-a-power predicate.

Source/core/bridge triage:
- `source-facing`: the textbook base-change map
  `id ⊗ 1 : \mathcal F \to \mathcal F \otimes_{\mathcal O} \mathcal O'`;
- `core/canonical`: `IsFlatHom α`, the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)`, and the shared
  quotient owner `quotientRingSheaf`;
- `bridge/view`: `quotientRingSheafMap α I` and `IsAnnihilatedByIdealPower I ℱ`.
-/

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.28.16: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness means preserving finite limits and finite colimits, and both
  -- preservation properties compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  let _ : CategoryTheory.Limits.PreservesFiniteLimits G := hG.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.16: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctor_of_natIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B} (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the functor
  -- isomorphism.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso e⟩

/-- Helper for Lemma 18.28.16: if the quotient ring sheaf map is an isomorphism, then each
sectionwise quotient map is an isomorphism of rings. -/
private theorem quotientRingSheafMap_app_isIso
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪))
    [IsIso (quotientRingSheafMap α I)]
    (U : Cᵒᵖ) :
    IsIso ((quotientRingSheafMap α I).hom.app U) := by
  letI :
      IsIso ((sheafToPresheaf J RingCat.{u}).map (quotientRingSheafMap α I)) :=
    Functor.map_isIso (sheafToPresheaf J RingCat.{u}) (quotientRingSheafMap α I)
  simpa using
    (show IsIso (((sheafToPresheaf J RingCat.{u}).map (quotientRingSheafMap α I)).app U) by
      infer_instance)

/-- Helper for Lemma 18.28.16: an ideal-power annihilation hypothesis on a sheaf of modules gives
the module-theoretic ideal-power torsion condition on each section module. -/
private theorem annihilated_sections_are_ideal_power_torsion
    (I : Subobject (unitModule J 𝒪))
    (ℱ : Mod(𝒪))
    (hpow : IsAnnihilatedByIdealPower I ℱ)
    (U : Cᵒᵖ) :
    Module.IsIdealPowerTorsion (idealSectionIdeal I U) (ℱ.val.obj U) := by
  rcases hpow with ⟨n, hn⟩
  rw [Module.isIdealPowerTorsion_iff]
  intro x
  refine ⟨⟨n + 1, Nat.succ_pos n⟩, ?_⟩
  intro a
  have haAnn :
      (a : 𝒪.obj.obj U) ∈ Module.annihilator (𝒪.obj.obj U) (ℱ.val.obj U) := by
    exact hn U (Ideal.pow_le_pow_right (Nat.le_succ n) a.2)
  exact Module.mem_annihilator.mp haAnn x

/-- Helper for Lemma 18.28.16: the sectionwise comparison map on quotient sheaves is exactly the
ordinary quotient map modulo the section ideal. -/
private theorem quotientRingSheafMap_app_hom_eq_quotientMapModIdeal
    (α : 𝒪 ⟶ 𝒪')
    (I : Subobject (unitModule J 𝒪))
    (U : Cᵒᵖ) :
    ((quotientRingSheafMap α I).hom.app U).hom =
      quotientMapModIdeal ((α.hom.app U).hom) (idealSectionIdeal I U) := by
  rfl

/-- Helper for Lemma 18.28.16: if evaluation at every object sends a sheaf-module morphism to an
isomorphism, then the original morphism is already an isomorphism. -/
private theorem module_isIso_of_evaluation_isIso
    {M N : ringedSiteModuleCategory J 𝒪} (f : M ⟶ N)
    (hf : ∀ U : Cᵒᵖ, IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f)) :
    IsIso f := by
  have hIsoPresheaf :
      IsIso
        ((sheafToPresheaf J AddCommGrpCat).map
          ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f)) := by
    -- Proof comment: after forgetting module structure and then the sheaf condition, evaluation is
    -- just objectwise application, so the hypothesis gives an isomorphism on each component.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    let _ : IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f) := hf U
    let _ := Functor.map_isIso
      (forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f)
    simpa [SheafOfModules.evaluation, SheafOfModules.toSheaf]
  have hIsoToSheaf :
      IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f) := by
    -- Proof comment: the additive sheaf forgetful functor reflects isomorphisms from the
    -- underlying presheaf, so the objectwise presheaf isomorphism upgrades to sheaves.
    letI :
        IsIso
          ((sheafToPresheaf J AddCommGrpCat).map
            ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f)
      (sheafToPresheaf J AddCommGrpCat)
  -- Proof comment: finally reflect the underlying additive-sheaf isomorphism back to module
  -- sheaves over `𝒪`.
  letI : IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f) := hIsoToSheaf
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf (ringSheaf J 𝒪))

/-- Helper for Lemma 18.28.16: on a fixed site, pushforward along the structure map induced by
`α` is definitionally the same as restriction of scalars along `α`. -/
private theorem pushforward_same_site_eq_restrictionAlong
    (α : 𝒪 ⟶ 𝒪') :
    SheafOfModules.pushforward (ringedSiteStructureMap α) = restrictionAlong α := by
  -- Proof comment: the base functor is the identity, so same-site pushforward carries no extra
  -- topological transport and only remembers the restriction-of-scalars action.
  rfl

/-- Helper for Lemma 18.28.16: the same-site pullback functor can be read through the canonical
ringed-site morphism `sameSiteHom α` without changing its structure-sheaf map. -/
private theorem pullback_same_site_eq_pullback_sameSiteHom
    (α : 𝒪 ⟶ 𝒪') :
    SheafOfModules.pullback (ringedSiteStructureMap α) =
      SheafOfModules.pullback (sameSiteHom α).structureSheafMap := by
  -- Proof comment: `sameSiteHom α` was introduced exactly to package `ringedSiteStructureMap α`
  -- as a ringed-site morphism over the identity functor.
  rfl

/-- Helper for Lemma 18.28.16: a flat same-site morphism of sheaves of rings induces a flat ring
map on every section ring. -/
private theorem evaluation_restrictionAlong_unitModule_eq_sectionTarget
    (α : 𝒪 ⟶ 𝒪')
    (U : Cᵒᵖ) :
    let φ : 𝒪.obj.obj U →+* 𝒪'.obj.obj U := (α.hom.app U).hom
    letI : Algebra (𝒪.obj.obj U) (𝒪'.obj.obj U) := φ.toAlgebra
    (SheafOfModules.evaluation (ringSheaf J 𝒪) U).obj
        ((restrictionAlong α).obj (unitModule J 𝒪')) =
      ModuleCat.of (𝒪.obj.obj U) (𝒪'.obj.obj U) := by
  -- Proof comment: same-site restriction of scalars keeps the underlying sheaf of sets, so
  -- evaluating the restricted unit module at `U` is definitionally the target section ring.
  rfl

/-- Helper for Lemma 18.28.16: a flat same-site morphism of sheaves of rings induces a flat ring
map on every section ring. -/
private theorem evaluation_over_terminal_obj_eq
    (U : Cᵒᵖ) (M : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) U).obj M =
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).obj
        (M.over U.unop) := by
  -- Proof comment: both sides are definitionally the same restricted module evaluated at the
  -- terminal object `U ⟶ U` of the slice category.
  rfl

/-- Helper for Lemma 18.28.16: objectwise evaluation of a morphism agrees with terminal
evaluation of its restriction to the slice over `U`. -/
private theorem evaluation_over_terminal_map_eq
    (U : Cᵒᵖ) {M N : ringedSiteModuleCategory J 𝒪} (f : M ⟶ N) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f =
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U.unop))).map f) := by
  -- Proof comment: after the preceding definitional identification, the evaluated morphism is
  -- literally the terminal component of the restricted morphism.
  rfl

/-- Helper for Lemma 18.28.16: a section on the slice over `U` is determined by its terminal
value. -/
private noncomputable def overSectionsFromTerminal
    (U : Cᵒᵖ) (M : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop))
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 U.unop)))) :
    M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (fun V W f ↦ by
      -- Proof comment: each component is the restriction of the terminal value along the unique
      -- map to the terminal object.
      have h :
          (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from W.unop).op := by
        apply Quiver.Hom.unop_inj
        simp only [Quiver.Hom.unop_op]
        exact Over.mkIdTerminal.hom_ext
          (f.unop ≫ Over.mkIdTerminal.from V.unop)
          (Over.mkIdTerminal.from W.unop)
      rw [← PresheafOfModules.map_comp_apply, h])

/-- Helper for Lemma 18.28.16: rebuilding a slice section from its terminal value recovers the
original section. -/
private theorem overSectionsEquivTerminal_leftInv
    (U : Cᵒᵖ) {M : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)}
    (s : M.sections) :
    overSectionsFromTerminal (J := J) (𝒪 := 𝒪) U M
        (s.1 (Opposite.op (Over.mk (𝟙 U.unop)))) = s := by
  -- Proof comment: every component is obtained by restricting the terminal component.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 18.28.16: evaluating the reconstructed slice section at the terminal object
recovers the chosen terminal value. -/
private theorem overSectionsEquivTerminal_rightInv
    (U : Cᵒᵖ) {M : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)}
    (m : M.val.obj (Opposite.op (Over.mk (𝟙 U.unop)))) :
    (overSectionsFromTerminal (J := J) (𝒪 := 𝒪) U M m).1
      (Opposite.op (Over.mk (𝟙 U.unop))) = m := by
  -- Proof comment: the terminal object only maps to itself by the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U.unop))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U.unop)) = 𝟙 (Over.mk (𝟙 U.unop)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.28.16: terminal evaluation identifies slice sections with terminal
values. -/
private noncomputable def overSectionsEquivTerminal
    (U : Cᵒᵖ) (M : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)) :
    M.sections ≃ M.val.obj (Opposite.op (Over.mk (𝟙 U.unop))) :=
  { toFun := fun s ↦ s.1 (Opposite.op (Over.mk (𝟙 U.unop)))
    invFun := overSectionsFromTerminal (J := J) (𝒪 := 𝒪) U M
    left_inv := overSectionsEquivTerminal_leftInv (J := J) (𝒪 := 𝒪) U
    right_inv := overSectionsEquivTerminal_rightInv (J := J) (𝒪 := 𝒪) U }

/-- Helper for Lemma 18.28.16: under terminal evaluation, a slice `sectionsMap` is exactly the
terminal component of the underlying morphism. -/
private theorem overSectionsEquivTerminal_sectionsMap
    (U : Cᵒᵖ)
    {M N : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)}
    (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (Opposite.op (Over.mk (𝟙 U.unop))))
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Lemma 18.28.16: the inverse terminal-evaluation equivalence is natural in a slice
module-sheaf morphism. -/
private theorem sectionsMap_overSectionsEquivTerminal_symm
    (U : Cᵒᵖ)
    {M N : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)}
    (ψ : M ⟶ N) (m : M.val.obj (Opposite.op (Over.mk (𝟙 U.unop)))) :
    SheafOfModules.sectionsMap ψ
        ((overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U M).symm m) =
      (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U N).symm
        ((ψ.val.app (Opposite.op (Over.mk (𝟙 U.unop)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation.
  apply (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U N).injective
  rw [overSectionsEquivTerminal_sectionsMap]
  simp

/-- Helper for Lemma 18.28.16: a finite family of terminal elements of a slice module sheaf
packages into the canonical morphism from a finite free sheaf. -/
private noncomputable def freeMorphismOfTerminalFamily
    (U : Cᵒᵖ) {n : ℕ}
    (M : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop))
    (s : Fin n → M.val.obj (Opposite.op (Over.mk (𝟙 U.unop)))) :
    (SheafOfModules.free (ULift (Fin n)) :
      ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)) ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm
    (fun i ↦
      (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U M).symm (s i.down))

/-- Helper for Lemma 18.28.16: evaluating the morphism attached to a terminal family on the
terminal free basis vector recovers the chosen coefficient. -/
private theorem freeMorphismOfTerminalFamily_app_terminal_freeSection
    (U : Cᵒᵖ) {n : ℕ}
    (M : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop))
    (s : Fin n → M.val.obj (Opposite.op (Over.mk (𝟙 U.unop)))) (i : ULift (Fin n)) :
    ((freeMorphismOfTerminalFamily (J := J) (𝒪 := 𝒪) U M s).val.app
        (Opposite.op (Over.mk (𝟙 U.unop))))
      ((show ((SheafOfModules.free (ULift (Fin n)) :
          ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)).sections) from
        SheafOfModules.freeSection (R := ringSheaf (J.over U.unop) (𝒪.over U.unop)) i).1
          (Opposite.op (Over.mk (𝟙 U.unop)))) = s i.down := by
  -- Proof comment: first use the defining basis formula for `freeHomEquiv.symm`, then evaluate
  -- the resulting section at the slice terminal object.
  have h :=
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (f := fun j : ULift (Fin n) ↦
        (overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U M).symm (s j.down))
      (R := ringSheaf (J.over U.unop) (𝒪.over U.unop)) (i := i))
  have hterminal :=
    congrArg
      (fun t : M.sections ↦ overSectionsEquivTerminal (J := J) (𝒪 := 𝒪) U M t)
      h
  simpa [freeMorphismOfTerminalFamily] using hterminal

/-- Helper for Lemma 18.28.16: evaluating a module sheaf on the terminal object of the slice site
is exact. -/
private theorem slice_terminal_evaluation_exact
    (U : Cᵒᵖ) :
    exactFunctor _ _
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
        (Opposite.op (Over.mk (𝟙 U.unop)))) := by
  -- Proof comment: evaluation on a fixed object preserves finite limits and finite colimits
  -- objectwise, so the terminal slice evaluation is exact just like any other module evaluation.
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.16: after restricting to the slice over `U` and evaluating at its
terminal object, the restricted target unit module is still the ordinary section ring
`\mathcal O'(U)`. -/
private theorem evaluation_over_terminal_restrictionAlong_unitModule_eq_sectionTarget
    (α : 𝒪 ⟶ 𝒪')
    (U : Cᵒᵖ) :
    let φ : 𝒪.obj.obj U →+* 𝒪'.obj.obj U := (α.hom.app U).hom
    letI : Algebra (𝒪.obj.obj U) (𝒪'.obj.obj U) := φ.toAlgebra
    (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
        (Opposite.op (Over.mk (𝟙 U.unop)))).obj
      (((restrictionAlong α).obj (unitModule J 𝒪')).over U.unop) =
        ModuleCat.of (𝒪.obj.obj U) (𝒪'.obj.obj U) := by
  -- Proof comment: first identify terminal slice evaluation with ordinary evaluation at `U`,
  -- then use the same-site restriction-of-scalars normalization already isolated above.
  simpa [evaluation_over_terminal_obj_eq, φ] using
    evaluation_restrictionAlong_unitModule_eq_sectionTarget (J := J) α U

/-- Helper for Lemma 18.28.16: a flat same-site morphism of sheaves of rings induces a flat ring
map on every section ring. -/
private theorem app_flat_of_isFlatHom
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (α : 𝒪 ⟶ 𝒪')
    (hflat : IsFlatHom α)
    (U : Cᵒᵖ) :
    ((α.hom.app U).hom).Flat := by
  let φ : 𝒪.obj.obj U →+* 𝒪'.obj.obj U := (α.hom.app U).hom
  letI : Algebra (𝒪.obj.obj U) (𝒪'.obj.obj U) := φ.toAlgebra
  let X : Mod(𝒪) := (restrictionAlong α).obj (unitModule J 𝒪')
  have hX : IsFlat 𝒪 X := by
    -- Proof comment: unpack the source-facing flatness hypothesis into the canonical flat target
    -- unit module on `Mod(\mathcal O)`.
    simpa [IsFlatHom, X] using hflat
  have hXOver : IsFlat (𝒪.over U.unop) (X.over U.unop) := by
    -- Proof comment: flatness localizes to the slice site over `U`.
    let _ : IsFlat 𝒪 X := hX
    simpa [X] using
      (isFlat_over (J := J) 𝒪 U.unop X : IsFlat (𝒪.over U.unop) (X.over U.unop))
  have hEvalExact :
      exactFunctor _ _
        (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))) :=
    slice_terminal_evaluation_exact (J := J) (𝒪 := 𝒪) U
  let E :
      ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop) ⥤
        ModuleCat (𝒪.obj.obj U) :=
    SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
      (Opposite.op (Over.mk (𝟙 U.unop)))
  have hTerminalTarget :
      E.obj (X.over U.unop) =
          ModuleCat.of (𝒪.obj.obj U) (𝒪'.obj.obj U) :=
    evaluation_over_terminal_restrictionAlong_unitModule_eq_sectionTarget
      (J := J) α U
  have hCompositeExact :
      exactFunctor _ _ (CategoryTheory.MonoidalCategory.tensorRight (X.over U.unop) ⋙ E) :=
    -- Proof comment: first tensor by the flat slice module, then evaluate at the slice terminal
    -- object, so the composite stays exact.
    exactFunctor_comp hXOver.exact_tensor hEvalExact
  -- Route correction: the earlier finite-presentation plan drifted here. A finitely generated
  -- ideal need not be finitely presented over an arbitrary section ring, so the remaining descent
  -- must use the single-relation/trivial-relation flatness criterion instead of a finite free
  -- presentation of every ideal.
  -- TODO: use the new terminal-slice adapters above to encode a terminal relation in
  -- `𝒪'.obj.obj U` as a relation among finite free slice sheaves, prove that flatness of
  -- `X.over U.unop` trivializes that relation on the slice, and then read the trivial-relation
  -- data back at the terminal object to invoke `Module.Flat.iff_forall_isTrivialRelation`.
  sorry

/-- Helper for Lemma 18.28.16: `ModuleCat.extendScalars` is the tensor-product module model. -/
private noncomputable def extendScalars_tensor_module_iso
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat R) :
    letI : Algebra R S := φ.toAlgebra
    (ModuleCat.extendScalars φ).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  letI : Algebra R S := φ.toAlgebra
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
    { __ := AddEquiv.refl S
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower R S ↑((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  -- Proof comment: normalize the wrapped `extendScalars` object to the standard tensor model.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl R M)).toModuleIso

/-- Helper for Lemma 18.28.16: after the standard tensor-model identification, the unit of
`ModuleCat.extendRestrictScalarsAdj` is the canonical map `m ↦ 1 ⊗ m`. -/
private theorem extendRestrictScalars_unit_eq_tensor_mk
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat R) :
    letI : Algebra R S := φ.toAlgebra
    (ModuleCat.extendRestrictScalarsAdj φ).unit.app M ≫
      (ModuleCat.restrictScalars φ).map (extendScalars_tensor_module_iso φ M).hom =
        ModuleCat.ofHom (TensorProduct.mk R S M 1) := by
  letI : Algebra R S := φ.toAlgebra
  -- Proof comment: both morphisms are definitionally the same linear map on an element `m`.
  ext m
  rfl

/-- Helper for Lemma 18.28.16: if postcomposition by an isomorphism is bijective, then the
original map is already bijective. -/
private theorem bijective_of_bijective_postcomp_isIso
    {R : Type u} [CommRing R]
    {A B C : ModuleCat.{u} R} (f : A ⟶ B) (g : B ⟶ C) [IsIso g]
    (hfg : Function.Bijective (f ≫ g)) :
    Function.Bijective f := by
  have hg : Function.Bijective g :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective g).1 inferInstance
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ h
    apply hfg.injective
    simpa using congrArg g h
  · intro y
    let z := g y
    rcases hfg.surjective z with ⟨x, hx⟩
    refine ⟨x, hg.injective ?_⟩
    simpa [z] using hx

/-- Helper for Lemma 18.28.16: quotienting by `J • T` produces a module annihilated by `J`. -/
private theorem ideal_le_annihilator_quotient_by_smul_top
    {R : Type u} [CommRing R]
    (J : Ideal R)
    {T : Type u} [AddCommGroup T] [Module R T] :
    J ≤ Module.annihilator R (T ⧸ (J • (⊤ : Submodule R T))) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R T)) x
  -- Proof comment: multiplication by an element of `J` lands in `J • T`, so the quotient class
  -- vanishes.
  change (Submodule.Quotient.mk ((a : R) • y) : T ⧸ (J • (⊤ : Submodule R T))) = 0
  rw [Submodule.Quotient.eq_zero_iff]
  exact Submodule.smul_mem_smul ha (Submodule.mem_top y)

/-- Helper for Lemma 18.28.16: in the standard quotient-by-`I^(m+1) • T` step, the submodule is
annihilated by `I` and the quotient is annihilated by `I^(m+1)`. -/
private theorem quotient_pow_step_annihilator_bounds
    {R : Type u} [CommRing R]
    (I : Ideal R)
    (m : ℕ)
    {T : Type u} [AddCommGroup T] [Module R T] :
    let K : Submodule R (T ⧸ I ^ (m + 2) • (⊤ : Submodule R T)) :=
      I ^ (m + 1) • (⊤ : Submodule R (T ⧸ I ^ (m + 2) • (⊤ : Submodule R T)))
    I ≤ Module.annihilator R K ∧
      I ^ (m + 1) ≤ Module.annihilator R ((T ⧸ I ^ (m + 2) • (⊤ : Submodule R T)) ⧸ K) := by
  let T' : Type u := T ⧸ I ^ (m + 2) • (⊤ : Submodule R T)
  let K : Submodule R T' := I ^ (m + 1) • (⊤ : Submodule R T')
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [Submodule.mem_annihilator]
    intro x
    rcases x with ⟨x, hx⟩
    rcases Submodule.mem_smul_top_iff_exists.mp hx with ⟨y, hy, rfl⟩
    apply Subtype.ext
    change (Submodule.Quotient.mk (((a : R) * y : R) • x) :
        T ⧸ I ^ (m + 2) • (⊤ : Submodule R T)) = 0
    rw [Submodule.Quotient.eq_zero_iff]
    refine Submodule.smul_mem_smul ?_ (Submodule.mem_top x)
    have hyI : y ∈ I ^ (m + 1) := by simpa [K] using hy
    have hmul : (a : R) * y ∈ I ^ (m + 2) := by
      simpa [pow_succ', mul_comm] using Ideal.mul_mem_mul ha hyI
    exact hmul
  · have hTann :
        I ^ (m + 1) ≤ Module.annihilator R T' := by
      intro a ha
      rw [Module.mem_annihilator]
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I ^ (m + 2) • (⊤ : Submodule R T)) x
      change (Submodule.Quotient.mk ((a : R) • y) :
          T ⧸ I ^ (m + 2) • (⊤ : Submodule R T)) = 0
      rw [Submodule.Quotient.eq_zero_iff]
      refine Submodule.smul_mem_smul ?_ (Submodule.mem_top y)
      exact Ideal.pow_le_pow_right (Nat.le_succ (m + 1)) ha
    -- Proof comment: the quotient of a module annihilated by `I^(m+1)` is still annihilated by
    -- `I^(m+1)`.
    intro a ha
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K x
    change (Submodule.Quotient.mk ((a : R) • y) : T' ⧸ K) = 0
    rw [Submodule.Quotient.eq_zero_iff]
    exact Module.mem_annihilator.mp (hTann ha) y

/-- Helper for Lemma 18.28.16: flatness lets one reconstruct bijectivity of the tensor unit on a
module from the corresponding bijectivity on a submodule and its quotient. -/
private theorem tensorBaseChange_bijective_of_submodule_and_quotient
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (hflat : (algebraMap R S).Flat)
    {T : Type u} [AddCommGroup T] [Module R T]
    (K : Submodule R T)
    (hK : Function.Bijective (TensorProduct.mk R S K 1))
    (hQ : Function.Bijective (TensorProduct.mk R S (T ⧸ K) 1)) :
    Function.Bijective (TensorProduct.mk R S T 1) := by
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  have hSubtypeTensor_injective :
      Function.Injective (LinearMap.lTensor S K.subtype) := by
    -- Proof comment: flatness preserves injectivity of the submodule inclusion after tensoring.
    simpa using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S)
        K.subtype (Submodule.injective_subtype K))
  have hExactTensor :
      Function.Exact (LinearMap.lTensor S K.subtype) (LinearMap.lTensor S K.mkQ) := by
    -- Proof comment: tensoring the canonical short exact row `0 → K → T → T/K → 0` stays exact.
    exact lTensor_exact S (LinearMap.exact_subtype_mkQ K) K.mkQ_surjective
  constructor
  · intro x y hxy
    have hqxy :
        TensorProduct.mk R S (T ⧸ K) 1 (K.mkQ x) =
          TensorProduct.mk R S (T ⧸ K) 1 (K.mkQ y) := by
      simpa [TensorProduct.mk] using congrArg (LinearMap.lTensor S K.mkQ) hxy
    have hqeq : K.mkQ x = K.mkQ y := hQ.1 hqxy
    have hsub : K.mkQ (x - y) = 0 := by
      change K.mkQ x - K.mkQ y = 0
      exact sub_eq_zero.mpr hqeq
    obtain ⟨k, hk⟩ := (LinearMap.exact_subtype_mkQ K (x - y)).1 hsub
    have hkTensor :
        (LinearMap.lTensor S K.subtype) (TensorProduct.mk R S K 1 k) = 0 := by
      calc
        (LinearMap.lTensor S K.subtype) (TensorProduct.mk R S K 1 k)
            = TensorProduct.mk R S T 1 (K.subtype k) := by
                simp [TensorProduct.mk]
        _ = TensorProduct.mk R S T 1 (x - y) := by
              simpa using congrArg (TensorProduct.mk R S T 1) hk
        _ = TensorProduct.mk R S T 1 x - TensorProduct.mk R S T 1 y := by
              simpa [TensorProduct.mk] using (TensorProduct.tmul_sub (1 : S) x y)
        _ = 0 := by
              simpa [hxy]
    have hkTensor_zero : TensorProduct.mk R S K 1 k = 0 :=
      hSubtypeTensor_injective hkTensor
    have hk_zero : k = 0 := hK.1 <| by simpa using hkTensor_zero
    have hxy_zero : x - y = 0 := by
      simpa [hk_zero] using hk.symm
    exact sub_eq_zero.mp hxy_zero
  · intro z
    obtain ⟨q, hq⟩ := hQ.2 ((LinearMap.lTensor S K.mkQ) z)
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K q
    have hker :
        (LinearMap.lTensor S K.mkQ) (z - TensorProduct.mk R S T 1 x) = 0 := by
      calc
        (LinearMap.lTensor S K.mkQ) (z - TensorProduct.mk R S T 1 x)
            = (LinearMap.lTensor S K.mkQ) z -
                (LinearMap.lTensor S K.mkQ) (TensorProduct.mk R S T 1 x) := by
                  simp
        _ = (LinearMap.lTensor S K.mkQ) z -
              TensorProduct.mk R S (T ⧸ K) 1 (K.mkQ x) := by
                simp [TensorProduct.mk]
        _ = 0 := by
              rw [hq]
              simp
    obtain ⟨w, hw⟩ := (hExactTensor (z - TensorProduct.mk R S T 1 x)).mp hker
    obtain ⟨k, hk⟩ := hK.2 w
    refine ⟨x + (k : T), ?_⟩
    have hkImage :
        TensorProduct.mk R S T 1 (k : T) =
          z - TensorProduct.mk R S T 1 x := by
      calc
        TensorProduct.mk R S T 1 (k : T)
            = (LinearMap.lTensor S K.subtype) (TensorProduct.mk R S K 1 k) := by
                simp [TensorProduct.mk]
        _ = (LinearMap.lTensor S K.subtype) w := by
              simpa [hk]
        _ = z - TensorProduct.mk R S T 1 x := hw
    calc
      TensorProduct.mk R S T 1 (x + (k : T))
          = TensorProduct.mk R S T 1 x + TensorProduct.mk R S T 1 (k : T) := by
              simpa [TensorProduct.mk] using (TensorProduct.tmul_add (1 : S) x (k : T))
      _ = TensorProduct.mk R S T 1 x + (z - TensorProduct.mk R S T 1 x) := by
            rw [hkImage]
      _ = z := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 18.28.16: bijectivity of the tensor unit on `R ⧸ J` is the quotient-ring
statement `R ⧸ J → S ⧸ JS`. -/
private theorem quotientMap_bijective_of_tensorBaseChange_bijective_on_quotient
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (J : Ideal R)
    (hbijJ : Function.Bijective (TensorProduct.mk R S (R ⧸ J) 1)) :
    Function.Bijective
      (Ideal.quotientMap
        (J.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  let e : S ⊗[R] (R ⧸ J) ≃+* S ⧸ J.map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J).symm.toRingEquiv
  have hAlg :
      Function.Bijective
        (Algebra.TensorProduct.includeRight : R ⧸ J →ₐ[R] S ⊗[R] (R ⧸ J)) := by
    -- Proof comment: `includeRight` is the ring-hom avatar of the tensor unit `x ↦ 1 ⊗ x`.
    simpa [Algebra.TensorProduct.includeRight_apply] using hbijJ
  have hEq :
      e.toRingHom.comp
          (Algebra.TensorProduct.includeRight : R ⧸ J →ₐ[R] S ⊗[R] (R ⧸ J)).toRingHom =
        Ideal.quotientMap
          (J.map (algebraMap R S))
          (algebraMap R S)
          Ideal.le_comap_map := by
    -- Proof comment: both quotient-side maps agree on the classes `x mod J`.
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J).symm
          ((1 : S) ⊗ₜ[R] (Ideal.Quotient.mk J x)) =
        (Ideal.Quotient.mk (J.map (algebraMap R S))) ((algebraMap R S) x)
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : S) = algebraMap R S x := by
      simpa [Algebra.smul_def]
    simpa [hs]
  rw [← hEq]
  exact e.bijective.comp hAlg

/-- Helper for Lemma 18.28.16: bijectivity of the quotient map modulo `I` propagates to every
positive power `I^n` once the base ring map is flat. -/
private theorem quotientMap_pow_bijective_of_quotientMap_bijective
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (I : Ideal R)
    (hflat : (algebraMap R S).Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map)) :
    ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  have hquot1 :
      Function.Bijective
        (Ideal.quotientMap
          ((I ^ (1 : ℕ)).map (algebraMap R S))
          (algebraMap R S)
          Ideal.le_comap_map) := by
    have hmap1 :
        (I ^ (1 : ℕ)).map (algebraMap R S) = I.map (algebraMap R S) := by
      simp [Ideal.map_pow, pow_one]
    let eR : R ⧸ I ^ (1 : ℕ) ≃+* R ⧸ I :=
      Ideal.quotEquivOfEq (pow_one I)
    let eS : S ⧸ (I ^ (1 : ℕ)).map (algebraMap R S) ≃+* S ⧸ I.map (algebraMap R S) :=
      Ideal.quotEquivOfEq hmap1
    have hq1_eq :
        Ideal.quotientMap
            ((I ^ (1 : ℕ)).map (algebraMap R S))
            (algebraMap R S)
            Ideal.le_comap_map =
          eS.symm.toRingHom.comp
            ((Ideal.quotientMap
                (I.map (algebraMap R S))
                (algebraMap R S)
                Ideal.le_comap_map).comp eR.toRingHom) := by
      apply Ideal.Quotient.ringHom_ext
      rw [Ideal.quotientMap_comp_mk]
      ext x
      change
        Ideal.Quotient.mk ((I ^ (1 : ℕ)).map (algebraMap R S)) ((algebraMap R S) x) =
          (Ideal.quotEquivOfEq hmap1.symm)
            (Ideal.Quotient.mk (I.map (algebraMap R S)) ((algebraMap R S) x))
      rw [Ideal.quotEquivOfEq_mk]
    rw [hq1_eq]
    exact eS.symm.bijective.comp (hquot.comp eR.bijective)
  let hpow :
      ∀ m : ℕ, Function.Bijective
        (Ideal.quotientMap
          ((I ^ (m + 1)).map (algebraMap R S))
          (algebraMap R S)
          Ideal.le_comap_map) := by
    intro m
    induction m with
    | zero =>
        -- Proof comment: the induction starts from the original quotient map modulo `I`.
        simpa using hquot1
    | succ m hm =>
        let T : Type u := R ⧸ I ^ (m + 2)
        let K : Submodule R T := I ^ (m + 1) • (⊤ : Submodule R T)
        have hbounds :
            I ≤ Module.annihilator R K ∧
              I ^ (m + 1) ≤ Module.annihilator R (T ⧸ K) := by
          simpa [T, K] using quotient_pow_step_annihilator_bounds (R := R) I m
        have hbounds1 : I ^ (1 : ℕ) ≤ Module.annihilator R K := by
          simpa [pow_one] using hbounds.1
        have hKbij :
            Function.Bijective (TensorProduct.mk R S K 1) := by
          -- Proof comment: the submodule is annihilated by `I`, so the one-step quotient
          -- hypothesis already controls its tensor unit.
          simpa using
            (tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective
              (I := I) (R' := S) (n := (1 : ℕ+)) hbounds1 hquot1)
        have hQbij :
            Function.Bijective (TensorProduct.mk R S (T ⧸ K) 1) := by
          -- Proof comment: the quotient is annihilated by `I^(m+1)`, so the induction
          -- hypothesis applies at the next finite stage.
          simpa [T, K] using
            (tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective
              (I := I) (R' := S)
              (n := ⟨m + 1, Nat.succ_pos m⟩) hbounds.2 hm)
        have hTbij :
            Function.Bijective (TensorProduct.mk R S T 1) :=
          tensorBaseChange_bijective_of_submodule_and_quotient
            (R := R) (S := S) hflat K hKbij hQbij
        -- Proof comment: once the tensor unit is bijective on `R / I^(m+2)`, the matching
        -- quotient-ring map is bijective as well.
        simpa [T] using
          (quotientMap_bijective_of_tensorBaseChange_bijective_on_quotient
            (R := R) (S := S) (J := I ^ (m + 2)) hTbij)
  intro n
  rcases n with ⟨n, hn⟩
  cases n with
  | zero =>
      exact (False.elim (Nat.not_lt_zero 0 hn))
  | succ m =>
      -- Proof comment: rewrite the positive index as `m + 1` and invoke the internal induction.
      simpa using hpow m

/-- Helper for Lemma 18.28.16: the Chapter 15 tensor base-change criterion needed here is the
forward direction from quotient-map bijectivity to bijectivity of the tensor unit on ideal-power
torsion modules. -/
private theorem tensorBaseChange_bijective_of_quotientMap_bijective_of_baseChangeFaithfulOnIdealPowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R)
    (hflat : (algebraMap R S).Flat)
    (hfaithful : (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I).Faithful)
    (hquot : Function.Bijective
      (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map))
    (M : ModuleCat R)
    (hM : Module.IsIdealPowerTorsion I M) :
    Function.Bijective (TensorProduct.mk R S M 1) := by
  -- Route correction: instead of importing `Lemma_15.90.2` and re-triggering the duplicated
  -- owner API, port only its local bridge: upgrade the quotient bijection from `I` to all powers
  -- `I^n`, then apply the Chapter 15 colimit theorem from `Lemma_15.89.9`.
  exact
    tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
      (I := I) (R' := S) hM <|
        quotientMap_pow_bijective_of_quotientMap_bijective
          (R := R) (S := S) I hflat hquot

-- Proof sketch: evaluate the sheaf-level base-change unit at each object `U`. The flatness
-- hypothesis is expressed by the chapter owner `IsFlatHom α`; the quotient hypothesis is the
-- sheaf-level isomorphism `quotientRingSheafMap α I : \mathcal O / \mathcal I \to
-- \mathcal O' / \mathcal I \mathcal O'`, and the nilpotence hypothesis is the source-facing
-- predicate `IsAnnihilatedByIdealPower I ℱ`.
-- Evaluate the base-change unit at each object `U`, apply the module statement from
-- Lemma `15.90.2` to `(α.hom.app U).hom`, then reassemble the sectionwise isomorphisms into the
-- sheaf-level adjunction unit.
/-- Lemma 18.28.16: let `\mathcal C` be a site, let `\mathcal O \to \mathcal O'` be a flat
homomorphism of sheaves of rings, and let `\mathcal I \subset \mathcal O` be an ideal sheaf,
formalized by a subobject `I : \operatorname{Sub}(\mathcal O)`, such that the canonical quotient
map `quotientRingSheafMap α I : \mathcal O/\mathcal I \to
\mathcal O'/\mathcal I \mathcal O'` is an isomorphism. If an `\mathcal O`-module `\mathcal F`
is annihilated by some power of
`\mathcal I`, expressed by `IsAnnihilatedByIdealPower I ℱ`, then the
canonical base-change morphism
`id ⊗ 1 : \mathcal F \to \mathcal F \otimes_{\mathcal O} \mathcal O'`, formalized here as the
unit of the pullback/pushforward adjunction for `ringedSiteStructureMap α`, is an isomorphism. -/
@[stacks 0GLY]
theorem tensorBaseChangeUnit_isIso_of_isFlatHom_of_quotientMap_bijective_of_annihilated
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (α : 𝒪 ⟶ 𝒪')
    (hflat : IsFlatHom α)
    (I : Subobject (unitModule J 𝒪))
    (ℱ : ringedSiteModuleCategory J 𝒪)
    [hquot : IsIso (quotientRingSheafMap α I)]
    (hpow : IsAnnihilatedByIdealPower I ℱ) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)).unit.app ℱ) :=
  by
    -- Prepare the exact sectionwise torsion hypothesis consumed by the Chapter 15 base-change
    -- theorem on ordinary rings and modules.
    have htors :
        ∀ U : Cᵒᵖ, Module.IsIdealPowerTorsion (idealSectionIdeal I U) (ℱ.val.obj U) := by
      intro U
      exact annihilated_sections_are_ideal_power_torsion (J := J) I ℱ hpow U
    have hquotApp :
        ∀ U : Cᵒᵖ, IsIso ((quotientRingSheafMap α I).hom.app U) := by
      intro U
      exact quotientRingSheafMap_app_isIso (J := J) α I U
    -- Proof comment: reflect the sheaf-level isomorphism from the objectwise evaluations. The
    -- sectionwise algebra now follows the Chapter 15 tensor base-change criterion; only the final
    -- transport from the evaluated sheaf unit to the ordinary tensor-unit map remains.
    refine module_isIso_of_evaluation_isIso (J := J) (𝒪 := 𝒪)
      ((SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)).unit.app ℱ) ?_
    intro U
    let φ : 𝒪.obj.obj U →+* 𝒪'.obj.obj U := (α.hom.app U).hom
    let M : ModuleCat (𝒪.obj.obj U) := (SheafOfModules.evaluation (ringSheaf J 𝒪) U).obj ℱ
    have hflatU : φ.Flat := app_flat_of_isFlatHom (J := J) α hflat U
    have hquotBij :
        Function.Bijective (quotientMapModIdeal φ (idealSectionIdeal I U)) := by
      letI : IsIso ((quotientRingSheafMap α I).hom.app U) := hquotApp U
      simpa [quotientRingSheafMap_app_hom_eq_quotientMapModIdeal (J := J) α I U, φ] using
        (CategoryTheory.ConcreteCategory.isIso_iff_bijective
          ((quotientRingSheafMap α I).hom.app U)).1
          inferInstance
    have hfaithful :
        (idealPowerTorsionRestrictedBaseChange.{u, u, u}
          φ (idealSectionIdeal I U)).Faithful := by
      have hqff : (quotientMapModIdeal φ (idealSectionIdeal I U)).FaithfullyFlat :=
        RingHom.FaithfullyFlat.of_bijective hquotBij
      have hTFAE :=
        flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules.{u, u, u, u}
          φ (idealSectionIdeal I U)
      have hClause1 :
          φ.Flat ∧ (quotientMapModIdeal φ (idealSectionIdeal I U)).FaithfullyFlat :=
        ⟨hflatU, hqff⟩
      have hClause4 :
          φ.Flat ∧
            (idealPowerTorsionRestrictedBaseChange.{u, u, u}
              φ (idealSectionIdeal I U)).Faithful :=
        (hTFAE.out 0 3).mp hClause1
      exact hClause4.2
    have htensorBij :
        letI : Algebra (𝒪.obj.obj U) (𝒪'.obj.obj U) := φ.toAlgebra
        Function.Bijective
          (TensorProduct.mk (𝒪.obj.obj U) (𝒪'.obj.obj U) M 1) := by
      letI : Algebra (𝒪.obj.obj U) (𝒪'.obj.obj U) := φ.toAlgebra
      have hflatAlg : (algebraMap (𝒪.obj.obj U) (𝒪'.obj.obj U)).Flat := by
        simpa [RingHom.algebraMap_toAlgebra, φ] using hflatU
      exact
        tensorBaseChange_bijective_of_quotientMap_bijective_of_baseChangeFaithfulOnIdealPowerTorsion
          (R := 𝒪.obj.obj U) (S := 𝒪'.obj.obj U) (I := idealSectionIdeal I U)
          (hflat := hflatAlg) (hfaithful := hfaithful) (hquot := hquotBij) M (htors U)
    letI : Algebra (𝒪.obj.obj U) (𝒪'.obj.obj U) := φ.toAlgebra
    have hmoduleUnitIso :
        IsIso ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M) := by
      let eTensor := extendScalars_tensor_module_iso φ M
      have hpostBij :
          Function.Bijective
            (((ModuleCat.extendRestrictScalarsAdj φ).unit.app M) ≫
              (ModuleCat.restrictScalars φ).map eTensor.hom) := by
        -- Proof comment: after the standard tensor-model comparison, the module adjunction unit
        -- is exactly the tensor map `m ↦ 1 ⊗ m`, whose bijectivity was already proved above.
        rw [extendRestrictScalars_unit_eq_tensor_mk (φ := φ) (M := M)]
        simpa using htensorBij
      have hunitBij :
          Function.Bijective ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M) :=
        bijective_of_bijective_postcomp_isIso
          ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M)
          ((ModuleCat.restrictScalars φ).map eTensor.hom) hpostBij
      exact
        (CategoryTheory.ConcreteCategory.isIso_iff_bijective
          ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M)).2 hunitBij
    -- Route correction: use the owner lemma from Lemma 18.25.1 to identify the evaluated sheaf
    -- unit directly with the module `extend/restrict` unit, instead of transporting through a
    -- separate pullback-object comparison.
    have hEvalEq :
        (SheafOfModules.evaluation (ringSheaf J 𝒪) U).map
            ((SheafOfModules.pullbackPushforwardAdjunction
              (ringedSiteStructureMap α)).unit.app ℱ) =
          (ModuleCat.extendRestrictScalarsAdj φ).unit.app M := by
      -- Proof comment: the sectionwise base-change unit is exactly the owner-level unit for
      -- extension and restriction of scalars along the section ring map `φ`.
      simpa [φ, M] using
        RingedSite.Hom.evaluation_pullbackPushforwardUnit_app_eq_extendRestrictScalars_unit
          (f := sameSiteHom α) (𝒢 := ℱ) (U := U)
    simpa [hEvalEq] using hmoduleUnitIso

end SheafOfModules.RingedSite
