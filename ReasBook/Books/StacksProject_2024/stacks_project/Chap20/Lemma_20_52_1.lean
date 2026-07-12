import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap17.Lemma_17_10_5
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Definition_20_46_1

open CategoryTheory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})

private abbrev topOpenX : TopologicalSpace.Opens X :=
  ⟨Set.univ, isOpen_univ⟩

local notation "ΓX" => globalSectionsRing X
local notation "ΓMod" => moduleGlobalSectionsFunctor X
local notation "FiniteProjectivesΓX" => finiteProjectiveModuleProperty ΓX
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/- Domain-style sampling for Lemma 20.52.1:
- primary domain: `𝒪_X`-modules on a ringed space, their global sections, the retract
  closure of finite free modules, and finite projective modules over `Γ(X, 𝒪_X)`;
- sampled owner declarations:
  `RingedSpace.ringCatSheaf`,
  `globalSectionsRing`,
  `moduleGlobalSectionsFunctor`,
  `SheafOfModules.finiteFreeRetractModuleProperty`,
  `finiteProjectiveModuleProperty`,
  `FiniteProjectiveModuleCat`;
- source/core/bridge triage:
  `source-facing`: the Chapter 20 assertion that global sections identify finite-free-retract
    `𝒪_X`-modules with finite projective `Γ(X, 𝒪_X)`-modules;
  `core/canonical`: the existing object properties
    `SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf` and
    `finiteProjectiveModuleProperty (globalSectionsRing X)`, together with the functor
    `moduleGlobalSectionsFunctor X`;
  `bridge/view`: the canonical `ObjectProperty.lift` of the global-sections functor from the full
    subcategory of finite-free-retract `𝒪_X`-modules to
    `FiniteProjectiveModuleCat (globalSectionsRing X)`.
- refined owner surface: the source-facing equivalence statement and canonical instance on that
  lifted global-sections functor expression, without a redundant public wrapper `abbrev`.
-/

/-- Helper for Lemma 20.52.1: sections of an `𝒪_X`-module are identified with its value on the
top open. -/
private abbrev topOpenHom (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    op (topOpenX X) ⟶ U :=
  (homOfLE (show U.unop ≤ topOpenX X from by
    intro x hx
    trivial)).op

/-- Helper for Lemma 20.52.1: terminal evaluation packages a top section into a compatible family
of sections. -/
private theorem topSectionsFromTerminal_naturality
    (M : X.Modules) (m : ((moduleGlobalSectionsFunctor X).obj M)) :
    ∀ U V : (TopologicalSpace.Opens X)ᵒᵖ, ∀ f : U ⟶ V,
      M.val.map f (M.val.map (topOpenHom X U) m) =
        M.val.map (topOpenHom X V) m := by
  intro U V f
  have h : topOpenHom X U ≫ f = topOpenHom X V := by
    exact Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 20.52.1: a top section determines a genuine sheaf section. -/
private noncomputable def topSectionsFromTerminal
    (M : X.Modules) (m : ((moduleGlobalSectionsFunctor X).obj M)) :
    M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.val.map (topOpenHom X U) m)
    (topSectionsFromTerminal_naturality X M m)

/-- Helper for Lemma 20.52.1: sections of an `𝒪_X`-module are identified with its value on the
top open. -/
private noncomputable def topSectionEquiv (M : X.Modules) :
    M.sections ≃ ((moduleGlobalSectionsFunctor X).obj M) where
  toFun s := s.1 (op (topOpenX X))
  invFun := topSectionsFromTerminal X M
  left_inv s := by
    ext U
    simpa using PresheafOfModules.sections_property s (topOpenHom X U)
  right_inv m := by
    change M.val.map (topOpenHom X (op (topOpenX X))) m = m
    have h : topOpenHom X (op (topOpenX X)) = 𝟙 (op (topOpenX X)) := Subsingleton.elim _ _
    simpa [h] using M.val.congr_map_apply h m

/-- Helper for Lemma 20.52.1: the inverse of `topSectionEquiv` is natural in a morphism of
`𝒪_X`-modules. -/
private theorem sectionsMap_topSectionEquiv_symm
    {M N : X.Modules} (p : M ⟶ N) (m : ((moduleGlobalSectionsFunctor X).obj M)) :
    SheafOfModules.sectionsMap p ((topSectionEquiv X M).symm m) =
      (topSectionEquiv X N).symm (((moduleGlobalSectionsFunctor X).map p).hom m) := by
  -- Proof comment: both sides are obtained by restricting the same top-open value along
  -- `topOpenHom`, so the claim is the naturality of `p`.
  ext U
  simp [topSectionEquiv, topSectionsFromTerminal]
  simpa using (ConcreteCategory.congr_hom (p.val.naturality (topOpenHom X U)) m)

/-- Helper for Lemma 20.52.1: top evaluation commutes with `sectionsMap`. -/
private theorem topSectionEquiv_sectionsMap
    {M N : X.Modules} (p : M ⟶ N) (s : M.sections) :
    topSectionEquiv X N (SheafOfModules.sectionsMap p s) =
      (((moduleGlobalSectionsFunctor X).map p).hom) (topSectionEquiv X M s) := by
  -- Proof comment: rewrite `s` as the inverse image of its top-open value, then use the
  -- naturality of `topSectionEquiv.symm`.
  simpa using congrArg (topSectionEquiv X N)
    (sectionsMap_topSectionEquiv_symm (X := X) (p := p) (m := topSectionEquiv X M s))

/-- Helper for Lemma 20.52.1: evaluating `unitHomEquiv` on the top open computes the
corresponding morphism on the distinguished unit section. -/
private theorem unitHomEquiv_apply_top
    (M : X.Modules) (f : 𝒪X ⟶ M) :
    topSectionEquiv X M (M.unitHomEquiv f) =
      (f.val.app (op (topOpenX X)))
        (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op (topOpenX X))) from
          (1 : ΓX)) := by
  -- Proof comment: top evaluation of `unitHomEquiv` is definitional evaluation of `f` at the
  -- distinguished top-open section `1`.
  rfl

/-- Helper for Lemma 20.52.1: a global section on the top open determines the corresponding
morphism `𝒪_X ⟶ M`. -/
private noncomputable def topSectionMorphism
    (M : X.Modules) (x : ((moduleGlobalSectionsFunctor X).obj M)) :
    𝒪X ⟶ M :=
  M.unitHomEquiv.symm ((topSectionEquiv X M).symm x)

/-- Helper for Lemma 20.52.1: evaluating `topSectionMorphism` on the distinguished top-open unit
section recovers the chosen top section. -/
private theorem topSectionMorphism_apply_top
    (M : X.Modules) (x : ((moduleGlobalSectionsFunctor X).obj M)) :
    ((topSectionMorphism (X := X) M x).val.app (op (topOpenX X)))
        (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op (topOpenX X))) from
          (1 : ΓX)) = x := by
  -- Proof comment: `topSectionMorphism` is defined as the inverse of `unitHomEquiv` followed by
  -- the inverse of `topSectionEquiv`.
  simpa [topSectionMorphism] using
    (unitHomEquiv_apply_top (X := X) M (topSectionMorphism (X := X) M x)).symm

/-- Helper for Lemma 20.52.1: equality of morphisms from `𝒪_X` can be checked on the
distinguished top section `1`. -/
private theorem topSectionMorphism_ext
    {M : X.Modules} {f g : 𝒪X ⟶ M}
    (h :
      ((f.val.app (op (topOpenX X)))
          (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op (topOpenX X))) from (1 : ΓX))) =
        ((g.val.app (op (topOpenX X)))
          (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op (topOpenX X))) from
            (1 : ΓX)))) :
    f = g := by
  -- Proof comment: transport both morphisms through `unitHomEquiv` and `topSectionEquiv`; after
  -- evaluating at the top open, the goal is exactly the assumed equality of distinguished values.
  apply M.unitHomEquiv.injective
  apply (topSectionEquiv X M).injective
  rw [unitHomEquiv_apply_top, unitHomEquiv_apply_top]
  exact h

/-- Helper for Lemma 20.52.1: applying `topSectionMorphism` after `topSectionEquiv` recovers the
corresponding morphism out of `𝒪_X`. -/
private theorem topSectionMorphism_topSectionEquiv
    (M : X.Modules) (s : M.sections) :
    topSectionMorphism (X := X) M (topSectionEquiv X M s) = M.unitHomEquiv.symm s := by
  -- Proof comment: this is the defining cancellation between `topSectionEquiv` and its inverse.
  simp [topSectionMorphism]

/-- Helper for Lemma 20.52.1: `topSectionMorphism` commutes with the global-sections action of a
module morphism. -/
private theorem topSectionMorphism_map
    {M N : X.Modules} (p : M ⟶ N) (x : ((moduleGlobalSectionsFunctor X).obj M)) :
    topSectionMorphism (X := X) N ((((moduleGlobalSectionsFunctor X).map p).hom) x) =
      topSectionMorphism (X := X) M x ≫ p := by
  -- Proof comment: both unit morphisms have the same top-open value, namely the image of `x`
  -- under `Γ(X, p)`.
  apply topSectionMorphism_ext (X := X)
  rw [topSectionMorphism_apply_top]
  change (((moduleGlobalSectionsFunctor X).map p).hom) x =
    (p.val.app (op (topOpenX X)))
      (((topSectionMorphism (X := X) M x).val.app (op (topOpenX X)))
        (show ((SheafOfModules.unit X.ringCatSheaf).val.obj (op (topOpenX X))) from
          (1 : ΓX)))
  rw [topSectionMorphism_apply_top]
  rfl

/-- Helper for Lemma 20.52.1: the unit morphism attached to the global section `1` of `𝒪_X` is
the identity of `𝒪_X`. -/
private theorem topSectionMorphism_one :
    topSectionMorphism (X := X) 𝒪X (show ((moduleGlobalSectionsFunctor X).obj 𝒪X) from
      (1 : ΓX)) = 𝟙 𝒪X := by
  -- Proof comment: both morphisms out of `𝒪_X` carry the distinguished top-open section `1` to
  -- the same element of `Γ(X, 𝒪_X)`.
  apply topSectionMorphism_ext (X := X)
  rw [topSectionMorphism_apply_top]
  rfl

/-- Helper for Lemma 20.52.1: applying `sectionsMap` to a section produced by `unitHomEquiv`
corresponds to postcomposing the underlying unit morphism. -/
private theorem sectionsMap_unitHomEquiv
    {M N : X.Modules} (φ : 𝒪X ⟶ M) (p : M ⟶ N) :
    SheafOfModules.sectionsMap p (M.unitHomEquiv φ) =
      N.unitHomEquiv (φ ≫ p) := by
  -- Proof comment: both sections evaluate on each open by applying `p` to the same value of `φ`.
  ext U
  rfl

/-- Helper for Lemma 20.52.1: the distinguished section of `𝒪_X` attached to a global section of
`X`. -/
private noncomputable def unitSectionOfGlobalSection (r : ΓX) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).sections :=
  (topSectionEquiv X 𝒪X).symm r

/-- Helper for Lemma 20.52.1: converting a global section into a section of `𝒪_X` and evaluating
it again on the top open recovers the original element of `Γ(X, 𝒪_X)`. -/
private theorem topSectionEquiv_unitSectionOfGlobalSection
    (r : ΓX) :
    topSectionEquiv X 𝒪X (unitSectionOfGlobalSection (X := X) r) = r := by
  -- Proof comment: this is the `left_inv` identity of `topSectionEquiv`.
  exact (topSectionEquiv X 𝒪X).apply_symm_apply r

/-- Helper for Lemma 20.52.1: the `i`th coordinate projection from the free sheaf to the unit
module is classified by the Kronecker-delta family of unit sections. -/
private noncomputable def freeCoordinateProjection
    {I : Type u} [DecidableEq I] (i : I) :
    (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules) ⟶ 𝒪X :=
  (SheafOfModules.freeHomEquiv 𝒪X).symm
    (fun j ↦ if _ : j = i then
      unitSectionOfGlobalSection (X := X) (show ΓX from (1 : ΓX))
    else
      unitSectionOfGlobalSection (X := X) (show ΓX from (0 : ΓX)))

/-- Helper for Lemma 20.52.1: the coordinate projection sends the `j`th free basis section to the
expected Kronecker-delta section of `𝒪_X`. -/
private theorem freeCoordinateProjection_freeSection
    {I : Type u} [DecidableEq I] (i j : I) :
    SheafOfModules.sectionsMap (freeCoordinateProjection (X := X) i)
        (SheafOfModules.freeSection (R := X.ringCatSheaf) j) =
      if _ : j = i then
        unitSectionOfGlobalSection (X := X) (show ΓX from (1 : ΓX))
      else
        unitSectionOfGlobalSection (X := X) (show ΓX from (0 : ΓX)) := by
  -- Proof comment: this is the defining basis-vector computation for
  -- `SheafOfModules.freeHomEquiv.symm`.
  simpa [freeCoordinateProjection] using
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (f := fun k ↦ if _ : k = i then
        unitSectionOfGlobalSection (X := X) (show ΓX from (1 : ΓX))
      else
        unitSectionOfGlobalSection (X := X) (show ΓX from (0 : ΓX)))
      (i := j))

/-- Helper for Lemma 20.52.1: a retract of a finite projective `Γ(X, 𝒪_X)`-module is again
finite projective. -/
theorem finiteProjective_of_moduleRetract {M P : ModuleCat ΓX}
    (hP : FiniteProjectivesΓX P) (r : Retract M P) :
    FiniteProjectivesΓX M := by
  -- Proof comment: finite generation descends along the retraction map, and projectivity descends
  -- along the split monomorphism/retraction pair.
  refine ⟨?_, ?_⟩
  · letI : Module.Finite ΓX P := hP.1
    exact Module.Finite.of_surjective r.r.hom fun x ↦ ⟨r.i.hom x, by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom r.retract) x⟩
  · letI : Module.Projective ΓX P := hP.2
    exact Module.Projective.of_split r.i.hom r.r.hom (by
      ext x
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom r.retract) x)

/-- Helper for Lemma 20.52.1: evaluating the unit sheaf on the top open gives the regular
`Γ(X, \mathcal O_X)`-module. -/
private noncomputable def moduleGlobalSectionsUnitIso :
    ((moduleGlobalSectionsFunctor X).obj 𝒪X) ≅ ModuleCat.of ΓX ΓX :=
  Iso.refl _

/-- Helper for Lemma 20.52.1: over a finite index type, the function-model free module and the
finitely supported free module are canonically isomorphic. -/
private noncomputable def functionFiniteFreeIsoFinsuppFiniteFree
    {R : Type u} [CommRing R] (I : Type u) [Finite I] :
    ModuleCat.of R (I → R) ≅ ModuleCat.of R (I →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R I).symm.toModuleIso

/-- Helper for Lemma 20.52.1: global sections of the finite free sheaf `SheafOfModules.free I`
identify with the finite free `Γ(X, 𝒪_X)`-module `ΓX^I`. -/
private noncomputable def moduleGlobalSectionsFreeIsoPi
    {I : Type u} [Finite I] :
    ((moduleGlobalSectionsFunctor X).obj
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)) ≅
      ModuleCat.of ΓX (I → ΓX) :=
  let hFreeFinsupp :
      ((moduleGlobalSectionsFunctor X).obj
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)) ≅
        ModuleCat.of ΓX (I →₀ ΓX) :=
    -- Proof comment: `SheafOfModules.free I` is the coproduct of `I` copies of `𝒪_X`, and
    -- evaluation on the top open preserves that coproduct.
    (isColimitOfPreserves (moduleGlobalSectionsFunctor X)
        (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)).coconePointsIsoOfEquivalence
      (ModuleCat.finsuppCoconeIsColimit ΓX ΓX I)
      CategoryTheory.Equivalence.refl
      (Discrete.natIso fun _ ↦ moduleGlobalSectionsUnitIso (X := X)).symm
  -- Proof comment: for finite `I`, finitely supported functions and plain functions coincide.
  exact hFreeFinsupp ≪≫ (functionFiniteFreeIsoFinsuppFiniteFree (R := ΓX) I).symm

/-- Helper for Lemma 20.52.1: the Chapter 17 associated-module-sheaf functor is used through its
canonical adjunction with global sections. -/
private noncomputable abbrev associatedModuleSheafAdjunction :
    AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX) ⊣
      (AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX)).rightAdjoint :=
  Adjunction.ofIsLeftAdjoint (AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX))

/-- Helper for Lemma 20.52.1: package the Chapter 17 Hom-equivalence as a reusable local bridge.
-/
private noncomputable abbrev associatedModuleSheafHomEquiv
    (M : ModuleCat ΓX) (𝒢 : X.Modules) :
    ((AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) M ⟶ 𝒢) ≃
      (M ⟶ AlgebraicGeometry.ringedSpaceModuleGlobalSections (RingHom.id ΓX) 𝒢)) :=
  associatedModuleSheafAdjunction (X := X) |>.homEquiv M 𝒢

/-- Helper for Lemma 20.52.1: the Chapter 17 global-sections module is canonically identified
with evaluation on the top open. -/
private noncomputable def ringedSpaceModuleGlobalSectionsTopIso
    (𝒢 : X.Modules) :
    AlgebraicGeometry.ringedSpaceModuleGlobalSections (RingHom.id ΓX) 𝒢 ≅
      (moduleGlobalSectionsFunctor X).obj 𝒢 where
  hom :=
    ModuleCat.ofHom
      { toFun := fun s ↦ topSectionEquiv X 𝒢 s
        map_add' := by
          intro s t
          rfl
        map_smul' := by
          intro r s
          rfl }
  inv :=
    ModuleCat.ofHom
      { toFun := fun s ↦ (topSectionEquiv X 𝒢).symm s
        map_add' := by
          intro s t
          rfl
        map_smul' := by
          intro r s
          rfl }
  hom_inv_id := by
    -- Proof comment: the forward map is evaluation at the top open, and the inverse repackages
    -- that value as the unique compatible family of sections.
    ext s
    exact (topSectionEquiv X 𝒢).apply_symm_apply s
  inv_hom_id := by
    -- Proof comment: rebuilding a global section family from its top-open value recovers the
    -- original family by the defining compatibility relation.
    ext s
    exact (topSectionEquiv X 𝒢).symm_apply_apply s

/-- Helper for Lemma 20.52.1: the Chapter 17 right adjoint agrees naturally with the Chapter 20
global-sections owner. -/
private noncomputable def ringedSpaceModuleGlobalSectionsTopNatIso :
    (AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX)).rightAdjoint ≅ ΓMod :=
  NatIso.ofComponents
    (fun 𝒢 ↦ ringedSpaceModuleGlobalSectionsTopIso (X := X) 𝒢)
    (by
      intro 𝒢 ℋ f
      ext s
      rfl)

/-- Helper for Lemma 20.52.1: normalize the Chapter 17 adjunction so its right adjoint is the
current Chapter 20 global-sections owner. -/
private noncomputable def associatedModuleSheafΓAdjunction :
    AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX) ⊣ ΓMod :=
  (associatedModuleSheafAdjunction (X := X)).ofNatIsoRight
    (ringedSpaceModuleGlobalSectionsTopNatIso (X := X))

/-- Helper for Lemma 20.52.1: the standard finite free module on `Fin n` matches the same free
module after reindexing the basis by `ULift (Fin n)`. -/
private noncomputable def functionFiniteFreeIsoUliftFunctionFiniteFree
    (n : ℕ) :
    ModuleCat.of ΓX (Fin n → ΓX) ≅ ModuleCat.of ΓX (ULift.{u} (Fin n) → ΓX) :=
  -- Proof comment: `ULift` only changes the basis indexing type, so reindexing functions along
  -- `Equiv.ulift` packages the same free module in the basis type used by the sheaf-side free
  -- object.
  (LinearEquiv.funCongrLeft ΓX ΓX (Equiv.ulift : Fin n ≃ ULift.{u} (Fin n)).symm).toModuleIso

/-- Helper for Lemma 20.52.1: a function-valued global section of the finite free
`Γ(X, \mathcal O_X)`-module determines the corresponding global section of the free
`\mathcal O_X`-module on `ULift (Fin n)`. -/
private noncomputable def freeFiniteFunctionSection
    (n : ℕ) (a : Fin n → ΓX) :
    (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules).sections := by
  let F :=
    (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)
  let eΓ :
      ModuleCat.of ΓX (Fin n → ΓX) ⟶ (moduleGlobalSectionsFunctor X).obj F :=
    functionFiniteFreeIsoUliftFunctionFiniteFree (X := X) n |>.hom ≫
      (moduleGlobalSectionsFreeIsoPi (X := X) (I := ULift.{u} (Fin n))).symm.hom
  -- Proof comment: transport the function-valued coefficient tuple to the top-open evaluation of
  -- the free sheaf, then extend that top section to a genuine sheaf section.
  exact (topSectionEquiv X F).symm (eΓ.hom a)

/-- Helper for Lemma 20.52.1: `freeFiniteFunctionSection` is defined by transporting the given
function through the `ULift` reindexing and the global-sections/free-sheaf identification. -/
private theorem topSectionEquiv_freeFiniteFunctionSection
    (n : ℕ) (a : Fin n → ΓX) :
    topSectionEquiv X
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)
        (freeFiniteFunctionSection (X := X) n a) =
      ((moduleGlobalSectionsFreeIsoPi (X := X) (I := ULift.{u} (Fin n))).symm.hom).hom
        (((functionFiniteFreeIsoUliftFunctionFiniteFree (X := X) n).hom).hom a) := by
  -- Proof comment: `freeFiniteFunctionSection` was defined by `topSectionEquiv.symm`, so
  -- applying `topSectionEquiv` collapses the packaging back to the transported coefficient tuple.
  rfl

/-- Helper for Lemma 20.52.1: the finite function free module is canonically the global-sections
module of the corresponding finite free sheaf. -/
private noncomputable def functionFiniteToGlobalSectionsFreeIso
    (n : ℕ) :
    ModuleCat.of ΓX (Fin n → ΓX) ≅
      ((moduleGlobalSectionsFunctor X).obj
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)) :=
  functionFiniteFreeIsoUliftFunctionFiniteFree (X := X) n ≪≫
    (moduleGlobalSectionsFreeIsoPi (X := X) (I := ULift.{u} (Fin n))).symm

/-- Helper for Lemma 20.52.1: the finite free comparison morphism is the adjoint transpose of the
canonical identification of global sections of the free sheaf. -/
private noncomputable def associatedModuleSheafFunctionFiniteToFree
    (n : ℕ) :
    AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX)) ⟶
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules) :=
  ((associatedModuleSheafΓAdjunction (X := X)).homEquiv
      (ModuleCat.of ΓX (Fin n → ΓX))
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)).symm
    ((functionFiniteToGlobalSectionsFreeIso (X := X) n).hom)

/-- Helper for Lemma 20.52.1: the delta basis vector in the function-model free
`Γ(X,\mathcal O_X)`-module attached to `i : ULift (Fin n)`. -/
private noncomputable def functionFiniteBasisVector
    (n : ℕ) (i : ULift.{u} (Fin n)) :
    Fin n → ΓX :=
  fun j ↦ if i.down = j then 1 else 0

/-- Helper for Lemma 20.52.1: the chosen basis section of the associated sheaf comes from the
adjunction unit applied to the delta basis vector. -/
private noncomputable def associatedModuleSheafFunctionFiniteBasisSection
    (n : ℕ) (i : ULift.{u} (Fin n)) :
    (AlgebraicGeometry.associatedModuleSheaf
      (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX))).sections :=
  (topSectionEquiv X
      (AlgebraicGeometry.associatedModuleSheaf
        (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX)))).symm
    ((((associatedModuleSheafΓAdjunction (X := X)).unit.app
        (ModuleCat.of ΓX (Fin n → ΓX))).hom)
      (functionFiniteBasisVector (X := X) n i))

/-- Helper for Lemma 20.52.1: the explicit inverse of the finite free comparison sends the `i`th
free basis section to the corresponding basis section of the associated sheaf. -/
private noncomputable def associatedModuleSheafFunctionFiniteToFreeInv
    (n : ℕ) :
    (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules) ⟶
      AlgebraicGeometry.associatedModuleSheaf
        (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX)) :=
  (SheafOfModules.freeHomEquiv
      (AlgebraicGeometry.associatedModuleSheaf
        (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX)))).symm
    (associatedModuleSheafFunctionFiniteBasisSection (X := X) n)

/-- Helper for Lemma 20.52.1: the explicit inverse sends each free basis section to the chosen
basis section in the associated sheaf. -/
private theorem associatedModuleSheafFunctionFiniteToFreeInv_freeSection
    (n : ℕ) (i : ULift.{u} (Fin n)) :
    SheafOfModules.sectionsMap
        (associatedModuleSheafFunctionFiniteToFreeInv (X := X) n)
        (SheafOfModules.freeSection (R := X.ringCatSheaf) i) =
      associatedModuleSheafFunctionFiniteBasisSection (X := X) n i := by
  -- Proof comment: this is the defining basis-vector computation encoded in
  -- `sectionsMap_freeHomEquiv_symm_freeSection`.
  simpa [associatedModuleSheafFunctionFiniteToFreeInv] using
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (R := X.ringCatSheaf)
      (f := associatedModuleSheafFunctionFiniteBasisSection (X := X) n)
      i)

/-- Helper for Lemma 20.52.1: transporting the delta basis vector through
`functionFiniteToGlobalSectionsFreeIso` recovers the corresponding free basis section. -/
private theorem freeFiniteFunctionSection_basis
    (n : ℕ) (i : ULift.{u} (Fin n)) :
    freeFiniteFunctionSection (X := X) n (functionFiniteBasisVector (X := X) n i) =
      SheafOfModules.freeSection (R := X.ringCatSheaf) i := by
  -- TODO: compare the two sections by moving to their top-open values and proving that
  -- `functionFiniteToGlobalSectionsFreeIso` sends the delta basis vector to the top-open value of
  -- `SheafOfModules.freeSection i`.
  sorry

/-- Helper for Lemma 20.52.1: the explicit inverse followed by the comparison morphism is the
identity on the free sheaf. -/
private theorem associatedModuleSheafFunctionFiniteToFreeInv_comp
    (n : ℕ) :
    associatedModuleSheafFunctionFiniteToFreeInv (X := X) n ≫
      associatedModuleSheafFunctionFiniteToFree (X := X) n = 𝟙 _ := by
  -- TODO: after `freeHomEquiv`-injectivity reduces the goal to basis sections, the remaining
  -- normalization is exactly `freeFiniteFunctionSection_basis`.
  sorry

/-- Helper for Lemma 20.52.1: the comparison morphism followed by the explicit inverse is the
identity on the associated sheaf. -/
private theorem associatedModuleSheafFunctionFiniteToFree_compInv
    (n : ℕ) :
    associatedModuleSheafFunctionFiniteToFree (X := X) n ≫
      associatedModuleSheafFunctionFiniteToFreeInv (X := X) n = 𝟙 _ := by
  -- TODO: apply `associatedModuleSheafΓAdjunction.homEquiv`-injectivity and then use the same
  -- delta-basis normalization as in `associatedModuleSheafFunctionFiniteToFreeInv_comp`.
  sorry

/-- Helper for Lemma 20.52.1: the finite free comparison morphism should be an isomorphism. -/
private theorem associatedModuleSheafFunctionFiniteToFree_isIso
    (n : ℕ) :
    IsIso (associatedModuleSheafFunctionFiniteToFree (X := X) n) := by
  -- Proof comment: construct the inverse from the standard free basis sections, then use
  -- `freeHomEquiv` together with the normalized adjunction identities to show both composites are
  -- identities.
  refine ⟨⟨associatedModuleSheafFunctionFiniteToFreeInv (X := X) n, ?_, ?_⟩⟩
  · exact associatedModuleSheafFunctionFiniteToFree_compInv (X := X) n
  · exact associatedModuleSheafFunctionFiniteToFreeInv_comp (X := X) n

/-- Helper for Lemma 20.52.1: the associated module sheaf of a finite function free
`Γ(X,\mathcal O_X)`-module should identify with the free `\mathcal O_X`-module on the same
basis. -/
private noncomputable theorem associatedModuleSheafFunctionFiniteIsoFree
    (n : ℕ) :
    AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX)) ≅
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules) := by
  -- Proof comment: the previous declaration is the actual comparison morphism; after isolating
  -- its invertibility, the packaged isomorphism is immediate.
  letI : IsIso (associatedModuleSheafFunctionFiniteToFree (X := X) n) :=
    associatedModuleSheafFunctionFiniteToFree_isIso (X := X) n
  exact asIso (associatedModuleSheafFunctionFiniteToFree (X := X) n)

/-- Helper for Lemma 20.52.1: the normalized adjunction unit is invertible on finite function free
modules. -/
private theorem associatedModuleSheafΓ_unit_app_functionFree_isIso
    (n : ℕ) :
    IsIso ((associatedModuleSheafΓAdjunction (X := X)).unit.app
      (ModuleCat.of ΓX (Fin n → ΓX))) := by
  let adj := associatedModuleSheafΓAdjunction (X := X)
  let M := ModuleCat.of ΓX (Fin n → ΓX)
  let S := (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)
  let eΓ := functionFiniteToGlobalSectionsFreeIso (X := X) n
  let f : AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) M ⟶ S :=
    associatedModuleSheafFunctionFiniteToFree (X := X) n
  letI : IsIso f := associatedModuleSheafFunctionFiniteToFree_isIso (X := X) n
  have hunit : adj.unit.app M ≫ ΓMod.map f = eΓ.hom := by
    -- Proof comment: `f` was defined as the transpose of `eΓ.hom`, so `homEquiv_unit` rewrites
    -- the unit into exactly that chosen comparison.
    simpa [adj, M, S, eΓ, f, associatedModuleSheafFunctionFiniteToFree,
      functionFiniteToGlobalSectionsFreeIso] using
      (Adjunction.homEquiv_unit (adj := adj) (f := f)).symm
  have hη : adj.unit.app M = eΓ.hom ≫ inv (ΓMod.map f) := by
    -- Proof comment: cancel the induced global-sections isomorphism on the right to expose the
    -- unit as a composition of explicit isomorphisms.
    apply (cancel_mono (ΓMod.map f)).1
    simpa [Category.assoc] using hunit
  rw [hη]
  infer_instance

/-- Helper for Lemma 20.52.1: the normalized adjunction counit is invertible on the finite free
sheaves indexed by `ULift (Fin n)`. -/
private theorem associatedModuleSheafΓ_counit_app_free_isIso
    (n : ℕ) :
    IsIso ((associatedModuleSheafΓAdjunction (X := X)).counit.app
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)) := by
  let adj := associatedModuleSheafΓAdjunction (X := X)
  let M := ModuleCat.of ΓX (Fin n → ΓX)
  let S := (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)
  let eΓ := functionFiniteToGlobalSectionsFreeIso (X := X) n
  let f : AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) M ⟶ S :=
    associatedModuleSheafFunctionFiniteToFree (X := X) n
  letI : IsIso f := associatedModuleSheafFunctionFiniteToFree_isIso (X := X) n
  have hcounit : adj.left.map eΓ.hom ≫ adj.counit.app S = f := by
    -- Proof comment: this is the counit-side transpose identity for the normalized adjunction.
    simpa [adj, M, S, eΓ, f, associatedModuleSheafFunctionFiniteToFree,
      functionFiniteToGlobalSectionsFreeIso] using
      (Adjunction.homEquiv_counit adj M S eΓ.hom)
  have hε : adj.counit.app S = inv (adj.left.map eΓ.hom) ≫ f := by
    -- Proof comment: cancel the left-adjoint image of `eΓ` to rewrite the counit as an explicit
    -- composition of isomorphisms.
    apply (cancel_mono (adj.left.map eΓ.hom)).1
    simp [hcounit, Category.assoc]
  rw [hε]
  infer_instance

/-- Helper for Lemma 20.52.1: the normalized adjunction counit is invertible on any finite free
sheaf after reindexing the basis to `ULift (Fin n)`. -/
private theorem associatedModuleSheafΓ_counit_app_free_isIso_of_finite
    {I : Type u} [Finite I] :
    IsIso ((associatedModuleSheafΓAdjunction (X := X)).counit.app
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)) := by
  classical
  let n := Fintype.card I
  let eI : I ≃ ULift.{u} (Fin n) := (Fintype.equivFin I).trans Equiv.ulift
  let eSheaf :
      (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules) ≅
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules) :=
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso (Equiv.toIso eI)
  letI :
      IsIso ((associatedModuleSheafΓAdjunction (X := X)).counit.app
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules)) :=
    associatedModuleSheafΓ_counit_app_free_isIso (X := X) n
  exact counit_app_isIso_of_retract
    (adj := associatedModuleSheafΓAdjunction (X := X))
    (Retract.ofIso eSheaf)

/-- Helper for Lemma 20.52.1: the associated module sheaf of a finite projective global-sections
module is a retract of a finite free `\mathcal O_X`-module. -/
private theorem associatedModuleSheaf_mem_finiteFreeRetractModuleProperty
    (P : FiniteProjectiveModuleCat ΓX) :
    SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf
      (AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) P.obj) := by
  -- Proof comment: choose a split finite free cover of the projective module, map that retract
  -- through the associated-module-sheaf functor, and rewrite the ambient free object using the
  -- finite-rank comparison above.
  obtain ⟨n, π, ι, hπsurj, _, hιπ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective ΓX P.obj
  let πCat : ModuleCat.of ΓX (Fin n → ΓX) ⟶ P.obj := ModuleCat.ofHom π
  let ιCat : P.obj ⟶ ModuleCat.of ΓX (Fin n → ΓX) := ModuleCat.ofHom ι
  have hsplit : ιCat ≫ πCat = 𝟙 P.obj := by
    -- Proof comment: the chosen section and projection split by construction.
    ext x
    simpa [πCat, ιCat, LinearMap.comp_apply] using
      congrArg (fun f : P.obj →ₗ[ΓX] P.obj ↦ f x) hιπ
  let r : Retract P.obj (ModuleCat.of ΓX (Fin n → ΓX)) := ⟨ιCat, πCat, hsplit⟩
  let hAssocRetract :
      Retract (AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) P.obj)
        (AlgebraicGeometry.associatedModuleSheaf
          (RingHom.id ΓX) (ModuleCat.of ΓX (Fin n → ΓX))) :=
    Retract.map r (AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX))
  let hFreeRetract :
      Retract (AlgebraicGeometry.associatedModuleSheaf (RingHom.id ΓX) P.obj)
        (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin n)) : X.Modules) :=
    hAssocRetract.trans (Retract.ofIso (associatedModuleSheafFunctionFiniteIsoFree (X := X) n))
  exact SheafOfModules.finiteFreeRetractModuleProperty_of_retract_free hFreeRetract

/-- Global sections of a finite-free-retract `𝒪_X`-module form a finite projective
module over `Γ(X, 𝒪_X)`. -/
theorem moduleGlobalSections_mem_finiteProjectiveModuleProperty
    (ℱ : (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).FullSubcategory) :
    FiniteProjectivesΓX
      (((SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).ι ⋙ ΓMod).obj ℱ) :=
  by
  -- Proof comment: present `ℱ.obj` as a retract of a finite free sheaf, map that retract through
  -- global sections, then rewrite the free ambient object using the free-case comparison above.
  change FiniteProjectivesΓX ((moduleGlobalSectionsFunctor X).obj ℱ.obj)
  obtain ⟨I, hI, ⟨r⟩⟩ :=
    (SheafOfModules.finiteFreeRetractModuleProperty_iff (𝒪 := X.ringCatSheaf) ℱ.obj).1 ℱ.2
  let _ : Finite I := hI
  let hΓretract :
      Retract ((moduleGlobalSectionsFunctor X).obj ℱ.obj)
        ((moduleGlobalSectionsFunctor X).obj
          (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)) :=
    Retract.map r (moduleGlobalSectionsFunctor X)
  let hFree : FiniteProjectivesΓX (ModuleCat.of ΓX (I → ΓX)) := by
    -- Proof comment: the function module on a finite index set is the standard finite free module.
    let _ : Module.Finite ΓX (I → ΓX) := inferInstance
    let _ : Module.Projective ΓX (I → ΓX) := inferInstance
    exact ⟨inferInstance, inferInstance⟩
  exact finiteProjective_of_moduleRetract (X := X) hFree
    (hΓretract.trans (Retract.ofIso (moduleGlobalSectionsFreeIsoPi (X := X) (I := I))))

/-- Helper for Lemma 20.52.1: if the adjunction unit is invertible on a retract ambient object,
then it is already invertible on the retract itself. -/
private theorem unit_app_isIso_of_retract
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M P : C} (r : Retract M P) [IsIso (adj.unit.app P)] :
    IsIso (adj.unit.app M) := by
  let invη : G.obj (F.obj M) ⟶ M :=
    G.map (F.map r.i.hom) ≫ inv (adj.unit.app P) ≫ r.r.hom
  refine ⟨⟨invη, ?_, ?_⟩⟩
  · -- Proof comment: use naturality for the section `r.i : M ⟶ P` and then cancel the ambient unit.
    calc
      adj.unit.app M ≫ invη
          = r.i.hom ≫ adj.unit.app P ≫ inv (adj.unit.app P) ≫ r.r.hom := by
              dsimp [invη]
              rw [← Category.assoc, ← Category.assoc, adj.unit.naturality r.i.hom]
      _ = r.i.hom ≫ r.r.hom := by simp
      _ = 𝟙 M := r.retract
  · -- Proof comment: use naturality for the retraction `r.r : P ⟶ M` and the split identity on `P`.
    calc
      invη ≫ adj.unit.app M
          = G.map (F.map r.i.hom) ≫ inv (adj.unit.app P) ≫
              (r.r.hom ≫ adj.unit.app M) := by
                dsimp [invη]
                simp [Category.assoc]
      _ = G.map (F.map r.i.hom) ≫ inv (adj.unit.app P) ≫
            (adj.unit.app P ≫ G.map (F.map r.r.hom)) := by
              rw [adj.unit.naturality r.r.hom]
      _ = G.map (F.map r.i.hom) ≫ G.map (F.map r.r.hom) := by
            simp [Category.assoc]
      _ = G.map (F.map (r.i.hom ≫ r.r.hom)) := by
            simp [Functor.map_comp, Category.assoc]
      _ = G.map (F.map (𝟙 M)) := by rw [r.retract]
      _ = 𝟙 (G.obj (F.obj M)) := by simp

/-- Helper for Lemma 20.52.1: if the adjunction counit is invertible on a retract ambient object,
then it is already invertible on the retract itself. -/
private theorem counit_app_isIso_of_retract
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M P : D} (r : Retract M P) [IsIso (adj.counit.app P)] :
    IsIso (adj.counit.app M) := by
  let invε : M ⟶ F.obj (G.obj M) :=
    r.i.hom ≫ inv (adj.counit.app P) ≫ F.map (G.map r.r.hom)
  refine ⟨⟨invε, ?_, ?_⟩⟩
  · -- Proof comment: use counit naturality for `r.i : M ⟶ P` and then cancel the ambient counit.
    calc
      invε ≫ adj.counit.app M
          = r.i.hom ≫ inv (adj.counit.app P) ≫
              (F.map (G.map r.r.hom) ≫ adj.counit.app M) := by
                dsimp [invε]
                simp [Category.assoc]
      _ = r.i.hom ≫ inv (adj.counit.app P) ≫
            (adj.counit.app P ≫ r.r.hom) := by
              rw [adj.counit.naturality r.r.hom]
      _ = r.i.hom ≫ r.r.hom := by simp [Category.assoc]
      _ = 𝟙 M := r.retract
  · -- Proof comment: use counit naturality for `r.r : P ⟶ M` and the split identity on `F G M`.
    calc
      adj.counit.app M ≫ invε
          = (adj.counit.app M ≫ r.i.hom) ≫ inv (adj.counit.app P) ≫
              F.map (G.map r.r.hom) := by
                dsimp [invε]
                simp [Category.assoc]
      _ = F.map (G.map r.i.hom) ≫ adj.counit.app P ≫ inv (adj.counit.app P) ≫
            F.map (G.map r.r.hom) := by
              rw [adj.counit.naturality r.i.hom]
      _ = F.map (G.map r.i.hom) ≫ F.map (G.map r.r.hom) := by
            simp [Category.assoc]
      _ = F.map (G.map (r.i.hom ≫ r.r.hom)) := by
            simp [Functor.map_comp, Category.assoc]
      _ = F.map (G.map (𝟙 M)) := by rw [r.retract]
      _ = 𝟙 (F.obj (G.obj M)) := by simp

/-- Lemma 20.52.1: global sections induce an equivalence from finite-free-retract
`𝒪_X`-modules on `X` to finite projective modules over `Γ(X, 𝒪_X)`. -/
@[stacks 0FPF]
theorem finiteFreeRetractModules_equiv_finiteProjectiveModules :
    Functor.IsEquivalence
      (ObjectProperty.lift FiniteProjectivesΓX
        ((SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).ι ⋙ ΓMod)
        (moduleGlobalSections_mem_finiteProjectiveModuleProperty X)) := by
  let F :=
    ObjectProperty.lift FiniteProjectivesΓX
      ((SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).ι ⋙ ΓMod)
      (moduleGlobalSections_mem_finiteProjectiveModuleProperty X)
  let G :=
    ObjectProperty.lift (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf)
      (AlgebraicGeometry.globalSectionsModuleFunctor (RingHom.id ΓX))
      (associatedModuleSheaf_mem_finiteFreeRetractModuleProperty X)
  let adj := associatedModuleSheafΓAdjunction (X := X)
  have hUnitApp :
      ∀ P : FiniteProjectiveModuleCat ΓX, IsIso (adj.unit.app P.obj) := by
    intro P
    -- Proof comment: finite projective modules are retracts of finite function free modules, so
    -- the unit is invertible by transport from the finite free generator case.
    obtain ⟨n, π, ι, _, _, hιπ⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective ΓX P.obj
    let πCat : ModuleCat.of ΓX (Fin n → ΓX) ⟶ P.obj := ModuleCat.ofHom π
    let ιCat : P.obj ⟶ ModuleCat.of ΓX (Fin n → ΓX) := ModuleCat.ofHom ι
    let r : Retract P.obj (ModuleCat.of ΓX (Fin n → ΓX)) := ⟨ιCat, πCat, by
      ext x
      simpa [πCat, ιCat, LinearMap.comp_apply] using
        congrArg (fun f : P.obj →ₗ[ΓX] P.obj ↦ f x) hιπ⟩
    letI : IsIso (adj.unit.app (ModuleCat.of ΓX (Fin n → ΓX))) :=
      associatedModuleSheafΓ_unit_app_functionFree_isIso (X := X) n
    exact unit_app_isIso_of_retract (adj := adj) r
  have hCounitApp :
      ∀ ℱ : (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).FullSubcategory,
        IsIso (adj.counit.app ℱ.obj) := by
    intro ℱ
    -- Proof comment: finite-free-retract sheaves are retracts of finite free sheaves, so the
    -- counit is invertible by transport from the finite free generator case.
    obtain ⟨I, hI, ⟨r⟩⟩ :=
      (SheafOfModules.finiteFreeRetractModuleProperty_iff (𝒪 := X.ringCatSheaf) ℱ.obj).1 ℱ.2
    let _ : Finite I := hI
    letI :
        IsIso ((associatedModuleSheafΓAdjunction (X := X)).counit.app
          (SheafOfModules.free.{u} (R := X.ringCatSheaf) I : X.Modules)) :=
      associatedModuleSheafΓ_counit_app_free_isIso_of_finite (X := X)
    exact counit_app_isIso_of_retract (adj := adj) r
  let unitLift : 𝟭 (FiniteProjectiveModuleCat ΓX) ⟶ G ⋙ F where
    app P := adj.unit.app P.obj
    naturality f := by
      simpa [F, G] using adj.unit.naturality f
  let counitLift :
      F ⋙ G ⟶ 𝟭 ((SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).FullSubcategory)
      where
    app ℱ := adj.counit.app ℱ.obj
    naturality f := by
      simpa [F, G] using adj.counit.naturality f
  haveI : ∀ P : FiniteProjectiveModuleCat ΓX, IsIso (unitLift.app P) := hUnitApp
  haveI :
      ∀ ℱ : (SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).FullSubcategory,
        IsIso (counitLift.app ℱ) := hCounitApp
  letI : IsIso unitLift := NatIso.isIso_of_isIso_app unitLift
  letI : IsIso counitLift := NatIso.isIso_of_isIso_app counitLift
  -- Proof comment: the restricted associated-module-sheaf functor and global-sections functor
  -- are quasi-inverse once the objectwise unit and counit are known to be isomorphisms.
  exact Functor.IsEquivalence.mk' G (asIso counitLift).symm (asIso unitLift).symm

instance instFiniteFreeRetractGlobalSectionsFunctorIsEquivalence :
    Functor.IsEquivalence
      (ObjectProperty.lift FiniteProjectivesΓX
        ((SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf).ι ⋙ ΓMod)
        (moduleGlobalSections_mem_finiteProjectiveModuleProperty X)) :=
  finiteFreeRetractModules_equiv_finiteProjectiveModules X

end

end AlgebraicGeometry.RingedSpace
