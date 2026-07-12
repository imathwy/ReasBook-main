import Mathlib
import StacksProject_2024.Chap18.Definition_18_10_1
import StacksProject_2024.Chap18.«18_19_2_1»
import StacksProject_2024.Chap12.Lemma_12_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.Presheaf
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable {I : Type w} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

/- Domain-style sampling for Lemma 18.30.1:
- primary domain: sheaves of modules on a ringed site, the standard summands
  `j_{U!}\mathcal O_U`, and the Čech sequence attached to a covering family;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_homEquiv`,
  `localizedStructureModuleExtensionByZeroMap`,
  `SheafOfModules.evaluation`,
  `quasiCompactObject_module_sections_preserves_direct_sums`;
- best owner abstraction: the chapter owner
  `ringedSiteModuleCategory J 𝒪` for sheaves of modules on the ringed site, together with
  `localizedStructureModuleExtensionByZero 𝒪 U = j_{U!}\mathcal O_U`, with the source-facing
  `Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)` bridge already owned by
  `localizedStructureModuleExtensionByZero_homEquiv`;
- primitive-vs-derived split:
  the primitive data are only the ringed site `(C, J, 𝒪)`, the covering family `Uᵢ ⟶ U`, and the
  canonical lower-shriek summands `localizedStructureModuleExtensionByZero 𝒪 V`;
  the Čech maps and the sectionwise restriction/compatibility maps are derived API built from the
  sections owner `SheafOfModules.evaluation (ringSheaf J 𝒪)` on
  `ringedSiteModuleCategory J 𝒪`.

Source/core/bridge triage:
- `source-facing`: the Čech sequence for the covering family and the induced sectionwise sequence;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `localizedStructureModuleExtensionByZero 𝒪 V` together with
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V` and the induced comparison morphisms
  `localizedStructureModuleExtensionByZeroMap J 𝒪`;
- `bridge/view`: the explicit Čech maps `coverCechδ₀`, `coverCechδ₁`, and the sectionwise
  functions below.

This file should therefore reuse the chapter owner `ringedSiteModuleCategory J 𝒪` for ambient
modules, together with the canonical object `localizedStructureModuleExtensionByZero 𝒪 V` and its
Hom/evaluation bridge, instead of exporting types built from private localized extension-by-zero
or private underlying-sheaf abbreviations. -/

section CechModule

private def sectionMap
    {V W : C} (f : V ⟶ W) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).obj ℱ →
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).obj ℱ :=
  ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op

/-- Helper for Lemma 18.30.1: successive section restrictions compose as restriction along the
composite map. -/
private theorem sectionMap_comp
    {V W X : C} (f : V ⟶ W) (g : W ⟶ X) (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op X)).obj ℱ) :
    sectionMap J 𝒪 f ℱ (sectionMap J 𝒪 g ℱ s) =
      sectionMap J 𝒪 (f ≫ g) ℱ s := by
  -- Restriction is just the presheaf action, so composition is functoriality of `map`.
  let F := ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1
  change ConcreteCategory.hom (F.map f.op) (ConcreteCategory.hom (F.map g.op) s) =
    ConcreteCategory.hom (F.map ((f ≫ g).op)) s
  rw [op_comp, Functor.map_comp]
  rfl

/-- Helper for Lemma 18.30.1: restriction of sections commutes with applying a morphism of
`\mathcal O`-modules. -/
private theorem sectionMap_naturality
    {V W : C} {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪}
    (f : V ⟶ W) (α : ℱ ⟶ 𝒢)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).obj ℱ) :
    ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α) (sectionMap J 𝒪 f ℱ s) =
      sectionMap J 𝒪 f 𝒢 (((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α) s) := by
  -- Naturality of `α` on the presheaf underlying `toSheaf` gives the commutative restriction
  -- square on sections.
  change ConcreteCategory.hom (α.val.app (op V))
      (ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op) s) =
    ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj 𝒢).1.map f.op)
      (ConcreteCategory.hom (α.val.app (op W)) s)
  simpa using ConcreteCategory.congr_hom (α.val.naturality f.op) s

/-- Restriction of a section over `U` to a family of sections over a covering family
`Uᵢ ⟶ U`. -/
def coverSectionRestriction
    (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ →
      ∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ :=
  fun s i ↦ sectionMap J 𝒪 (π i) ℱ s

/-- The Čech compatibility map sending a family of sections on the cover to the pairwise
differences of their restrictions to the fiber products `Uᵢ ×[U] Uⱼ`. -/
def coverSectionCompatibility
    (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ) →
      ∀ i j : I,
        (SheafOfModules.evaluation (ringSheaf J 𝒪)
          (op (Limits.pullback (π i) (π j)))).obj ℱ :=
  fun s i j ↦
    sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i) -
      sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j)

/-- Helper for Lemma 18.30.1: the family of sections on the cover, regarded as a family of
elements of the underlying `Type`-valued sheaf on the slice site over `U`. -/
private def over_cover_family
    (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : ∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ) :
    FamilyOfElementsOnObjects
      (((sheafForget (J.over U)).obj
        ((SheafOfModules.toSheaf ((ringSheaf J 𝒪).over U)).obj (SheafOfModules.over ℱ U))).1)
      (fun i ↦ Over.mk (π i)) :=
  fun i ↦ show
    (((sheafForget (J.over U)).obj
      ((SheafOfModules.toSheaf ((ringSheaf J 𝒪).over U)).obj
        (SheafOfModules.over ℱ U))).1.obj (op (Over.mk (π i)))) from
    s i

/-- Helper for Lemma 18.30.1: sections of the restriction of `ℱ` to the slice site over `U`
are equivalent to ordinary sections of `ℱ` on `U`. -/
private noncomputable def overSectionsEquivEvaluation
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.over ℱ U).sections ≃
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (SheafOfModules.over ℱ U).val.sectionsMk
      (fun X ↦ (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun (X Y : (Over U)ᵒᵖ) (f : X ⟶ Y) ↦ by
        -- Every slice arrow to the terminal object agrees with the canonical one.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A section over the slice is determined by its values on the canonical maps to `U`.
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Evaluating the reconstructed section at the terminal slice object recovers `m`.
    change
      (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (SheafOfModules.over ℱ U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.30.1: morphisms from `j_{U!}\mathcal O_U` to `ℱ` are equivalent to
sections of `ℱ` on the slice site over `U`. -/
private noncomputable def localizedStructureModuleExtensionByZero_homOverSectionsEquiv
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    (j![𝒪, U] ⟶ ℱ) ≃ (SheafOfModules.over ℱ U).sections :=
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (((ringSheaf J 𝒪)).over U))).homEquiv
      (SheafOfModules.unit ((ringSheaf J 𝒪).over U)) ℱ).trans
    (SheafOfModules.over ℱ U).unitHomEquiv)

/-- Helper for Lemma 18.30.1: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    {V : C} {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪}
    (β : j![𝒪, V] ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ β) := by
  -- The imported owner equivalence is defined by composing target-functorial equivalences, so
  -- target naturality is definitional here.
  rfl

/-- Helper for Lemma 18.30.1: `localizedStructureModuleExtensionByZero_homEquiv` sends
precomposition by `localizedStructureModuleExtensionByZeroMap` to restriction of sections. -/
private theorem localizedStructureModuleExtensionByZeroMap_hom_equiv
    {V W : C} (f : V ⟶ W) (ℱ : ringedSiteModuleCategory J 𝒪)
    (α : j![𝒪, W] ⟶ ℱ) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ
        (localizedStructureModuleExtensionByZeroMap J 𝒪 f ≫ α) =
      sectionMap J 𝒪 f ℱ
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α) := by
  -- The universal map `localizedStructureModuleExtensionByZeroMap` is defined by restricting the
  -- identity section of `j_{W!}\mathcal O_W`, and target naturality then transports that section
  -- through `α`.
  have hα : localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W (j![𝒪, W]) (𝟙 _)) := by
    simpa using
      localizedStructureModuleExtensionByZero_homEquiv_naturality_right (J := J) (𝒪 := 𝒪)
        (β := 𝟙 (j![𝒪, W])) (α := α)
  -- Route correction: instead of expanding the slice-site adjunction by hand, use the imported
  -- target naturality and the defining universal section of `localizedStructureModuleExtensionByZeroMap`.
  rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right (J := J) (𝒪 := 𝒪)
    (β := localizedStructureModuleExtensionByZeroMap J 𝒪 f) (α := α)]
  rw [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroMap]
  rw [Equiv.apply_symm_apply]
  rw [hα]
  exact sectionMap_naturality (J := J) (𝒪 := 𝒪) f α _

/-- Helper for Lemma 18.30.1: the owner equivalence is additive on morphisms, so subtraction of
module maps becomes subtraction of sections. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_sub
    {V : C} (ℱ : ringedSiteModuleCategory J 𝒪)
    (α β : j![𝒪, V] ⟶ ℱ) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ (α - β) =
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ α -
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ β := by
  -- The imported owner equivalence is defined by additive maps, so this reduction is definitional.
  rfl

section CechSequence

variable (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasCoproducts.{w} (ringedSiteModuleCategory J 𝒪)]

/-- The first canonical Čech map
`\bigoplus_{i,j} j_{U_i \times_U U_j!}\mathcal O_{U_i \times_U U_j} \to
\bigoplus_i j_{U_i!}\mathcal O_{U_i}` attached to a covering family `Uᵢ ⟶ U`. -/
private noncomputable def coverCechδ₀Component (p : I × I) :
    j![𝒪, (Limits.pullback (π p.1) (π p.2))] ⟶ (∐ fun i : I ↦ j![𝒪, (Uᵢ i)]) :=
  localizedStructureModuleExtensionByZeroMap J 𝒪 (Limits.pullback.fst (π p.1) (π p.2)) ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (Uᵢ i)]) p.1 -
      localizedStructureModuleExtensionByZeroMap J 𝒪 (Limits.pullback.snd (π p.1) (π p.2)) ≫
        Sigma.ι (fun i : I ↦ j![𝒪, (Uᵢ i)]) p.2

noncomputable def coverCechδ₀ :
    (∐ fun p : I × I ↦ j![𝒪, (Limits.pullback (π p.1) (π p.2))]) ⟶
      (∐ fun i : I ↦ j![𝒪, (Uᵢ i)]) :=
  Sigma.desc (coverCechδ₀Component J 𝒪 Uᵢ π)

/-- The augmentation
`\bigoplus_i j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U`
attached to a covering family `Uᵢ ⟶ U`. -/
noncomputable def coverCechδ₁ :
    (∐ fun i : I ↦ j![𝒪, (Uᵢ i)]) ⟶ j![𝒪, U] :=
  Sigma.desc fun i ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 (π i)

/-- Helper for Lemma 18.30.1: each `(i,j)` summand of the Čech differential composite vanishes
after evaluating it against the universal section of `j_{U!}\mathcal O_U`. -/
private theorem coverCechCompZero_component (p : I × I) :
    Sigma.ι (fun q : I × I ↦ j![𝒪, (Limits.pullback (π q.1) (π q.2))]) p ≫
      coverCechδ₀ J 𝒪 Uᵢ π ≫ coverCechδ₁ J 𝒪 Uᵢ π = 0 := by
  -- Proof comment: precompose with the `p`-summand, read off the two coproduct legs, and then
  -- compare them through the owner equivalence `Hom(j_{U_i\times_U U_j!}\mathcal O,-) ≃ (-)(U_i×_U U_j)`.
  rw [coverCechδ₀, Limits.Sigma.ι_desc_assoc]
  rw [coverCechδ₀Component, Preadditive.sub_comp, sub_eq_zero, Category.assoc, Category.assoc,
    coverCechδ₁, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
  apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪
    (Limits.pullback (π p.1) (π p.2)) (j![𝒪, U])).injective
  -- The two composites are just the two ways of restricting the universal section of `j![𝒪, U]`
  -- to the pullback object, and the pullback square identifies them.
  rw [localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := Limits.pullback.fst (π p.1) (π p.2)) (ℱ := j![𝒪, U])]
  rw [localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := Limits.pullback.snd (π p.1) (π p.2)) (ℱ := j![𝒪, U])]
  have hπ₁ :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ p.1) (j![𝒪, U])
          (localizedStructureModuleExtensionByZeroMap J 𝒪 (π p.1)) =
        sectionMap J 𝒪 (π p.1) (j![𝒪, U])
          (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U (j![𝒪, U]) (𝟙 _)) := by
    simpa using localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := π p.1) (ℱ := j![𝒪, U]) (α := 𝟙 _)
  have hπ₂ :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ p.2) (j![𝒪, U])
          (localizedStructureModuleExtensionByZeroMap J 𝒪 (π p.2)) =
        sectionMap J 𝒪 (π p.2) (j![𝒪, U])
          (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U (j![𝒪, U]) (𝟙 _)) := by
    simpa using localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := π p.2) (ℱ := j![𝒪, U]) (α := 𝟙 _)
  rw [hπ₁, hπ₂]
  let s :
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj (j![𝒪, U]) :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U (j![𝒪, U]) (𝟙 _)
  change sectionMap J 𝒪 (Limits.pullback.fst (π p.1) (π p.2)) (j![𝒪, U])
      (sectionMap J 𝒪 (π p.1) (j![𝒪, U]) s) =
    sectionMap J 𝒪 (Limits.pullback.snd (π p.1) (π p.2)) (j![𝒪, U])
      (sectionMap J 𝒪 (π p.2) (j![𝒪, U]) s)
  calc
    sectionMap J 𝒪 (Limits.pullback.fst (π p.1) (π p.2)) (j![𝒪, U])
        (sectionMap J 𝒪 (π p.1) (j![𝒪, U]) s)
      = sectionMap J 𝒪
          (Limits.pullback.fst (π p.1) (π p.2) ≫ π p.1) (j![𝒪, U]) s := by
            exact sectionMap_comp (J := J) (𝒪 := 𝒪)
              (Limits.pullback.fst (π p.1) (π p.2)) (π p.1) (j![𝒪, U]) s
    _ = sectionMap J 𝒪
          (Limits.pullback.snd (π p.1) (π p.2) ≫ π p.2) (j![𝒪, U]) s := by
            rw [Limits.pullback.condition]
    _ = sectionMap J 𝒪 (Limits.pullback.snd (π p.1) (π p.2)) (j![𝒪, U])
          (sectionMap J 𝒪 (π p.2) (j![𝒪, U]) s) := by
            symm
            exact sectionMap_comp (J := J) (𝒪 := 𝒪)
              (Limits.pullback.snd (π p.1) (π p.2)) (π p.2) (j![𝒪, U]) s

theorem coverCechCompZero :
    coverCechδ₀ J 𝒪 Uᵢ π ≫ coverCechδ₁ J 𝒪 Uᵢ π = 0 := by
  -- Proof comment: coproduct morphisms are determined by their summand restrictions, so the
  -- componentwise vanishing lemma upgrades directly to the whole composite.
  apply Limits.Sigma.hom_ext
  intro p
  exact coverCechCompZero_component (J := J) (𝒪 := 𝒪) (U := U) Uᵢ π p

section

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoproducts.{w} (ringedSiteModuleCategory J 𝒪)]

/-- Helper for Lemma 18.30.1: evaluating the reconstructed slice-site section on the cover object
`Uᵢ i ⟶ U` recovers the ordinary restriction of the original section to `Uᵢ i`. -/
private theorem overSectionsEquivEvaluation_symm_apply_cover
    (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) (i : I) :
    ((overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) (U := U) ℱ).symm s).1
        (op (Over.mk (π i))) =
      coverSectionRestriction J 𝒪 Uᵢ π ℱ s i := by
  -- The canonical map from `Uᵢ i` to the terminal slice object is `π i`.
  have h :
      Over.mkIdTerminal.from (Over.mk (π i)) = Over.homMk (π i) := by
    exact Over.mkIdTerminal.hom_ext _ _
  -- Unfolding the explicit inverse identifies the evaluation map with ordinary restriction.
  change (ConcreteCategory.hom ((SheafOfModules.over ℱ U).val.map
      ((Over.mkIdTerminal.from (Over.mk (π i))).op))) s =
    (ConcreteCategory.hom (ℱ.val.presheaf.map (π i).op)) s
  rw [h]
  rfl

end

section

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasCoproducts.{w} (ringedSiteModuleCategory J 𝒪)]

/-- Helper for Lemma 18.30.1: compatibility of the named slice-site family is equivalent to the
usual pairwise equality of restrictions to the pullbacks `Uᵢ ×[U] Uⱼ`. -/
private theorem over_cover_family_isCompatible_iff
    (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : ∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ) :
    FamilyOfElementsOnObjects.IsCompatible (over_cover_family (J := J) (𝒪 := 𝒪) (U := U)
        Uᵢ π ℱ s) ↔
      ∀ i j,
        sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i) =
          sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j) := by
  -- Route correction: the old placeholder hid the coercion-heavy family reconstruction. The
  -- repaired route names the slice-site family first and proves compatibility on that fixed data.
  constructor
  · intro hs i j
    let P : Over U := Over.mk (Limits.pullback.fst (π i) (π j) ≫ π i)
    let fstMap : P ⟶ Over.mk (π i) :=
      Over.homMk (Limits.pullback.fst (π i) (π j)) rfl
    let sndMap : P ⟶ Over.mk (π j) :=
      Over.homMk (Limits.pullback.snd (π i) (π j))
        (Limits.pullback.condition (f := π i) (g := π j)).symm
    -- Evaluating compatibility on the pullback object gives the usual pairwise restriction
    -- identity on `Uᵢ i ×[U] Uᵢ j`.
    have hpull := hs P i j fstMap sndMap
    simpa [P, fstMap, sndMap, sectionMap] using hpull
  · intro hs Z i j f g
    let liftMap : Z.left ⟶ Limits.pullback (π i) (π j) :=
      Limits.pullback.lift f.left g.left <| by
        exact Eq.trans (Over.w f) (Over.w g).symm
    -- Any two arrows into the cover objects factor through the pullback, so the given pairwise
    -- equality propagates to arbitrary slice-site restrictions.
    change sectionMap J 𝒪 f.left ℱ (s i) = sectionMap J 𝒪 g.left ℱ (s j)
    calc
      sectionMap J 𝒪 f.left ℱ (s i)
          = sectionMap J 𝒪 (liftMap ≫ Limits.pullback.fst (π i) (π j)) ℱ (s i) := by
              dsimp [liftMap]
              rw [Limits.pullback.lift_fst]
      _ = sectionMap J 𝒪 liftMap ℱ
            (sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i)) := by
              symm
              exact sectionMap_comp (J := J) (𝒪 := 𝒪) liftMap
                (Limits.pullback.fst (π i) (π j)) ℱ (s i)
      _ = sectionMap J 𝒪 liftMap ℱ
            (sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j)) := by
              rw [hs i j]
      _ = sectionMap J 𝒪 (liftMap ≫ Limits.pullback.snd (π i) (π j)) ℱ (s j) := by
              exact sectionMap_comp (J := J) (𝒪 := 𝒪) liftMap
                (Limits.pullback.snd (π i) (π j)) ℱ (s j)
      _ = sectionMap J 𝒪 g.left ℱ (s j) := by
              dsimp [liftMap]
              rw [Limits.pullback.lift_snd]

/-- Helper for Lemma 18.30.1: the public difference map vanishes exactly when the two pullback
restrictions agree for every pair `(i,j)`. -/
private theorem cover_pairwise_equal_iff_coverSectionCompatibility_eq_zero
    (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : ∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ) :
    (∀ i j,
      sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i) =
        sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j)) ↔
      coverSectionCompatibility J 𝒪 Uᵢ π ℱ s = 0 := by
  constructor
  · intro h
    -- Proof comment: equality with the zero family is pointwise, and each point is a
    -- `sub_eq_zero` reformulation of the corresponding pullback equality.
    ext i j
    change
      sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i) -
          sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j) = 0
    exact sub_eq_zero.mpr (h i j)
  · intro hs i j
    -- Proof comment: evaluate the zero-family identity at `(i,j)` and cancel the difference.
    have hij := congrFun (congrFun hs i) j
    change
      sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i) -
          sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j) = 0 at hij
    exact sub_eq_zero.mp hij

/-- Helper for Lemma 18.30.1: a compatible family in the kernel of the Čech difference map glues
to a global section over `U`. -/
private theorem cover_sections_kernel_lift
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i)))
    (ℱ : ringedSiteModuleCategory J 𝒪)
    {s : ∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ}
    (hs : coverSectionCompatibility J 𝒪 Uᵢ π ℱ s = 0) :
    ∃ t, coverSectionRestriction J 𝒪 Uᵢ π ℱ t = s := by
  -- TODO: convert `hs` to compatibility of `over_cover_family`, glue on the slice-site sheaf via
  -- `existsUnique_section`, and then identify the glued section with an ordinary section using
  -- `overSectionsEquivEvaluation`.
  have hpair :
      ∀ i j,
        sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ (s i) =
          sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ (s j) := by
    exact
      (cover_pairwise_equal_iff_coverSectionCompatibility_eq_zero (J := J) (𝒪 := 𝒪)
        (U := U) Uᵢ π ℱ s).2 hs
  have hcompat :
      FamilyOfElementsOnObjects.IsCompatible
        (over_cover_family (J := J) (𝒪 := 𝒪) (U := U) Uᵢ π ℱ s) := by
    exact
      (over_cover_family_isCompatible_iff (J := J) (𝒪 := 𝒪) (U := U) Uᵢ π ℱ s).2 hpair
  let F0 := ((sheafForget (J.over U)).obj
    ((SheafOfModules.toSheaf ((ringSheaf J 𝒪).over U)).obj (SheafOfModules.over ℱ U)))
  let σ := hcompat.section_ hcover F0.2
  refine ⟨overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) (U := U) ℱ σ, ?_⟩
  funext i
  -- The glued slice-site section agrees with the original family on each cover object.
  rw [← overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
    (U := U) (Uᵢ := Uᵢ) (π := π)
    (ℱ := ℱ)
    (s := overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) (U := U) ℱ σ) i]
  change ConcreteCategory.hom ((SheafOfModules.over ℱ U).val.map
      ((Over.mkIdTerminal.from (Over.mk (π i))).op))
      (σ.1 (op (Over.mk (𝟙 U)))) = s i
  have hsec :
      ConcreteCategory.hom ((SheafOfModules.over ℱ U).val.map
          ((Over.mkIdTerminal.from (Over.mk (π i))).op))
          (σ.1 (op (Over.mk (𝟙 U)))) =
        σ.1 (op (Over.mk (π i))) := by
    simpa using
      PresheafOfModules.sections_property σ ((Over.mkIdTerminal.from (Over.mk (π i))).op)
  have happly : σ.1 (op (Over.mk (π i))) = s i := by
    simpa [σ, over_cover_family] using hcompat.section_apply hcover F0.2 i
  exact hsec.trans happly

/-- Helper for Lemma 18.30.1: the usual restriction and compatibility sequence on sections is
injective and exact for every `\mathcal O`-module. -/
private theorem cover_section_sequence_exact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i)))
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    Function.Injective (coverSectionRestriction J 𝒪 Uᵢ π ℱ) ∧
      Function.Exact
        (coverSectionRestriction J 𝒪 Uᵢ π ℱ)
        (coverSectionCompatibility J 𝒪 Uᵢ π ℱ) := by
  -- TODO: injectivity should come from `hcover.sections_ext` on the slice-site sheaf, while the
  -- exactness step is exactly `cover_sections_kernel_lift`.
  let F := ((sheafForget (J.over U)).obj
    ((SheafOfModules.toSheaf ((ringSheaf J 𝒪).over U)).obj (SheafOfModules.over ℱ U)))
  refine ⟨?_, ?_⟩
  · intro a b hab
    -- Restriction to the cover detects equality because sections on the slice site are
    -- determined by their values on a covering family.
    have hs :
        (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) (U := U) ℱ).symm a =
          (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) (U := U) ℱ).symm b := by
      apply hcover.sections_ext F
      intro i
      rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
        (U := U) (Uᵢ := Uᵢ) (π := π) (ℱ := ℱ) (s := a) i]
      rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
        (U := U) (Uᵢ := Uᵢ) (π := π) (ℱ := ℱ) (s := b) i]
      exact congrFun hab i
    simpa using congrArg
      (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) (U := U) ℱ) hs
  · intro y
    constructor
    · intro hy
      rcases cover_sections_kernel_lift (J := J) (𝒪 := 𝒪) (U := U) (Uᵢ := Uᵢ) (π := π)
        hcover ℱ hy with ⟨t, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, rfl⟩
      -- A restricted global section has equal pullback restrictions on every overlap.
      ext i j
      change
        sectionMap J 𝒪 (Limits.pullback.fst (π i) (π j)) ℱ
            (sectionMap J 𝒪 (π i) ℱ t) -
          sectionMap J 𝒪 (Limits.pullback.snd (π i) (π j)) ℱ
            (sectionMap J 𝒪 (π j) ℱ t) = 0
      rw [sectionMap_comp, sectionMap_comp, Limits.pullback.condition]
      simp

end

/-- Helper for Lemma 18.30.1: morphisms out of the single-indexed coproduct are exactly families
of sections on the cover objects. -/
private noncomputable def cover_single_coproduct_hom_equiv
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    ((∐ fun i : I ↦ j![𝒪, (Uᵢ i)]) ⟶ ℱ) ≃
      (∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Uᵢ i))).obj ℱ) where
  toFun α i :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ
      (Sigma.ι (fun i : I ↦ j![𝒪, (Uᵢ i)]) i ≫ α)
  invFun s :=
    Sigma.desc
      (fun i : I ↦
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ).symm (s i))
  left_inv α := by
    -- A coproduct morphism is determined by its restrictions to the summands.
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ)
      (Sigma.ι (fun i : I ↦ j![𝒪, (Uᵢ i)]) i ≫ α)
  right_inv s := by
    -- Evaluating the reconstructed coproduct morphism on a summand recovers the original section.
    funext i
    change localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ
        (Sigma.ι (fun k : I ↦ j![𝒪, (Uᵢ k)]) i ≫
          Sigma.desc
            (fun k : I ↦
              (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ k) ℱ).symm
                (s k))) = s i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ)
      (s i)

/-- Helper for Lemma 18.30.1: morphisms out of the pair-indexed coproduct are exactly families
of sections on the overlaps `Uᵢ ×[U] Uⱼ`. -/
private noncomputable def cover_pair_coproduct_hom_equiv
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    ((∐ fun p : I × I ↦ j![𝒪, (Limits.pullback (π p.1) (π p.2))]) ⟶ ℱ) ≃
      (∀ i j : I,
      (SheafOfModules.evaluation (ringSheaf J 𝒪)
          (op (Limits.pullback (π i) (π j)))).obj ℱ) where
  toFun α i j :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪
      (Limits.pullback (π i) (π j)) ℱ
      (Sigma.ι (fun p : I × I ↦ j![𝒪, (Limits.pullback (π p.1) (π p.2))]) (i, j) ≫ α)
  invFun s :=
    Sigma.desc
      (fun p : I × I ↦
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪
          (Limits.pullback (π p.1) (π p.2)) ℱ).symm (s p.1 p.2))
  left_inv α := by
    -- A pair-indexed coproduct morphism is likewise determined by its summand restrictions.
    apply Limits.Sigma.hom_ext
    intro p
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪
        (Limits.pullback (π p.1) (π p.2)) ℱ)
      (Sigma.ι (fun q : I × I ↦ j![𝒪, (Limits.pullback (π q.1) (π q.2))]) p ≫ α)
  right_inv s := by
    -- Evaluating on each pair summand recovers the prescribed overlap section.
    funext i j
    change localizedStructureModuleExtensionByZero_homEquiv J 𝒪
        (Limits.pullback (π i) (π j)) ℱ
        (Sigma.ι (fun p : I × I ↦ j![𝒪, (Limits.pullback (π p.1) (π p.2))]) (i, j) ≫
          Sigma.desc
            (fun p : I × I ↦
              (localizedStructureModuleExtensionByZero_homEquiv J 𝒪
                (Limits.pullback (π p.1) (π p.2)) ℱ).symm (s p.1 p.2))) = s i j
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪
        (Limits.pullback (π i) (π j)) ℱ)
      (s i j)

/-- Helper for Lemma 18.30.1: the single-indexed coproduct-Hom equivalence sends the zero
morphism to the zero family of sections. -/
private theorem cover_single_coproduct_hom_equiv_zero
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ 0 = 0 := by
  -- Each component is the image of the zero morphism under the owner equivalence.
  funext i
  rfl

/-- Helper for Lemma 18.30.1: the pair-indexed coproduct-Hom equivalence sends the zero morphism
to the zero family of overlap sections. -/
private theorem cover_pair_coproduct_hom_equiv_zero
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    cover_pair_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ π ℱ 0 = 0 := by
  -- Each overlap component is the image of the zero morphism under the owner equivalence.
  funext i j
  rfl

/-- Helper for Lemma 18.30.1: precomposition by the Čech augmentation corresponds to the usual
restriction map on sections. -/
private theorem cover_single_coproduct_hom_equiv_comp_coverCechδ₁
    (ℱ : ringedSiteModuleCategory J 𝒪) (α : j![𝒪, U] ⟶ ℱ) :
    cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ
        (coverCechδ₁ J 𝒪 Uᵢ π ≫ α) =
      coverSectionRestriction J 𝒪 Uᵢ π ℱ
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α) := by
  -- Evaluate the coproduct morphism on each summand and rewrite via the owner comparison map.
  funext i
  change localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ
      ((Sigma.ι (fun k : I ↦ j![𝒪, (Uᵢ k)]) i ≫ coverCechδ₁ J 𝒪 Uᵢ π) ≫ α) = _
  rw [coverCechδ₁, Limits.Sigma.ι_desc]
  simpa [coverSectionRestriction] using
    localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := π i) (ℱ := ℱ) (α := α)

/-- Helper for Lemma 18.30.1: precomposition by the first Čech differential corresponds to the
usual compatibility difference on sections. -/
private theorem cover_pair_coproduct_hom_equiv_comp_coverCechδ₀
    (ℱ : ringedSiteModuleCategory J 𝒪)
    (β : (∐ fun i : I ↦ j![𝒪, (Uᵢ i)]) ⟶ ℱ) :
    cover_pair_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ π ℱ
        (coverCechδ₀ J 𝒪 Uᵢ π ≫ β) =
      coverSectionCompatibility J 𝒪 Uᵢ π ℱ
        (cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ β) := by
  -- Work pointwise on each overlap summand and rewrite the two terms via the owner comparison.
  funext i j
  change localizedStructureModuleExtensionByZero_homEquiv J 𝒪
      (Limits.pullback (π i) (π j)) ℱ
      ((Sigma.ι (fun p : I × I ↦ j![𝒪, (Limits.pullback (π p.1) (π p.2))]) (i, j) ≫
          coverCechδ₀ J 𝒪 Uᵢ π) ≫ β) = _
  rw [coverCechδ₀, Limits.Sigma.ι_desc, coverCechδ₀Component,
    Preadditive.sub_comp]
  rw [localizedStructureModuleExtensionByZero_homEquiv_sub (J := J) (𝒪 := 𝒪)
      (V := Limits.pullback (π i) (π j)) (ℱ := ℱ)]
  rw [Category.assoc, Category.assoc]
  rw [localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := Limits.pullback.fst (π i) (π j)) (ℱ := ℱ)
      (α := Sigma.ι (fun k : I ↦ j![𝒪, (Uᵢ k)]) i ≫ β)]
  rw [localizedStructureModuleExtensionByZeroMap_hom_equiv (J := J) (𝒪 := 𝒪)
      (f := Limits.pullback.snd (π i) (π j)) (ℱ := ℱ)
      (α := Sigma.ι (fun k : I ↦ j![𝒪, (Uᵢ k)]) j ≫ β)]
  rfl

/-- Helper for Lemma 18.30.1: for every target module sheaf, the Hom sequence out of the Čech
short complex is injective on the left and exact in the middle. -/
private theorem cover_hom_sequence_exact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i)))
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    let T := ((ShortComplex.mk
      (coverCechδ₀ J 𝒪 Uᵢ π)
      (coverCechδ₁ J 𝒪 Uᵢ π)
      (coverCechCompZero J 𝒪 Uᵢ π)).op.map (preadditiveYoneda.obj ℱ))
    T.Exact ∧ Mono T.f := by
  -- Route correction: instead of reopening the slice-site proof, identify the Yoneda image of
  -- the Čech complex with the already-proved restriction/compatibility sequence on sections.
  let S : ShortComplex (ringedSiteModuleCategory J 𝒪) :=
    ShortComplex.mk
      (coverCechδ₀ J 𝒪 Uᵢ π)
      (coverCechδ₁ J 𝒪 Uᵢ π)
      (coverCechCompZero J 𝒪 Uᵢ π)
  let T := S.op.map (preadditiveYoneda.obj ℱ)
  change T.Exact ∧ Mono T.f
  refine ⟨?_, ?_⟩
  · -- Exactness becomes the concrete lifting property in `AddCommGrpCat`.
    rw [ShortComplex.ab_exact_iff]
    intro β hβ
    change coverCechδ₀ J 𝒪 Uᵢ π ≫ β = 0 at hβ
    have hcompat :
        coverSectionCompatibility J 𝒪 Uᵢ π ℱ
            (cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ β) = 0 := by
      have hβ' := congrArg
        (cover_pair_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ π ℱ) hβ
      rw [cover_pair_coproduct_hom_equiv_comp_coverCechδ₀ (J := J) (𝒪 := 𝒪)
          (ℱ := ℱ) (β := β),
        cover_pair_coproduct_hom_equiv_zero (J := J) (𝒪 := 𝒪) (ℱ := ℱ)] at hβ'
      exact hβ'
    rcases
        (cover_section_sequence_exact (J := J) (𝒪 := 𝒪) (U := U) Uᵢ π hcover ℱ).2
          (cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ β) |>.1
          hcompat with
      ⟨t, ht⟩
    refine ⟨(localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ).symm t, ?_⟩
    change coverCechδ₁ J 𝒪 Uᵢ π ≫
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ).symm t = β
    apply (cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ).injective
    rw [cover_single_coproduct_hom_equiv_comp_coverCechδ₁ (J := J) (𝒪 := 𝒪)
        (ℱ := ℱ) (α := (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ).symm t)]
    simpa using ht
  · -- Injectivity on the Hom side is the injectivity of the restriction map on sections.
    refine (AddCommGrpCat.mono_iff_injective T.f).2 ?_
    intro α β hαβ
    change coverCechδ₁ J 𝒪 Uᵢ π ≫ α = coverCechδ₁ J 𝒪 Uᵢ π ≫ β at hαβ
    have hrestr := congrArg
      (cover_single_coproduct_hom_equiv (J := J) (𝒪 := 𝒪) Uᵢ ℱ) hαβ
    rw [cover_single_coproduct_hom_equiv_comp_coverCechδ₁ (J := J) (𝒪 := 𝒪)
        (ℱ := ℱ) (α := α),
      cover_single_coproduct_hom_equiv_comp_coverCechδ₁ (J := J) (𝒪 := 𝒪)
        (ℱ := ℱ) (α := β)] at hrestr
    have hsec :
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α =
          localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β :=
      (cover_section_sequence_exact (J := J) (𝒪 := 𝒪) (U := U) Uᵢ π hcover ℱ).1 hrestr
    exact (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ).injective hsec

-- Proof sketch: apply the sheaf condition on the localized site `(C/U, J.over U)` to the
-- underlying presheaf of types of the restriction `ℱ|_U`, using the covering family
-- `Over.mk (π i)` of the terminal object of `C/U`. Via `18.19.2.1`, this identifies the induced
-- Hom sequence out of the canonical Čech arrows with the usual sequence of sections. Lemma `12.5.8`
-- then upgrades the section exactness for all `\mathcal O`-modules to exactness and
-- epimorphicity of the canonical module sequence itself.
/-- Lemma 18.30.1: for a ringed site `(\mathcal C, \mathcal O)` and a covering family
`\{ U_i \to U \}` of an object `U`, the canonical Čech sequence
`\bigoplus_{i,j} j_{U_i \times_U U_j!}\mathcal O_{U_i \times_U U_j} \to
\bigoplus_i j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U \to 0`
is exact in `\mathrm{Mod}(\mathcal O)`. -/
@[stacks 0934]
theorem coverCechExact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i))) :
    (ShortComplex.mk
      (coverCechδ₀ J 𝒪 Uᵢ π)
      (coverCechδ₁ J 𝒪 Uᵢ π)
      (coverCechCompZero J 𝒪 Uᵢ π)).Exact ∧
      Epi (coverCechδ₁ J 𝒪 Uᵢ π) := by
  -- Apply the Hom-into criterion from Lemma 12.5.8 after rewriting the Yoneda image of the Čech
  -- complex to the section restriction/compatibility sequence.
  let S : ShortComplex (ringedSiteModuleCategory J 𝒪) :=
    ShortComplex.mk
      (coverCechδ₀ J 𝒪 Uᵢ π)
      (coverCechδ₁ J 𝒪 Uᵢ π)
      (coverCechCompZero J 𝒪 Uᵢ π)
  simpa [S] using
    (epi_exact_iff_hom_into_exact S).2
      (fun ℱ ↦ cover_hom_sequence_exact (J := J) (𝒪 := 𝒪) (U := U)
        (Uᵢ := Uᵢ) (π := π) hcover ℱ)

end CechSequence

end CechModule

-- Proof sketch: the main theorem gives the source-facing exact sequence in `Mod(\mathcal O)`.
-- Applying `Hom_{\mathcal O}(-, \mathcal F)` and using `18.19.2.1` identifies the resulting
-- sequence with the usual restriction and compatibility maps on sections.
/-- Companion bridge: for every `\mathcal O`-module `\mathcal F`, the induced sequence of
sections
`0 \to \mathcal F(U) \to \prod_i \mathcal F(U_i) \to \prod_{i,j} \mathcal F(U_i \times_U U_j)`
is injective and exact. -/
theorem coverSectionCechExact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i)))
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    Function.Injective (coverSectionRestriction J 𝒪 Uᵢ π ℱ) ∧
      Function.Exact
        (coverSectionRestriction J 𝒪 Uᵢ π ℱ)
        (coverSectionCompatibility J 𝒪 Uᵢ π ℱ) := by
  -- TODO: reuse `cover_section_sequence_exact` once the compatibility bridge is restated in a
  -- coercion-stable form that does not trigger typeclass search through large coproduct instances.
  exact cover_section_sequence_exact (J := J) (𝒪 := 𝒪) (U := U) Uᵢ π hcover ℱ

end

end SheafOfModules.RingedSite
