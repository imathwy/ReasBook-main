import Mathlib
import stacks_project.Chap18.«18_19_2_1»
import stacks_project.Chap18.Lemma_18_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u w

section

variable {C : Type u} [Category.{u} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable {I : Type w} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 18.30.1:
- primary domain: sheaves of modules on a ringed site, the standard summands
  `j_{U!}\mathcal O_U`, and the Čech sequence attached to a covering family;
- sampled owner declarations:
  `localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_homEquiv`,
  `SheafOfModules.evaluation`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the chapter owner
  `localizedStructureModuleExtensionByZero 𝒪 U = j_{U!}\mathcal O_U`, with the source-facing
  `Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)` bridge already owned by
  `localizedStructureModuleExtensionByZero_homEquiv`;
- primitive-vs-derived split:
  the primitive data are only the ringed site `(C, J, 𝒪)`, the covering family `Uᵢ ⟶ U`, and the
  canonical lower-shriek summands `localizedStructureModuleExtensionByZero 𝒪 V`;
  the Čech maps, short complex, and sectionwise restriction/compatibility maps are derived API.

Source/core/bridge triage:
- `source-facing`: the Čech sequence for the covering family and the induced sectionwise sequence;
- `core/canonical`: `localizedStructureModuleExtensionByZero 𝒪 V` together with
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V`;
- `bridge/view`: the explicit Čech maps `ringedSiteCoverCechδ₀`, `ringedSiteCoverCechδ₁`, the
  derived short complex, and the sectionwise functions below.

This file should therefore reuse the chapter owner
`localizedStructureModuleExtensionByZero 𝒪 V` and its canonical Hom/evaluation bridge directly,
instead of exporting types built from private localized extension-by-zero or private
underlying-sheaf abbreviations. -/

section CechModule

/-- Restriction of a section over `U` to a family of sections over a covering family
`Uᵢ ⟶ U`. -/
def ringedSiteCoverSectionRestriction
    (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (ℱ : Mod) :
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op U) →
      ∀ i : I, ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op (Uᵢ i)) :=
  fun s i ↦ ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map (π i).op s

/-- The Čech compatibility map sending a family of sections on the cover to the pairwise
differences of their restrictions to the fiber products `Uᵢ ×[U] Uⱼ`. -/
def ringedSiteCoverSectionCompatibility
    (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U) (ℱ : Mod) :
    (∀ i : I, ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op (Uᵢ i))) →
      ∀ i j : I,
        ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.obj (op (pullback (π i) (π j))) :=
  fun s i j ↦
    ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map
        (pullback.fst (π i) (π j)).op (s i) -
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map
        (pullback.snd (π i) (π j)).op (s j)

section CechSequence

variable {I : Type u} {U : C} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ U)

/-- The canonical augmentation component
`j_{V!}\mathcal O_V \to j_{U!}\mathcal O_U`
attached to a morphism `f : V ⟶ U`. -/
noncomputable def ringedSiteCoverCechArrow
    {V U : C} (f : V ⟶ U) :
    localizedStructureModuleExtensionByZero 𝒪 V ⟶
      localizedStructureModuleExtensionByZero 𝒪 U :=
  (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V
      (localizedStructureModuleExtensionByZero 𝒪 U)).symm
    ((localizedStructureModuleExtensionByZero 𝒪 U).val.map f.op
      ((localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U
          (localizedStructureModuleExtensionByZero 𝒪 U)) (𝟙 _)))

/-- The first canonical Čech map
`\bigoplus_{i,j} j_{U_i \times_U U_j!}\mathcal O_{U_i \times_U U_j} \to
\bigoplus_i j_{U_i!}\mathcal O_{U_i}` attached to a covering family `Uᵢ ⟶ U`. -/
private noncomputable def ringedSiteCoverCechδ₀Component
    (p : I × I) :
    localizedStructureModuleExtensionByZero 𝒪 (pullback (π p.1) (π p.2)) ⟶
      (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) :=
  ringedSiteCoverCechArrow J 𝒪 (pullback.fst (π p.1) (π p.2)) ≫
      Sigma.ι (fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) p.1 -
    ringedSiteCoverCechArrow J 𝒪 (pullback.snd (π p.1) (π p.2)) ≫
      Sigma.ι (fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) p.2

noncomputable def ringedSiteCoverCechδ₀ :
    (∐ fun p : I × I ↦ localizedStructureModuleExtensionByZero 𝒪 (pullback (π p.1) (π p.2))) ⟶
        (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) :=
  Sigma.desc (ringedSiteCoverCechδ₀Component J 𝒪 Uᵢ π)

/-- The augmentation
`\bigoplus_i j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U`
attached to a covering family `Uᵢ ⟶ U`. -/
noncomputable def ringedSiteCoverCechδ₁ :
    (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) ⟶
      localizedStructureModuleExtensionByZero 𝒪 U :=
  Sigma.desc fun i ↦ ringedSiteCoverCechArrow J 𝒪 (π i)

theorem ringedSiteCoverCechCompZero :
    ringedSiteCoverCechδ₀ J 𝒪 Uᵢ π ≫ ringedSiteCoverCechδ₁ J 𝒪 Uᵢ π = 0 := by
  sorry

/-- The canonical Čech short complex attached to a covering family `Uᵢ ⟶ U`. -/
noncomputable def ringedSiteCoverCechShortComplex : ShortComplex Mod :=
  ShortComplex.mk
    (ringedSiteCoverCechδ₀ J 𝒪 Uᵢ π)
    (ringedSiteCoverCechδ₁ J 𝒪 Uᵢ π)
    (ringedSiteCoverCechCompZero J 𝒪 Uᵢ π)

-- Proof sketch: apply the sheaf condition on the localized site `(C/U, J.over U)` to the
-- underlying presheaf of types of the restriction `ℱ|_U`, using the covering family
-- `Over.mk (π i)` of the terminal object of `C/U`. Via `18.19.2.1`, this identifies the induced
-- Hom sequence out of the Čech short complex with the usual sequence of sections. Lemma `12.5.8`
-- then upgrades the section exactness for all `\mathcal O`-modules to exactness and
-- epimorphicity of the canonical module sequence itself.
/-- Lemma 18.30.1: for a ringed site `(\mathcal C, \mathcal O)` and a covering family
`\{ U_i \to U \}` of an object `U`, the canonical Čech sequence
`\bigoplus_{i,j} j_{U_i \times_U U_j!}\mathcal O_{U_i \times_U U_j} \to
\bigoplus_i j_{U_i!}\mathcal O_{U_i} \to j_{U!}\mathcal O_U \to 0`
is exact in `\mathrm{Mod}(\mathcal O)`. -/
theorem ringedSite_cover_cech_exact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i))) :
    (ringedSiteCoverCechShortComplex J 𝒪 Uᵢ π).Exact ∧
      Epi (ringedSiteCoverCechδ₁ J 𝒪 Uᵢ π) := by
  sorry

end CechSequence

end CechModule

-- Proof sketch: the main theorem gives the source-facing exact sequence in `Mod(\mathcal O)`.
-- Applying `Hom_{\mathcal O}(-, \mathcal F)` and using `18.19.2.1` identifies the resulting
-- sequence with the usual restriction and compatibility maps on sections.
/-- Companion bridge: for every `\mathcal O`-module `\mathcal F`, the induced sequence of
sections
`0 \to \mathcal F(U) \to \prod_i \mathcal F(U_i) \to \prod_{i,j} \mathcal F(U_i \times_U U_j)`
is injective and exact. -/
theorem ringedSite_cover_section_cech_exact
    (hcover : (J.over U).CoversTop (fun i : I ↦ Over.mk (π i)))
    (ℱ : Mod) :
    Function.Injective (ringedSiteCoverSectionRestriction J 𝒪 Uᵢ π ℱ) ∧
      Function.Exact
        (ringedSiteCoverSectionRestriction J 𝒪 Uᵢ π ℱ)
        (ringedSiteCoverSectionCompatibility J 𝒪 Uᵢ π ℱ) := by
  sorry

end
