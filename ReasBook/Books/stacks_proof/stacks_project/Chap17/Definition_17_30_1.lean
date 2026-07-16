import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_132_2
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Definition_17_28_3
import stacks_proof.stacks_project.Chap17.Lemma_17_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open ModuleCat.exteriorPower
open TopCat.Sheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

local notation "ModO₁" => SheafOfModules (ringSheaf O₁)
local notation "ModO₂" => SheafOfModules (ringSheaf O₂)
local notation "𝒪₂" => (SheafOfModules.unit (ringSheaf O₂) : ModO₂)
local notation "RSp₂" => O₂.toRingedSpace
local notation "ModRSp₂" => RingedSpace.Modules RSp₂

/- Domain-style sampling for Definition 17.30.1:
- primary domain: relative de Rham complexes for a morphism of sheaves of rings on a fixed
  topological space;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `RingedSpace.Modules`,
  `Λ^[n]`,
  `AlgebraicGeometry.RingedSpace.exteriorPowerPresheaf`;
- best owner abstraction: the source-facing owner is the sheaf-level de Rham complex
  `TopCat.Sheaf.deRhamComplex φ`, attached directly to a morphism `φ : O₁ ⟶ O₂`;
- primitive data: the graded sheaves `\Omega^n_{O₂/O₁}` and the unique de Rham differential family
  on them;
- derived API: the source-facing notation `Ω^[n](φ)` for the graded form sheaves, the direct
  restriction-of-scalars object formula `deRhamComplex_obj`, the basic-form theorem
  `deRhamComplex_d_basicForm`, and the ringed-space specialization obtained by taking
  `φ = RingedSpace.Hom.inverseImageStructureSheafHomComm f`.

Source/core/bridge triage:
- `source-facing`: `deRhamComplex φ`;
- `core/canonical`: `Ω(φ)`, `relativeDifferential φ`, `RingedSpace.Modules`, and `Λ^[n]`;
- `bridge/view`: `deRhamComplex_obj`, `deRhamComplex_d_basicForm`, and the ringed-space
  specialization at the end of the file. -/

/-- The graded sheaf `\Omega^n_{O₂/O₁}` underlying the relative de Rham complex of a morphism
`φ : O₁ ⟶ O₂` of sheaves of rings. -/
def deRhamForm (φ : O₁ ⟶ O₂) (n : ℕ) :
    SheafOfModules (ringSheaf O₂) :=
  match n with
  | 0 => 𝒪₂
  | 1 => Ω(φ)
  | n + 2 => Λ^[n + 2] (Ω(φ) : ModRSp₂)

scoped[AlgebraicGeometry] notation3:max "Ω^[" n "](" φ ")" =>
  deRhamForm φ n

private abbrev deRhamTerm (φ : O₁ ⟶ O₂) (n : ℕ) :
    ModO₁ :=
  (SheafOfModules.restrictScalars (ringSheafMap φ)).obj Ω^[n](φ)

/-- The exact one-form `db` on an open set, relative to the morphism `φ : O₁ ⟶ O₂`. -/
private abbrev exactOneFormSection
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U → (Ω(φ)).val.obj U :=
  fun b ↦ ((relativeDifferential φ).app U).d b

/-- The canonical map from objectwise exterior-power sections to the sheafified higher de Rham
term. -/
private def higherExteriorPowerSection
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj U →
      (deRhamForm φ (n + 2)).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
    (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2))).app U

/-- The section of the exterior-power presheaf obtained by wedging a distinguished leading
one-form with a family of further one-forms. -/
private def wedgeOneFormsSection
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (ω₀ : (Ω(φ)).val.obj U) (ω : Fin (n + 1) → (Ω(φ)).val.obj U) :
    (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj U := by
  let R := O₂.presheaf.obj U
  exact exteriorPower.ιMulti R (n + 2) (fun i : Fin (n + 2) ↦ Fin.cases ω₀ ω i)

/-- The canonical basic `p`-form `b₀ \, db₁ ∧ \cdots ∧ dbₚ` on an open set of `X`. -/
def basicFormSection
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U → (Fin p → O₂.presheaf.obj U) → (deRhamTerm φ p).val.obj U :=
  match p with
  | 0 => fun b₀ _ ↦ by
      simpa [deRhamTerm, deRhamForm] using b₀
  | 1 => fun b₀ b ↦ by
      simpa [deRhamTerm, deRhamForm] using
        (b₀ • exactOneFormSection φ U (b 0))
  | n + 2 => fun b₀ b ↦ by
      simpa [deRhamTerm, deRhamForm] using
        higherExteriorPowerSection φ n U
          (wedgeOneFormsSection φ n U
            (b₀ • exactOneFormSection φ U (b 0))
            (fun j ↦ exactOneFormSection φ U (b j.succ)))

/-- The target form `db₀ ∧ db₁ ∧ \cdots ∧ dbₚ` on the right-hand side of the de Rham rule. -/
def differentialTargetSection
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U → (Fin p → O₂.presheaf.obj U) →
      (deRhamTerm φ (p + 1)).val.obj U :=
  match p with
  | 0 => fun b₀ _ ↦ by
      simpa [deRhamTerm, deRhamForm] using
        exactOneFormSection φ U b₀
  | n + 1 => fun b₀ b ↦ by
      simpa [deRhamTerm, deRhamForm] using
        higherExteriorPowerSection φ n U
          (wedgeOneFormsSection φ n U
            (exactOneFormSection φ U b₀)
            (fun j ↦ exactOneFormSection φ U (b j)))

/-- Helper for Definition 17.30.1: restricting an exact one-form section gives the exact one-form
of the restricted coefficient. -/
private theorem exactOneFormSection_naturality
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (b : O₂.presheaf.obj U) :
    ((Ω(φ)).val.map i).hom (exactOneFormSection φ U b) =
      exactOneFormSection φ V ((O₂.presheaf.map i).hom b) := by
  -- Proof comment: this is exactly the naturality of the universal relative differential.
  simpa [exactOneFormSection, relativeDifferential, FunctorToTypes.map_comp_apply] using
    congrArg ModuleCat.Hom.hom ((relativeDifferential φ).naturality i)

/-- Helper for Definition 17.30.1: restriction in the exterior-power presheaf sends the wedge
generator used in higher basic forms to the corresponding restricted wedge generator. -/
private theorem wedgeOneFormsSection_naturality
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (ω₀ : (Ω(φ)).val.obj U) (ω : Fin (n + 1) → (Ω(φ)).val.obj U) :
    ((exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map i).hom
        (wedgeOneFormsSection φ n U ω₀ ω) =
      wedgeOneFormsSection φ n V
        (((Ω(φ)).val.map i).hom ω₀)
        (fun j ↦ ((Ω(φ)).val.map i).hom (ω j)) := by
  -- Proof comment: unfold the restriction map on exterior powers to the universal `ιMulti` lift.
  let R := O₂.presheaf.obj U
  let S := O₂.presheaf.obj V
  let M := (Ω(φ)).val.obj U
  let N := (Ω(φ)).val.obj V
  letI : Algebra R S := (O₂.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (O₂.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^(n + 2) N) := Module.compHom _ (algebraMap R S)
  let f : M →ₗ[R] N := ((Ω(φ)).val.map i).hom
  let ιN : N [⋀^Fin (n + 2)]→ₗ[S] ↥(⋀[S]^(n + 2) N) := exteriorPower.ιMulti S (n + 2)
  let ιN' : N [⋀^Fin (n + 2)]→ₗ[R] ↥(⋀[S]^(n + 2) N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m j x y
            simpa using ιN.map_update_add m j x y
          map_update_smul' := by
            intro _ m j r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m j (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m j k hjk hne
        exact ιN.map_eq_zero_of_eq m hjk hne }
  let A : M [⋀^Fin (n + 2)]→ₗ[R] ↥(⋀[S]^(n + 2) N) := ιN'.compLinearMap f
  change (exteriorPower.alternatingMapLinearEquiv A)
      (exteriorPower.ιMulti R (n + 2) (fun j : Fin (n + 2) ↦ Fin.cases ω₀ ω j)) =
    exteriorPower.ιMulti S (n + 2)
      (fun j : Fin (n + 2) ↦ Fin.cases (((Ω(φ)).val.map i).hom ω₀) (fun k ↦ f (ω k)) j)
  calc
    (exteriorPower.alternatingMapLinearEquiv A)
        (exteriorPower.ιMulti R (n + 2) (fun j : Fin (n + 2) ↦ Fin.cases ω₀ ω j))
      = (exteriorPower.alternatingMapLinearEquiv.symm
            (exteriorPower.alternatingMapLinearEquiv A))
          (fun j : Fin (n + 2) ↦ Fin.cases ω₀ ω j) := by
            symm
            simpa using
              (exteriorPower.alternatingMapLinearEquiv_symm_apply
                (F := exteriorPower.alternatingMapLinearEquiv A)
                (fun j : Fin (n + 2) ↦ Fin.cases ω₀ ω j))
    _ = A (fun j : Fin (n + 2) ↦ Fin.cases ω₀ ω j) := by
          simpa using
            congrArg
              (fun F : M [⋀^Fin (n + 2)]→ₗ[R] ↥(⋀[S]^(n + 2) N) ↦
                F (fun j : Fin (n + 2) ↦ Fin.cases ω₀ ω j))
              (exteriorPower.alternatingMapLinearEquiv.symm_apply_apply A)
    _ = exteriorPower.ιMulti S (n + 2)
          (fun j : Fin (n + 2) ↦ Fin.cases (((Ω(φ)).val.map i).hom ω₀) (fun k ↦ f (ω k)) j) := rfl

/-- Helper for Definition 17.30.1: the sheafification map on higher forms carries a raw
exterior-power section to the image of that section after restriction. -/
private theorem higherExteriorPowerSection_naturality
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (z : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj U) :
    ((deRhamForm φ (n + 2)).val.map i).hom (higherExteriorPowerSection φ n U z) =
      higherExteriorPowerSection φ n V
        (((exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map i).hom z) := by
  -- Proof comment: this is just naturality of the sheafification unit for exterior-power
  -- presheaves, rewritten in the `deRhamForm` spelling.
  simpa [deRhamForm, higherExteriorPowerSection, FunctorToTypes.map_comp_apply] using
    congrArg ModuleCat.Hom.hom
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
        (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2))).naturality i)

/-- Helper for Definition 17.30.1: the canonical basic forms commute with restriction. -/
private theorem basicFormSection_naturality
    (φ : O₁ ⟶ O₂) (p : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    ((deRhamTerm φ p).val.map i).hom (basicFormSection φ p U b₀ b) =
      basicFormSection φ p V ((O₂.presheaf.map i).hom b₀) (fun j ↦ (O₂.presheaf.map i).hom (b j)) := by
  cases p with
  | zero =>
      -- Proof comment: in degree `0`, a basic form is just the coefficient section itself.
      rfl
  | succ p =>
      cases p with
      | zero =>
          -- Proof comment: in degree `1`, compatibility follows from linearity together with the
          -- naturality of the universal differential.
          simp [basicFormSection, exactOneFormSection_naturality, FunctorToTypes.map_comp_apply]
      | succ n =>
          -- Proof comment: in higher degree, combine the sheafification-unit naturality with the
          -- naturality of the wedge generator built from exact one-forms.
          rw [basicFormSection, basicFormSection]
          simp only [FunctorToTypes.map_comp_apply]
          rw [higherExteriorPowerSection_naturality]
          congr 1
          exact wedgeOneFormsSection_naturality φ i n
            (b₀ • exactOneFormSection φ U (b 0))
            (fun j ↦ exactOneFormSection φ U (b j.succ))

/-- Helper for Definition 17.30.1: the target forms on the right-hand side of the de Rham rule
commute with restriction. -/
private theorem differentialTargetSection_naturality
    (φ : O₁ ⟶ O₂) (p : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    ((deRhamTerm φ (p + 1)).val.map i).hom (differentialTargetSection φ p U b₀ b) =
      differentialTargetSection φ p V
        ((O₂.presheaf.map i).hom b₀) (fun j ↦ (O₂.presheaf.map i).hom (b j)) := by
  cases p with
  | zero =>
      -- Proof comment: in degree `0`, the target is the exact one-form `db₀`.
      simpa [differentialTargetSection] using
        exactOneFormSection_naturality φ i b₀
  | succ n =>
      -- Proof comment: in higher degree, apply the same wedge-and-sheafification naturality as
      -- for basic forms, now with the leading factor `db₀`.
      rw [differentialTargetSection, differentialTargetSection]
      simp only [FunctorToTypes.map_comp_apply]
      rw [higherExteriorPowerSection_naturality]
      congr 1
      exact wedgeOneFormsSection_naturality φ i n
        (exactOneFormSection φ U b₀)
        (fun j ↦ exactOneFormSection φ U (b j))

/-- Helper for Definition 17.30.1: the raw presheaf differential on sections is sent by the
sheafification unit to the exact one-form section in `Ω(φ)`. -/
private abbrev rawSectionDerivation
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :=
  (PresheafOfModules.DifferentialsConstruction.derivation' φ.hom).app U

/-- Helper for Definition 17.30.1: the raw presheaf differential on sections is sent by the
sheafification unit to the exact one-form section in `Ω(φ)`. -/
private abbrev rawExactOneFormSection
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    O₂.presheaf.obj U →
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).obj U :=
  fun b ↦ (rawSectionDerivation φ U).d b

/-- Helper for Definition 17.30.1: after applying the sheafification unit, the raw exact
one-form section agrees with the current `exactOneFormSection`. -/
private theorem rawExactOneFormSection_sheafify
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) (b : O₂.presheaf.obj U) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).app U).hom
        (rawExactOneFormSection φ U b) =
      exactOneFormSection φ U b := by
  -- Proof comment: `relativeDifferential φ` is the raw universal derivation postcomposed with
  -- the sheafification unit, so evaluating on a section gives the desired identity.
  simpa [rawExactOneFormSection, exactOneFormSection, relativeDifferential]

/-- Helper for Definition 17.30.1: the raw exact one-form sections commute with restriction in
the presheaf of objectwise differentials. -/
private theorem rawExactOneFormSection_naturality
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (b : O₂.presheaf.obj U) :
    ((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).map i).hom
        (rawExactOneFormSection φ U b) =
      rawExactOneFormSection φ V ((O₂.presheaf.map i).hom b) := by
  -- Proof comment: this is the naturality of the raw universal derivation before sheafification.
  simpa [rawExactOneFormSection, rawSectionDerivation, FunctorToTypes.map_comp_apply] using
    congrArg ModuleCat.Hom.hom
      ((PresheafOfModules.DifferentialsConstruction.derivation' φ.hom).naturality i)

/-- Helper for Definition 17.30.1: the raw higher exact generator with leading coefficient `b₀`
in the presheaf of objectwise Kähler forms. -/
private abbrev rawHigherExactGenerator
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 2) → O₂.presheaf.obj U) :
    ⋀[(O₂.presheaf.obj U)]^(n + 2)
      ((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).obj U) :=
  b₀ • exteriorPower.ιMulti (O₂.presheaf.obj U) (n + 2)
    (fun i ↦ rawExactOneFormSection φ U (b i))

/-- Helper for Definition 17.30.1: the raw target generator without the leading scalar factor in
the presheaf of objectwise Kähler forms. -/
private abbrev rawDifferentialTargetGenerator
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 1) → O₂.presheaf.obj U) :
    ⋀[(O₂.presheaf.obj U)]^(n + 2)
      ((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).obj U) :=
  exteriorPower.ιMulti (O₂.presheaf.obj U) (n + 2)
    (Fin.cases (rawExactOneFormSection φ U b₀) fun j ↦ rawExactOneFormSection φ U (b j))

/-- Helper for Definition 17.30.1: restriction carries a raw higher exact generator to the
corresponding restricted generator. -/
private theorem rawHigherExactGenerator_naturality
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 2) → O₂.presheaf.obj U) :
    exteriorPower.map (n + 2)
        (((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).map i).hom)
        (rawHigherExactGenerator φ n U b₀ b) =
      rawHigherExactGenerator φ n V
        ((O₂.presheaf.map i).hom b₀)
        (fun j ↦ (O₂.presheaf.map i).hom (b j)) := by
  -- Proof comment: `exteriorPower.map_apply_ιMulti` reduces the restriction comparison to the
  -- raw degree-one naturality on each exact generator.
  rw [rawHigherExactGenerator, rawHigherExactGenerator, LinearMap.map_smul,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  exact rawExactOneFormSection_naturality φ i (b j)

/-- Helper for Definition 17.30.1: restriction carries the raw higher differential-target
generator to the corresponding restricted target generator. -/
private theorem rawDifferentialTargetGenerator_naturality
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 1) → O₂.presheaf.obj U) :
    exteriorPower.map (n + 2)
        (((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).map i).hom)
        (rawDifferentialTargetGenerator φ n U b₀ b) =
      rawDifferentialTargetGenerator φ n V
        ((O₂.presheaf.map i).hom b₀)
        (fun j ↦ (O₂.presheaf.map i).hom (b j)) := by
  -- Proof comment: the target generator is another `ιMulti` expression, so restriction is again
  -- checked entrywise on the raw exact one-form factors.
  rw [rawDifferentialTargetGenerator, rawDifferentialTargetGenerator,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  cases j using Fin.cases with
  | zero =>
      exact rawExactOneFormSection_naturality φ i b₀
  | succ k =>
      exact rawExactOneFormSection_naturality φ i (b k)

/-- Helper for Definition 17.30.1: applying the degree-`1` sheafification map entrywise to the
raw higher exact generator produces the higher basic-form wedge generator. -/
private theorem sheafifiedRawHigherExactGenerator_eq_wedgeOneFormsSection
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 2) → O₂.presheaf.obj U) :
    exteriorPower.map (n + 2)
        ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).app U).hom)
        (rawHigherExactGenerator φ n U b₀ b) =
      wedgeOneFormsSection φ n U
        (b₀ • exactOneFormSection φ U (b 0))
        (fun j ↦ exactOneFormSection φ U (b j.succ)) := by
  -- Proof comment: `exteriorPower.map_apply_ιMulti` reduces the comparison to the degree-`1`
  -- bridge `rawExactOneFormSection_sheafify` on each generator.
  rw [rawHigherExactGenerator, wedgeOneFormsSection, LinearMap.map_smul,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [rawExactOneFormSection_sheafify]
  | succ j =>
      simp [rawExactOneFormSection_sheafify]

/-- Helper for Definition 17.30.1: applying the degree-`1` sheafification map entrywise to the
raw target generator produces the higher differential-target wedge generator. -/
private theorem sheafifiedRawDifferentialTargetGenerator_eq_wedgeOneFormsSection
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 1) → O₂.presheaf.obj U) :
    exteriorPower.map (n + 2)
        ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
            (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).app U).hom)
        (rawDifferentialTargetGenerator φ n U b₀ b) =
      wedgeOneFormsSection φ n U
        (exactOneFormSection φ U b₀)
        (fun j ↦ exactOneFormSection φ U (b j)) := by
  -- Proof comment: the same entrywise comparison applies to the target generator, now with the
  -- leading term `db₀` and no scalar coefficient.
  rw [rawDifferentialTargetGenerator, wedgeOneFormsSection, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [rawExactOneFormSection_sheafify]
  | succ j =>
      simp [rawExactOneFormSection_sheafify]

/-- Helper for Definition 17.30.1: the sheafified image of the raw higher exact generator is the
current higher basic form. -/
private theorem higherExteriorPowerSection_rawHigherExactGenerator
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 2) → O₂.presheaf.obj U) :
    higherExteriorPowerSection φ n U
        (exteriorPower.map (n + 2)
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
              (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).app U).hom)
          (rawHigherExactGenerator φ n U b₀ b)) =
      basicFormSection φ (n + 2) U b₀ b := by
  -- Proof comment: after the generator comparison above, `basicFormSection` is exactly the
  -- higher-form image under `higherExteriorPowerSection`.
  simpa [basicFormSection] using
    congrArg (higherExteriorPowerSection φ n U)
      (sheafifiedRawHigherExactGenerator_eq_wedgeOneFormsSection φ n U b₀ b)

/-- Helper for Definition 17.30.1: the sheafified image of the raw target generator is the
current higher differential target section. -/
private theorem higherExteriorPowerSection_rawDifferentialTargetGenerator
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 1) → O₂.presheaf.obj U) :
    higherExteriorPowerSection φ n U
        (exteriorPower.map (n + 2)
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
              (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).app U).hom)
          (rawDifferentialTargetGenerator φ n U b₀ b)) =
      differentialTargetSection φ (n + 1) U b₀ b := by
  -- Proof comment: the higher differential target is defined by the same sheafification map
  -- applied to the exact wedge with leading term `db₀`.
  simpa [differentialTargetSection] using
    congrArg (higherExteriorPowerSection φ n U)
      (sheafifiedRawDifferentialTargetGenerator_eq_wedgeOneFormsSection φ n U b₀ b)

/-- Helper for Definition 17.30.1: on each open set, the Chapter 10 algebraic de Rham family on
the raw Kähler differentials of the section ring map exists and is unique. -/
private theorem existsUnique_sectionwiseRawDeRhamDifferentialFamily
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    ∃! δ : DeRhamFamily (O₁.presheaf.obj U) (O₂.presheaf.obj U)
        ((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).obj U),
      IsExteriorPowerDeRhamDifferential (rawSectionDerivation φ U) δ := by
  let A := O₁.presheaf.obj U
  let B := O₂.presheaf.obj U
  letI : Algebra A B := (φ.hom.app U).hom.toAlgebra
  -- Proof comment: this is exactly the Chapter 10 algebraic existence-and-uniqueness theorem,
  -- specialized to the section ring map on the open set `U`.
  simpa [rawSectionDerivation] using
    (_root_.existsUnique_deRhamDifferentialFamily (A := A) (B := B))

/-- Helper for Definition 17.30.1: the canonical raw de Rham differential family on the section
ring map over an open set. -/
private noncomputable def sectionwiseRawDeRhamDifferentialFamily
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    DeRhamFamily (O₁.presheaf.obj U) (O₂.presheaf.obj U)
      ((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).obj U) :=
  Classical.choose (ExistsUnique.exists (existsUnique_sectionwiseRawDeRhamDifferentialFamily φ U))

/-- Helper for Definition 17.30.1: the chosen raw sectionwise de Rham family satisfies the exact
form rules and `d ∘ d = 0` on the raw Kähler forms over `U`. -/
private theorem sectionwiseRawDeRhamDifferentialFamily_spec
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    IsExteriorPowerDeRhamDifferential (rawSectionDerivation φ U)
      (sectionwiseRawDeRhamDifferentialFamily φ U) := by
  -- Proof comment: this is the defining property of the chosen witness extracted from the
  -- sectionwise Chapter 10 existence theorem.
  simpa [sectionwiseRawDeRhamDifferentialFamily] using
    (Classical.choose_spec
      (ExistsUnique.exists (existsUnique_sectionwiseRawDeRhamDifferentialFamily φ U)))

/-- Helper for Definition 17.30.1: on degree `0`, the chosen raw sectionwise de Rham family is
the raw universal differential. -/
private theorem sectionwiseRawDeRhamDifferentialFamily_zero
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) (b : O₂.presheaf.obj U) :
    sectionwiseRawDeRhamDifferentialFamily φ U 0 b =
      rawExactOneFormSection φ U b := by
  -- Proof comment: the degree-`0` field of the algebraic de Rham owner evaluates to the raw
  -- exact one-form section.
  simpa [rawSectionDerivation, rawExactOneFormSection] using
    LinearMap.congr_fun (sectionwiseRawDeRhamDifferentialFamily_spec φ U).degree_zero b

/-- Helper for Definition 17.30.1: on higher raw exact generators, the chosen raw sectionwise de
Rham family satisfies the usual left-wedge formula. -/
private theorem sectionwiseRawDeRhamDifferentialFamily_higher
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 2) → O₂.presheaf.obj U) :
    sectionwiseRawDeRhamDifferentialFamily φ U (n + 2)
        (rawHigherExactGenerator φ n U b₀ b) =
      rawDifferentialTargetGenerator φ (n + 1) U b₀ (fun j ↦ b j.succ) := by
  -- Proof comment: this is the higher exact-form clause of the sectionwise Chapter 10 de Rham
  -- family, rewritten in the raw generator notation used in this file.
  simpa [rawSectionDerivation, rawExactOneFormSection, rawHigherExactGenerator,
    rawDifferentialTargetGenerator] using
    (sectionwiseRawDeRhamDifferentialFamily_spec φ U).higher n b₀ b

/-- Helper for Definition 17.30.1: on exact degree-one generators, restricting the raw
sectionwise differential agrees with taking the raw differential after restriction. -/
private theorem sectionwiseRawDeRhamDifferentialFamily_degreeOne_natural_on_exactGenerator
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (b₀ b₁ : O₂.presheaf.obj U) :
    exteriorPower.map 2
        (((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).map i).hom)
        (sectionwiseRawDeRhamDifferentialFamily φ U 1
          (b₀ • rawExactOneFormSection φ U b₁)) =
      sectionwiseRawDeRhamDifferentialFamily φ V 1
        (((O₂.presheaf.map i).hom b₀) •
          rawExactOneFormSection φ V ((O₂.presheaf.map i).hom b₁)) := by
  -- Proof comment: both sides reduce to the explicit raw target generator, whose restriction
  -- compatibility was isolated above.
  rw [show sectionwiseRawDeRhamDifferentialFamily φ U 1
        (b₀ • rawExactOneFormSection φ U b₁) =
      rawDifferentialTargetGenerator φ 0 U b₀ (fun _ ↦ b₁) by
        simpa [rawSectionDerivation, rawExactOneFormSection, rawDifferentialTargetGenerator] using
          (sectionwiseRawDeRhamDifferentialFamily_spec φ U).degree_one b₀ b₁]
  rw [show sectionwiseRawDeRhamDifferentialFamily φ V 1
        (((O₂.presheaf.map i).hom b₀) •
          rawExactOneFormSection φ V ((O₂.presheaf.map i).hom b₁)) =
      rawDifferentialTargetGenerator φ 0 V
        ((O₂.presheaf.map i).hom b₀)
        (fun _ ↦ (O₂.presheaf.map i).hom b₁) by
        simpa [rawSectionDerivation, rawExactOneFormSection, rawDifferentialTargetGenerator] using
          (sectionwiseRawDeRhamDifferentialFamily_spec φ V).degree_one
            ((O₂.presheaf.map i).hom b₀) ((O₂.presheaf.map i).hom b₁)]
  simpa using
    rawDifferentialTargetGenerator_naturality φ i 0 b₀ (fun _ ↦ b₁)

/-- Helper for Definition 17.30.1: on higher exact generators, restricting the raw sectionwise
differential agrees with taking the raw differential after restriction. -/
private theorem sectionwiseRawDeRhamDifferentialFamily_higher_natural_on_exactGenerator
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (b₀ : O₂.presheaf.obj U) (b : Fin (n + 2) → O₂.presheaf.obj U) :
    exteriorPower.map (n + 3)
        (((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom).map i).hom)
        (sectionwiseRawDeRhamDifferentialFamily φ U (n + 2)
          (rawHigherExactGenerator φ n U b₀ b)) =
      sectionwiseRawDeRhamDifferentialFamily φ V (n + 2)
        (rawHigherExactGenerator φ n V
          ((O₂.presheaf.map i).hom b₀)
          (fun j ↦ (O₂.presheaf.map i).hom (b j))) := by
  -- Proof comment: the higher-degree raw rule already gives the differential on exact
  -- generators, so the comparison is exactly the naturality of the target generator.
  rw [sectionwiseRawDeRhamDifferentialFamily_higher,
    sectionwiseRawDeRhamDifferentialFamily_higher]
  simpa using
    rawDifferentialTargetGenerator_naturality φ i (n + 1) b₀
      (fun j ↦ b j.succ)

/-- Helper for Definition 17.30.1: the chosen raw sectionwise de Rham family squares to zero on
the raw Kähler forms over an open set. -/
private theorem sectionwiseRawDeRhamDifferentialFamily_sq_zero
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) (p : ℕ) :
    (sectionwiseRawDeRhamDifferentialFamily φ U (p + 1)).comp
      (sectionwiseRawDeRhamDifferentialFamily φ U p) = 0 := by
  -- Proof comment: the square-zero clause is the final field of the sectionwise Chapter 10 owner.
  exact (sectionwiseRawDeRhamDifferentialFamily_spec φ U).square_zero p

/-- Helper for Definition 17.30.1: a section of the sheafification of a presheaf of
`(ringSheaf O₂)`-modules comes from a genuine presheaf section after shrinking to a neighborhood
of the chosen point. -/
private theorem moduleSheafificationUnitSectionLiftsNearPoint
    (P : PresheafOfModules (ringSheaf O₂).obj) {U : Opens X} (x : X) (hxU : x ∈ U)
    (s : ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U) (z : P.obj (op V)),
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P).app
          (op V)) z =
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map
          (homOfLE ‹V ≤ U›).op s := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: rewrite the module-sheafification unit as the additive sheafification unit.
    simpa [η] using
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (ringSheaf O₂).obj) P)
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) := by
    -- Proof comment: on stalks, the sheafification unit is an isomorphism, so it is locally
    -- surjective on sections.
    rw [hη]
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf)
  have hη_surj :
      Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) :=
    (CategoryTheory.isIso_iff_bijective _).1 hη_iso |>.2
  -- Proof comment: lift the germ of `s` through the stalk isomorphism and shrink to make the
  -- chosen representative agree with `s`.
  obtain ⟨m, hm⟩ :=
    hη_surj (TopCat.Presheaf.germ
      (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
      U x hxU s)
  obtain ⟨V₀, hxV₀, z₀, hz₀⟩ := TopCat.Presheaf.germ_exist P.presheaf x m
  have hgerm :
      TopCat.Presheaf.germ
          (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
          V₀ x hxV₀ ((η.app (op V₀)) z₀) =
        TopCat.Presheaf.germ
          (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
          U x hxU s := by
    -- Proof comment: replace the abstract lifted stalk element by its local section
    -- representative.
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply V₀ x hxV₀
      ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η) z₀, hz₀, hm]
  obtain ⟨V, hxV, iV₀, iU, hsec⟩ :=
    TopCat.Presheaf.germ_eq
      (((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.presheaf)
      x hxV₀ hxU ((η.app (op V₀)) z₀) s hgerm
  let hVU : V ≤ U := iU.le
  let z : P.obj (op V) := P.map iV₀.op z₀
  refine ⟨V, hxV, hVU, z, ?_⟩
  have hnat :
      (η.app (op V)) z =
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map iV₀.op
          ((η.app (op V₀)) z₀) := by
    -- Proof comment: naturality of the unit identifies restriction of the lifted section.
    simpa [η, z, FunctorToTypes.map_comp_apply] using
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (η.val.naturality iV₀.op)) z₀
  have hsec' :
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map iV₀.op
          ((η.app (op V₀)) z₀) =
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf O₂).obj)).obj P).val.map iU.op s := by
    simpa using hsec
  rw [hnat, hsec']
  rfl

/-- Helper for Definition 17.30.1: if a presheaf section maps to zero in the sheafification, then
after shrinking around any chosen point its restriction is already zero in the presheaf. -/
private theorem moduleSheafificationUnitZeroNearPoint
    (P : PresheafOfModules (ringSheaf O₂).obj) {U : Opens X} (x : X) (hxU : x ∈ U)
    (z : P.obj (op U))
    (hz :
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P).app
          (op U)) z = 0) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      P.map (homOfLE ‹V ≤ U›).op z = 0 := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: rewrite the module-sheafification unit as the additive sheafification unit.
    simpa [η] using
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (ringSheaf O₂).obj) P)
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) := by
    -- Proof comment: on stalks the sheafification unit is an isomorphism, so its stalk map is
    -- injective.
    rw [hη]
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf)
  have hη_inj :
      Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)) :=
    (CategoryTheory.isIso_iff_bijective _).1 hη_iso |>.1
  have hgerm_zero :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η)
          (TopCat.Presheaf.germ P.presheaf U x hxU z) = 0 := by
    -- Proof comment: push the source germ forward and use the assumed vanishing upstairs.
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      ((PresheafOfModules.toPresheaf (ringSheaf O₂).obj).map η) z, hz]
    exact map_zero _
  have hgerm :
      TopCat.Presheaf.germ P.presheaf U x hxU z =
        TopCat.Presheaf.germ P.presheaf U x hxU (0 : P.obj (op U)) := by
    exact hη_inj (by simpa using hgerm_zero)
  obtain ⟨V, hxV, i₁, _, hsec⟩ :=
    TopCat.Presheaf.germ_eq P.presheaf x hxU hxU z 0 hgerm
  let hVU : V ≤ U := i₁.le
  refine ⟨V, hxV, hVU, ?_⟩
  -- Proof comment: equality of germs gives equality of restrictions on a smaller neighborhood.
  simpa using hsec

/-- Helper for Definition 17.30.1: any higher-degree de Rham form section lifts locally to the
exterior-power presheaf on one-forms. -/
private theorem higherFormSectionLiftsNearPoint
    (φ : O₁ ⟶ O₂) (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
    (s : (Ω^[n + 2](φ)).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U)
      (z : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op V)),
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
          (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2))).app (op V)) z =
        (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U›).op s := by
  -- Proof comment: this is exactly the generic sheafification lift specialized to the higher-form
  -- sheaf `Ω^[n + 2](φ) = Λ^[n + 2] Ω(φ)`.
  simpa [deRhamForm] using
    moduleSheafificationUnitSectionLiftsNearPoint
      (O₂ := O₂) (P := exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)) x hxU s

/-- Helper for Definition 17.30.1: the `O₂(U)`-submodule of one-form sections spanned by exact
differentals on the open set `U`. -/
private abbrev exactOneFormSpan
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    Submodule (O₂.presheaf.obj U) ((Ω(φ)).val.obj U) :=
  Submodule.span (O₂.presheaf.obj U) (Set.range (exactOneFormSection φ U))

/-- Helper for Definition 17.30.1: the degree-`n + 2` exterior-power generators built from exact
one-forms on the open set `U`. -/
private abbrev exactWedgeGenerator
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    (Fin (n + 2) → O₂.presheaf.obj U) →
      (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj U :=
  fun b ↦ exteriorPower.ιMulti (O₂.presheaf.obj U) (n + 2)
    (fun i ↦ exactOneFormSection φ U (b i))

/-- Helper for Definition 17.30.1: the `O₂(U)`-submodule generated by exact wedge sections in
degree `n + 2`. -/
private abbrev exactWedgeSpan
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ) :
    Submodule (O₂.presheaf.obj U)
      ((exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj U) :=
  Submodule.span (O₂.presheaf.obj U) (Set.range (exactWedgeGenerator φ n U))

/-- Helper for Definition 17.30.1: the `O₁(U)`-submodule of degree-`p` forms generated by the
source-facing basic forms `b₀ \, db₁ ∧ \cdots ∧ dbₚ`. -/
private abbrev basicFormSpan
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) :
    Submodule (O₁.presheaf.obj U) ((deRhamTerm φ p).val.obj U) :=
  Submodule.span (O₁.presheaf.obj U)
    (Set.range fun q : O₂.presheaf.obj U × (Fin p → O₂.presheaf.obj U) ↦
      basicFormSection φ p U q.1 q.2)

/-- Helper for Definition 17.30.1: every degree-`0` section is already a basic form, so it lies
in the degree-`0` basic-form span. -/
private theorem basicFormSpan_zero_mem
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) (s : (deRhamTerm φ 0).val.obj U) :
    s ∈ basicFormSpan φ 0 U := by
  -- Proof comment: choose the degree-`0` basic generator whose leading coefficient is `s`.
  exact Submodule.subset_span
    ⟨(s, fun i ↦ Fin.elim0 i), by simp [basicFormSection, deRhamTerm, deRhamForm]⟩

/-- Helper for Definition 17.30.1: multiplying a basic form by a coefficient of `O₂(U)` is the
same as multiplying its leading coefficient by that section. -/
private theorem basicFormSection_leading_mul
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ)
    (a b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    basicFormSection φ p U (a * b₀) b = a • basicFormSection φ p U b₀ b := by
  cases p with
  | zero =>
      -- Proof comment: in degree `0`, a basic form is just the coefficient section itself.
      simp [basicFormSection, mul_comm, mul_left_comm, mul_assoc]
  | succ p =>
      cases p with
      | zero =>
          -- Proof comment: in degree `1`, the leading coefficient multiplies the exact one-form.
          simp [basicFormSection, mul_smul, mul_comm, mul_left_comm, mul_assoc]
      | succ n =>
          -- Proof comment: in higher degree, the same coefficient sits on the distinguished
          -- leading wedge factor.
          simp [basicFormSection, wedgeOneFormsSection, mul_smul, mul_comm, mul_left_comm,
            mul_assoc]

/-- Helper for Definition 17.30.1: the basic-form span is stable under multiplying by
coefficients from `O₂(U)` by absorbing them into the leading coefficient of each generator. -/
private theorem basicFormSpan_smul_mem
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ)
    (a : O₂.presheaf.obj U) {s : (deRhamTerm φ p).val.obj U}
    (hs : s ∈ basicFormSpan φ p U) :
    a • s ∈ basicFormSpan φ p U := by
  refine Submodule.span_induction hs ?_ ?_ ?_ ?_
  · rintro _ ⟨⟨b₀, b⟩, rfl⟩
    -- Proof comment: on a basic generator, absorb the scalar into the leading coefficient.
    exact Submodule.subset_span ⟨(a * b₀, b), basicFormSection_leading_mul φ p U a b₀ b⟩
  · simpa using (Submodule.zero_mem (basicFormSpan φ p U))
  · intro s t hs ht
    exact Submodule.add_mem _ hs ht
  · intro r t ht
    -- Proof comment: `O₁(U)`-scalars commute with the ambient `O₂(U)`-scalar multiplication.
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      Submodule.smul_mem (basicFormSpan φ p U) r ht

/-- Helper for Definition 17.30.1: restriction preserves the source-facing span of local basic
forms. -/
private theorem basicFormSpanMapMem
    (φ : O₁ ⟶ O₂) (p : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    {s : (deRhamTerm φ p).val.obj U} (hs : s ∈ basicFormSpan φ p U) :
    ((deRhamTerm φ p).val.map i).hom s ∈ basicFormSpan φ p V := by
  -- Proof comment: restriction sends each basic generator to the corresponding restricted basic
  -- generator, so it preserves the generated span.
  refine Submodule.span_induction hs ?_ ?_ ?_ ?_
  · rintro _ ⟨⟨b₀, b⟩, rfl⟩
    rw [basicFormSection_naturality]
    exact Submodule.subset_span
      ⟨((O₂.presheaf.map i).hom b₀, fun j ↦ (O₂.presheaf.map i).hom (b j)), rfl⟩
  · simpa using (Submodule.zero_mem (basicFormSpan φ p V))
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b hb
    exact Submodule.smul_mem _ ((O₁.presheaf.map i).hom a) hb

/-- Helper for Definition 17.30.1: after shrinking around a chosen point, any one-form section
lies in the span of exact differentials. -/
private theorem oneFormSectionMemSpanExactNearPoint
    (φ : O₁ ⟶ O₂) {U : Opens X} (x : X) (hxU : x ∈ U)
    (ω : (Ω(φ)).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      (Ω(φ)).val.map (homOfLE ‹V ≤ U›).op ω ∈
        exactOneFormSpan φ (op V) := by
  obtain ⟨V, hxV, hVU, z, hz⟩ :=
    moduleSheafificationUnitSectionLiftsNearPoint
      (O₂ := O₂)
      (P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)
      x hxU ω
  refine ⟨V, hxV, hVU, ?_⟩
  let R := O₂.presheaf.obj (op V)
  have hzspan :
      z ∈ Submodule.span R
        (Set.range (KaehlerDifferential.D (O₁.presheaf.obj (op V)) (O₂.presheaf.obj (op V)))) := by
    -- Proof comment: the raw Kähler differentials are generated by exact one-forms on each open.
    rw [KaehlerDifferential.span_range_derivation (R := O₁.presheaf.obj (op V))
      (S := O₂.presheaf.obj (op V))]
    trivial
  have himage :
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf O₂).obj)).unit.app
          (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).app
          (op V)) z ∈
        exactOneFormSpan φ (op V) := by
    -- Proof comment: push the spanning relation forward through the universal one-form map.
    refine Submodule.span_induction hzspan ?_ ?_ ?_ ?_
    · rintro _ ⟨b, rfl⟩
      exact Submodule.subset_span ⟨b, rawExactOneFormSection_sheafify φ (op V) b⟩
    · simpa using (Submodule.zero_mem (exactOneFormSpan φ (op V)))
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
    · intro a b hb
      exact Submodule.smul_mem _ a hb
  simpa using (hz ▸ himage)

/-- Helper for Definition 17.30.1: restriction in the exterior-power presheaf sends an `ιMulti`
generator to the entrywise restricted generator. -/
private theorem exteriorPowerPresheafMapApplyIMulti
    (φ : O₁ ⟶ O₂) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (m : Fin n → (Ω(φ)).val.obj U) :
    ((exteriorPowerPresheaf (Ω(φ) : ModRSp₂) n).map i).hom
        (exteriorPower.ιMulti (O₂.presheaf.obj U) n m) =
      exteriorPower.ιMulti (O₂.presheaf.obj V) n
        (fun j ↦ ((Ω(φ)).val.map i).hom (m j)) := by
  -- Proof comment: this is the exterior-power restriction formula specialized to the one-form
  -- sheaf `Ω(φ)`.
  let R := O₂.presheaf.obj U
  let S := O₂.presheaf.obj V
  let M := (Ω(φ)).val.obj U
  let N := (Ω(φ)).val.obj V
  letI : Algebra R S := (O₂.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (O₂.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  let f : M →ₗ[R] N := ((Ω(φ)).val.map i).hom
  let ιN : N [⋀^Fin n]→ₗ[S] ↥(⋀[S]^n N) := exteriorPower.ιMulti S n
  let ιN' : N [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m j x y
            simpa using ιN.map_update_add m j x y
          map_update_smul' := by
            intro _ m j r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m j (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m j k hjk hne
        exact ιN.map_eq_zero_of_eq m hjk hne }
  let A : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) := ιN'.compLinearMap f
  change (exteriorPower.alternatingMapLinearEquiv A)
      (exteriorPower.ιMulti R n m) =
    exteriorPower.ιMulti S n (fun j ↦ f (m j))
  calc
    (exteriorPower.alternatingMapLinearEquiv A) (exteriorPower.ιMulti R n m)
        = (exteriorPower.alternatingMapLinearEquiv.symm
            (exteriorPower.alternatingMapLinearEquiv A)) m := by
            symm
            simpa using
              (exteriorPower.alternatingMapLinearEquiv_symm_apply
                (F := exteriorPower.alternatingMapLinearEquiv A) m)
    _ = A m := by
          simpa using
            congrArg (fun F : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) ↦ F m)
              (exteriorPower.alternatingMapLinearEquiv.symm_apply_apply A)
    _ = exteriorPower.ιMulti S n (f ∘ m) := rfl

/-- Helper for Definition 17.30.1: restricting an exact one-form span element keeps it inside the
exact one-form span on the smaller open. -/
private theorem exactOneFormSpanMapMem
    (φ : O₁ ⟶ O₂) {U V : Opens X} (i : V ⟶ U)
    {ω : (Ω(φ)).val.obj (op U)} (hω : ω ∈ exactOneFormSpan φ (op U)) :
    (Ω(φ)).val.map i.op ω ∈ exactOneFormSpan φ (op V) := by
  -- Proof comment: restriction preserves exact generators by naturality of the universal
  -- differential, so it preserves their span.
  refine Submodule.span_induction hω ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    rw [exactOneFormSection_naturality]
    exact Submodule.subset_span ⟨(O₂.presheaf.map i.op).hom b, rfl⟩
  · simpa using (Submodule.zero_mem (exactOneFormSpan φ (op V)))
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b hb
    exact Submodule.smul_mem _ ((O₂.presheaf.map i.op).hom a) hb

/-- Helper for Definition 17.30.1: the exact one-forms span the exact-one-form submodule even
after viewing them as subtype-valued generators. -/
private theorem exactOneFormSubtypeSpanEqTop
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) :
    Submodule.span (O₂.presheaf.obj U)
      (Set.range fun b : O₂.presheaf.obj U ↦
        (⟨exactOneFormSection φ U b, Submodule.subset_span ⟨b, rfl⟩⟩ :
          exactOneFormSpan φ U)) = ⊤ := by
  classical
  -- Proof comment: this is the same span as `exactOneFormSpan`, just rewritten inside its
  -- subtype carrier.
  apply top_unique
  intro x hx
  clear hx
  let S : Submodule (O₂.presheaf.obj U) (exactOneFormSpan φ U) :=
    Submodule.span (O₂.presheaf.obj U)
      (Set.range fun b : O₂.presheaf.obj U ↦
        (⟨exactOneFormSection φ U b, Submodule.subset_span ⟨b, rfl⟩⟩ :
          exactOneFormSpan φ U))
  have hxS :
      x ∈ S := by
    have hyS :
        ∀ {y : (Ω(φ)).val.obj U} (hy : y ∈ exactOneFormSpan φ U),
          (⟨y, hy⟩ : exactOneFormSpan φ U) ∈ S := by
      intro y hy
      refine Submodule.span_induction hy ?_ ?_ ?_ ?_
      · rintro _ ⟨b, rfl⟩
        exact Submodule.subset_span ⟨b, rfl⟩
      · simpa [S] using (Submodule.zero_mem S)
      · intro a b ha hb
        simpa [S] using Submodule.add_mem S ha hb
      · intro a b hb
        simpa [S] using Submodule.smul_mem S a hb
    exact hyS x.property
  simpa [S] using hxS

/-- Helper for Definition 17.30.1: if every entry of an alternating generator lies in the exact
one-form span, then the whole generator lies in the exact-wedge span. -/
private theorem iMultiMemExactWedgeSpanOfMemExactOneFormSpan
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (m : Fin (n + 2) → (Ω(φ)).val.obj U)
    (hm : ∀ i, m i ∈ exactOneFormSpan φ U) :
    exteriorPower.ιMulti (O₂.presheaf.obj U) (n + 2) m ∈ exactWedgeSpan φ n U := by
  classical
  let R := O₂.presheaf.obj U
  let P := exactOneFormSpan φ U
  let mP : Fin (n + 2) → P := fun i ↦ ⟨m i, hm i⟩
  let sP : Set P := Set.range fun b : R ↦
    (⟨exactOneFormSection φ U b, Submodule.subset_span ⟨b, rfl⟩⟩ : P)
  have hsP : Submodule.span R sP = ⊤ := exactOneFormSubtypeSpanEqTop (φ := φ) U
  have hspanP :
      Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP}) =
        (⋀[R]^(n + 2) P : Submodule R (ExteriorAlgebra R P)) := by
    simpa using
      (exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top
        (R := R) (n := n + 2) (M := P) (s := sP) hsP)
  have hmemP :
      (exteriorPower.ιMulti R (n + 2) mP : ↥(⋀[R]^(n + 2) P)) ∈
        Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP}) := by
    -- Proof comment: inside the exact-one-form submodule, the exact generators span the whole
    -- module, so the fixed-degree exterior power is spanned by exact tuples.
    rw [hspanP]
    exact (exteriorPower.ιMulti R (n + 2) mP).property
  let f : P →ₗ[R] (Ω(φ)).val.obj U := P.subtype
  have hmap_mem :
      exteriorPower.map (n + 2) f (exteriorPower.ιMulti R (n + 2) mP) ∈
        Submodule.map (exteriorPower.map (n + 2) f)
          (Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP})) := by
    exact Submodule.map_mem _ hmemP
  have hmap_le :
      Submodule.map (exteriorPower.map (n + 2) f)
          (Submodule.span R (exteriorPower.ιMulti R (n + 2) '' {a | Set.range a ⊆ sP})) ≤
        exactWedgeSpan φ n U := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨a, ha, rfl⟩
    let b : Fin (n + 2) → R := fun i ↦ Classical.choose (ha ⟨i, rfl⟩)
    have hb : ∀ i, a i =
        (⟨exactOneFormSection φ U (b i), Submodule.subset_span ⟨b i, rfl⟩⟩ : P) := by
      intro i
      exact Classical.choose_spec (ha ⟨i, rfl⟩)
    have htuple : f ∘ a = fun i ↦ exactOneFormSection φ U (b i) := by
      funext i
      exact congrArg Subtype.val (hb i)
    rw [show exteriorPower.map (n + 2) f (exteriorPower.ιMulti R (n + 2) a) =
        exteriorPower.ιMulti R (n + 2) (f ∘ a) by
          rw [exteriorPower.map_apply_ιMulti]]
    rw [htuple]
    exact Submodule.subset_span ⟨b, rfl⟩
  have htarget :
      exteriorPower.map (n + 2) f (exteriorPower.ιMulti R (n + 2) mP) ∈ exactWedgeSpan φ n U :=
    hmap_le hmap_mem
  simpa [mP, f] using htarget

/-- Helper for Definition 17.30.1: restriction preserves the exact-wedge span on higher-form
presheaf sections. -/
private theorem exactWedgeSpanMapMem
    (φ : O₁ ⟶ O₂) (n : ℕ) {U V : Opens X} (i : V ⟶ U)
    {z : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op U)}
    (hz : z ∈ exactWedgeSpan φ n (op U)) :
    (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map i.op z ∈
      exactWedgeSpan φ n (op V) := by
  -- Proof comment: restriction sends each exact wedge generator to the corresponding exact wedge
  -- generator on the smaller open, so it preserves the generated span.
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    have hmap :
        (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map i.op
            (exactWedgeGenerator φ n (op U) b) =
          exactWedgeGenerator φ n (op V) (fun j ↦ (O₂.presheaf.map i.op).hom (b j)) := by
      rw [show exactWedgeGenerator φ n (op U) b =
          exteriorPower.ιMulti (O₂.presheaf.obj (op U)) (n + 2)
            (fun j ↦ exactOneFormSection φ (op U) (b j)) by rfl]
      rw [exteriorPowerPresheafMapApplyIMulti (φ := φ) (i := i.op) (n := n + 2)]
      congr
      funext j
      exact exactOneFormSection_naturality φ i.op (b j)
    rw [hmap]
    exact Submodule.subset_span ⟨fun j ↦ (O₂.presheaf.map i.op).hom (b j), rfl⟩
  · simpa using (Submodule.zero_mem (exactWedgeSpan φ n (op V)))
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b hb
    exact Submodule.smul_mem _ ((O₂.presheaf.map i.op).hom a) hb

/-- Helper for Definition 17.30.1: a finite tuple of one-form sections can be made simultaneously
exact-span after shrinking around a chosen point. -/
private theorem finiteFamilyOneFormSectionsMemSpanExactNearPoint
    (φ : O₁ ⟶ O₂) :
    ∀ (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
      (ω : Fin n → (Ω(φ)).val.obj (op U)),
      ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
        ∀ i : Fin n,
          (Ω(φ)).val.map (homOfLE ‹V ≤ U›).op (ω i) ∈ exactOneFormSpan φ (op V)
  | 0, U, x, hxU, ω => by
      refine ⟨U, hxU, le_rfl, ?_⟩
      intro i
      exact (Fin.elim0 i)
  | n + 1, U, x, hxU, ω => by
      obtain ⟨V₀, hxV₀, hV₀U, hω₀⟩ :=
        oneFormSectionMemSpanExactNearPoint (φ := φ) x hxU (ω 0)
      let i₀ : V₀ ⟶ U := homOfLE hV₀U
      obtain ⟨V, hxV, hVV₀, htail⟩ :=
        finiteFamilyOneFormSectionsMemSpanExactNearPoint (φ := φ) n x hxV₀
          (fun j ↦ (Ω(φ)).val.map i₀.op (ω j.succ))
      refine ⟨V, hxV, hVV₀.trans hV₀U, ?_⟩
      intro i
      cases i using Fin.cases with
      | zero =>
          have hrestrict :
              (Ω(φ)).val.map (homOfLE hVV₀).op
                  ((Ω(φ)).val.map i₀.op (ω 0)) ∈
                exactOneFormSpan φ (op V) :=
            exactOneFormSpanMapMem (φ := φ) (i := homOfLE hVV₀) hω₀
          simpa [FunctorToTypes.map_comp_apply] using hrestrict
      | succ j =>
          simpa [FunctorToTypes.map_comp_apply] using htail j

/-- Helper for Definition 17.30.1: after shrinking around a chosen point, a lifted higher-form
section lies in the span of exact wedge generators. -/
private theorem localLiftedHigherFormMemSpanExactWedgesNearPoint
    (φ : O₁ ⟶ O₂) (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
    (z : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map (homOfLE ‹V ≤ U›).op z ∈
        exactWedgeSpan φ n (op V) := by
  let R := O₂.presheaf.obj (op U)
  have hz :
      z ∈ Submodule.span R
        (Set.range (exteriorPower.ιMulti R (n + 2) :
          (Fin (n + 2) → (Ω(φ)).val.obj (op U)) →
            (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op U))) := by
    -- Proof comment: the exterior-power presheaf object is generated by its `ιMulti` sections.
    rw [← exteriorPower.ιMulti_span_fixedDegree
      (R := R) (n := n + 2) (M := (Ω(φ)).val.obj (op U))]
    exact z.property
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · intro y hy
    rcases hy with ⟨m, rfl⟩
    obtain ⟨V, hxV, hVU, hmV⟩ :=
      finiteFamilyOneFormSectionsMemSpanExactNearPoint (φ := φ) (n + 2) x hxU m
    refine ⟨V, hxV, hVU, ?_⟩
    rw [exteriorPowerPresheafMapApplyIMulti (φ := φ) (i := (homOfLE hVU).op) (n := n + 2)]
    exact iMultiMemExactWedgeSpanOfMemExactOneFormSpan (φ := φ) n (op V)
      (fun j ↦ ((Ω(φ)).val.map (homOfLE hVU).op).hom (m j)) hmV
  · refine ⟨U, hxU, le_rfl, ?_⟩
    simpa using (Submodule.zero_mem (exactWedgeSpan φ n (op U)))
  · intro a b ha hb
    rcases ha with ⟨V₁, hxV₁, hV₁U, haV₁⟩
    rcases hb with ⟨V₂, hxV₂, hV₂U, hbV₂⟩
    let V : Opens X := V₁ ⊓ V₂
    have hxV : x ∈ V := ⟨hxV₁, hxV₂⟩
    have hVU : V ≤ U := fun y hy ↦ hV₁U hy.1
    let i₁ : V ⟶ V₁ := homOfLE inf_le_left
    let i₂ : V ⟶ V₂ := homOfLE inf_le_right
    refine ⟨V, hxV, hVU, ?_⟩
    have haV :
        (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map i₁.op
            ((exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map (homOfLE hV₁U).op a) ∈
          exactWedgeSpan φ n (op V) :=
      exactWedgeSpanMapMem (φ := φ) n i₁ haV₁
    have hbV :
        (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map i₂.op
            ((exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map (homOfLE hV₂U).op b) ∈
          exactWedgeSpan φ n (op V) :=
      exactWedgeSpanMapMem (φ := φ) n i₂ hbV₂
    have haV' :
        (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map (homOfLE hVU).op a ∈
          exactWedgeSpan φ n (op V) := by
      simpa [FunctorToTypes.map_comp_apply] using haV
    have hbV' :
        (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map (homOfLE hVU).op b ∈
          exactWedgeSpan φ n (op V) := by
      simpa [FunctorToTypes.map_comp_apply] using hbV
    simpa [map_add] using Submodule.add_mem _ haV' hbV'
  · intro a b hb
    rcases hb with ⟨V, hxV, hVU, hbV⟩
    refine ⟨V, hxV, hVU, ?_⟩
    simpa [FunctorToTypes.map_smul] using
      Submodule.smul_mem (exactWedgeSpan φ n (op V))
        ((O₂.presheaf.map (homOfLE hVU).op).hom a) hbV

/-- Helper for Definition 17.30.1: after shrinking around a chosen point, any one-form section
lies in the `O₁`-span of genuine basic one-forms. -/
private theorem localOneFormMemBasicFormSpanNearPoint
    (φ : O₁ ⟶ O₂) {U : Opens X} (x : X) (hxU : x ∈ U)
    (ω : (Ω(φ)).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      (Ω(φ)).val.map (homOfLE ‹V ≤ U›).op ω ∈ basicFormSpan φ 1 (op V) := by
  obtain ⟨V, hxV, hVU, hωV⟩ := oneFormSectionMemSpanExactNearPoint (φ := φ) x hxU ω
  refine ⟨V, hxV, hVU, ?_⟩
  -- Proof comment: every exact one-form is already the degree-`1` basic form with leading
  -- coefficient `1`, and coefficients are absorbed into that leading factor.
  refine Submodule.span_induction hωV ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    exact Submodule.subset_span ⟨(1, fun _ ↦ b), by
      simp [basicFormSection, exactOneFormSection]⟩
  · simpa using (Submodule.zero_mem (basicFormSpan φ 1 (op V)))
  · intro s t hs ht
    exact Submodule.add_mem _ hs ht
  · intro a s hs
    exact basicFormSpan_smul_mem (φ := φ) (p := 1) (U := op V) a hs

/-- Helper for Definition 17.30.1: the sheafified image of a local exact wedge-span element lies
in the `O₁(U)`-span of genuine higher basic forms. -/
private theorem higherExteriorPowerSection_mem_basicFormSpan_of_mem_exactWedgeSpan
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    {z : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj U}
    (hz : z ∈ exactWedgeSpan φ n U) :
    higherExteriorPowerSection φ n U z ∈ basicFormSpan φ (n + 2) U := by
  refine Submodule.span_induction hz ?_ ?_ ?_ ?_
  · rintro _ ⟨b, rfl⟩
    -- Proof comment: an exact wedge generator is exactly the higher basic form with leading
    -- coefficient `1`.
    exact Submodule.subset_span ⟨(1, b), by
      simp [exactWedgeGenerator, basicFormSection, higherExteriorPowerSection,
        wedgeOneFormsSection]⟩
  · simpa using (Submodule.zero_mem (basicFormSpan φ (n + 2) U))
  · intro s t hs ht
    exact Submodule.add_mem _ hs ht
  · intro a s hs
    exact basicFormSpan_smul_mem (φ := φ) (p := n + 2) (U := U) a hs

/-- Helper for Definition 17.30.1: after shrinking around a chosen point, any higher-form section
lies in the `O₁`-span of genuine higher basic forms. -/
private theorem localHigherFormMemBasicFormSpanNearPoint
    (φ : O₁ ⟶ O₂) (n : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
    (s : (Ω^[n + 2](φ)).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U›).op s ∈ basicFormSpan φ (n + 2) (op V) := by
  obtain ⟨V, hxV, hVU, z, hz⟩ :=
    higherFormSectionLiftsNearPoint (φ := φ) (n := n) x hxU s
  obtain ⟨W, hxW, hWV, hzW⟩ :=
    localLiftedHigherFormMemSpanExactWedgesNearPoint (φ := φ) (n := n) x hxV z
  let iWV : W ⟶ V := homOfLE hWV
  let iWU : W ⟶ U := homOfLE (hWV.trans hVU)
  let zW : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op W) :=
    (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map iWV.op z
  have hzW' :
      higherExteriorPowerSection φ n (op W) zW =
        (Ω^[n + 2](φ)).val.map iWU.op s := by
    -- Proof comment: restrict the chosen lift equality from `V` to the smaller neighborhood `W`.
    have hnatη :
        (Ω^[n + 2](φ)).val.map iWV.op (higherExteriorPowerSection φ n (op V) z) =
          higherExteriorPowerSection φ n (op W) zW := by
      simpa [zW, FunctorToTypes.map_comp_apply] using
        higherExteriorPowerSection_naturality (φ := φ) (i := iWV.op) (n := n) z
    rw [← hnatη, hz]
    simpa [iWU, iWV, FunctorToTypes.map_comp_apply]
  refine ⟨W, hxW, hWV.trans hVU, ?_⟩
  rw [← hzW']
  exact higherExteriorPowerSection_mem_basicFormSpan_of_mem_exactWedgeSpan
    (φ := φ) (n := n) (U := op W) hzW

/-- Helper for Definition 17.30.1: every local de Rham form becomes a section of the corresponding
basic-form span after shrinking around any chosen point. -/
private theorem localFormMemBasicFormSpanNearPoint
    (φ : O₁ ⟶ O₂) (p : ℕ) {U : Opens X} (x : X) (hxU : x ∈ U)
    (s : (deRhamTerm φ p).val.obj (op U)) :
    ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U),
      ((deRhamTerm φ p).val.map (homOfLE ‹V ≤ U›).op).hom s ∈
        basicFormSpan φ p (op V) := by
  cases p with
  | zero =>
      refine ⟨U, hxU, le_rfl, ?_⟩
      simpa using basicFormSpan_zero_mem (φ := φ) (U := op U) s
  | succ p =>
      cases p with
      | zero =>
          simpa using localOneFormMemBasicFormSpanNearPoint (φ := φ) x hxU s
      | succ n =>
          simpa using localHigherFormMemBasicFormSpanNearPoint (φ := φ) (n := n) x hxU s

/-- Helper for Definition 17.30.1: two higher-form sections are equal once their restrictions
agree on a neighborhood of every point of the ambient open set. -/
private theorem higherFormSectionEqOfLocallyEqual
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (s t : (Ω^[n + 2](φ)).val.obj U)
    (hlocal : ∀ x : X, x ∈ U.unop →
      ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U.unop),
        (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U.unop›).op s =
          (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U.unop›).op t) :
    s = t := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨(Ω^[n + 2](φ)).val.presheaf, (Ω^[n + 2](φ)).isSheaf⟩
  -- Proof comment: sheaf sections are determined by their germs, so it suffices to compare the
  -- germs after shrinking to a neighborhood where the two restrictions coincide.
  apply TopCat.Presheaf.section_ext F U.unop s t
  intro x hxU
  obtain ⟨V, hxV, hVU, hst⟩ := hlocal x hxU
  calc
    TopCat.Presheaf.germ F.presheaf U.unop x hxU s =
        TopCat.Presheaf.germ F.presheaf V x hxV
          ((Ω^[n + 2](φ)).val.map (homOfLE hVU).op s) := by
            symm
            exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV s
    _ = TopCat.Presheaf.germ F.presheaf V x hxV
          ((Ω^[n + 2](φ)).val.map (homOfLE hVU).op t) := by
            rw [hst]
    _ = TopCat.Presheaf.germ F.presheaf U.unop x hxU t := by
          exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hVU) x hxV t

/-- The basic-form rule characterizing a de Rham differential family on `Ω^[p](φ)`. -/
private def SatisfiesDeRhamBasicFormRule
    (φ : O₁ ⟶ O₂)
    (δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)) : Prop :=
  ∀ (p : ℕ) (U : (Opens X)ᵒᵖ) (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U),
    ((δ p).val.app U) (basicFormSection φ p U b₀ b) =
      differentialTargetSection φ p U b₀ b

/-- Consecutive de Rham differentials compose to zero. -/
private def DeRhamDifferentialSquaresZero
    (φ : O₁ ⟶ O₂)
    (δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)) : Prop :=
  ∀ p : ℕ, δ p ≫ δ (p + 1) = 0

/-- Helper for Definition 17.30.1: the basic-form rule already determines the de Rham
differential family uniquely. -/
private theorem deRhamDifferentialFamilyEqOfBasicForm
    (φ : O₁ ⟶ O₂)
    {δ δ' : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)}
    (hδ : SatisfiesDeRhamBasicFormRule φ δ)
    (hδ' : SatisfiesDeRhamBasicFormRule φ δ') :
    δ = δ' := by
  funext p
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  intro s
  cases p with
  | zero =>
      -- Proof comment: in degree `0`, the basic-form rule evaluates the differential on an
      -- arbitrary coefficient section and forces both candidates to be the universal derivation.
      simpa [basicFormSection, differentialTargetSection, deRhamTerm, deRhamForm] using
        (hδ 0 U s (fun i ↦ Fin.elim0 i)).trans
          (hδ' 0 U s (fun i ↦ Fin.elim0 i)).symm
  | succ p =>
      cases p with
      | zero =>
          -- Proof comment: for one-forms, shrink around each point until the section becomes a
          -- span of exact one-forms, and then compare the two differentials on those generators.
          apply higherFormSectionEqOfLocallyEqual (φ := φ) (n := 0) (U := U)
          intro x hxU
          obtain ⟨V, hxV, hVU, hsV⟩ := oneFormSectionMemSpanExactNearPoint (φ := φ) x hxU s
          refine ⟨V, hxV, hVU, ?_⟩
          let L := ((δ 1).val.app (op V)).hom
          let L' := ((δ' 1).val.app (op V)).hom
          change L (((Ω(φ)).val.map (homOfLE hVU).op).hom s) =
            L' (((Ω(φ)).val.map (homOfLE hVU).op).hom s)
          refine Submodule.span_induction hsV ?_ ?_ ?_ ?_
          · rintro _ ⟨b, rfl⟩
            simpa [L, L', basicFormSection, differentialTargetSection, exactOneFormSection] using
              (hδ 1 (op V) 1 (fun _ ↦ b)).trans (hδ' 1 (op V) 1 (fun _ ↦ b)).symm
          · simp [L, L']
          · intro a b ha hb
            simp [L, L', ha, hb]
          · intro a b hb
            simp [L, L', hb]
      | succ n =>
          -- Proof comment: in higher degree, first lift locally to the exterior-power presheaf,
          -- shrink further until the lift lies in the span of exact wedge generators, and then
          -- compare both differentials on those generators via the basic-form rule.
          apply higherFormSectionEqOfLocallyEqual (φ := φ) (n := n + 1) (U := U)
          intro x hxU
          obtain ⟨V, hxV, hVU, z, hz⟩ :=
            higherFormSectionLiftsNearPoint (φ := φ) (n := n) x hxU s
          obtain ⟨W, hxW, hWV, hzW⟩ :=
            localLiftedHigherFormMemSpanExactWedgesNearPoint
              (φ := φ) (n := n) x hxV z
          let iWV : W ⟶ V := homOfLE hWV
          let iWU : W ⟶ U.unop := homOfLE (hWV.trans hVU)
          let zW : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op W) :=
            (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map iWV.op z
          have hzW' :
              higherExteriorPowerSection φ n (op W) zW =
                (Ω^[n + 2](φ)).val.map iWU.op s := by
            have hnatη :
                (Ω^[n + 2](φ)).val.map iWV.op (higherExteriorPowerSection φ n (op V) z) =
                  higherExteriorPowerSection φ n (op W) zW := by
              simpa [zW, FunctorToTypes.map_comp_apply] using
                higherExteriorPowerSection_naturality (φ := φ) (i := iWV.op) (n := n) z
            rw [← hnatη, hz]
            simpa [iWU, iWV, FunctorToTypes.map_comp_apply]
          refine ⟨W, hxW, hWV.trans hVU, ?_⟩
          let L := ((δ (n + 2)).val.app (op W)).hom
          let L' := ((δ' (n + 2)).val.app (op W)).hom
          rw [← hzW']
          refine Submodule.span_induction hzW ?_ ?_ ?_ ?_
          · rintro _ ⟨b, rfl⟩
            simpa [L, L', exactWedgeGenerator, basicFormSection, differentialTargetSection,
              wedgeOneFormsSection, exactOneFormSection] using
              (hδ (n + 2) (op W) 1 b).trans (hδ' (n + 2) (op W) 1 b).symm
          · simp [L, L', higherExteriorPowerSection]
          · intro a b ha hb
            simp [L, L', ha, hb]
          · intro a b hb
            simp [L, L', hb]

/-- Helper for Definition 17.30.1: a higher-form section is zero once its restriction vanishes on
a neighborhood of every point of the ambient open set. -/
private theorem higherFormSectionEqZeroOfLocallyZero
    (φ : O₁ ⟶ O₂) (n : ℕ) (U : (Opens X)ᵒᵖ)
    (s : (Ω^[n + 2](φ)).val.obj U)
    (hlocal : ∀ x : X, x ∈ U.unop →
      ∃ (V : Opens X) (_ : x ∈ V) (_ : V ≤ U.unop),
        (Ω^[n + 2](φ)).val.map (homOfLE ‹V ≤ U.unop›).op s = 0) :
    s = 0 := by
  -- Proof comment: apply the local equality criterion with the comparison section chosen to be
  -- the zero section.
  apply higherFormSectionEqOfLocallyEqual (φ := φ) (n := n) (U := U) (s := s) (t := 0)
  intro x hxU
  obtain ⟨V, hxV, hVU, hsV⟩ := hlocal x hxU
  refine ⟨V, hxV, hVU, ?_⟩
  simpa using hsV

/-- Helper for Definition 17.30.1: the target basic form with leading coefficient `1` vanishes,
because `d(1) = 0`. -/
private theorem differentialTargetSection_one_eq_zero
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ) (b : Fin p → O₂.presheaf.obj U) :
    differentialTargetSection φ p U 1 b = 0 := by
  cases p with
  | zero =>
      -- Proof comment: in degree `0`, the target is the exact differential `d(1)`.
      simp [differentialTargetSection, exactOneFormSection]
  | succ n =>
      -- Proof comment: in higher degree, the leading wedge factor is `d(1) = 0`, so the whole
      -- alternating generator vanishes before sheafification.
      simp [differentialTargetSection, wedgeOneFormsSection, exactOneFormSection]

/-- Helper for Definition 17.30.1: any differential family satisfying the basic-form rule already
squares to zero. -/
private theorem deRhamDifferentialSquaresZeroOfBasicForm
    (φ : O₁ ⟶ O₂)
    {δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)}
    (hδ : SatisfiesDeRhamBasicFormRule φ δ) :
    DeRhamDifferentialSquaresZero φ δ := by
  intro p
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  intro s
  cases p with
  | zero =>
      -- Proof comment: the first differential sends `s` to `ds`, and the degree-one rule sends
      -- every exact one-form `d b` to `d(1) ∧ d b = 0`.
      change ((δ 1).val.app U).hom (((δ 0).val.app U).hom s) = 0
      rw [hδ 0 U s (fun i ↦ Fin.elim0 i)]
      simpa [basicFormSection, exactOneFormSection] using
        (hδ 1 U (1 : O₂.presheaf.obj U) (fun _ ↦ s)).trans
          (differentialTargetSection_one_eq_zero (φ := φ) 1 U (fun _ ↦ s))
  | succ p =>
      cases p with
      | zero =>
          -- Proof comment: after shrinking around each point, a one-form is a span of exact
          -- one-forms, and the degree-one rule kills every exact generator.
          apply higherFormSectionEqZeroOfLocallyZero (φ := φ) (n := 1) (U := U)
          intro x hxU
          obtain ⟨V, hxV, hVU, hsV⟩ := oneFormSectionMemSpanExactNearPoint (φ := φ) x hxU s
          let i : V ⟶ U.unop := homOfLE hVU
          let L : (Ω(φ)).val.obj (op V) →ₗ[O₂.presheaf.obj (op V)]
              (deRhamTerm φ 2).val.obj (op V) :=
            ((δ 1).val.app (op V)).hom
          have hnatL :
              ((deRhamTerm φ 2).val.map i.op).hom (((δ 1).val.app U).hom s) =
                L (((Ω(φ)).val.map i.op).hom s) := by
            -- Proof comment: restriction commutes with the degree-one differential by naturality.
            simpa [L, i, FunctorToTypes.map_comp_apply] using
              congrArg ModuleCat.Hom.hom (((δ 1).val.naturality i.op))
          have hlocalZero :
              L (((Ω(φ)).val.map i.op).hom s) = 0 := by
            refine Submodule.span_induction hsV ?_ ?_ ?_ ?_
            · rintro _ ⟨b, rfl⟩
              simpa [L, basicFormSection, exactOneFormSection] using
                (hδ 1 (op V) (1 : O₂.presheaf.obj (op V)) (fun _ ↦ b)).trans
                  (differentialTargetSection_one_eq_zero (φ := φ) 1 (op V) (fun _ ↦ b))
            · simp [L]
            · intro a b ha hb
              simp [L, ha, hb]
            · intro a b hb
              simp [L, hb]
          refine ⟨V, hxV, hVU, ?_⟩
          change ((deRhamTerm φ 3).val.map i.op).hom
              (((δ 2).val.app U).hom (((δ 1).val.app U).hom s)) = 0
          rw [show ((deRhamTerm φ 3).val.map i.op).hom
                (((δ 2).val.app U).hom (((δ 1).val.app U).hom s)) =
              ((δ 2).val.app (op V)).hom
                (((deRhamTerm φ 2).val.map i.op).hom (((δ 1).val.app U).hom s)) by
                simpa [i, FunctorToTypes.map_comp_apply] using
                  congrArg ModuleCat.Hom.hom (((δ 2).val.naturality i.op))]
          rw [hnatL, hlocalZero]
          simp
      | succ n =>
          -- Proof comment: in higher degree, shrink until the source section comes from an
          -- exterior-power lift lying in the span of exact wedge generators; the basic-form rule
          -- kills each generator with leading coefficient `1`.
          apply higherFormSectionEqZeroOfLocallyZero (φ := φ) (n := n + 2) (U := U)
          intro x hxU
          obtain ⟨V, hxV, hVU, z, hz⟩ :=
            higherFormSectionLiftsNearPoint (φ := φ) (n := n) x hxU s
          obtain ⟨W, hxW, hWV, hzW⟩ :=
            localLiftedHigherFormMemSpanExactWedgesNearPoint
              (φ := φ) (n := n) x hxV z
          let iWV : W ⟶ V := homOfLE hWV
          let iWU : W ⟶ U.unop := homOfLE (hWV.trans hVU)
          let zW : (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op W) :=
            (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).map iWV.op z
          have hzW' :
              higherExteriorPowerSection φ n (op W) zW =
                (Ω^[n + 2](φ)).val.map iWU.op s := by
            -- Proof comment: restricting the chosen lift equality from `V` to `W` identifies the
            -- restricted source section with the shrunk raw lift.
            have hnatη :
                (Ω^[n + 2](φ)).val.map iWV.op (higherExteriorPowerSection φ n (op V) z) =
                  higherExteriorPowerSection φ n (op W) zW := by
              simpa [zW, FunctorToTypes.map_comp_apply] using
                higherExteriorPowerSection_naturality (φ := φ) (i := iWV.op) (n := n) z
            rw [← hnatη, hz]
            simpa [iWU, iWV, FunctorToTypes.map_comp_apply]
          let Lraw :
              (exteriorPowerPresheaf (Ω(φ) : ModRSp₂) (n + 2)).obj (op W) →
                (deRhamTerm φ (n + 3)).val.obj (op W) :=
            fun t ↦ ((δ (n + 2)).val.app (op W)).hom (higherExteriorPowerSection φ n (op W) t)
          have hfirstZero : Lraw zW = 0 := by
            refine Submodule.span_induction hzW ?_ ?_ ?_ ?_
            · rintro _ ⟨b, rfl⟩
              simpa [Lraw, exactWedgeGenerator, basicFormSection, wedgeOneFormsSection,
                exactOneFormSection] using
                (hδ (n + 2) (op W) (1 : O₂.presheaf.obj (op W)) b).trans
                  (differentialTargetSection_one_eq_zero (φ := φ) (n + 2) (op W) b)
            · simp [Lraw, higherExteriorPowerSection]
            · intro a b ha hb
              simp [Lraw, ha, hb]
            · intro a b hb
              simp [Lraw, hb]
          refine ⟨W, hxW, hWV.trans hVU, ?_⟩
          change ((deRhamTerm φ (n + 4)).val.map iWU.op).hom
              (((δ (n + 3)).val.app U).hom (((δ (n + 2)).val.app U).hom s)) = 0
          rw [show ((deRhamTerm φ (n + 4)).val.map iWU.op).hom
                (((δ (n + 3)).val.app U).hom (((δ (n + 2)).val.app U).hom s)) =
              ((δ (n + 3)).val.app (op W)).hom
                (((deRhamTerm φ (n + 3)).val.map iWU.op).hom
                  (((δ (n + 2)).val.app U).hom s)) by
                simpa [iWU, FunctorToTypes.map_comp_apply] using
                  congrArg ModuleCat.Hom.hom (((δ (n + 3)).val.naturality iWU.op))]
          rw [show ((deRhamTerm φ (n + 3)).val.map iWU.op).hom
                (((δ (n + 2)).val.app U).hom s) =
              ((δ (n + 2)).val.app (op W)).hom
                ((Ω^[n + 2](φ)).val.map iWU.op s) by
                simpa [iWU, FunctorToTypes.map_comp_apply] using
                  congrArg ModuleCat.Hom.hom (((δ (n + 2)).val.naturality iWU.op))]
          rw [← hzW', hfirstZero]
          simp

/-- Helper for Definition 17.30.1: once one differential family satisfies the basic-form rule,
the already-established uniqueness and square-zero lemmas upgrade it to the unique de Rham
differential family. -/
private theorem existsUnique_deRhamDifferentialFamily_of_exists_basicForm
    (φ : O₁ ⟶ O₂) :
    (∃ δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1),
        SatisfiesDeRhamBasicFormRule φ δ) →
      ∃! δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1),
        SatisfiesDeRhamBasicFormRule φ δ ∧ DeRhamDifferentialSquaresZero φ δ := by
  intro hδ
  rcases hδ with ⟨δ, hδ⟩
  refine ⟨δ, ?_, ?_⟩
  · -- Proof comment: the square-zero part is automatic once the basic-form rule is known.
    exact ⟨hδ, deRhamDifferentialSquaresZeroOfBasicForm (φ := φ) hδ⟩
  · intro δ' hδ'
    -- Proof comment: uniqueness reduces to the basic-form uniqueness theorem, and then the
    -- square-zero predicate is propositional data transported along that equality.
    have hEq :
        δ' = δ := deRhamDifferentialFamilyEqOfBasicForm (φ := φ) hδ'.1 hδ
    exact hEq

/-- Helper for Definition 17.30.1: once the positive-degree differentials are constructed, adding
the universal derivation in degree `0` yields a full basic-form-compatible family. -/
private theorem existsBasicFormCompatibleDeRhamDifferentialFamily_of_positive
    (φ : O₁ ⟶ O₂)
    (hpos :
      ∃ δPos : ∀ p : ℕ, deRhamTerm φ (p + 1) ⟶ deRhamTerm φ (p + 2),
        ∀ (p : ℕ) (U : (Opens X)ᵒᵖ) (b₀ : O₂.presheaf.obj U)
          (b : Fin (p + 1) → O₂.presheaf.obj U),
          ((δPos p).val.app U) (basicFormSection φ (p + 1) U b₀ b) =
            differentialTargetSection φ (p + 1) U b₀ b) :
    ∃ δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1),
      SatisfiesDeRhamBasicFormRule φ δ := by
  rcases hpos with ⟨δPos, hδPos⟩
  refine ⟨fun
    | 0 => (relativeDifferential φ).val
    | p + 1 => δPos p, ?_⟩
  intro p U b₀ b
  cases p with
  | zero =>
      -- Proof comment: in degree `0`, the differential is exactly the universal derivation.
      rfl
  | succ p =>
      -- Proof comment: the positive-degree rule is the supplied hypothesis.
      exact hδPos p U b₀ b

/-- A morphism of sheaves of rings carries a unique differential family on the graded forms
`Ω^•_{O₂/O₁}` whose degree-`0` part is the universal derivation and whose higher-degree parts send
`b₀ \, db₁ ∧ \cdots ∧ dbₚ` to `db₀ ∧ db₁ ∧ \cdots ∧ dbₚ`. -/
private theorem existsUnique_deRhamDifferentialFamily
    (φ : O₁ ⟶ O₂) :
    ∃! δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1),
      SatisfiesDeRhamBasicFormRule φ δ ∧ DeRhamDifferentialSquaresZero φ δ := by
  -- Route correction: the direct route on `Ω^[p](φ)` is blocked because the algebraic Chapter 10
  -- differential family lives on raw sectionwise Kähler forms, while the current higher terms are
  -- sheafified exterior powers.
  have hunique :
      ∀ {δ δ' : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)},
        SatisfiesDeRhamBasicFormRule φ δ →
          SatisfiesDeRhamBasicFormRule φ δ' → δ = δ' := by
    intro δ δ' hδ hδ'
    exact deRhamDifferentialFamilyEqOfBasicForm (φ := φ) hδ hδ'
  have hsq :
      ∀ {δ : ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1)},
        SatisfiesDeRhamBasicFormRule φ δ → DeRhamDifferentialSquaresZero φ δ := by
    intro δ hδ
    exact deRhamDifferentialSquaresZeroOfBasicForm (φ := φ) hδ
  -- Proof comment: after isolating uniqueness and square-zero, only the existence of one basic-
  -- form-compatible family remains, and the degree-`0` piece has already been isolated.
  refine existsUnique_deRhamDifferentialFamily_of_exists_basicForm (φ := φ) ?_
  refine existsBasicFormCompatibleDeRhamDifferentialFamily_of_positive (φ := φ) ?_
  -- TODO: the only remaining blocker is the positive-degree family
  -- `δPos p : deRhamTerm φ (p + 1) ⟶ deRhamTerm φ (p + 2)`.
  -- The planned route is to define the local operator on `basicFormSpan`, prove restriction
  -- compatibility using `basicFormSpanMapMem`, and glue the resulting local target sections.
  sorry

/-- The canonical differential family on the graded forms `Ω^•_{O₂/O₁}`. -/
private def deRhamDifferentialFamily
    (φ : O₁ ⟶ O₂) :
    ∀ p : ℕ, deRhamTerm φ p ⟶ deRhamTerm φ (p + 1) :=
  Classical.choose (ExistsUnique.exists (existsUnique_deRhamDifferentialFamily φ))

/-- The chosen de Rham differential family satisfies the de Rham rule and squares to zero. -/
private theorem deRhamDifferentialFamily_spec
    (φ : O₁ ⟶ O₂) :
    SatisfiesDeRhamBasicFormRule φ (deRhamDifferentialFamily φ) ∧
      DeRhamDifferentialSquaresZero φ (deRhamDifferentialFamily φ) := by
  simpa [deRhamDifferentialFamily] using
    (Classical.choose_spec (ExistsUnique.exists (existsUnique_deRhamDifferentialFamily φ)))

/-- The chosen de Rham differentials satisfy the basic-form rule on local sections. -/
private theorem deRhamDifferentialFamily_basicForm
    (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens X)ᵒᵖ)
    (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    ((deRhamDifferentialFamily φ p).val.app U) (basicFormSection φ p U b₀ b) =
      differentialTargetSection φ p U b₀ b :=
  (deRhamDifferentialFamily_spec φ).1 p U b₀ b

/-- Consecutive chosen de Rham differentials compose to zero. -/
private theorem deRhamDifferentialFamily_sq_zero
    (φ : O₁ ⟶ O₂) (p : ℕ) :
    deRhamDifferentialFamily φ p ≫ deRhamDifferentialFamily φ (p + 1) = 0 := by
  exact (deRhamDifferentialFamily_spec φ).2 p

/-- Definition 17.30.1: for a morphism `φ : O₁ ⟶ O₂` of sheaves of rings on a topological space,
the de Rham complex of `φ` is the cochain complex of `O₁`-module sheaves whose degree-`n` term is
`\Omega^n_{O₂/O₁}` and whose differential is the canonical de Rham differential on local basic
forms. -/
@[stacks 0FKM]
def deRhamComplex
    (φ : O₁ ⟶ O₂) :
    CochainComplex ModO₁ ℕ :=
  CochainComplex.of
    (deRhamTerm φ)
    (deRhamDifferentialFamily φ)
    (deRhamDifferentialFamily_sq_zero φ)

scoped[AlgebraicGeometry] notation3:max "Ω^•(" φ ")" =>
  deRhamComplex φ

/-- The degree-`n` object of the relative de Rham complex is the sheaf `\Omega^n_{O₂/O₁}`,
viewed as an `O₁`-module sheaf by restriction of scalars along `φ`. -/
theorem deRhamComplex_obj
    (φ : O₁ ⟶ O₂) (n : ℕ) :
    (Ω^•(φ)).X n =
      (SheafOfModules.restrictScalars (ringSheafMap φ)).obj Ω^[n](φ) :=
  rfl

/-- On every open set, the degree-`p` differential of the relative de Rham complex sends the
canonical basic form `b₀ \, db₁ ∧ \cdots ∧ dbₚ` to `db₀ ∧ db₁ ∧ \cdots ∧ dbₚ`. -/
theorem deRhamComplex_d_basicForm
    (φ : O₁ ⟶ O₂) (U : (Opens X)ᵒᵖ) (p : ℕ)
    (b₀ : O₂.presheaf.obj U) (b : Fin p → O₂.presheaf.obj U) :
    (((Ω^•(φ)).d p (p + 1)).val.app U) (basicFormSection φ p U b₀ b) =
      differentialTargetSection φ p U b₀ b := by
  simpa [deRhamComplex] using
    deRhamDifferentialFamily_basicForm φ p U b₀ b

end TopCat.Sheaf

namespace AlgebraicGeometry.RingedSpace

variable {X S : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable (f : X ⟶ S) (n : ℕ)

open RingedSpace.Hom

scoped[AlgebraicGeometry] notation3:max "Ω^•[" f "]" =>
  deRhamComplex (inverseImageStructureSheafHomComm f)

scoped[AlgebraicGeometry] notation3:max "Ω^[" n "][" f "]" =>
  deRhamForm (inverseImageStructureSheafHomComm f) n

/- For a morphism of ringed spaces `f : X ⟶ S`, the degree-`n` object of the relative de Rham
complex `Ω^•[f]` is obtained by direct specialization of the sheaf-level owner theorem
`deRhamComplex_obj` along `inverseImageStructureSheafHomComm f`. -/
#check
  (deRhamComplex_obj (inverseImageStructureSheafHomComm f) n :
    (Ω^•[f]).X n =
      (SheafOfModules.restrictScalars
        (ringSheafMap (inverseImageStructureSheafHomComm f))).obj
        Ω^[n][f])

end AlgebraicGeometry.RingedSpace
