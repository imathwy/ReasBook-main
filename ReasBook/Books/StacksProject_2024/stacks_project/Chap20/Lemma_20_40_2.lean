import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_40_1

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

section

variable (𝒰 : ι → Opens X.carrier)

local notation "AltCechF" => moduleAlternatingCechToDerivedFunctor X 𝒰
local notation "RΓAb" =>
  (DerivedCategory.Q :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
      moduleDerivedGlobalSectionsToAbelian X
local notation "AbSheaf" => moduleUnderlyingSheaf X

/- The source-facing basiswise acyclicity data in Lemma 20.40.2 packages the finite-intersection
condition on the cover together with the positive-degree vanishing for the terms of `F`, their
cokernels, and their cohomology sheaves on the chosen basis opens. -/
/-- The basiswise acyclicity hypothesis used in Lemma 20.40.2. -/
class ModuleAlternatingCechBasiswiseAcyclicity
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    (𝓑 : Set (Opens X.carrier)) : Prop where
  inter_mem (p : ℕ) (σ : Fin (p + 1) → ι) :
    (⨅ a, 𝒰 (σ a)) ∈ 𝓑
  term_isZero {U : Opens X.carrier} (hU : U ∈ 𝓑) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (((AbSheaf).obj (F.X q)).H' p U)
  cokernel_isZero {U : Opens X.carrier} (hU : U ∈ 𝓑) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (((AbSheaf).obj (cokernel (F.d (q - 1) q))).H' p U)
  cohomology_isZero {U : Opens X.carrier} (hU : U ∈ 𝓑) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (((AbSheaf).obj (F.homology q)).H' p U)

/- Domain-style sampling for Lemma 20.40.2:
- primary domain: alternating Čech-to-derived-global-sections comparisons for complexes of
  `𝒪_X`-modules on a finite open cover;
- sampled owner declarations:
  `moduleAlternatingCechToDerivedFunctor`,
  `moduleDerivedGlobalSectionsToAbelian`,
  `moduleGlobalSectionsAdditiveDerivedUnitApp`,
  `IsModuleAlternatingCechToDerivedGlobalSectionsComparison`,
  `exists_moduleAlternatingCechToDerivedGlobalSections`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the comparison natural transformation from the alternating Čech total
  complex to abelian-valued derived global sections is already owned by
  `exists_moduleAlternatingCechToDerivedGlobalSections`, with its compatibility recorded by
  `IsModuleAlternatingCechToDerivedGlobalSectionsComparison`; this file is source-facing only in
  adding the basiswise acyclicity criterion that forces the component at one fixed complex `F` to
  be an isomorphism;
- primitive data: the finite cover `𝒰`, the complex `F`, a basis `𝓑` of opens, and the
  basiswise vanishing hypotheses on the underlying abelian sheaves of the terms, cokernels, and
  cohomology sheaves;
- derived API: the existence of the comparison morphism with the same compatibility relation as
  Lemma `20.40.1`, together with `IsIso (τ.app F)`.

Source/core/bridge triage:
- `source-facing`: `exists_moduleAlternatingCechToDerivedGlobalSections_isIso_of_basiswise_acyclicity`;
- `core/canonical`: `moduleAlternatingCechToDerivedFunctor`,
  `moduleDerivedGlobalSectionsToAbelian`,
  `moduleGlobalSectionsAdditiveDerivedUnitApp`,
  `IsModuleAlternatingCechToDerivedGlobalSectionsComparison`, and
  `exists_moduleAlternatingCechToDerivedGlobalSections`;
- `bridge/view`: the basiswise acyclicity hypotheses turning the general comparison of
  Lemma `20.40.1` into an isomorphism at `F`.
-/

-- Proof sketch: for any compatible comparison `τ`, pass to bounded-below truncations `τ_{≥ -n}
-- F`. Lemma `20.23.6` identifies alternating and ordinary Čech total complexes, and
-- Lemma `20.25.2` computes `RΓ(X, τ_{≥ -n} F)` from the ordinary Čech complex using the
-- basiswise acyclicity of the terms. The cokernel and cohomology-sheaf vanishing hypotheses let
-- one pass to a truncation-limit injective resolution as in Lemma `20.38.1`; the resulting
-- inverse systems are eventually constant in each total degree because the alternating Čech
-- complex is finite. Applying the Milnor-type limit comparison then shows that `τ.app F` is an
-- isomorphism in `D(Ab)`.
instance isIso_app_of_basiswise_acyclicity
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    (𝓑 : Set (Opens X.carrier))
    (h𝓑 : Opens.IsBasis 𝓑)
    (τ : AltCechF ⟶ RΓAb)
    (hτ : IsModuleAlternatingCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (hacyclic : ModuleAlternatingCechBasiswiseAcyclicity 𝒰 F 𝓑) :
    IsIso (τ.app F) := by
  sorry

/-- Lemma 20.40.2: for a finite open covering `𝒰` with `iSup 𝒰 = ⊤` of a ringed space
`(X, 𝒪_X)`, assume `𝓑` is a basis of opens of `X`, every finite intersection of members of `𝒰`
lies in `𝓑`, and for every `U ∈ 𝓑`, every `p > 0`, and every `q : ℤ`, the higher cohomology
groups of the underlying abelian sheaves of `F.X q`, `cokernel (F.d (q - 1) q)`, and
`F.homology q` vanish on `U`. Then there exists a comparison morphism of Lemma `20.40.1` from the
total alternating Čech complex of `F` to `RΓ(X, F)` whose component at `F` is an isomorphism in
`D(AddCommGrpCat)`. -/
@[stacks 08C2]
theorem exists_moduleAlternatingCechToDerivedGlobalSections_isIso_of_basiswise_acyclicity
    (h𝒰 : iSup 𝒰 = ⊤)
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    (𝓑 : Set (Opens X.carrier))
    (h𝓑 : Opens.IsBasis 𝓑)
    (hacyclic : ModuleAlternatingCechBasiswiseAcyclicity 𝒰 F 𝓑) :
    ∃ τ : AltCechF ⟶ RΓAb,
      IsModuleAlternatingCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧ IsIso (τ.app F) := by
  obtain ⟨τ, hτ⟩ := exists_moduleAlternatingCechToDerivedGlobalSections 𝒰 h𝒰
  exact ⟨τ, hτ, isIso_app_of_basiswise_acyclicity 𝒰 F 𝓑 h𝓑 τ hτ hacyclic⟩

end

end AlgebraicGeometry.RingedSpace
