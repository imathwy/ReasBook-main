import StacksProject_2024.stacks_project.Chap21.Lemma_21_16_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_52_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open DerivedCategory
open Opposite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [HasFiniteWidePullbacks C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

variable [Abelian (SheafOfModules (ringSheaf J 𝒪))]

local notation "Mod𝒪" => SheafOfModules (ringSheaf J 𝒪)
local notation "single0" => DerivedCategory.singleFunctor Mod𝒪 (0 : ℤ)

/- Domain-style sampling for Lemma 21.52.4:
- primary domain: bounded-below coproduct preservation for represented `Hom` functors in the
  derived category of sheaves of modules, deduced from site-theoretic cohomology colimit
  compatibility;
- sampled owner declarations:
  `Sheaf.cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow`,
  `DerivedCategory.singleFunctor`,
  `preadditiveCoyoneda.obj`;
- best owner abstraction: this file should stay at the `bridge/view` layer, reusing the
  source-facing site-cover owner `CofinalFiniteCoverings` together with the canonical degree-zero
  object `((single0).obj (j![𝒪, U]))` introduced in Lemma `21.52.3`;
- primitive data: the cofinal finite covering system `(B, Cov, hCov)`, the chosen object `U ∈ B`,
  and the bounded-below coproduct family `M`;
- derived API: the represented `Hom`-functor coproduct comparison for
  `((single0).obj (j![𝒪, U]))`.

Source/core/bridge triage:
- `source-facing`: the cofinal finite covering hypothesis on the site;
- `core/canonical`: `Sheaf.cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings` and
  `((single0).obj (j![𝒪, U]))`;
- `bridge/view`: the theorem below, feeding the site-theoretic cohomology comparison into the
  bounded-below derived `Hom`-coproduct comparison. -/

-- Proof sketch: first use Lemma `21.16.1` to show that for each `U ∈ B` the functors
-- `ℱ ↦ H^p(U, ℱ)` commute with direct sums, by writing a direct sum as the
-- filtered colimit of its finite partial sums. Then apply Lemma `21.52.3`, which upgrades this
-- cohomological direct-sum compatibility to the bounded-below Hom-coproduct comparison for
-- `j_{U!}𝒪_U[0]`.

/-- Lemma 21.52.4: under the cofinal finite covering hypotheses on `B` and `Cov`, the degree-zero
derived object attached to `j_{U!}𝒪_U` satisfies the bounded-below coproduct comparison over each
`U ∈ B`. -/
@[stacks 0G22]
theorem localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_cofinal_finite_coverings
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    (hCov : CofinalFiniteCoverings J B Cov)
    {U : C} (hU : U ∈ B)
    {ι : Type (u + 1)}
    (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M]
    (hM : ∃ a : ℤ, (∐ M).IsGE a) :
    PreservesColimit (Discrete.functor M)
      (preadditiveCoyoneda.obj (op ((single0).obj (j![𝒪, U])))) := by
  refine
    localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow J 𝒪 U M ?_ hM
  intro p κ
  -- The site-theoretic input is exactly Lemma `21.16.1`, applied to the filtered diagram of
  -- finite partial sums of a `κ`-indexed coproduct. Keeping this step local avoids exporting a
  -- second public wrapper around
  -- `Sheaf.cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings`.
  sorry

end

end SheafOfModules.RingedSite
