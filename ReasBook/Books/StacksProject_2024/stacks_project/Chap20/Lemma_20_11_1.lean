import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap20.Sections_on_open
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits
open scoped CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.11.1:
- primary domain: Čech cohomology of `𝒪_X`-modules on a ringed space and its
  degree-zero comparison with sections of the underlying additive sheaf;
- sampled owner declarations:
  `SheafOfModules.evaluation`,
  `moduleSectionsAsAbelianFunctor`,
  `moduleCechCohomology`,
  `CategoryTheory.ringedSiteModuleCechCohomology_zero_isomorphic_evaluation`,
  `CategoryTheory.ringedSiteModuleCechCohomology_isZero_of_pos_of_injective`;
- best owner abstraction: the source-facing ringed-space owner is
  `moduleCechCohomology 𝒰 ℐ p`, while sections on an open subset are canonically owned by
  `SheafOfModules.evaluation X.ringCatSheaf`; the additive-group-valued target is canonically
  exposed by `moduleSectionsAsAbelianFunctor X U`. The Chapter 21 ringed-site theorems are the
  core/canonical
  Čech comparison and injective Čech-acyclicity owners specialized by this file;
- primitive data: a ringed space `X`, a family of opens `𝒰`, and a module sheaf
  `ℱ : RingedSpace.Modules X`;
- derived API: the degree-zero identification with sections on `iSup 𝒰`, and positive-degree
  Čech-acyclicity for injective module sheaves on the indexed family `𝒰`.

Source/core/bridge triage:
- `source-facing`: the degree-zero identification for an `𝒪_X`-module on an open cover, and the
  higher vanishing statement for an injective `𝒪_X`-module on an open cover;
- `core/canonical`: `moduleCechCohomology` together with the Chapter 21 owners
  `ringedSiteModuleCechCohomology_zero_isomorphic_evaluation` and
  `ringedSiteModuleCechCohomology_isZero_of_pos_of_injective`;
- `bridge/view`: `moduleSectionsAsAbelianFunctor X U`, the abelian-valued sections owner obtained
  from `SheafOfModules.evaluation`.
-/

section

variable {X : RingedSpace.{u}}

-- Proof sketch: `moduleCechCohomology 𝒰 ℱ 0` is the ringed-space specialization of the Chapter 21
-- degree-zero ringed-site comparison theorem applied to the cover of its canonical union
-- `iSup 𝒰`. The resulting identification is the sheaf equalizer statement, expressed on the
-- public surface by the chapter owner `moduleSectionsAsAbelianFunctor X (iSup 𝒰)`.
/-- Lemma 20.11.1 (1): if `𝒰` is an indexed family of opens, equivalently an open covering of
`iSup 𝒰`, then the degree-zero Čech cohomology of an `𝒪_X`-module `ℱ` with respect to `𝒰`
identifies with the section group `ℱ(iSup 𝒰)`. -/
@[stacks 01EP]
theorem cech_cohomology_zero_iso_sections
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (ℱ : X.Modules) :
    IsIsomorphic (moduleCechCohomology 𝒰 ℱ 0)
      ((moduleSectionsAsAbelianFunctor X (iSup 𝒰)).obj ℱ) := sorry

-- Proof sketch: an injective `𝒪_X`-module is injective in the ambient presheaf-module
-- category, so the Chapter 21 ringed-site injective Čech-acyclicity theorem specializes through
-- `moduleCechCohomology`. The resulting positive-degree vanishing depends only on the indexed
-- family `𝒰`, not on a separately named union open.
/-- Lemma 20.11.1 (2): if `ℐ` is an injective `𝒪_X`-module and `𝒰` is an indexed family of
opens, equivalently an open covering of its union, then the positive-degree Čech cohomology of
`ℐ` with respect to `𝒰` vanishes. -/
@[stacks 01EP]
theorem cech_cohomology_isZero_of_injective_succ
    {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℐ : X.Modules) [Injective ℐ] (p : ℕ) :
    IsZero (moduleCechCohomology 𝒰 ℐ (p + 1)) := sorry

/-- Typeclass form of Lemma 20.11.1 (2) on the source-facing owner `moduleCechCohomology`. -/
instance instIsZeroModuleCechCohomologyOfInjectiveSucc
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (ℐ : X.Modules) [Injective ℐ] (p : ℕ) :
    IsZero (moduleCechCohomology 𝒰 ℐ (p + 1)) :=
  cech_cohomology_isZero_of_injective_succ 𝒰 ℐ p

/-- Companion form of Lemma 20.11.1 (2): every positive-degree Čech cohomology object attached to
an injective `𝒪_X`-module is zero. -/
theorem cech_cohomology_isZero_of_pos_of_injective
    {ι : Type u} (𝒰 : ι → Opens X.carrier)
    (ℐ : X.Modules) [Injective ℐ] (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCechCohomology 𝒰 ℐ p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa [Nat.add_comm] using
    (cech_cohomology_isZero_of_injective_succ 𝒰 ℐ q)

/-- Typeclass form of positive-degree Čech acyclicity on the source-facing owner
`moduleCechCohomology`, using `Fact (0 < p)` for the positivity input. -/
instance instIsZeroModuleCechCohomologyOfPosOfInjective
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (ℐ : X.Modules) [Injective ℐ]
    (p : ℕ) [Fact (0 < p)] :
    IsZero (moduleCechCohomology 𝒰 ℐ p) :=
  cech_cohomology_isZero_of_pos_of_injective 𝒰 ℐ p Fact.out

end

end AlgebraicGeometry.RingedSpace
