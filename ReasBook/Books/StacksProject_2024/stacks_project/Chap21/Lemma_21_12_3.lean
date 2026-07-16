import Mathlib.CategoryTheory.Sites.CoversTop
import StacksProject_2024.stacks_project.Chap20.«20_10_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.12.3:
- primary domain: Čech cohomology of sheaves of `𝒪`-modules on a ringed site, with the
  degree-zero term controlled by the sheaf condition and the higher terms controlled by
  injectivity after forgetting to presheaves of modules;
- sampled owner declarations:
  `ringedSiteModuleCechCohomology`,
  `SheafOfModules.evaluation`,
  `cechCohomology_zero_of_sheaf`,
  `cechCohomology_isZero_of_injective_succ`,
  `injective_as_presheaf_of_modules`;
- best owner abstraction: the source-facing owners here are the degree-zero comparison and the
  positive-degree vanishing for the module-valued Čech cohomology object
  `ringedSiteModuleCechCohomology`; the additive-sheaf owners from Section 21.10 and the
  forgetful functor `SheafOfModules.forget` form the core/canonical layer;
- primitive data: a sheaf of rings `𝒪`, an object `U`, a covering family `family : ι → Over U`,
  and a sheaf of `𝒪`-modules;
- derived API: the degree-zero identification with evaluation at `U`, and the positive-degree
  vanishing for injective module sheaves.

Source/core/bridge triage:
- `source-facing`: the two clauses of Lemma 21.12.3 for module-valued Čech cohomology on a
  covering family in `Over U`;
- `core/canonical`: `ringedSiteModuleCechCohomology`, `SheafOfModules.evaluation`,
  `cechCohomology_zero_of_sheaf`, `cechCohomology_isZero_of_injective_succ`, and
  `injective_as_presheaf_of_modules`;
- `bridge/view`: forgetting a sheaf of modules first to a sheaf of abelian groups and then to a
  presheaf when comparing with the additive Čech owners.
-/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat) (U : C)
variable [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

-- Proof sketch: forget `ℱ` to a sheaf of abelian groups and apply the degree-zero owner
-- `cechCohomology_zero_of_sheaf` to the covering family `family`. The module-valued target is the
-- same underlying object as evaluation by `SheafOfModules.evaluation 𝒪 (op U)`, so the result is
-- expressed directly on the module owner.
/-- Lemma 21.12.3 (1): for a sheaf of `𝒪`-modules on a ringed site, the degree-zero Čech
cohomology of a covering family `family : ι → Over U` is canonically isomorphic to the module of
sections over `U`. -/
@[stacks 03FC]
theorem ringedSiteModuleCechCohomology_zero_isomorphic_evaluation
    (hfamily : (J.over U).CoversTop family) (ℱ : SheafOfModules 𝒪) :
    IsIsomorphic
      (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℱ) 0)
      ((SheafOfModules.evaluation 𝒪 (op U)).obj ℱ) := sorry

-- Proof sketch: by Lemma `21.9.3` and Lemma `18.9.2`, the Čech complex of an injective
-- `𝒪`-module sheaf identifies with the Hom complex
-- `Mor_{PMod(𝒪)}(Z_{𝒰, •} ⊗ 𝒪, ℐ)`.
-- Lemma `21.12.1` makes `ℐ` injective in `PMod(𝒪)`, so exactness of
-- `Hom_{PMod(𝒪)}(-, ℐ)` turns Lemma `21.9.5` into vanishing of the higher
-- homology groups.
/-- Lemma 21.12.3 (2): for an injective `𝒪`-module sheaf on a ringed site, the degree-`p + 1`
Čech cohomology attached to a family `family : ι → Over U` vanishes. -/
@[stacks 03FC]
theorem ringedSiteModuleCechCohomology_isZero_of_injective_succ
    (ℐ : SheafOfModules 𝒪) [Injective ℐ] (p : ℕ) :
    IsZero
      (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) (p + 1)) :=
  by
    sorry

/-- Typeclass form of Lemma 21.12.3 (2) on the source-facing owner
`ringedSiteModuleCechCohomology`. -/
instance instIsZeroRingedSiteModuleCechCohomologyOfInjectiveSucc
    (ℐ : SheafOfModules 𝒪) [Injective ℐ] (p : ℕ) :
    IsZero
      (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) (p + 1)) :=
  ringedSiteModuleCechCohomology_isZero_of_injective_succ 𝒪 U family ℐ p

/-- Companion form of Lemma 21.12.3 (2): every positive-degree Čech cohomology object attached to
an injective `𝒪`-module sheaf is zero. -/
theorem ringedSiteModuleCechCohomology_isZero_of_pos_of_injective
    (ℐ : SheafOfModules 𝒪) [Injective ℐ] (p : ℕ) (hp : 0 < p) :
    IsZero
      (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
  have hsucc :
      IsZero
        (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) (q + 1)) :=
    ringedSiteModuleCechCohomology_isZero_of_injective_succ 𝒪 U family ℐ q
  simpa [Nat.add_comm] using hsucc

/-- Typeclass form of positive-degree Čech acyclicity on the source-facing owner
`ringedSiteModuleCechCohomology`, using `Fact (0 < p)` for the positivity input. -/
instance instIsZeroRingedSiteModuleCechCohomologyOfPosOfInjective
    (ℐ : SheafOfModules 𝒪) [Injective ℐ] (p : ℕ) [Fact (0 < p)] :
    IsZero
      (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) p) :=
  ringedSiteModuleCechCohomology_isZero_of_pos_of_injective 𝒪 U family ℐ p Fact.out

end

end CategoryTheory
