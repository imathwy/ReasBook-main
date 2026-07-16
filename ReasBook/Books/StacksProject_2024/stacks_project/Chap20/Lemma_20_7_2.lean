import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.7.2:
- primary domain: sheaf cohomology of `𝒪_X`-modules on the opens site of a ringed space;
- sampled owner declarations:
  `GrothendieckTopology.Cover`,
  `GrothendieckTopology.Cover.Arrow`,
  `moduleUnderlyingSheaf`,
  `CategoryTheory.Sheaf.exists_cover_restrict_eq_zero_of_positive_cohomology_class`;
- best owner abstraction: the core owner is the general site-level abelian-sheaf theorem
  `CategoryTheory.Sheaf.exists_cover_restrict_eq_zero_of_positive_cohomology_class`,
  specialized here to the opens-site ringed space `X`; the ringed-space bridge to the underlying
  additive sheaf is the Chapter 20 owner `moduleUnderlyingSheaf`;
- primitive-vs-derived split:
  primitive data are the ringed space `X`, the module `ℱ : X.Modules`, the open `U :
  Opens X.carrier`, and the cohomology class `ξ`;
  the underlying additive sheaf and the restriction maps on cohomology are derived canonically by
  `RingedSpace.moduleUnderlyingSheaf`;
- source/core/bridge triage:
  `source-facing`: local vanishing of a positive-degree cohomology class after refining by a
  cover of `U`;
  `core/canonical`: `CategoryTheory.Sheaf.exists_cover_restrict_eq_zero_of_positive_cohomology_class`;
  `bridge/view`: this ringed-space specialization along `RingedSpace.moduleUnderlyingSheaf X`.
-/

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

local notation "AbSheaf" => moduleUnderlyingSheaf X

-- Proof sketch: represent `ξ` by a cocycle in an injective resolution of `ℱ`. In positive degree
-- exactness identifies this cocycle locally with a coboundary, so after refining to a suitable
-- cover of `U` in the opens site its restrictions vanish in cohomology on every cover arrow.
/-- Lemma 20.7.2: every positive-degree cohomology class of a sheaf of `𝒪_X`-modules on an open
subset `U` becomes zero after restricting to a suitable open covering of `U`. -/
@[stacks 01E3]
theorem exists_cover_restrict_eq_zero_of_positive_cohomology_class
    (ℱ : X.Modules) {U : Opens X.carrier} {n : ℕ} (hn : 0 < n)
    (ξ : ((AbSheaf).obj ℱ).H' n U) :
    ∃ T : (Opens.grothendieckTopology X.carrier).Cover U, ∀ I : T.Arrow,
      ((((AbSheaf).obj ℱ).cohomologyPresheaf n).map I.f.op) ξ = 0 := by
  simpa using
    CategoryTheory.Sheaf.exists_cover_restrict_eq_zero_of_positive_cohomology_class
      ((AbSheaf).obj ℱ) hn ξ

end AlgebraicGeometry.RingedSpace
