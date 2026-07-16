import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import StacksProject_2024.stacks_project.Chap21.Lemma_21_10_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe wI v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Sheaf

section CofinalFiniteCoverings

variable {J : GrothendieckTopology C}
variable [∀ U : C, Limits.HasFiniteProducts (Over U)]

/- Domain-style sampling for Lemma 21.16.1:
- primary domain: filtered colimits in abelian sheaves on a site, objectwise cohomology via
  `cohomologyPresheafFunctor`, and cofinal finite covering systems stable under iterated Čech
  intersections;
- sampled owner declarations:
  `Sheaf.CofinalCoveringSystem`,
  `CofinalFiniteCoverings`,
  `colimit.post`,
  `cohomologyPresheafFunctor`,
  `cechCoverIntersectionIndex`,
  `cechCoverIntersectionObject`;
- best owner abstraction: the comparison morphism is already the canonical
  `colimit.post ℱ (cohomologyPresheafFunctor J p)`, while the site-theoretic covering hypothesis
  is the source-facing finite-cover strengthening of the shared owner
  `Sheaf.CofinalCoveringSystem`.

Source/core/bridge triage:
- `source-facing`: `CofinalFiniteCoverings` and the theorem below;
- `core/canonical`: `colimit.post` and `cohomologyPresheafFunctor`;
- `bridge/view`: the inherited chapter-wide cofinal-cover owner
  `Sheaf.CofinalCoveringSystem` and the Čech-intersection owners from `Definition_21_8_1`.

Primitive data versus derived API:
- primitive data: the basis-like collection `B`, the selected covering system `Cov`, and the
  filtered diagram `ℱ`;
- derived API: the cohomology comparison morphism, already supplied canonically by `colimit.post`.
-/

/-- The site-theoretic hypothesis that `B` admits a cofinal system `Cov` of finite coverings whose
members lie in `B`; this strengthens `Sheaf.CofinalCoveringSystem J B Cov` by adding finiteness
and target membership in `B`, while memberwise basis membership remains a derived companion lemma
from the inherited Čech-intersection closure. -/
structure CofinalFiniteCoverings
    (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop
    extends Sheaf.CofinalCoveringSystem J B Cov where
  finite : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → Finite cover.I
  target_mem : ∀ ⦃U : C⦄ (cover : FormalCoproduct (Over U)),
    cover ∈ Cov U → U ∈ B

namespace CofinalFiniteCoverings

/-- Every member of a chosen covering lies in `B`; this is the degree-`0` case of the inherited
Čech-intersection closure. -/
theorem members_mem
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct (Over U))}
    (hCov : CofinalFiniteCoverings J B Cov)
    {U : C} {cover : FormalCoproduct (Over U)} (hcover : cover ∈ Cov U) (i : cover.I) :
    (cover.obj i).left ∈ B := sorry

/-- Unfolding `CofinalFiniteCoverings J B Cov` yields a refining covering inside the chosen finite
system `Cov`. -/
theorem exists_refinement
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct (Over U))}
    (hCov : CofinalFiniteCoverings J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type*} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  Sheaf.CofinalCoveringSystem.exists_refinement hCov.toCofinalCoveringSystem hU family hfamily

end CofinalFiniteCoverings
end CofinalFiniteCoverings

section ColimitComparison

variable {J : GrothendieckTopology C}
variable {I : Type wI} [Category.{wI} I] [IsFiltered I]
variable [∀ U : C, Limits.HasFiniteProducts (Over U)]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Sheaf J AddCommGrpCat.{v})]
variable [HasColimitsOfShape I (Cᵒᵖ ⥤ AddCommGrpCat.{v})]

-- Proof sketch: argue by induction on `p`. For `p = 0`, the chosen finite cofinal coverings force
-- the objects of `B` to satisfy the quasi-compactness criterion used to commute sections with
-- filtered colimits. For the inductive step, embed the filtered diagram into a filtered diagram of
-- injective sheaves, use exactness of filtered colimits to pass to cokernels, and reduce via the
-- long exact cohomology sequence. The injective-colimit term is acyclic in positive degree because
-- the finite chosen coverings keep all Čech intersections inside `B`, so degree-zero commutation
-- identifies the Čech complex of the colimit with the filtered colimit of the injective Čech
-- complexes, which are acyclic by Lemma `21.10.2`; then Lemma `21.10.9` upgrades this Čech
-- vanishing to vanishing of higher cohomology over every `U ∈ B`.
/-- Lemma 21.16.1: let `B` be a collection of objects of the site `(𝒞, J)` and, for each
`U`, let `Cov` be a set of coverings of `U` formalized as a set of `FormalCoproduct (Over U)`.
Assume that every selected covering in `Cov` is finite, has target in `B`, all of its members lie
in `B`, and every iterated Čech intersection of its members lies in `B`. Assume moreover that for
every `U ∈ B`, the coverings of `U` occurring in `Cov` form a cofinal system among all coverings
of `U`. Then for every filtered diagram of abelian sheaves, every `p : ℕ`, and every `U ∈ B`, the
canonical map `colim_i H^p(U, 𝓕_i) ⟶ H^p(U, colim_i 𝓕_i)` is an isomorphism. -/
@[stacks 0739]
theorem cohomologyOverColimitComparison_isIso_of_cofinal_finite_coverings
    (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    (hCov : CofinalFiniteCoverings J B Cov)
    (ℱ : I ⥤ Sheaf J AddCommGrpCat.{v}) (p : ℕ) {U : C} (hU : U ∈ B) :
    IsIso ((colimit.post ℱ (cohomologyPresheafFunctor J p)).app (op U)) := sorry

end ColimitComparison
end Sheaf
end CategoryTheory
