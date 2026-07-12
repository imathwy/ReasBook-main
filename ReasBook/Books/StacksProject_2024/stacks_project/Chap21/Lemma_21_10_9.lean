import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.10.9:
- primary domain: higher Čech cohomology of abelian presheaves on the slice site `(C / U, J.over
  U)` and its comparison with site cohomology of abelian sheaves, using cofinal covering systems
  closed under iterated Čech intersections inside a chosen family `B` of objects;
- sampled owner declarations:
  `Sheaf.CofinalCoveringSystem`,
  `Sheaf.HasCofinalCoveringsWithVanishingHigherCech`,
  `cechCohomology`,
  `GrothendieckTopology.CoversTop`,
  `FormalCoproduct`,
  `FormalCoproduct.mk`,
  `cechCoverIntersectionIndex`,
  `cechCoverIntersectionObject`,
  `Sheaf.H'`;
- best owner abstraction:
  `source-facing`: the Stacks hypotheses consisting of a family `B` of objects and, for each
    `U ∈ B`, a cofinal set `Cov U` of coverings of `U` whose iterated Čech intersections stay in
    `B`, packaged below as `Sheaf.CofinalCoveringSystem`; the added acyclicity hypothesis of
    Lemma 21.10.9 is the strengthening
    `Sheaf.HasCofinalCoveringsWithVanishingHigherCech`;
  `core/canonical`: the degree-`p` Čech cohomology owner `cechCohomology U family F p` together
    with the site cohomology owner `F.H' p U`;
  `bridge/view`: the chapter-wide covering-system owner `FormalCoproduct (Over U)`, its
    canonical morphism witnesses into `FormalCoproduct.mk ι family`, and the Čech intersection
    owners `cechCoverIntersectionIndex` / `cechCoverIntersectionObject`.

Primitive data versus derived API:
- primitive data: the site `(C, J)`, the basis-like subset `B ⊂ C`, the covering system
  `Cov U ⊂ FormalCoproduct (Over U)` for each `U ∈ B`, and the underlying abelian presheaf `F`;
- derived API: the canonical refinement hypothesis for the chosen covering system and the
  higher-cohomology vanishing theorem on every `U ∈ B`; the cofinality clause is phrased
  directly through the formal-coproduct owner witness
  `Nonempty (cover ⟶ FormalCoproduct.mk ι family)`, while the chosen covering system `Cov`
  itself lives in the fixed owner `FormalCoproduct.{w} (Over U)`.

Source/core/bridge triage:
- `source-facing`: the explicit cofinal-covering and higher-Čech-vanishing hypotheses in the
  theorems below;
- `core/canonical`: `cechCohomology` and `Sheaf.H'`;
- `bridge/view`: restriction along `(Over.forget U).op`, the formal-coproduct owner for covering
  systems, its canonical morphism witnesses into `FormalCoproduct.mk ι family`, and the shared
  Čech-intersection owners.

The refinement therefore keeps the source-facing cofinal-covering hypotheses in the reusable owner
`Sheaf.CofinalCoveringSystem`, records the additional higher Čech vanishing for a sheaf in the
strengthening `Sheaf.HasCofinalCoveringsWithVanishingHigherCech`, and rewrites the acyclicity
payload to the chapter owners `cechCohomology`, `FormalCoproduct`, and the shared
Čech-intersection API.
-/

namespace Sheaf

/-- A family `Cov U` of coverings of the objects `U ∈ B` is cofinal among all coverings of `U`
and is closed under iterated Čech intersections inside `B`. -/
structure CofinalCoveringSystem
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ U : C, Limits.HasFiniteProducts (Over U)]
    (B : Set C) (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop where
  coversTop :
    ∀ ⦃U : C⦄, U ∈ B → ∀ {cover : FormalCoproduct (Over U)},
      cover ∈ Cov U → (J.over U).CoversTop cover.obj
  intersections_mem :
    ∀ ⦃U : C⦄, U ∈ B → ∀ {cover : FormalCoproduct (Over U)},
      cover ∈ Cov U → ∀ n : ℕ, ∀ i : cechCoverIntersectionIndex cover n,
        cechCoverIntersectionObject cover n i ∈ B
  cofinal :
    ∀ ⦃U : C⦄, U ∈ B → ∀ ⦃ι : Type*⦄ (family : ι → Over U),
      (J.over U).CoversTop family →
        ∃ cover : FormalCoproduct (Over U),
          cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family)

namespace CofinalCoveringSystem

/-- Unfolding the cofinal-covering hypothesis yields a refining covering inside the chosen system
`Cov`. -/
theorem exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, Limits.HasFiniteProducts (Over U)]
    {B : Set C} {Cov : ∀ U : C, Set (FormalCoproduct (Over U))}
    (hCov : CofinalCoveringSystem J B Cov)
    {U : C} (hU : U ∈ B) {ι : Type*} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  hCov.cofinal hU family hfamily

end CofinalCoveringSystem

/-- A sheaf of abelian groups has a cofinal covering system indexed by `Cov` over the objects of
`B` if the chosen coverings are closed under iterated Čech intersections inside `B` and have
vanishing positive-degree Čech cohomology. -/
structure HasCofinalCoveringsWithVanishingHigherCech
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    (F : Sheaf J AddCommGrpCat.{v}) (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U))) : Prop
    extends CofinalCoveringSystem J B Cov where
  higherCech_isZero :
    ∀ ⦃U : C⦄, U ∈ B → ∀ {cover : FormalCoproduct (Over U)},
      cover ∈ Cov U → ∀ p : ℕ, 0 < p →
        IsZero
          (cechCohomology U cover.obj
            ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p)

namespace HasCofinalCoveringsWithVanishingHigherCech

/-- Unfolding the cofinal-covering hypothesis yields a refining covering inside the chosen system
`Cov`. -/
theorem exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    {F : Sheaf J AddCommGrpCat.{v}} {B : Set C}
    {Cov : ∀ U : C, Set (FormalCoproduct (Over U))}
    (hF : HasCofinalCoveringsWithVanishingHigherCech F B Cov)
    {U : C} (hU : U ∈ B) {ι : Type*} (family : ι → Over U)
    (hfamily : (J.over U).CoversTop family) :
    ∃ cover : FormalCoproduct (Over U),
      cover ∈ Cov U ∧ Nonempty (cover ⟶ FormalCoproduct.mk ι family) :=
  CofinalCoveringSystem.exists_refinement hF.toCofinalCoveringSystem hU family hfamily

end HasCofinalCoveringsWithVanishingHigherCech
end Sheaf

/-- Lemma 21.10.9: let `B` be a family of objects and, for each `U ∈ B`, let `Cov U` be a
cofinal collection of coverings of `U` such that every chosen covering and all of its iterated
Čech intersections stay in `B`. If an abelian sheaf has vanishing positive-degree Čech cohomology
for every covering in every `Cov U`, then every higher cohomology group `H^p(U, 𝓕)` with
`p > 0` vanishes for every `U ∈ B`. -/
@[stacks 03F9]
theorem higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (B : Set C)
    (Cov : ∀ U : C, Set (FormalCoproduct (Over U)))
    [∀ U : C, Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v})
    (hF : Sheaf.HasCofinalCoveringsWithVanishingHigherCech F B Cov)
    {U : C} (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

end CategoryTheory
