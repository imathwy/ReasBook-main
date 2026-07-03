import Mathlib
import Mathlib.Algebra.Category.Grp.Limits
import stacks_project.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.10.8:
- primary domain: Čech cohomology of abelian presheaves on the slice site `(C / U, J.over U)` and
  its interaction with short exact sequences of abelian sheaves;
- sampled owner declarations:
  `cechComplex`,
  `cechCohomology`,
  `cechCohomologyDegree`,
  `cechComplexFunctor_exact`;
- best owner abstraction: the source-facing owner for the degree-`1` Čech cohomology object is the
  chapter declaration `cechCohomology U family F 1`, built from the core/canonical owner
  `cechComplexFunctor`;
- primitive data: the site `(C, J)`, the object `U`, the covering family, and the underlying
  abelian presheaf `F`;
- derived API here: the cofinal-refinement predicate and the surjectivity consequence for a short
  exact sequence of abelian sheaves.

Source/core/bridge triage:
- `source-facing`: `HasVanishingFirstCechOnCofinalCoverings` and the surjectivity lemma;
- `core/canonical`: `cechComplexFunctor` and the chapter owner `cechCohomology`;
- `bridge/view`: restriction along `(Over.forget U).op` from presheaves on `C` to presheaves on
  `Over U`.

The refinement therefore keeps the source-facing predicate, but rewrites its payload to the owner
`cechCohomology U family F 1` instead of repeating the raw homology expression.
-/

/-- A presheaf has vanishing first Čech cohomology on a cofinal collection of coverings of `U` if
every covering family of `U` admits a refinement whose first Čech cohomology vanishes. -/
def HasVanishingFirstCechOnCofinalCoverings
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{max u v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Prop :=
  ∀ {ι : Type w} (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        IsZero (cechCohomology U W F 1)

-- Proof sketch: this is just the defining expansion of
-- `HasVanishingFirstCechOnCofinalCoverings`; apply the hypothesis to the chosen covering family.
/-- Unfolding the cofinal Čech-vanishing hypothesis yields a refining covering of `U` with trivial
first Čech cohomology. -/
theorem hasVanishingFirstCechOnCofinalCoverings_exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{max u v}]
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (hF : HasVanishingFirstCechOnCofinalCoverings J U F)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        IsZero (cechCohomology U W F 1) :=
  hF V hV

-- Proof sketch: use exactness to identify local lifts of a section of `S.X₃` as a Čech
-- `1`-cocycle with values in `S.X₁`; then refine the chosen cover so that the first Čech
-- cohomology of `S.X₁` vanishes, making the cocycle a coboundary. Correct the local lifts by this
-- coboundary and glue the resulting compatible sections of `S.X₂` to a global lift over `U`.
/-- Lemma 21.10.8: if `0 ⟶ \mathcal F ⟶ \mathcal G ⟶ \mathcal H ⟶ 0` is a short exact sequence
of abelian sheaves on a site and the left term has vanishing first Čech cohomology on a cofinal
collection of coverings of `U`, then the map `\mathcal G(U) \to \mathcal H(U)` is surjective. -/
theorem shortExact_right_map_surjective_of_vanishingFirstCech_on_cofinal_coverings
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{max u v}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (hS : S.ShortExact)
    (hcech :
      HasVanishingFirstCechOnCofinalCoverings J U
        ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj S.X₁)) :
    Function.Surjective (S.g.app (op U)) := sorry

end CategoryTheory
