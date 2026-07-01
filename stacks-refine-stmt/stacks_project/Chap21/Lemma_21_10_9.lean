import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/-- A presheaf has vanishing higher Čech cohomology on a cofinal collection of coverings of `U` if
every covering family of `U` admits a refinement whose positive-degree Čech cohomology vanishes. -/
def HasVanishingHigherCechOnCofinalCoverings
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ {ι : Type w} (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        ∀ (p : ℕ), 0 < p →
          IsZero
            ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
              ((cechComplexFunctor W).obj ((Over.forget U).op ⋙ F)))

-- Proof sketch: this is just the defining expansion of
-- `HasVanishingHigherCechOnCofinalCoverings`; apply the hypothesis to the chosen covering family.
/-- Unfolding the cofinal higher Čech-vanishing hypothesis yields a refining covering of `U`
whose positive-degree Čech cohomology is trivial in every degree. -/
theorem hasVanishingHigherCechOnCofinalCoverings_exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hF : HasVanishingHigherCechOnCofinalCoverings J U F)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Nonempty
          ((FormalCoproduct.mk κ W : FormalCoproduct (Over U)) ⟶
            (FormalCoproduct.mk ι V : FormalCoproduct (Over U))) ∧
        ∀ (p : ℕ), 0 < p →
          IsZero
            ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
              ((cechComplexFunctor W).obj ((Over.forget U).op ⋙ F))) := sorry

-- Proof sketch: embed `F` into an injective abelian sheaf `ℐ`, let `ℚ := ℐ/F`, and use
-- Lemma `21.10.8` degreewise on the short exact sequence
-- `0 ⟶ F ⟶ ℐ ⟶ ℚ ⟶ 0` to make sections exact over `U`. The long exact sequence in Čech
-- cohomology shows that `ℚ` again satisfies the same cofinal higher Čech-vanishing hypothesis,
-- while injectivity of `ℐ` gives vanishing of `H^n(U, ℐ)` for `n > 0`. Induct on `p` through the
-- long exact cohomology sequence of `0 ⟶ F ⟶ ℐ ⟶ ℚ ⟶ 0`.
/-- Lemma 21.10.9: if an abelian sheaf on a site has vanishing higher Čech cohomology on a
cofinal collection of coverings of `U`, then every higher cohomology group `H^p(U, \mathcal F)`
with `p > 0` is zero. -/
theorem higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)] [Limits.HasProducts AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v})
    (hF :
      HasVanishingHigherCechOnCofinalCoverings J U
        ((sheafToPresheaf J AddCommGrpCat.{v}).obj F))
    (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

end CategoryTheory
