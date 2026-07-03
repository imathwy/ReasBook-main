import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

-- Proof sketch: `u.sheafPullback AddCommGrpCat J K` is the canonical lower shriek `g_!`, hence
-- right exact because it is a left adjoint. Under the pullback and equalizer hypotheses on `u`,
-- the Chapter 7 owner API upgrades the source-style finite connected limit argument to the
-- canonical sheaf-pullback owner, yielding exactness on abelian sheaves.
/-- Lemma 18.16.3: if `u : C ⥤ D` is continuous, `C` has fibre products and equalizers, and `u`
commutes with them, then the lower shriek
`g_! : Ab(\mathcal C) ⥤ Ab(\mathcal D)`, realized in the project API as
`u.sheafPullback AddCommGrpCat J K`, is exact. The additional sheafification and Kan-extension
hypotheses are the standard Lean assumptions needed to construct this functor. -/
theorem sheafPullback_addCommGrp_exact_of_continuous_preserves_pullbacks_equalizers
    (u : C ⥤ D)
    [u.IsContinuous J K]
    [∀ ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension ℱ]
    [HasSheafify K AddCommGrpCat.{w}]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

end CategoryTheory
