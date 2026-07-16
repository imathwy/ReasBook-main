import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap21.Lemma_21_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : FibredCategoryOver.{u, v, max u v, max u v} C)

/-
Domain-style sampling for Lemma 21.40.2:
- primary domain: left derived lower shriek on abelian sheaves over the inherited site of a
  fibred category, identified with the fiberwise category-homology sheaf from Lemma `21.40.1`;
- sampled owner declarations:
  `Functor.sheafPullback`,
  `Functor.leftDerived`,
  `CategoryTheory.FibredCategoryOver.lowerShriek_is_sheafification_of_fiberwiseColimitPresheaf`,
  `CategoryTheory.FibredCategoryOver.fiberCategoryHomologySheafOfSheaf`;
- best owner abstraction: the source-facing object on the right is already the chapter owner
  `fiberCategoryHomologySheafOfSheaf J P`, while the left side should stay centered on the
  canonical derived lower shriek `L_n π_!`, built from the canonical lower-shriek functor
  `P.p.sheafPullback AddCommGrpCat (inheritedTopology J P) J`;
- primitive data: the projection `P.p`, the inherited topology `inheritedTopology J P`, the sheaf
  `ℱ`, the continuity of `P.p`, and the
  projective-preservation hypothesis for the chapter owner `fiberPullbackPrecomp P f`;
- derived API: the comparison isomorphism below between the canonical left-derived lower shriek
  value `(((P.p.sheafPullback AddCommGrpCat Jₚ J).leftDerived n).obj ℱ)` and
  `fiberCategoryHomologySheafOfSheaf J P ℱ n`; as in nearby Chapter 21 files, this source-facing
  comparison is kept at the proposition-level owner `IsIsomorphic` until the concrete comparison
  morphism is exported.

Source/core/bridge triage:
- `source-facing`: `projectionLowerShriek_leftDerived_iso_fiberCategoryHomologySheaf`;
- `core/canonical`: `Functor.sheafPullback`, `Functor.leftDerived`, and
  `fiberCategoryHomologySheafOfSheaf J P`;
- `bridge/view`: the projective-preservation instance for fiberwise pullback precomposition. -/

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (inheritedTopology J P) AddCommGrpCat.{max u v}]
variable [∀ V : C, HasProjectiveResolutions ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]
variable [Functor.IsContinuous P.p (inheritedTopology J P) J]
variable [HasProjectiveResolutions (Sheaf (inheritedTopology J P) AddCommGrpCat.{max u v})]
variable [∀ ⦃U V : C⦄ (f : V ⟶ U), (fiberPullbackPrecomp P f).PreservesProjectiveObjects]

local notation "Jₚ" => inheritedTopology J P

variable [hLowerShriekAdditive :
  (P.p.sheafPullback AddCommGrpCat.{max u v} (inheritedTopology J P) J).Additive]

-- Proof sketch: for `n = 0`, this is Lemma `21.38.8`, which identifies `π_! ℱ` with the
-- sheafification of the fiberwise colimit presheaf, i.e. with `L_0(ℱ)`. Lemma `21.40.1` and the
-- vanishing argument from the Stacks proof show that
-- `n ↦ L_n(ℱ)` forms the universal delta functor
-- extending degree zero, so uniqueness of universal delta functors identifies it with the left
-- derived functors of `π_!`. The public surface is theorem-level `IsIsomorphic`, rather than a
-- concrete `Iso`, until the comparison morphism itself is constructed.
/-- Lemma 21.40.2: for a fibred category `P` over a Grothendieck site `J`, an abelian sheaf `ℱ`
on the inherited total site, and `n ≥ 0`, the `n`-th left derived functor
`L_n π_!(ℱ)` of the abelian lower shriek is canonically isomorphic to the source-facing
sheaf `L_n(ℱ)` constructed in Lemma `21.40.1`. -/
@[stacks 08PJ]
theorem projectionLowerShriek_leftDerived_iso_fiberCategoryHomologySheaf
    (ℱ : Sheaf Jₚ AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIsomorphic
      (((P.p.sheafPullback AddCommGrpCat.{max u v} Jₚ J).leftDerived n).obj ℱ)
      (fiberCategoryHomologySheafOfSheaf J P ℱ n) := by
  sorry

end

end FibredCategoryOver
end CategoryTheory
