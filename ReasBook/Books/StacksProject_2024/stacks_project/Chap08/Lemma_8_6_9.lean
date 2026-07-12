import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryMor

/-
Domain-style sampling for Lemma 8.6.9:
- primary domain: stacks in groupoids over a site, their morphisms, and bicategorical
  `2`-fibre-product squares;
- sampled owner declarations:
  the owner homs `S₂ ⟶ S₁`,
  `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- sampled bridge/model declarations:
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the source-facing square should be organized around the stack-morphism
  owner `BicategoricalTwoCommutativeSquare F G`, with the local essential-image hypothesis stated
  directly as `F.LocallyEssentiallySurjectiveOnObjects`; the based-functor and fibred-category
  coercions are bridge/view data, while the canonical pullback square from Lemma `8.5.6` is only
  the comparison model used to prove this owner-level statement;
- primitive data: the stack morphisms `F`, `G`, `F'`, `G'`, the square `2`-isomorphism `α` on
  stack morphisms, the local essential-image hypothesis on `F`, and faithfulness of `F'`;
- derived API: transport of faithfulness across the owner `2`-cartesian square.

Source/core/bridge triage:
- `source-facing`: the faithfulness descent statement of Lemma `8.6.9`;
- `core/canonical`: the owner homs in `StackInGroupoidsOver J`,
  `FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare F G`, and `Bicategory.IsFinal`;
- `bridge/view`: coercions from stack morphisms to fibred-category morphisms and based functors,
  together with the canonical pullback square from Lemma `8.5.6`, used only as a model for the
  owner-level square statement. -/

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S₁ S₂ T₁ T₂ : StackInGroupoidsOver J}

section

variable (F : S₂ ⟶ S₁)
variable (G : T₁ ⟶ S₁)

-- Proof sketch: replace the given `2`-cartesian square by the canonical explicit `2`-fibre
-- product `S₂ ×[S₁] T₁` from Lemma `8.5.6`. For a vertical morphism `γ : y ⟶ y` in a fiber of
-- `T₁` with trivial image in `S₁`, refine the base using the local essential-image hypothesis on
-- `F` so that `G(y)` becomes locally isomorphic to some `F(x)`. This turns `(1, γ)` into a
-- vertical endomorphism of the pullback object `(x, y, f)`. Faithfulness of the left projection
-- to `S₂`, transported back across the `2`-cartesian comparison square, forces `(1, γ)` to be
-- the identity, hence `γ = 𝟙`.
/-- Lemma 8.6.9: in a `2`-cartesian square of stacks in groupoids over `(C, J)`, if every object
of every fiber of `S₁` is locally in the essential image of `F : S₂ ⟶ S₁` and
`F' : T₂ ⟶ S₂` is faithful, then `G : T₁ ⟶ S₁` is faithful. -/
theorem faithful_of_twoCartesian_of_locallyEssentiallySurjective
    (hF : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F)
    (F' : T₂ ⟶ S₂)
    (G' : T₂ ⟶ T₁)
    (α : F' ≫ F ≅ G' ≫ G)
    (hcart :
      Bicategory.IsFinal
        (⟨T₂, F', G', α⟩ : BicategoricalTwoCommutativeSquare F G))
    (hF' : F'.toBasedFunctor.Faithful) :
    G.toBasedFunctor.Faithful := sorry

end

end CategoryTheory
