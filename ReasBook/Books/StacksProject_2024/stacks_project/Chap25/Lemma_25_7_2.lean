import Mathlib
import StacksProject_2024.stacks_project.Chap25.Lemma_25_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: `lean_leansearch` recalled mathlib's `GrothendieckTopology.OneHypercover.inter`
-- as the canonical one-hypercover analogue. The source item here is the local fixed-target
-- Chapter 25 owner `Hypercovering (J := J) X`, so the statement is exposed as the product
-- simplicial object in `SR(C, X)`.

namespace Hypercovering

/-- The degree-`0` family of the product simplicial object of two hypercoverings is covering. -/
private theorem prod_zero_isCovering
    {X : C}
    (K L : @Hypercovering C _ J X) :
    ((K.toSimplicialObject ⨯ L.toSimplicialObject).obj (op <| SimplexCategory.mk 0)).toSieve ∈
      J X := sorry

/-- Each higher matching map of the product simplicial object of two hypercoverings is covering.
-/
private theorem prod_succ_isCovering
    {X : C}
    (K L : @Hypercovering C _ J X)
    (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Hom.IsCovering J (matchingMap (K.toSimplicialObject ⨯ L.toSimplicialObject) n) := sorry

/-- Lemma 25.7.2: if `K` and `L` are hypercoverings of `X` on a site with fibre products, then
their product `K × L` is again a hypercovering of `X`. -/
@[stacks 01GI]
noncomputable def prod
    {X : C}
    (K L : @Hypercovering C _ J X) :
    @Hypercovering C _ J X where
  toSimplicialObject := K.toSimplicialObject ⨯ L.toSimplicialObject
  zero_isCovering := prod_zero_isCovering K L
  succ_isCovering := prod_succ_isCovering K L

/-- The hypercovering `prod K L` has underlying simplicial object `K.toSimplicialObject ×
L.toSimplicialObject`. -/
theorem prod_toSimplicialObject
    {X : C}
    (K L : @Hypercovering C _ J X) :
    (prod K L).toSimplicialObject = (K.toSimplicialObject ⨯ L.toSimplicialObject) := sorry

end Hypercovering

end CategoryTheory
