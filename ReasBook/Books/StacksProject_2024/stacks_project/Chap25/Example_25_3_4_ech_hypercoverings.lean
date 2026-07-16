import StacksProject_2024.stacks_project.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- Semantic search note: no `lean_leansearch` tool was available in this run; the owner choice
-- uses the local `Hypercovering`/`matchingMap` API from `Lemma_25_3_7` and the existing
-- formal-coproduct Čech simplicial object whose degreewise terms are the usual iterated fiber
-- products over `X`.
--
-- Source/core/bridge triage for Example 25.3.4:
-- `source-facing`: the proof that the Čech simplicial object attached to a covering family `𝒰`
--   satisfies the hypercovering conditions;
-- `core/canonical`: the Chapter 25 matching-map owner `matchingMap` together with the canonical
--   formal-coproduct Čech object `(toFormalCoproduct.obj 𝒰).cech`;
-- `bridge/view`: the fixed-target simplicial object `cechSimplicial 𝒰`.

private instance hasFiniteProductsOver (X : C) : HasFiniteProducts (Over X) := by
  let _ : HasBinaryProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  exact hasFiniteProducts_of_has_binary_and_terminal

namespace SemiRepresentableFamily
namespace Over

/-- The Čech simplicial object attached to a fixed-target family over `X`, whose degreewise terms
are the usual iterated fiber products over `X`. When `𝒰` is covering, this is the simplicial
object underlying the Čech hypercovering `Hypercovering.cech 𝒰 h𝒰`. -/
noncomputable def cechSimplicial {X : C} (𝒰 : SR(C, X)) :
    SimplicialObject (SR(C, X)) :=
  (toFormalCoproduct.obj 𝒰).cech ⋙ ofFormalCoproduct

/-- The degree-`0` term of the Čech simplicial object of `𝒰` generates the same sieve as `𝒰`. -/
@[simp] theorem cechSimplicial_zero_toSieve {X : C} (𝒰 : SR(C, X)) :
    ((cechSimplicial 𝒰).obj (op <| SimplexCategory.mk 0)).toSieve = 𝒰.toSieve := sorry

/-- The degree-`0` term of the Čech simplicial object of `𝒰` is covering whenever `𝒰` is. -/
theorem cechSimplicial_zero_isCovering {X : C} (𝒰 : SR(C, X)) (h𝒰 : 𝒰.toSieve ∈ J X) :
    ((cechSimplicial 𝒰).obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X := by
  rw [cechSimplicial_zero_toSieve]
  exact h𝒰

/-- Every higher matching map of the Čech simplicial object of `𝒰` is covering. Equivalently, the
Čech simplicial object is `0`-coskeletal. -/
theorem cechSimplicial_succ_isCovering {X : C} (𝒰 : SR(C, X)) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Hom.IsCovering J (matchingMap (cechSimplicial 𝒰) n) := sorry

end Over
end SemiRepresentableFamily

namespace Hypercovering

variable {X : C}

/-- The hypercovering attached to a covering family `𝒰` by its Čech simplicial object. -/
noncomputable def cech (𝒰 : SR(C, X)) (h𝒰 : 𝒰.toSieve ∈ J X) :
    Hypercovering J X where
  toSimplicialObject := cechSimplicial 𝒰
  zero_isCovering := cechSimplicial_zero_isCovering 𝒰 h𝒰
  succ_isCovering := cechSimplicial_succ_isCovering 𝒰

end Hypercovering

namespace SemiRepresentableFamily
namespace Over

/-- Example 25.3.4 (Čech hypercoverings): the Čech simplicial object attached to a covering family
`𝒰` over `X` is a hypercovering of `X`. -/
@[stacks 01G6]
noncomputable def cechHypercovering {X : C} (𝒰 : SR(C, X))
    (h𝒰 : 𝒰.toSieve ∈ J X) :
    Hypercovering J X :=
  Hypercovering.cech 𝒰 h𝒰

end Over
end SemiRepresentableFamily

end CategoryTheory
