import Mathlib
import stacks_project.Chap20.Remark_20_42_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.6: the canonical morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} R\mathcal H\!\mathit{om}(M, L) \to
R\mathcal H\!\mathit{om}(M, K \otimes_{\mathcal O_X}^{\mathbf L} L)`
in `D(\mathcal O_X)`, obtained from the chapter's tensor-internal-Hom comparison by viewing the
left tensor factor `K` as `R\mathcal H\!\mathit{om}(\mathbf 1, K)` and then restricting the source
of the resulting internal Hom along the left unitor. -/
noncomputable def ringedSpaceDerivedTensorLeftInternalHomComparison
    (K L M : RingedSpaceDerived X) :
    K ⊗ (ihom M).obj L ⟶ (ihom M).obj (K ⊗ L) :=
  ((MonoidalClosed.unitIsoSelf K).inv ⊗ₘ 𝟙 ((ihom M).obj L)) ≫
    ringedSpaceDerivedTensorInternalHomComparison (𝟙_ (RingedSpaceDerived X)) K M L ≫
    (MonoidalClosed.pre (λ_ M).inv).app (K ⊗ L)

-- Proof sketch: uncurry both sides and use the naturality of the associator, braiding,
-- evaluation morphism, and `MonoidalClosed.pre`. This is the abstract monoidal-closed form of
-- the complex-level comparison from Lemma 20.41.3.
/-- Naturality of the derived tensor-internal-Hom comparison in the tensor factor, the target of
the internal Hom, and contravariantly in its source. -/
theorem ringedSpaceDerivedTensorLeftInternalHomComparison_naturality
    {K K' L L' M M' : RingedSpaceDerived X}
    (f : K ⟶ K') (g : L ⟶ L') (h : M' ⟶ M) :
    (f ⊗ₘ ((MonoidalClosed.pre h).app L ≫ (ihom M').map g)) ≫
        ringedSpaceDerivedTensorLeftInternalHomComparison K' L' M' =
      ringedSpaceDerivedTensorLeftInternalHomComparison K L M ≫
        (MonoidalClosed.pre h).app (K ⊗ L) ≫
        (ihom M').map (f ⊗ₘ g) := sorry

end

end AlgebraicGeometry.RingedSpace
