import StacksProject_2024.Chap20.«20_42_8_1»

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

/-- Lemma 20.42.8: for `L, M ∈ D(\mathcal O_X)`, the canonical morphism
`M \otimes_{\mathcal O_X}^{\mathbf L} L^\vee \to R\mathcal H\!\mathit{om}(L, M)` from
`20.42.8.1` induces a canonical map
`H^0(X, M \otimes_{\mathcal O_X}^{\mathbf L} L^\vee) \to \operatorname{Hom}_{D(\mathcal O_X)}(L, M)`.
In Lean, `H^0(X, K)` is modeled by morphisms `𝟙_ (RingedSpaceDerived X) ⟶ K`, where the monoidal unit is the
structure sheaf `\mathcal O_X` in `D(\mathcal O_X)`. -/
noncomputable def ringedSpaceDerivedEvaluationH0ToHom
    (L M : RingedSpaceDerived X) :
    (𝟙_ (RingedSpaceDerived X) ⟶ M ⊗ L^∨) → (L ⟶ M) :=
  fun s ↦
    (ρ_ L).inv ≫
      MonoidalClosed.uncurry (s ≫ ringedSpaceDerivedEvaluationHom L M)

-- Proof sketch: postcompose a class `𝟙 ⟶ M ⊗ L^\vee` with the evaluation morphism
-- `M ⊗ L^\vee ⟶ R\mathcal H\!\mathit{om}(L, M)`, then uncurry to a morphism
-- `L ⊗ 𝟙 ⟶ M` and transport across the right unitor `L ⊗ 𝟙 ≅ L`. Naturality in `M` comes from
-- functoriality of the evaluation morphism in its target variable together with naturality of
-- uncurrying.
/-- The induced map on `H^0(X, -)` is functorial in the target object `M`. -/
theorem ringedSpaceDerivedEvaluationH0ToHom_natural
    {L M M' : RingedSpaceDerived X} (f : M ⟶ M')
    (s : 𝟙_ (RingedSpaceDerived X) ⟶ M ⊗ L^∨) :
    ringedSpaceDerivedEvaluationH0ToHom L M' (s ≫ (f ⊗ₘ 𝟙 L^∨)) =
      ringedSpaceDerivedEvaluationH0ToHom L M s ≫ f := sorry

end

end AlgebraicGeometry.RingedSpace
