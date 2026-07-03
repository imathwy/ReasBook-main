import StacksProject_2024.Chap20.Lemma_20_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.42.7:
- primary domain: the braided closed monoidal structure on `D(\mathcal O_X)`;
- sampled owner declarations:
  `RingedSpaceDerived`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry_curry`,
  `MonoidalClosed.curry_natural_left`,
  `MonoidalClosed.curry_pre_app`;
- best owner abstraction: the chapter owner `RingedSpaceDerived X`, with the coevaluation map
  obtained from the tensor-internal-Hom adjunction on that owner;
- primitive data: a ringed space `X`, a braided monoidal closed structure on
  `RingedSpaceDerived X`, and objects `K`, `L`;
- derived API: the source-facing coevaluation morphism
  `K ⟶ R\mathcal H\!\mathit{om}(L, K ⊗^{\mathbf L} L)` and its functoriality.

Source/core/bridge triage:
- `source-facing`: the textbook coevaluation morphism
  `K ⟶ R\mathcal H\!\mathit{om}(L, K ⊗^{\mathbf L} L)`;
- `core/canonical`: `MonoidalClosed.curry` together with the braided-monoidal naturality API;
- `bridge/view`: the specialization of that owner API to `RingedSpaceDerived X` and the Stacks
  Project tensor order `K ⊗ L`.
-/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.7: for objects `K, L ∈ D(\mathcal O_X)` on a ringed space `(X, \mathcal O_X)`,
there is a canonical morphism
`K \to R\mathcal H\!\mathit{om}(L, K \otimes_{\mathcal O_X}^{\mathbf L} L)`,
obtained by transporting the braiding `L \otimes_{\mathcal O_X}^{\mathbf L} K \to
K \otimes_{\mathcal O_X}^{\mathbf L} L` across the derived tensor-internal-Hom adjunction. -/
noncomputable def ringedSpaceDerivedTensorInternalHomUnit
    (K L : RingedSpaceDerived X) :
    K ⟶ (ihom L).obj (K ⊗ L) :=
  MonoidalClosed.curry ((β_ L K).hom)

/-- Uncurrying the canonical unit morphism recovers the braiding
`L \otimes_{\mathcal O_X}^{\mathbf L} K \to K \otimes_{\mathcal O_X}^{\mathbf L} L`. -/
theorem ringedSpaceDerivedTensorInternalHomUnit_spec
    (K L : RingedSpaceDerived X) :
    MonoidalClosed.uncurry (ringedSpaceDerivedTensorInternalHomUnit K L) =
      (β_ L K).hom := by
  simp [ringedSpaceDerivedTensorInternalHomUnit]

/-- The canonical morphism `K \to R\mathcal H\!\mathit{om}(L, K \otimes^{\mathbf L} L)` is
natural in the first variable `K`. -/
theorem ringedSpaceDerivedTensorInternalHomUnit_natural_left
    {K K' L : RingedSpaceDerived X} (f : K ⟶ K') :
    f ≫ ringedSpaceDerivedTensorInternalHomUnit K' L =
      ringedSpaceDerivedTensorInternalHomUnit K L ≫
        (ihom L).map (f ⊗ₘ 𝟙 L) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right,
    ringedSpaceDerivedTensorInternalHomUnit_spec, ringedSpaceDerivedTensorInternalHomUnit_spec]
  simp

/-- The canonical morphism `K \to R\mathcal H\!\mathit{om}(L, K \otimes^{\mathbf L} L)` is
natural in the second variable `L`. -/
theorem ringedSpaceDerivedTensorInternalHomUnit_natural_right
    (K : RingedSpaceDerived X) {L L' : RingedSpaceDerived X} (g : L ⟶ L') :
    ringedSpaceDerivedTensorInternalHomUnit K L' ≫
        (MonoidalClosed.pre g).app (K ⊗ L') =
      ringedSpaceDerivedTensorInternalHomUnit K L ≫
        (ihom L).map (𝟙 K ⊗ₘ g) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_right,
    ringedSpaceDerivedTensorInternalHomUnit_spec, ringedSpaceDerivedTensorInternalHomUnit_spec]
  simp

end

end AlgebraicGeometry.RingedSpace
