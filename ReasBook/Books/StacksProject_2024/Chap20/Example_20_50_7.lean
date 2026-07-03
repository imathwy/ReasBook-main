import Mathlib
import StacksProject_2024.Chap20.Lemma_20_50_5

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
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- The canonical morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee \to R\mathcal H\!\mathit{om}(K, K)` attached to the
derived dual `K^\vee = R\mathcal H\!\mathit{om}(K, \mathcal O_X)`. -/
noncomputable abbrev ringedSpaceDerivedDualTensorToEnd
    (K : DMod) :
    K ⊗ ringedSpaceDerivedDual K ⟶ (ihom K).obj K :=
  ringedSpaceDerivedEvaluationHom K K

-- Proof sketch: this is Lemma `20.50.5 (3)` specialized to `M = K`: for a perfect object, the
-- canonical tensor-to-internal-Hom comparison is an isomorphism, hence in particular so is the
-- tensor-to-endomorphism morphism.
/-- For a perfect object, the canonical morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee \to R\mathcal H\!\mathit{om}(K, K)` is an
isomorphism. -/
theorem ringedSpaceDerivedDualTensorToEnd_isIso_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedDualTensorToEnd K) := by
  simpa [ringedSpaceDerivedDualTensorToEnd] using
    isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect (K := K) (M := K) hK

/-- The evaluation morphism
`\epsilon : K^\vee \otimes_{\mathcal O_X}^{\mathbf L} K \to \mathcal O_X`. -/
noncomputable def ringedSpaceDerivedDualEvaluation
    (K : DMod) :
    ringedSpaceDerivedDual K ⊗ K ⟶ 𝟙_ DMod :=
  (β_ (ringedSpaceDerivedDual K) K).hom ≫
    MonoidalClosed.uncurry (𝟙 (ringedSpaceDerivedDual K))

/-- The coevaluation morphism
`\eta : \mathcal O_X \to K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee` corresponding to
`\mathrm{id}_K` under the tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSpaceDerivedDualCoevaluation
    (K : DMod)
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    𝟙_ DMod ⟶ K ⊗ ringedSpaceDerivedDual K :=
  MonoidalClosed.curry' (𝟙 K) ≫
    inv (ringedSpaceDerivedDualTensorToEnd K)

-- Proof sketch: transport the identity morphism of `K^\vee` across the adjunction defining
-- `ringedSpaceDerivedDualCoevaluation`. After composing with the inverse of the
-- tensor-to-endomorphism isomorphism, the composite reduces to the first triangle identity.
/-- The derived coevaluation and evaluation maps satisfy the first triangle identity. -/
theorem ringedSpaceDerivedDual_coevaluation_evaluation
    {K : DMod}
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    ringedSpaceDerivedDual K ◁ ringedSpaceDerivedDualCoevaluation K ≫
        (α_ _ _ _).inv ≫
        ringedSpaceDerivedDualEvaluation K ▷ ringedSpaceDerivedDual K =
      (ρ_ (ringedSpaceDerivedDual K)).hom ≫
        (λ_ (ringedSpaceDerivedDual K)).inv := sorry

-- Proof sketch: transport the identity morphism of `K` through the same tensor-to-endomorphism
-- isomorphism. The adjunction formulas for `curry'` and `uncurry` then give the second triangle
-- identity.
/-- The derived coevaluation and evaluation maps satisfy the second triangle identity. -/
theorem ringedSpaceDerivedDual_evaluation_coevaluation
    {K : DMod}
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    ringedSpaceDerivedDualCoevaluation K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ ringedSpaceDerivedDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := sorry

/-- The derived dual together with the canonical coevaluation and evaluation maps gives a left
dual once the tensor-to-endomorphism morphism is an isomorphism. -/
@[reducible] noncomputable def ringedSpaceDerivedDualExactPairingOfIsIso
    (K : DMod)
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    ExactPairing K (ringedSpaceDerivedDual K) :=
  { coevaluation' := ringedSpaceDerivedDualCoevaluation K
    evaluation' := ringedSpaceDerivedDualEvaluation K
    coevaluation_evaluation' := ringedSpaceDerivedDual_coevaluation_evaluation
    evaluation_coevaluation' := ringedSpaceDerivedDual_evaluation_coevaluation }

/-- Example 20.50.7: if `K` is a perfect object of `D(\mathcal O_X)`, then the derived dual
`K^\vee = R\mathcal H\!\mathit{om}(K, \mathcal O_X)`, together with the coevaluation
`\eta : \mathcal O_X \to K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee` corresponding to
`\mathrm{id}_K` under the isomorphism
`K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee \cong R\mathcal H\!\mathit{om}(K, K)` and the
evaluation map `\epsilon : K^\vee \otimes_{\mathcal O_X}^{\mathbf L} K \to \mathcal O_X`, is a
left dual of `K`. In Lean this left-duality datum is packaged by
`CategoryTheory.ExactPairing`. -/
noncomputable abbrev ringedSpaceDerivedDualExactPairing
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    ExactPairing K (ringedSpaceDerivedDual K) :=
  letI : IsIso (ringedSpaceDerivedDualTensorToEnd K) :=
    ringedSpaceDerivedDualTensorToEnd_isIso_of_isPerfect hK
  ringedSpaceDerivedDualExactPairingOfIsIso K

-- Proof sketch: unfold `ringedSpaceDerivedDualExactPairing`; after introducing the local `IsIso`
-- instance coming from perfectness, the coevaluation field of the packaged `ExactPairing` is
-- definitionally `ringedSpaceDerivedDualCoevaluation K`.
/-- The coevaluation of the exact pairing from Example 20.50.7 is the canonical coevaluation map
attached to the derived dual. -/
theorem ringedSpaceDerivedDualExactPairing_coevaluation
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    letI : IsIso (ringedSpaceDerivedDualTensorToEnd K) :=
      ringedSpaceDerivedDualTensorToEnd_isIso_of_isPerfect hK
    @ExactPairing.coevaluation _ _ _ K (ringedSpaceDerivedDual K)
        (ringedSpaceDerivedDualExactPairing hK) =
      ringedSpaceDerivedDualCoevaluation K := sorry

-- Proof sketch: unfold `ringedSpaceDerivedDualExactPairing`; the evaluation field of the
-- packaged `ExactPairing` is definitionally `ringedSpaceDerivedDualEvaluation K`.
/-- The evaluation of the exact pairing from Example 20.50.7 is the canonical evaluation map
attached to the derived dual. -/
theorem ringedSpaceDerivedDualExactPairing_evaluation
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    @ExactPairing.evaluation _ _ _ K (ringedSpaceDerivedDual K)
        (ringedSpaceDerivedDualExactPairing hK) =
      ringedSpaceDerivedDualEvaluation K := sorry

end

end AlgebraicGeometry.RingedSpace
