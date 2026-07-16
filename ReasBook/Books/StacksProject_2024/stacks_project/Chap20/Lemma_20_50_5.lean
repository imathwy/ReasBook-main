import StacksProject_2024.stacks_project.Chap20.Lemma_20_42_8
import StacksProject_2024.stacks_project.Chap20.Lemma_20_50_4

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

local notation "DMod" => RingedSpaceDerived X

/- Domain-style sampling for Lemma 20.50.5:
- primary domain: perfect objects and duality in the braided closed monoidal derived category
  `D(𝒪_X)`;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ringedSpaceDerivedDual`,
  `MonoidalClosed.unitIsoSelf`,
  `ringedSpaceDerivedEvaluationHom`,
  `ringedSpaceDerivedEvaluationH0ToHom`,
  `isIso_tensorInternalHomToIteratedInternalHom_of_isPerfect`;
- best owner abstraction:
  the source-facing ringed-space duality statements should be expressed directly on the canonical
  owners `DerivedCategory.IsPerfect`, `ringedSpaceDerivedDual`, and the Chapter 20
  tensor/internal-Hom comparison API, with the bidual comparison exposed directly as the adjoint
  transpose of the canonical evaluation morphism instead of being left implicit in prose, and
  without introducing extra packaging around the evaluation comparisons;
- primitive data:
  the object `K` (and `M` for parts `(3)` and `(4)`), together with the perfectness hypothesis
  `K.IsPerfect`;
- derived API:
  the source-facing bidual comparison, its `IsIso` consequence, the evaluation comparison
  isomorphism, and the induced bijection on `H^0`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.50.5 itself;
- `core/canonical`: `DerivedCategory.IsPerfect`, `ringedSpaceDerivedDual`,
  `ringedSpaceDerivedEvaluationHom`, `ringedSpaceDerivedEvaluationH0ToHom`,
  `tensorInternalHomToIteratedInternalHom`, `ringedSpaceDerivedDualEvaluation`, and
  `MonoidalClosed.curry`;
- `bridge/view`: the perfectness result for `ringedSpaceDerivedBidualComparison K` is obtained by
  comparing this source-facing bidual map with the tensor-unit specialization
  `tensorInternalHomToIteratedInternalHom K (𝟙_ DMod) (𝟙_ DMod)`. -/

-- Proof sketch: work locally on `X` and replace `K` by a strictly perfect representative. The
-- termwise dual complex is again strictly perfect, hence represents the derived dual, so the dual
-- object is perfect locally and therefore perfect.
/-- Lemma 20.50.5 (1): if `K` is a perfect object of `D(𝒪_X)`, then its derived dual
`K^∨ = RHom(K, 𝒪_X)` is perfect. -/
@[stacks 08DQ]
theorem isPerfect_derivedDual_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect K^∨ := sorry

-- Proof sketch: transpose the canonical evaluation morphism
-- `K^∨ ⊗[𝒪_X]^L K ⟶ 𝒪_X` across the closed monoidal
-- adjunction. This is the source-facing bidual map; its perfectness-isomorphism property is then
-- read from the Chapter 20 tensor/internal-Hom comparison specialized to the tensor unit.
/-- Lemma 20.50.5 (2): the canonical bidual comparison
`K ⟶ (K^∨)^∨`. -/
@[stacks 08DQ]
noncomputable abbrev ringedSpaceDerivedBidualComparison
    (K : DMod) :
    K ⟶ (K^∨)^∨ :=
  MonoidalClosed.curry (ringedSpaceDerivedDualEvaluation K)

/-
Uncurrying the canonical bidual comparison recovers the canonical evaluation morphism
`K^∨ ⊗ K ⟶ 𝟙`.
-/
@[simp] theorem ringedSpaceDerivedBidualComparison_uncurry
    (K : DMod) :
    MonoidalClosed.uncurry (ringedSpaceDerivedBidualComparison K) =
      ringedSpaceDerivedDualEvaluation K := by
  simp [ringedSpaceDerivedBidualComparison]

/-- Lemma 20.50.5 (2): if `K` is a perfect object of `D(𝒪_X)`, then the canonical
bidual comparison `K ⟶ (K^∨)^∨` is an isomorphism. -/
@[stacks 08DQ]
instance isIso_ringedSpaceDerivedBidualComparison_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedBidualComparison K) := by
  sorry

-- Proof sketch: first apply part `(1)` to see that `K^∨` is perfect. Then specialize the owner
-- theorem `20.50.4` to the perfect object `K^∨` and `L = 𝟙_ DMod`; this gives an
-- isomorphism `M ⊗[𝒪_X]^L K^∨ ⟶ RHom((K^∨)^∨, M)`. Finally, transport across the
-- bidual comparison isomorphism from part `(2)` to identify the target with
-- `RHom(K, M)`.
/-- Lemma 20.50.5 (3): if `K` is a perfect object of `D(𝒪_X)`, then for every
`M ∈ D(𝒪_X)` the canonical morphism
`M ⊗[𝒪_X]^L K^∨ ⟶ RHom(K, M)` is an
isomorphism. -/
@[stacks 08DQ]
instance isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect
    {K M : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedEvaluationHom K M) := by
  sorry

-- Proof sketch: `ringedSpaceDerivedEvaluationH0ToHom K M` is the composite of postcomposition by
-- `ringedSpaceDerivedEvaluationHom K M` with the canonical owner bijection
-- `MonoidalClosed.uncurry' : (𝟙_ DMod ⟶ (K ⟹ M)) → (K ⟶ M)`. Once part `(3)` identifies
-- `ringedSpaceDerivedEvaluationHom K M` as an isomorphism, both factors are bijective.
/-- Lemma 20.50.5 (4): if `K` is a perfect object of `D(𝒪_X)`, then for every
`M ∈ D(𝒪_X)` the canonical map
`H^0(X, M ⊗[𝒪_X]^L K^∨) → (K ⟶ M)` is bijective. In Lean, `H^0(X, -)` is modeled by
morphisms from the monoidal unit `𝟙_ DMod`. -/
@[stacks 08DQ] theorem bijective_ringedSpaceDerivedEvaluationH0ToHom_of_isPerfect
    {K M : DMod} (hK : DerivedCategory.IsPerfect K) :
    Function.Bijective (ringedSpaceDerivedEvaluationH0ToHom K M) := by
  letI : IsIso (ringedSpaceDerivedEvaluationHom K M) :=
    isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect hK
  let postcompEquiv : (𝟙_ DMod ⟶ M ⊗ K^∨) ≃ (𝟙_ DMod ⟶ (ihom K).obj M) :=
    { toFun := fun s ↦ s ≫ ringedSpaceDerivedEvaluationHom K M
      invFun := fun t ↦ t ≫ inv (ringedSpaceDerivedEvaluationHom K M)
      left_inv := by
        intro s
        simp [Category.assoc]
      right_inv := by
        intro t
        simp [Category.assoc] }
  refine ⟨?_, ?_⟩
  · intro s t hst
    apply postcompEquiv.injective
    apply MonoidalClosed.uncurry'_injective
    simpa [postcompEquiv] using hst
  · intro f
    refine ⟨postcompEquiv.symm (MonoidalClosed.curry' f), ?_⟩
    simp [postcompEquiv]

end

end AlgebraicGeometry.RingedSpace
