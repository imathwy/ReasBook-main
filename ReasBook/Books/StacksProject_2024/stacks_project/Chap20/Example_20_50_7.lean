import StacksProject_2024.Chap20.Lemma_20_50_5

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

/- Domain-style sampling for Example 20.50.7:
- primary domain: rigid duality in the braided closed monoidal derived category `D(𝒪_X)`;
- sampled owner declarations:
  `ringedSpaceDerivedEvaluationHom`,
  `ringedSpaceDerivedDualEvaluation`,
  `CategoryTheory.ExactPairing`,
  `DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: Example 20.50.7 on the derived dual `K^∨` of a perfect object;
  `core/canonical`: the left-dual owner `ExactPairing K^∨ K`;
  `bridge/view`: the Chapter 20 comparison morphism `ringedSpaceDerivedEvaluationHom K K`,
    whose inverse transports `𝟙 K` to the canonical coevaluation, together with the perfectness
    specialization supplied by Lemma 20.50.5;
- primitive data: a perfect object `K` and the canonical evaluation comparison
  `K ⊗ K^∨ ⟶ K ⟹ K`;
- derived API: the coevaluation map, the generic exact pairing obtained from an isomorphism
  `ringedSpaceDerivedEvaluationHom K K`, and the two perfect-object triangle identities
  deduced from Lemma 20.50.5.

The source-facing API here remains the coevaluation map and the two perfect-object triangle
identities, while the reusable canonical owner is the exact pairing
`ringedSpaceDerivedDualExactPairingOfIsIso`. -/

/-- The canonical coevaluation `η : 𝟙 ⟶ K ⊗ K^∨` corresponding to `𝟙 K` under the comparison
`ringedSpaceDerivedEvaluationHom K K`. -/
noncomputable def ringedSpaceDerivedDualCoevaluation
    (K : DMod)
    [IsIso (ringedSpaceDerivedEvaluationHom K K)] :
    𝟙_ DMod ⟶ K ⊗ K^∨ :=
  MonoidalClosed.curry' (𝟙 K) ≫ inv (ringedSpaceDerivedEvaluationHom K K)

/-- Composing the canonical coevaluation with `ringedSpaceDerivedEvaluationHom K K` recovers the
curried identity of `K`. -/
theorem ringedSpaceDerivedDualCoevaluation_comp_evaluationHom
    {K : DMod}
    [IsIso (ringedSpaceDerivedEvaluationHom K K)] :
    ringedSpaceDerivedDualCoevaluation K ≫ ringedSpaceDerivedEvaluationHom K K =
      MonoidalClosed.curry' (𝟙 K) := by
  simp [ringedSpaceDerivedDualCoevaluation]

/-- A morphism `η : 𝟙 ⟶ K ⊗ K^∨` is the canonical coevaluation as soon as it corresponds to
`𝟙 K` under `ringedSpaceDerivedEvaluationHom K K`. -/
theorem ringedSpaceDerivedDualCoevaluation_eq_of_comp_evaluationHom
    {K : DMod}
    [IsIso (ringedSpaceDerivedEvaluationHom K K)]
    {η : 𝟙_ DMod ⟶ K ⊗ K^∨}
    (hη : η ≫ ringedSpaceDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)) :
    η = ringedSpaceDerivedDualCoevaluation K := by
  calc
    η = η ≫ ringedSpaceDerivedEvaluationHom K K ≫ inv (ringedSpaceDerivedEvaluationHom K K) := by
      simp
    _ = MonoidalClosed.curry' (𝟙 K) ≫ inv (ringedSpaceDerivedEvaluationHom K K) := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ t ≫ inv (ringedSpaceDerivedEvaluationHom K K)) hη
    _ = ringedSpaceDerivedDualCoevaluation K := rfl

/-- The derived coevaluation and evaluation maps satisfy the first triangle identity. -/
theorem ringedSpaceDerivedDual_coevaluation_evaluation
    {K : DMod}
    [IsIso (ringedSpaceDerivedEvaluationHom K K)] :
    K^∨ ◁ ringedSpaceDerivedDualCoevaluation K ≫
        (α_ _ _ _).inv ≫
        ringedSpaceDerivedDualEvaluation K ▷ K^∨ =
      (ρ_ K^∨).hom ≫ (λ_ K^∨).inv := by
  sorry

/-- The derived coevaluation and evaluation maps satisfy the second triangle identity. -/
theorem ringedSpaceDerivedDual_evaluation_coevaluation
    {K : DMod}
    [IsIso (ringedSpaceDerivedEvaluationHom K K)] :
    ringedSpaceDerivedDualCoevaluation K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ ringedSpaceDerivedDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  sorry

/-- Once `ringedSpaceDerivedEvaluationHom K K` is an isomorphism, the derived dual `K^∨`
is equipped with its canonical exact pairing with `K`. -/
@[reducible] noncomputable def ringedSpaceDerivedDualExactPairingOfIsIso
    (K : DMod)
    [IsIso (ringedSpaceDerivedEvaluationHom K K)] :
    ExactPairing K^∨ K :=
  letI : ExactPairing K K^∨ :=
    { coevaluation' := ringedSpaceDerivedDualCoevaluation K
      evaluation' := ringedSpaceDerivedDualEvaluation K
      coevaluation_evaluation' := ringedSpaceDerivedDual_coevaluation_evaluation
      evaluation_coevaluation' := ringedSpaceDerivedDual_evaluation_coevaluation }
  BraidedCategory.exactPairing_swap K K^∨

/-- For a perfect object `K`, there is a unique coevaluation
`η : 𝟙 ⟶ K ⊗ K^∨` corresponding to `𝟙 K` under the comparison morphism
`ringedSpaceDerivedEvaluationHom K K`. -/
theorem existsUnique_ringedSpaceDerivedDualCoevaluation_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    ∃! η : 𝟙_ DMod ⟶ K ⊗ K^∨,
      η ≫ ringedSpaceDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K) := by
  letI : IsIso (ringedSpaceDerivedEvaluationHom K K) :=
    isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect hK
  refine ⟨ringedSpaceDerivedDualCoevaluation K, ?_, ?_⟩
  · exact ringedSpaceDerivedDualCoevaluation_comp_evaluationHom
  · intro η hη
    exact ringedSpaceDerivedDualCoevaluation_eq_of_comp_evaluationHom hη

/-- Example 20.50.7, first triangle identity: if `K` is a perfect object of `D(𝒪_X)`, then the
coevaluation `η : 𝟙 ⟶ K ⊗ K^∨` characterized by
`η ≫ ringedSpaceDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)` and the evaluation
`ε : K^∨ ⊗ K ⟶ 𝟙` satisfy the left-dual identity on `K^∨`. -/
  @[stacks 0FPC]
  theorem ringedSpaceDerivedDual_coevaluation_evaluation_of_isPerfect
      {K : DMod} (hK : DerivedCategory.IsPerfect K)
      {η : 𝟙_ DMod ⟶ K ⊗ K^∨}
      (hη : η ≫ ringedSpaceDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)) :
    K^∨ ◁ η ≫
        (α_ _ _ _).inv ≫
        ringedSpaceDerivedDualEvaluation K ▷ K^∨ =
      (ρ_ K^∨).hom ≫ (λ_ K^∨).inv := by
  letI : IsIso (ringedSpaceDerivedEvaluationHom K K) :=
    isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect hK
  rw [ringedSpaceDerivedDualCoevaluation_eq_of_comp_evaluationHom hη]
  exact ringedSpaceDerivedDual_coevaluation_evaluation

/-- Example 20.50.7, second triangle identity: if `K` is a perfect object of `D(𝒪_X)`, then the
coevaluation `η : 𝟙 ⟶ K ⊗ K^∨` characterized by
`η ≫ ringedSpaceDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)` and the evaluation
`ε : K^∨ ⊗ K ⟶ 𝟙` satisfy the left-dual identity on `K`. -/
  @[stacks 0FPC]
  theorem ringedSpaceDerivedDual_evaluation_coevaluation_of_isPerfect
      {K : DMod} (hK : DerivedCategory.IsPerfect K)
      {η : 𝟙_ DMod ⟶ K ⊗ K^∨}
      (hη : η ≫ ringedSpaceDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)) :
    η ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ ringedSpaceDerivedDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  letI : IsIso (ringedSpaceDerivedEvaluationHom K K) :=
    isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect hK
  rw [ringedSpaceDerivedDualCoevaluation_eq_of_comp_evaluationHom hη]
  exact ringedSpaceDerivedDual_evaluation_coevaluation

end

end AlgebraicGeometry.RingedSpace
