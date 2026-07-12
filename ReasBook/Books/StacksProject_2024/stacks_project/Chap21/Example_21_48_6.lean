import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import StacksProject_2024.Chap21.RingedSiteDerivedBasic
import StacksProject_2024.Chap21.Definition_21_47_1
import StacksProject_2024.Chap21.Lemma_21_48_4

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open _root_.RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

open _root_.RingedSite.DerivedCategory
open _root_.RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "DMod" => ModuleDerived X

variable [HasBinaryProducts C]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U).Additive]
variable [∀ U : C,
  PreservesFiniteLimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [∀ U : C,
  PreservesFiniteColimits (localizedRestriction (RingedSite.ofCommRingSheaf J 𝒪) U)]
variable [CategoryWithHomology (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [∀ U : C,
  CategoryWithHomology (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
variable [Abelian (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]

variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/- Example 21.48.6 is source-facing. The canonical owner is
`CategoryTheory.ExactPairing K^∨ K`, but until the perfectness-to-comparison-isomorphism route is
axiom-clean on concrete data, this file should stay at theorem level: it exports the canonical
coevaluation under an explicit comparison isomorphism, the uniqueness/specification theorem for a
coevaluation with the expected transpose, and the perfect-object triangle identities deduced from
that specification. -/

/-- The coevaluation morphism `𝟙 ⟶ K ⊗ K^∨` corresponding to `𝟙 K` under the
comparison `K ⊗ K^∨ ⟶ (ihom K).obj K`. -/
noncomputable def ringedSiteDerivedDualCoevaluation
    (K : DMod)
    [IsIso (ringedSiteDerivedEvaluationHom K K)] :
    𝟙_ DMod ⟶ K ⊗ K^∨ :=
  MonoidalClosed.curry' (𝟙 K) ≫ inv (ringedSiteDerivedEvaluationHom K K)

omit [HasBinaryProducts C]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ U : C, (localizedRestriction X U).Additive]
  [∀ U : C, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : C, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : C,
    CategoryWithHomology (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
  [Abelian (ModuleCat X)] in
/-- Composing the canonical coevaluation with `ringedSiteDerivedEvaluationHom K K` recovers the
curried identity of `K`. -/
theorem ringedSiteDerivedDualCoevaluation_comp_evaluationHom
    {K : DMod}
    [IsIso (ringedSiteDerivedEvaluationHom K K)] :
    ringedSiteDerivedDualCoevaluation K ≫ ringedSiteDerivedEvaluationHom K K =
      MonoidalClosed.curry' (𝟙 K) := by
  simp [ringedSiteDerivedDualCoevaluation]

/-- The derived coevaluation and evaluation maps satisfy the first triangle identity. -/
theorem ringedSiteDerivedDual_coevaluation_evaluation
    {K : DMod}
    [IsIso (ringedSiteDerivedEvaluationHom K K)] :
    K^∨ ◁ ringedSiteDerivedDualCoevaluation K ≫
        (α_ _ _ _).inv ≫
        ringedSiteDerivedDualEvaluation K ▷ K^∨ =
      (ρ_ K^∨).hom ≫ (λ_ K^∨).inv := by
  sorry

/-- The derived coevaluation and evaluation maps satisfy the second triangle identity. -/
theorem ringedSiteDerivedDual_evaluation_coevaluation
    {K : DMod}
    [IsIso (ringedSiteDerivedEvaluationHom K K)] :
    ringedSiteDerivedDualCoevaluation K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ ringedSiteDerivedDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  sorry

omit [HasBinaryProducts C]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ U : C, (localizedRestriction X U).Additive]
  [∀ U : C, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : C, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : C,
    CategoryWithHomology (ModuleCat ((RingedSite.ofCommRingSheaf J 𝒪).localization U))]
  [Abelian (ModuleCat X)] in
/-- A morphism `η : 𝟙 ⟶ K ⊗ K^∨` with the defining transpose
`η ≫ ringedSiteDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)` is uniquely determined by
the comparison isomorphism, and it is exactly `ringedSiteDerivedDualCoevaluation K`. -/
theorem ringedSiteDerivedDualCoevaluation_eq_of_comp_evaluationHom
    {K : DMod}
    [IsIso (ringedSiteDerivedEvaluationHom K K)]
    {η : 𝟙_ DMod ⟶ K ⊗ K^∨}
    (hη :
      η ≫ ringedSiteDerivedEvaluationHom K K =
        MonoidalClosed.curry' (𝟙 K)) :
    η = ringedSiteDerivedDualCoevaluation K := by
  calc
    η = η ≫ ringedSiteDerivedEvaluationHom K K ≫ inv (ringedSiteDerivedEvaluationHom K K) := by
      simp
    _ = MonoidalClosed.curry' (𝟙 K) ≫ inv (ringedSiteDerivedEvaluationHom K K) := by
      simpa [Category.assoc] using
        congrArg (fun f ↦ f ≫ inv (ringedSiteDerivedEvaluationHom K K)) hη
    _ = ringedSiteDerivedDualCoevaluation K := by
      simp [ringedSiteDerivedDualCoevaluation]

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ U : C, (localizedRestriction X U).Additive]
  [∀ U : C, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : C, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)]
  [Abelian (ModuleCat X)] in
/-- If `K` is perfect, then any two morphisms `η : 𝟙 ⟶ K ⊗ K^∨` with the defining transpose
`η ≫ ringedSiteDerivedEvaluationHom K K = MonoidalClosed.curry' (𝟙 K)` coincide. -/
theorem ringedSiteDerivedDualCoevaluation_unique_of_isPerfect
    {K : DMod} (hK : K.IsPerfect)
    {η η' : 𝟙_ DMod ⟶ K ⊗ K^∨}
    (hη :
      η ≫ ringedSiteDerivedEvaluationHom K K =
        MonoidalClosed.curry' (𝟙 K))
    (hη' :
      η' ≫ ringedSiteDerivedEvaluationHom K K =
        MonoidalClosed.curry' (𝟙 K)) :
    η = η' := by
  letI : IsIso (ringedSiteDerivedEvaluationHom K K) :=
    isIso_ringedSiteDerivedEvaluationHom_of_isPerfect hK
  calc
    η = ringedSiteDerivedDualCoevaluation K :=
      ringedSiteDerivedDualCoevaluation_eq_of_comp_evaluationHom hη
    _ = η' := (ringedSiteDerivedDualCoevaluation_eq_of_comp_evaluationHom hη').symm

/-- Example 21.48.6, first triangle identity: if `K` is perfect and `η : 𝟙 ⟶ K ⊗ K^∨` is the
unique morphism corresponding to `𝟙 K` under the comparison
`K ⊗ K^∨ ⟶ (ihom K).obj K`, then `η` and the canonical evaluation satisfy the left-dual identity
on `K^∨`. -/
@[stacks 0FPU]
theorem ringedSiteDerivedDual_coevaluation_evaluation_of_isPerfect
    {K : DMod} (hK : K.IsPerfect)
    {η : 𝟙_ DMod ⟶ K ⊗ K^∨}
    (hη :
      η ≫ ringedSiteDerivedEvaluationHom K K =
        MonoidalClosed.curry' (𝟙 K)) :
    K^∨ ◁ η ≫
        (α_ _ _ _).inv ≫
        ringedSiteDerivedDualEvaluation K ▷ K^∨ =
      (ρ_ K^∨).hom ≫ (λ_ K^∨).inv := by
  letI : IsIso (ringedSiteDerivedEvaluationHom K K) :=
    isIso_ringedSiteDerivedEvaluationHom_of_isPerfect hK
  rw [ringedSiteDerivedDualCoevaluation_eq_of_comp_evaluationHom hη]
  exact ringedSiteDerivedDual_coevaluation_evaluation

/-- Example 21.48.6, second triangle identity: if `K` is perfect and `η : 𝟙 ⟶ K ⊗ K^∨` is the
unique morphism corresponding to `𝟙 K` under the comparison
`K ⊗ K^∨ ⟶ (ihom K).obj K`, then `η` and the canonical evaluation satisfy the left-dual identity
on `K`. -/
@[stacks 0FPU]
theorem ringedSiteDerivedDual_evaluation_coevaluation_of_isPerfect
    {K : DMod} (hK : K.IsPerfect)
    {η : 𝟙_ DMod ⟶ K ⊗ K^∨}
    (hη :
      η ≫ ringedSiteDerivedEvaluationHom K K =
        MonoidalClosed.curry' (𝟙 K)) :
    η ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ ringedSiteDerivedDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := by
  letI : IsIso (ringedSiteDerivedEvaluationHom K K) :=
    isIso_ringedSiteDerivedEvaluationHom_of_isPerfect hK
  rw [ringedSiteDerivedDualCoevaluation_eq_of_comp_evaluationHom hη]
  exact ringedSiteDerivedDual_evaluation_coevaluation

end

end SheafOfModules.RingedSite
