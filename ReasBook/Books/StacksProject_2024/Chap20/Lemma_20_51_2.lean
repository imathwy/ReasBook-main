import StacksProject_2024.Chap20.Example_20_50_7

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

-- Proof sketch: the top arrow sends a pair of degree-zero classes to their tensor product, the
-- left arrow is the canonical map `H^0(X, K ⊗ E^\vee) → Hom(E, K)` from Lemma `20.50.5`, and the
-- right arrow evaluates against `ε : E^\vee ⊗ E → \mathcal O_X`. Unwinding the definitions, both
-- composites send `(ξ, η)` to `(1_K ⊗ ε) ∘ (ξ ⊗ η)`, with the bottom route factoring this through
-- the morphism `E ⟶ K` associated to `ξ`.
/-- Lemma 20.51.2: for a ringed space `(X, \mathcal O_X)`, objects `K, E ∈ D(\mathcal O_X)`, and
`E` perfect, the square comparing the cup product
`H^0(X, K \otimes_{\mathcal O_X}^{\mathbf L} E^\vee) × H^0(X, E) →
H^0(X, K \otimes_{\mathcal O_X}^{\mathbf L} E^\vee \otimes_{\mathcal O_X}^{\mathbf L} E)` with
the identification
`H^0(X, K \otimes_{\mathcal O_X}^{\mathbf L} E^\vee) → \operatorname{Hom}_{D(\mathcal O_X)}(E, K)`
from Lemma `20.50.5` and the evaluation map
`ε : E^\vee \otimes_{\mathcal O_X}^{\mathbf L} E → \mathcal O_X` from Example `20.50.7`
commutes. In Lean, `H^0(X, M)` is modeled by morphisms `𝟙_ D(\mathcal O_X) ⟶ M`. -/
theorem ringedSpaceDerivedCupProduct_evaluation_commSq
    {K E : DMod} (hE : DerivedCategory.IsPerfect E) :
    let A := (𝟙_ DMod ⟶ K ⊗ ringedSpaceDerivedDual E) × (𝟙_ DMod ⟶ E)
    let B := 𝟙_ DMod ⟶ (K ⊗ ringedSpaceDerivedDual E) ⊗ E
    let C := (E ⟶ K) × (𝟙_ DMod ⟶ E)
    let D := 𝟙_ DMod ⟶ K
    let top : A ⟶ B := fun p ↦ (λ_ (𝟙_ DMod)).inv ≫ (p.1 ⊗ₘ p.2)
    let left : A ⟶ C := fun p ↦ (ringedSpaceDerivedEvaluationH0ToHom E K p.1, p.2)
    let right : B ⟶ D := fun s ↦
      s ≫ (α_ K (ringedSpaceDerivedDual E) E).hom ≫
        (K ◁ ringedSpaceDerivedDualEvaluation E) ≫
        (ρ_ K).hom
    let bot : C ⟶ D := fun p ↦ p.2 ≫ p.1
    CommSq top left right bot := sorry

end

end AlgebraicGeometry.RingedSpace
