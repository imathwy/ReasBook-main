import StacksProject_2024.Chap20.Lemma_20_42_8

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

/- Domain-style sampling for Lemma 20.51.2:
- primary domain: the braided monoidal closed structure on `D(\mathcal O_X)` and the evaluation
  pairing for the derived dual;
- sampled owner declarations:
  `RingedSpaceDerived`,
  `CategoryTheory.CommSq`,
  `ringedSpaceDerivedEvaluationH0ToHom`,
  `ringedSpaceDerivedDualEvaluation`;
- best owner abstraction: the source-facing statement is a commutative square in `Type`, so the
  canonical owner is `CommSq`, while the left edge should reuse the existing `H^0`-to-`Hom`
  comparison and the right edge should reuse the chapter dual-evaluation morphism already used in
  Example `20.50.7`, rather than rebuilding either edge locally;
- primitive data: the ambient braided monoidal closed structure on `RingedSpaceDerived X` and the
  objects `K`, `E`;
- derived API: the `H^0`-level compatibility square between cup product, evaluation, and the
  induced map to `Hom(E, K)`.

Source/core/bridge triage:
- `source-facing`: the Stacks Project square comparing cup product with evaluation;
- `core/canonical`: `CommSq`, `ringedSpaceDerivedEvaluationH0ToHom`, and
  `ringedSpaceDerivedDualEvaluation`;
- `bridge/view`: the theorem-local specializations from those core owners to the `H^0(X, -)`
  pairing map and the dual-evaluation edge.

The perfectness assumption from the source is redundant for the square itself: it is only needed
later to know that the left edge is bijective via Lemma `20.50.5`. The refined main statement
therefore keeps the square in its canonical owner form without that extra binder.
-/
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DMod" => RingedSpaceDerived X

/-- The top edge in the cup-product/evaluation square of Lemma 20.51.2 sends
`(ξ, η)` to the induced section of `(K ⊗ E^∨) ⊗ E`. -/
def ringedSpaceDerivedCupProductTop
    (K E : DMod) :
    ((𝟙_ DMod ⟶ K ⊗ E^∨) × (𝟙_ DMod ⟶ E)) ⟶
      (𝟙_ DMod ⟶ (K ⊗ E^∨) ⊗ E) :=
  fun p ↦ (λ_ (𝟙_ DMod)).inv ≫ (p.1 ⊗ₘ p.2)

/-- The left edge in Lemma 20.51.2 applies the canonical comparison
`H⁰(X, K ⊗ E^∨) → (E ⟶ K)` from Lemma 20.42.8 to the first factor. -/
def ringedSpaceDerivedCupProductLeft
    (K E : DMod) :
    ((𝟙_ DMod ⟶ K ⊗ E^∨) × (𝟙_ DMod ⟶ E)) ⟶
      ((E ⟶ K) × (𝟙_ DMod ⟶ E)) :=
  fun p ↦ (ringedSpaceDerivedEvaluationH0ToHom E K p.1, p.2)

/-- The right edge in Lemma 20.51.2 evaluates a section of `(K ⊗ E^∨) ⊗ E`
against the derived dual-evaluation morphism of `E`. -/
def ringedSpaceDerivedCupProductRight
    (K E : DMod) :
    (𝟙_ DMod ⟶ (K ⊗ E^∨) ⊗ E) ⟶ (𝟙_ DMod ⟶ K) :=
  fun s ↦
    s ≫ (α_ K E^∨ E).hom ≫
      K ◁ ringedSpaceDerivedDualEvaluation E ≫
      (ρ_ K).hom

/-- The bottom edge in Lemma 20.51.2 evaluates the morphism `E ⟶ K` at the
chosen degree-zero class of `E`. -/
def ringedSpaceDerivedCupProductBottom
    (K E : DMod) :
    ((E ⟶ K) × (𝟙_ DMod ⟶ E)) ⟶ (𝟙_ DMod ⟶ K) :=
  fun p ↦ p.2 ≫ p.1

-- Proof sketch: the top arrow sends a pair of degree-zero classes to their tensor product, the
-- left arrow is the canonical map `H⁰(X, K ⊗ E^∨) → Hom(E, K)` from Lemma `20.42.8`, and the
-- right arrow is the canonical `K`-tensor specialization of the derived-dual evaluation
-- `ringedSpaceDerivedDualEvaluation E : E^∨ ⊗ E ⟶ 𝟙`, namely
-- `(α_ K E^∨ E).hom ≫ K ◁ ringedSpaceDerivedDualEvaluation E ≫ (ρ_ K).hom`. Unwinding the core
-- definitions, both composites send `(ξ, η)` to `(1_K ⊗ ε) ∘ (ξ ⊗ η)`, with the bottom route
-- factoring this through the morphism `E ⟶ K` associated to `ξ`. When `E` is perfect,
-- Lemma `20.50.5` upgrades the left arrow to the bijection used in the source statement.
private theorem ringedSpaceDerivedCupProduct_evaluation_aux
    (K E : DMod)
    (s : 𝟙_ DMod ⟶ K ⊗ E^∨)
    (t : 𝟙_ DMod ⟶ E) :
    ((λ_ (𝟙_ DMod)).inv ≫ (s ⊗ₘ t)) ≫
        (α_ K E^∨ E).hom ≫
        K ◁ ringedSpaceDerivedDualEvaluation E ≫
        (ρ_ K).hom =
      t ≫ ringedSpaceDerivedEvaluationH0ToHom E K s := by
  sorry

/-- Lemma 20.51.2: for a ringed space `(X, 𝒪_X)` and objects `K, E ∈ D(𝒪_X)`,
the square comparing the cup product
`H⁰(X, K ⊗ E^∨) × H⁰(X, E) → H⁰(X, (K ⊗ E^∨) ⊗ E)` with
the canonical map
`H⁰(X, K ⊗ E^∨) → Hom_{D(𝒪_X)}(E, K)`
and the evaluation map `ε : E^∨ ⊗ E → 𝒪_X` from Example `20.50.7`
commutes. When `E` is perfect, Lemma `20.50.5` upgrades the left edge to the bijection appearing
in the source. In Lean, `H⁰(X, M)` is modeled by morphisms `𝟙_ D(𝒪_X) ⟶ M`. -/
@[stacks 0FVB]
theorem ringedSpaceDerivedCupProduct_evaluation_commSq
    (K E : DMod) :
    CommSq
      (ringedSpaceDerivedCupProductTop K E)
      (ringedSpaceDerivedCupProductLeft K E)
      (ringedSpaceDerivedCupProductRight K E)
      (ringedSpaceDerivedCupProductBottom K E) := by
  refine CommSq.mk ?_
  funext p
  rcases p with ⟨s, t⟩
  exact ringedSpaceDerivedCupProduct_evaluation_aux K E s t

/-- Lemma 20.51.2, pointwise form: tensoring a degree-zero class
`ξ : H⁰(X, K ⊗ E^∨)` with `η : H⁰(X, E)` and then applying the canonical
evaluation on `E` is the same as evaluating the corresponding morphism `E ⟶ K` at `η`. -/
@[stacks 0FVB]
theorem ringedSpaceDerivedCupProduct_evaluation_apply
    (K E : DMod)
    (s : 𝟙_ DMod ⟶ K ⊗ E^∨)
    (t : 𝟙_ DMod ⟶ E) :
    ((λ_ (𝟙_ DMod)).inv ≫ (s ⊗ₘ t)) ≫
        (α_ K E^∨ E).hom ≫
        K ◁ ringedSpaceDerivedDualEvaluation E ≫
        (ρ_ K).hom =
      t ≫ ringedSpaceDerivedEvaluationH0ToHom E K s := by
  exact ringedSpaceDerivedCupProduct_evaluation_aux K E s t

end

end AlgebraicGeometry.RingedSpace
