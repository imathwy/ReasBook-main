import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [HasFiniteBiproducts C]
variable [MonoidalPreadditive C]
variable {X₁ Y₁ X₂ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]

local notation "X" => X₁ ⊞ X₂
local notation "Y" => Y₁ ⊞ Y₂

/-
Domain-style sampling for Lemma 12.17.2:
- primary domain: rigid monoidal category theory in a preadditive monoidal category with finite
  biproducts
- core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.HasLeftDual`
  - `CategoryTheory.Retract.hasLeftDual` from `Lemma_12_17_3`
  - `Limits.hasBinaryBiproducts_of_finite_biproducts` as the ambient biproduct bridge actually
    used by the construction
- best owner abstraction: `ExactPairing`
- primitive data: explicit exact pairings `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`
- derived API: the chosen-left-dual owner `HasLeftDual (Y₁ ⊞ Y₂)` when `Xᵢ = ᘁYᵢ`
- source/core/bridge triage:
  - source-facing: the direct sums of two explicit dual pairs again form an explicit dual pair
  - core/canonical: `ExactPairing`
  - bridge/view: `HasLeftDual.biprod` obtained by specializing to the chosen left duals
-/

/-- The diagonal summands `(X₁ ⊗ Y₁) ⊞ (X₂ ⊗ Y₂)` embed canonically into
`X ⊗ Y` by first inserting them into the two distributed tensor factors and then undoing the
left distributor. -/
private def biprodDiagonalCoevaluationMap :
    (X₁ ⊗ Y₁) ⊞ (X₂ ⊗ Y₂) ⟶ X ⊗ Y :=
  biprod.map
      ((biprod.inl : X₁ ⊗ Y₁ ⟶ (X₁ ⊗ Y₁) ⊞ (X₂ ⊗ Y₁)) ≫
        ((tensorRight Y₁).mapBiprod X₁ X₂).inv)
      ((biprod.inr : X₂ ⊗ Y₂ ⟶ (X₁ ⊗ Y₂) ⊞ (X₂ ⊗ Y₂)) ≫
        ((tensorRight Y₂).mapBiprod X₁ X₂).inv) ≫
    ((tensorLeft X).mapBiprod Y₁ Y₂).inv

/-- The coevaluation for the biproduct exact-pairing datum is obtained by inserting the two given
coevaluations on the diagonal summands and transporting through the binary distributor isomorphisms
for tensoring on the left and on the right. -/
private def biprodCoevaluation : 𝟙_ C ⟶ X ⊗ Y :=
  biprod.lift (η_ X₁ Y₁) (η_ X₂ Y₂) ≫ biprodDiagonalCoevaluationMap

/-- Projecting `Y ⊗ X` to the two diagonal summands amounts to distributing the tensor product and
then keeping only the `Y₁ ⊗ X₁` and `Y₂ ⊗ X₂` pieces. -/
private def biprodDiagonalEvaluationMap :
    Y ⊗ X ⟶ (Y₁ ⊗ X₁) ⊞ (Y₂ ⊗ X₂) :=
  ((tensorLeft Y).mapBiprod X₁ X₂).hom ≫
    biprod.map
      (((tensorRight X₁).mapBiprod Y₁ Y₂).hom ≫
        (biprod.fst : (Y₁ ⊗ X₁) ⊞ (Y₂ ⊗ X₁) ⟶ Y₁ ⊗ X₁))
      (((tensorRight X₂).mapBiprod Y₁ Y₂).hom ≫
        (biprod.snd : (Y₁ ⊗ X₂) ⊞ (Y₂ ⊗ X₂) ⟶ Y₂ ⊗ X₂))

/-- The evaluation for the biproduct exact-pairing datum first distributes tensor product across
the direct sum, projects to the two diagonal summands, and then applies the given evaluations. -/
private def biprodEvaluation : Y ⊗ X ⟶ 𝟙_ C :=
  biprodDiagonalEvaluationMap ≫ biprod.desc (ε_ X₁ Y₁) (ε_ X₂ Y₂)

/-- The first triangle identity for the biproduct exact-pairing datum. -/
-- Proof sketch: expand `biprodCoevaluation` and `biprodEvaluation`, use the binary biproduct
-- relations to eliminate the off-diagonal terms, and then apply the two given triangle identities
-- on the diagonal summands together with the biproduct extensionality lemmas.
private theorem biprodCoevaluation_evaluation :
    Y ◁ biprodCoevaluation ≫
        (α_ Y X Y).inv ≫
        biprodEvaluation ▷ Y =
      (ρ_ Y).hom ≫ (λ_ Y).inv := sorry

/-- The second triangle identity for the biproduct exact-pairing datum. -/
-- Proof sketch: distribute tensoring over the two biproducts, project to the diagonal summands,
-- observe that every off-diagonal composite vanishes by the biproduct identities, and reduce the
-- remaining diagonal pieces to the given triangle identities for `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`.
private theorem biprodEvaluation_coevaluation :
    biprodCoevaluation ▷ X ≫
        (α_ X Y X).hom ≫
        X ◁ biprodEvaluation =
      (λ_ X).hom ≫ (ρ_ X).inv := sorry

namespace ExactPairing

/-- If `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`, then their binary direct sums again form an exact pairing. -/
instance biprod : ExactPairing X Y where
  coevaluation' := biprodCoevaluation
  evaluation' := biprodEvaluation
  coevaluation_evaluation' := biprodCoevaluation_evaluation
  evaluation_coevaluation' := biprodEvaluation_coevaluation

end ExactPairing

namespace HasLeftDual

/-- If two objects have chosen left duals, then their direct sum has the direct sum of those
chosen left duals as a chosen left dual. -/
instance biprod {A B : C} [HasLeftDual A] [HasLeftDual B] : HasLeftDual (A ⊞ B) where
  leftDual := (ᘁA : C) ⊞ (ᘁB : C)
  exact := inferInstance

end HasLeftDual

end CategoryTheory
