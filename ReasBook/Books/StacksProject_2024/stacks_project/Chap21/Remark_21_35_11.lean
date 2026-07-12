import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.Chap18.Lemma_18_27_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u₁ u₂ v₁ v₂

namespace SheafOfModules.RingedSite

section

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D']

set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

variable [MonoidalCategory D]
variable [BraidedCategory D]
variable [MonoidalClosed D]
variable (leftDerivedPullback : D' ⥤ D)
variable [MonoidalCategory D']
variable [BraidedCategory D']
variable [MonoidalClosed D']

/- Domain-style sampling for Remark 21.35.11:
- primary domain: pullback/internal-Hom comparison morphisms in braided closed monoidal derived
  categories of sheaves of modules on ringed sites;
- sampled owner declarations:
  `MonoidalClosed.braidedHomEquiv`,
  `MonoidalClosed.braidedHomEquiv_symm_apply`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `RingedSite.Hom.derivedPushforwardInternalHomComparison`;
- best owner abstraction:
  `source-facing`: the comparison morphism
    `Lh^* RHom(K, L) ⟶ RHom(Lh^* K, Lh^* L)`;
  `core/canonical`: the ambient braided tensor/internal-Hom adjunction
    `MonoidalClosed.braidedHomEquiv` together with the closed-monoidal evaluation morphism
    `(β_ (K ⟹ L) K).hom ≫ (ihom.ev K).app L`;
  `bridge/view`: this file, which packages the pulled-back evaluation morphism using that owner
  abstraction for a chosen pullback functor and tensor comparison.
- primitive data: the chosen pullback functor `leftDerivedPullback`, the pullback-tensor
  comparison, and the objects `K`, `L`;
- derived API: the source-facing comparison morphism and its adjunction-side specification
  theorem.

This item is a bridge/view declaration, not a second owner parallel to the ambient
tensor/internal-Hom adjunction. The public API therefore keeps the comparison morphism itself and
uses only the ambient braided closed monoidal structure required to define it. -/

/-- The canonical evaluation morphism
`RHom(K, L) ⊗ K ⟶ L`
in the source category. -/
private abbrev derivedInternalHomEvaluation
    (K L : D') :
    (K ⟹ L) ⊗ K ⟶ L :=
  (β_ (K ⟹ L) K).hom ≫ (ihom.ev K).app L

private def pullbackDerivedInternalHomComparisonTensorMap
    (pullbackTensorComparison :
      ∀ A B : D',
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : D') :
    leftDerivedPullback.obj (K ⟹ L) ⊗ leftDerivedPullback.obj K ⟶ leftDerivedPullback.obj L :=
  (pullbackTensorComparison (K ⟹ L) K).inv ≫
    leftDerivedPullback.map (derivedInternalHomEvaluation K L)

/-- Remark 21.35.11: for a morphism of ringed topoi, represented here by a chosen pullback
functor `Lh^* : D' ⥤ D`, the pullback-tensor comparison of Lemma `21.18.4` and the
tensor/internal-Hom adjunction `21.35.0.1` induce the canonical morphism
`Lh^* RHom(K, L) ⟶ RHom(Lh^* K, Lh^* L)` in the target category. -/
@[stacks 08JF]
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorComparison :
      ∀ A B : D',
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : D') :
    leftDerivedPullback.obj (K ⟹ L) ⟶
      (leftDerivedPullback.obj K ⟹ leftDerivedPullback.obj L) :=
  braidedHomEquiv
      (leftDerivedPullback.obj (K ⟹ L))
      (leftDerivedPullback.obj K)
      (leftDerivedPullback.obj L) <|
    pullbackDerivedInternalHomComparisonTensorMap
      leftDerivedPullback pullbackTensorComparison K L

/-- Applying `MonoidalClosed.braidedHomEquiv` to
`pullbackDerivedInternalHomComparison` recovers the pulled-back evaluation morphism after
transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_braidedHomEquiv_spec
    (pullbackTensorComparison :
      ∀ A B : D',
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : D') :
    (braidedHomEquiv
        (leftDerivedPullback.obj (K ⟹ L))
        (leftDerivedPullback.obj K)
        (leftDerivedPullback.obj L)).symm
      (pullbackDerivedInternalHomComparison
        leftDerivedPullback pullbackTensorComparison K L) =
      (pullbackTensorComparison (K ⟹ L) K).inv ≫
        leftDerivedPullback.map ((β_ (K ⟹ L) K).hom ≫ (ihom.ev K).app L) := by
  simp [pullbackDerivedInternalHomComparison,
    pullbackDerivedInternalHomComparisonTensorMap, derivedInternalHomEvaluation]

-- Proof sketch: applying `MonoidalClosed.braidedHomEquiv_symm_apply` to the comparison morphism
-- identifies its source-order adjoint transpose with the pulled-back evaluation morphism; left
-- multiplication by the inverse braiding then recovers the `uncurry` formulation used in
-- downstream evaluation-side computations.
/-- Uncurrying `pullbackDerivedInternalHomComparison` recovers the braiding-adjusted pulled-back
evaluation morphism after transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorComparison :
      ∀ A B : D',
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : D') :
    uncurry
      (pullbackDerivedInternalHomComparison
        leftDerivedPullback pullbackTensorComparison K L) =
      (β_ (leftDerivedPullback.obj (K ⟹ L)) (leftDerivedPullback.obj K)).inv ≫
        (pullbackTensorComparison (K ⟹ L) K).inv ≫
          leftDerivedPullback.map ((β_ (K ⟹ L) K).hom ≫ (ihom.ev K).app L) := by
  sorry

end

end SheafOfModules.RingedSite
