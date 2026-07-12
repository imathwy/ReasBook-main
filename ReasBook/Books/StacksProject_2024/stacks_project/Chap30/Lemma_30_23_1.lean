import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem

-- Semantic recall hits: `FGModuleCat`, `AdicCompletion`, `SequentialInverseSystem`, and
-- `CategoryTheory.ObjectProperty.FullSubcategory`. The Stacks proof models
-- `\textit{Coh}(X, \mathcal{I})` on an affine scheme by compatible inverse systems of finite
-- modules, so the source-facing owner here is the corresponding full subcategory of
-- `SequentialInverseSystem (FGModuleCat A)`.

variable {A : Type u} [CommRing A]

/-- The underlying finite `A`-module at stage `n` of a sequential inverse system of finite
`A`-modules. -/
abbrev stageModule (F : SequentialInverseSystem (FGModuleCat A)) (n : ℕ) : Type u :=
  ↑(F.obj (op n)).obj

/-- The successor transition map of a sequential inverse system of finite `A`-modules, viewed as
an `A`-linear map. -/
abbrev stepLinearMap (F : SequentialInverseSystem (FGModuleCat A)) (n : ℕ) :
    F.stageModule (n + 1) →ₗ[A] F.stageModule n :=
  ModuleCat.homEquiv (F.stepMap n).hom

/-- The affine inverse-system model for coherent formal modules along `I`: stage `n` is annihilated
by `I ^ n`, and each transition map induces a bijection
`M_(n + 1) / I ^ n M_(n + 1) \cong M_n`. -/
@[stacks 087W]
def IsAffineCoherentFormalModuleSystem (I : Ideal A) :
    ObjectProperty (SequentialInverseSystem (FGModuleCat A)) :=
  fun F ↦
    (∀ n : ℕ,
      I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) ∧
    ∀ n : ℕ,
      ∃ hquot :
          I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤ (F.stepLinearMap n).ker,
        Function.Bijective
          (Submodule.liftQ
            (I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
            (F.stepLinearMap n)
            hquot)

/-- The category of affine coherent formal modules along `I`, formalized as the full subcategory
of sequential inverse systems of finite `A`-modules satisfying the Stacks compatibility
conditions. -/
@[stacks 087W]
abbrev AffineCoherentFormalModules (A : Type u) [CommRing A] (I : Ideal A) :=
  (IsAffineCoherentFormalModuleSystem I).FullSubcategory

/-- Source-semantic unfolding of `IsAffineCoherentFormalModuleSystem`. -/
@[stacks 087W]
theorem isAffineCoherentFormalModuleSystem_iff {I : Ideal A}
    (F : SequentialInverseSystem (FGModuleCat A)) :
    IsAffineCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ,
        I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) ∧
      ∀ n : ℕ,
        ∃ hquot :
            I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤ (F.stepLinearMap n).ker,
          Function.Bijective
            (Submodule.liftQ
              (I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
              (F.stepLinearMap n)
              hquot) := sorry

variable [IsNoetherianRing A]

/-- Lemma 30.23.1: if `X = \operatorname{Spec}(A)` with `A` Noetherian and `\mathcal{I}` is the
quasi-coherent ideal sheaf associated to `I`, then `\textit{Coh}(X, \mathcal{I})` is equivalent to
the category of finite `A^\wedge`-modules. In this file, the source category is formalized by the
affine inverse-system model used in the Stacks proof. -/
@[stacks 087W]
theorem affineCoherentFormalModules_has_equivalence_to_FGModuleCat_adicCompletion
    (I : Ideal A) :
    ∃ F : AffineCoherentFormalModules A I ⥤ FGModuleCat (AdicCompletion I A),
      F.IsEquivalence := sorry

end CategoryTheory.SequentialInverseSystem
