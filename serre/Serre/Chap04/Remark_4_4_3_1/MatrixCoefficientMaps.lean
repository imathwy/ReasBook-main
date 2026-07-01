import Mathlib

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule

noncomputable section

universe u v

namespace Representation

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: a continuous matrix coefficient
`t ↦ ℓ (σ (t⁻¹) x)` defines a continuous complex-valued function on `G`. -/
noncomputable def matrixCoefficientContinuousMap
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    (x : W) (ℓ : Module.Dual ℂ W) : C(G, ℂ) where
  toFun t := ℓ (σ t⁻¹ x)
  continuous_toFun := by
    have hpair : Continuous fun t : G ↦ (t⁻¹, x) :=
      continuous_inv.prodMk continuous_const
    simpa using (ℓ.continuous_of_finiteDimensional.comp (hσ.comp hpair))

/-- Helper for Remark 4-4.3-1: left translation of the matrix coefficient for `x` is the
matrix coefficient for `σ g x`. -/
lemma matrixCoefficientContinuousMap_mul_left
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    (g : G) (x : W) (ℓ : Module.Dual ℂ W) :
    matrixCoefficientContinuousMap σ hσ (σ g x) ℓ =
      (matrixCoefficientContinuousMap σ hσ x ℓ).comp
        ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := by
  ext t
  simp [matrixCoefficientContinuousMap]

/-- Helper for Remark 4-4.3-1: fixing a linear functional gives a linear family of continuous
matrix coefficients. -/
noncomputable def matrixCoefficientLinear
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    (ℓ : Module.Dual ℂ W) : W →ₗ[ℂ] C(G, ℂ) where
  toFun x := matrixCoefficientContinuousMap σ hσ x ℓ
  map_add' x y := by
    ext t
    simp [matrixCoefficientContinuousMap]
  map_smul' a x := by
    ext t
    simp [matrixCoefficientContinuousMap]

end PeterWeyl

end Representation
