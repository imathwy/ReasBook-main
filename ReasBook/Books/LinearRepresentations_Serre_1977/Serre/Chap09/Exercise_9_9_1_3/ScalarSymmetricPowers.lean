import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.RepresentationTheory.SymmetricExterior
import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.InvariantSubspaces

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem symmetricPower_map_smul_id
    (n : ℕ) (μ : k) :
    SymmetricPower.map n (μ • (LinearMap.id : V →ₗ[k] V)) =
      μ ^ n •
        (LinearMap.id :
          SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) V) := by
  have hcomp :
      (SymmetricPower.map n (μ • (LinearMap.id : V →ₗ[k] V))).comp
          (SymmetricPower.mk k (Fin n) V) =
        (SymmetricPower.mk k (Fin n) V).comp
          (PiTensorProduct.map fun _ : Fin n ↦ μ • (LinearMap.id : V →ₗ[k] V)) := by
    -- Unfolding the symmetric-power map on quotient representatives shows that precomposing with
    -- the quotient map is the same as first mapping the tensor power and then quotienting.
    ext x
    rfl
  have hmk :
      (SymmetricPower.mk k (Fin n) V).comp
          (PiTensorProduct.map fun _ : Fin n ↦ μ • (LinearMap.id : V →ₗ[k] V)) =
        μ ^ n • (SymmetricPower.mk k (Fin n) V) := by
    -- On pure tensors, every tensor factor contributes one scalar `μ`, so multilinearity
    -- produces the global factor `μ ^ n`.
    apply PiTensorProduct.ext
    ext v
    simp [MultilinearMap.map_smul_univ]
  ext y
  obtain ⟨x, rfl⟩ :=
    LinearMap.range_eq_top.mp
      (SymmetricPower.range_mk (R := k) (ι := Fin n) (M := V)) y
  -- The quotient map onto the symmetric power is surjective, so equality after precomposition
  -- with `SymmetricPower.mk` already determines the endomorphism.
  change
    ((SymmetricPower.map n (μ • (LinearMap.id : V →ₗ[k] V))).comp
        (SymmetricPower.mk k (Fin n) V)) x =
      ((μ ^ n •
          (LinearMap.id :
            SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) V)).comp
        (SymmetricPower.mk k (Fin n) V)) x
  rw [hcomp, hmk]
  rfl

end

end Representation
