import Mathlib
import StacksProject_2024.Chap10.Lemma_10_13_3

-- Tensor-power scalar-restriction comparison helpers for Lemma 10.13.4.

open scoped TensorProduct
open PiTensorProduct exteriorPower

section

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
variable (n : ℕ) (M : Type) [AddCommGroup M] [Module A M] [Module B M]
  [IsScalarTower A B M]

local instance exteriorPowerModule : Module A (⋀[B]^n M) :=
  Module.compHom _ (algebraMap A B)

local instance exteriorPowerIsScalarTower : IsScalarTower A B (⋀[B]^n M) :=
  IsScalarTower.of_compHom A B _

local instance tensorPowerOverBaseModule : Module A (⨂[B]^n M) := by
  infer_instance

local instance tensorPowerOverBaseIsScalarTower : IsScalarTower A B (⨂[B]^n M) := by
  infer_instance

/-- Helper for Lemma 10.13.4: the scalar-tower actions let us view the canonical `B`-linear map
from tensor power to exterior power as an `A`-linear map. -/
local instance tensorPowerToExteriorCompatibleSMul :
    LinearMap.CompatibleSMul (⨂[B]^n M) (⋀[B]^n M) A B where
  map_smul f a x := by
    -- Both `A`-actions are induced through `algebraMap A B`, so `B`-linearity is enough.
    simpa [Algebra.smul_def] using f.map_smul (algebraMap A B a) x

/-- Helper for Lemma 10.13.4: the canonical comparison map from the tensor power over `A` to the
tensor power over `B`, obtained by restricting the multilinear pure-tensor map along `A → B`. -/
noncomputable def tensorPowerRestrictScalarsToBase :
    (⨂[A]^n M) →ₗ[A] (⨂[B]^n M) :=
  lift ((tprod B : MultilinearMap B (fun _ : Fin n ↦ M) (⨂[B]^n M)).restrictScalars A)

/-- Helper for Lemma 10.13.4: the scalar-restriction comparison map preserves pure tensors. -/
@[simp] lemma tensorPowerRestrictScalarsToBase_tprod (m : Fin n → M) :
    tensorPowerRestrictScalarsToBase A B n M (tprod A m) = tprod B m := by
  -- The comparison map was defined by the universal property of the tensor power over `A`.
  simp [tensorPowerRestrictScalarsToBase]

/-- Helper for Lemma 10.13.4: in positive degree, every tensor over `B` comes from the tensor
power over `A` by absorbing the leading `B`-scalar into one chosen tensor slot. -/
lemma tensorPowerRestrictScalarsToBase_surjective (hn : 0 < n) :
    Function.Surjective (tensorPowerRestrictScalarsToBase A B n M) := by
  let i0 : Fin n := ⟨0, hn⟩
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod b m =>
      -- In positive degree, move the scalar `b` into the fixed slot `i0`.
      refine ⟨tprod A (Function.update m i0 (b • m i0)), ?_⟩
      rw [tensorPowerRestrictScalarsToBase_tprod]
      simpa [i0] using
        (tprod B : MultilinearMap B (fun _ : Fin n ↦ M) (⨂[B]^n M)).map_update_smul
          m i0 b (m i0)
  | add z₁ z₂ hz₁ hz₂ =>
      -- Surjectivity is stable under sums because the comparison map is linear.
      rcases hz₁ with ⟨x₁, rfl⟩
      rcases hz₂ with ⟨x₂, rfl⟩
      refine ⟨x₁ + x₂, by simp⟩

/-- Helper for Lemma 10.13.4: the canonical map to the exterior power factors through the tensor
power formed over `B`. -/
lemma tensorPowerToExterior_factor_tprod (m : Fin n → M) :
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M)
      (tprod A m) =
      (((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M)) (tprod A m) := by
  -- Both sides evaluate pure tensors through the same alternating multilinear map over `B`.
  calc
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M)
        (tprod A m) =
      ((ιMulti B n).toMultilinearMap.restrictScalars A) m := by
        rw [PiTensorProduct.lift.tprod]
    _ = (ιMulti B n).toMultilinearMap m := rfl
    _ = (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M) (tprod B m) := by
        rw [PiTensorProduct.lift.tprod]
        rfl
    _ =
      (((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M)) (tprod A m) := by
        simp [LinearMap.comp_apply, tensorPowerRestrictScalarsToBase_tprod]

/-- Helper for Lemma 10.13.4: the canonical map to the exterior power factors through the tensor
power formed over `B`. -/
lemma tensorPowerToExterior_factor :
    (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) : (⨂[A]^n M) →ₗ[A] ⋀[B]^n M) =
      ((lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).restrictScalars A).comp
        (tensorPowerRestrictScalarsToBase A B n M) := by
  -- Route correction: prove the factorization on pure tensors first, then invoke tensor-power
  -- induction to extend the pure-tensor computation across the whole tensor power.
  refine LinearMap.ext fun z ↦ ?_
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
      -- The factorization is already known on pure tensors, and both sides are linear.
      rw [map_smul, LinearMap.comp_apply, map_smul,
        tensorPowerToExterior_factor_tprod (A := A) (B := B) (n := n) (M := M)]
      rw [map_smul, LinearMap.comp_apply]
  | add x y hx hy =>
      -- The equality is stable under addition because both maps are linear.
      simp [hx, hy]

/-- Helper for Lemma 10.13.4: over `B`, every repeated-entry tensor lies in the kernel of the
canonical map to the exterior power. -/
lemma repeated_relation_mem_exterior_ker_over_B
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M) :
    tprod B (insertTwoTensorEntries n p y y m) ∈
      (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).ker := by
  -- Route correction: instead of unfolding the inserted tensor directly, realize it as one of the
  -- explicit generators already packaged in Lemma 10.13.3.
  have hker :
      (lift (ιMulti B n).toMultilinearMap : (⨂[B]^n M) →ₗ[B] ⋀[B]^n M).ker =
        LinearMap.range
          (exteriorRelationMapOfFamily (R := B) (n := n) (x := fun z : M ↦ z)) := by
    simpa [Set.range_id] using
      (generator_exterior_power_ker_eq_range (R := B) (M := M) (I := M)
        (n := n) (x := fun z : M ↦ z)
        (by simpa [Set.range_id] using
          (Submodule.span_univ (R := B) (s := (Set.univ : Set M)))))
  rw [hker]
  refine LinearMap.mem_range.mpr ?_
  refine ⟨(0, Finsupp.single (p, y) (tprod B m)), ?_⟩
  simpa using
    (exteriorRelationMapOfFamily_snd_single_tprod (R := B) (n := n)
      (x := fun z : M ↦ z) p y m)

/-- Helper for Lemma 10.13.4: after pulling back along the tensor-power comparison, the
repeated-entry generators already lie in the target kernel. -/
lemma repeated_relation_mem_target_ker
    (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M) :
    tprod A (insertTwoTensorEntries n p y y m) ∈
      (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
        (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker := by
  -- Factor the target map through the tensor power over `B`, then use the known kernel generator
  -- description from Lemma 10.13.3.
  rw [tensorPowerToExterior_factor (A := A) (B := B) (n := n) (M := M), LinearMap.mem_ker]
  simpa using
    (LinearMap.mem_ker.mp
      (repeated_relation_mem_exterior_ker_over_B (B := B) (n := n) (M := M) p m y))

/-- Helper for Lemma 10.13.4: the `A`-span of the repeated-entry generators is contained in the
kernel of the canonical map to the exterior power over `B`. -/
lemma repeated_relations_span_le_ker :
    Submodule.span A
      {x | ∃ (p : TensorSlotPair n) (m : Fin (n - 2) → M) (y : M),
          x = tprod A (insertTwoTensorEntries n p y y m)} ≤
      (lift ((ιMulti B n).toMultilinearMap.restrictScalars A) :
        (⨂[A]^n M) →ₗ[A] ⋀[B]^n M).ker := by
  -- It suffices to check the claimed generators.
  rw [Submodule.span_le]
  rintro _ ⟨p, m, y, rfl⟩
  exact repeated_relation_mem_target_ker (A := A) (B := B) (n := n) (M := M) p m y

end
