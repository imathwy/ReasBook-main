import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct

/-- The canonical `ℤ`-linear map `ℚ → ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ / nℤ)` induced by the residue-class
map `ℤ → ∏_{n ≥ 1} ℤ / nℤ`, `m ↦ (m mod n)_n`. -/
noncomputable def rat_to_tensor_pnat_zmod_product :
    ℚ →ₗ[ℤ] ℚ ⊗[ℤ] ((n : ℕ+) → ZMod n) :=
  (TensorProduct.comm ℤ ((n : ℕ+) → ZMod n) ℚ).toLinearMap.comp
    ((LinearMap.rTensor ℚ (Algebra.linearMap ℤ ((n : ℕ+) → ZMod n))).comp
      (TensorProduct.lid ℤ ℚ).symm.toLinearMap)

/-- A sequence of rational numbers has a common nonzero integer denominator if all of its terms
can be written as `aₙ / m` for one fixed nonzero integer `m`. -/
def has_common_integer_denominator (x : ℕ+ → ℚ) : Prop :=
  ∃ a : ℕ+ → ℤ, ∃ m : ℤ, m ≠ 0 ∧ ∀ n : ℕ+, x n = (a n : ℚ) / m

-- Proof sketch: each tensor product `ℚ ⊗[ℤ] ZMod n` vanishes because `ℚ` is torsion-free and
-- divisible while `ZMod n` is `n`-torsion; hence every component in the product is zero.
/-- Example 10.89.1 (1): for the family `Q_n = ℤ / nℤ` indexed by positive integers, the product
`∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is the zero module. -/
theorem rat_tensor_pnat_zmod_product_subsingleton :
    Subsingleton ((n : ℕ+) → ℚ ⊗[ℤ] ZMod n) := sorry

/-- The canonical map from Example 10.89.1 (2) is injective. -/
theorem rat_to_tensor_pnat_zmod_product_injective :
    Function.Injective rat_to_tensor_pnat_zmod_product := sorry

-- Proof sketch: tensor the injective map `ℤ → ∏_{n ≥ 1} ℤ / nℤ`, `m ↦ (m mod n)_n`, with `ℚ`;
-- since `ℚ ⊗[ℤ] ℤ ≃ₗ[ℤ] ℚ`, this yields an injective linear map into
-- `ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ / nℤ)`.
/-- Example 10.89.1 (2): there exists an injective `ℤ`-linear map
`ℚ → ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ / nℤ)`. -/
theorem exists_injective_rat_to_tensor_pnat_zmod_product :
    ∃ f : ℚ →ₗ[ℤ] ℚ ⊗[ℤ] ((n : ℕ+) → ZMod n), Function.Injective f :=
  ⟨rat_to_tensor_pnat_zmod_product, rat_to_tensor_pnat_zmod_product_injective⟩

-- Proof sketch: the codomain of `piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n)` is subsingleton by the
-- previous vanishing statement, while the domain is nontrivial because it receives an injective
-- map from `ℚ`.
/-- Example 10.89.1 (3): for `Q_n = ℤ / nℤ`, the canonical map
`ℚ ⊗[ℤ] (∏_{n ≥ 1} Q_n) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is not injective. -/
theorem rat_tensor_pnat_zmod_product_map_not_injective :
    ¬ Function.Injective (piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n)) := sorry

-- Proof sketch: identify `ℚ ⊗[ℤ] ℤ` with `ℚ` and unwind the tensor-product map on pure tensors;
-- an element in the image comes from one tensor, so all coordinates share a single nonzero
-- integer denominator, and conversely any such sequence is represented by that tensor.
/-- Example 10.89.1 (4): for the constant family `Q_n = ℤ`, a sequence of rationals lies in the
range of the canonical map `ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] ℤ)` exactly when it has a
common nonzero integer denominator. -/
theorem mem_rat_tensor_pnat_int_product_map_range_iff_has_common_integer_denominator
    (x : ℕ+ → ℚ) :
    x ∈ LinearMap.range (piScalarRightHom ℤ ℤ ℚ ℕ+) ↔ has_common_integer_denominator x := sorry

-- Proof sketch: choose a rational sequence with unbounded reduced denominators, such as
-- `n ↦ 1 / n`; by the range characterization above it cannot come from a single tensor, so the
-- canonical map fails to be surjective.
/-- Example 10.89.1 (5): for the constant family `Q_n = ℤ`, the canonical map
`ℚ ⊗[ℤ] (∏_{n ≥ 1} Q_n) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is not surjective. -/
theorem rat_tensor_pnat_int_product_map_not_surjective :
    ¬ Function.Surjective (piScalarRightHom ℤ ℤ ℚ ℕ+) := sorry
