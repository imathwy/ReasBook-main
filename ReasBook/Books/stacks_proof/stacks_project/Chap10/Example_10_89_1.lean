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

/-- Helper for Example 10.89.1: every pure tensor in `ℚ ⊗[ℤ] ZMod n` vanishes because `ZMod n`
is annihilated by `n`. -/
lemma rat_tmul_zmod_eq_zero (n : ℕ+) (q : ℚ) (z : ZMod n) :
    q ⊗ₜ[ℤ] z = 0 := by
  have hnz : ((n : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hq : (n : ℤ) • ((1 / (((n : ℤ) : ℚ))) * q) = q := by
    rw [zsmul_eq_mul, ← mul_assoc]
    have hunit : ((n : ℤ) : ℚ) * (1 / (((n : ℤ) : ℚ))) = 1 := by
      field_simp [hnz]
    rw [hunit, one_mul]
  have hz : (n : ℤ) • z = 0 := by
    have hcast : ((n : ℤ) : ZMod n) = 0 := by
      exact_mod_cast ZMod.natCast_self (n : ℕ)
    simpa [zsmul_eq_mul] using congrArg (fun x : ZMod n ↦ x * z) hcast
  -- Move the scalar `n` across the tensor and use the torsion relation on `z`.
  calc
    q ⊗ₜ[ℤ] z = (((n : ℤ) • ((1 / (((n : ℤ) : ℚ))) * q)) ⊗ₜ[ℤ] z) := by rw [hq]
    _ = (((1 / (((n : ℤ) : ℚ))) * q) ⊗ₜ[ℤ] ((n : ℤ) • z)) := by
      rw [TensorProduct.smul_tmul]
    _ = 0 := by simp [hz]

/-- Helper for Example 10.89.1: each component `ℚ ⊗[ℤ] ZMod n` is trivial because all pure
tensors are zero. -/
lemma rat_tensor_zmod_subsingleton (n : ℕ+) : Subsingleton (ℚ ⊗[ℤ] ZMod n) := by
  refine ⟨fun x y ↦ ?_⟩
  have hzero : ∀ t : ℚ ⊗[ℤ] ZMod n, t = 0 := by
    intro t
    -- Reduce the tensor to pure tensors and use the vanishing lemma above.
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · rfl
    · intro q z
      exact rat_tmul_zmod_eq_zero n q z
    · intro t₁ t₂ ht₁ ht₂
      simp [ht₁, ht₂]
  exact (hzero x).trans (hzero y).symm

/-- Helper for Example 10.89.1: the residue map `ℤ → ∏ n, ZMod n` is injective. -/
lemma pnat_zmod_residue_map_injective :
    Function.Injective (Algebra.linearMap ℤ ((n : ℕ+) → ZMod n)) := by
  have hzero :
      ∀ m : ℤ, Algebra.linearMap ℤ ((n : ℕ+) → ZMod n) m = 0 → m = 0 := by
    intro m hm
    by_cases hm0 : m = 0
    · exact hm0
    · let n : ℕ+ := ⟨Int.natAbs m + 1, Nat.succ_pos _⟩
      have hcoord : (m : ZMod n) = 0 := by
        simpa using congrFun hm n
      have hdiv : ((n : ℕ) : ℤ) ∣ m := by
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd m (n : ℕ)).mp hcoord
      have hle' : Int.natAbs ((n : ℕ) : ℤ) ≤ Int.natAbs m :=
        Int.natAbs_le_of_dvd_ne_zero hdiv hm0
      have hleNat : (n : ℕ) ≤ Int.natAbs m := by
        simpa using hle'
      have hle : Int.natAbs m + 1 ≤ Int.natAbs m := by
        simpa [n] using hleNat
      exact False.elim (Nat.not_succ_le_self _ hle)
  intro a b hab
  -- Compare the difference with the zero sequence and invoke the kernel computation.
  apply sub_eq_zero.mp
  apply hzero (a - b)
  rw [LinearMap.map_sub, hab, sub_self]

/-- Helper for Example 10.89.1: common integer denominators are stable under addition. -/
lemma has_common_integer_denominator_add {x y : ℕ+ → ℚ}
    (hx : has_common_integer_denominator x) (hy : has_common_integer_denominator y) :
    has_common_integer_denominator (x + y) := by
  rcases hx with ⟨a, m, hm, hxm⟩
  rcases hy with ⟨b, n, hn, hyn⟩
  refine ⟨fun i ↦ n * a i + m * b i, m * n, mul_ne_zero hm hn, fun i ↦ ?_⟩
  have hmq : (m : ℚ) ≠ 0 := by
    exact_mod_cast hm
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn
  -- Cross-multiplying shows that the sum has denominator `m * n`.
  calc
    (x + y) i = (a i : ℚ) / m + (b i : ℚ) / n := by simp [hxm i, hyn i]
    _ = ↑((fun i ↦ n * a i + m * b i) i) / ↑(m * n) := by
      field_simp [hmq, hnq]
      norm_num [Int.cast_add, Int.cast_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Example 10.89.1: a pure tensor in `ℚ ⊗[ℤ] (∏ n, ℤ)` yields a sequence with one
common nonzero integer denominator. -/
lemma has_common_integer_denominator_piScalarRightHom_tmul (q : ℚ) (f : ℕ+ → ℤ) :
    has_common_integer_denominator (piScalarRightHom ℤ ℤ ℚ ℕ+ (q ⊗ₜ[ℤ] f)) := by
  refine ⟨fun n ↦ f n * q.num, q.den, by exact_mod_cast q.den_nz, fun n ↦ ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by
    exact_mod_cast q.den_nz
  -- Unwind the pure tensor image and rewrite `q` in lowest terms.
  calc
    TensorProduct.piScalarRightHom ℤ ℤ ℚ ℕ+ (q ⊗ₜ[ℤ] f) n = f n • q := by
      simp [TensorProduct.piScalarRightHom_tmul]
    _ = (f n : ℚ) * q := by rw [zsmul_eq_mul]
    _ = (f n : ℚ) * ((q.num : ℚ) / q.den) := by
      simpa using congrArg (fun r : ℚ ↦ (f n : ℚ) * r) (Rat.num_div_den q).symm
    _ = (((f n * q.num : ℤ) : ℚ) / q.den) := by
      rw [div_eq_mul_inv, ← mul_assoc, ← Int.cast_mul, div_eq_mul_inv]

/-- Helper for Example 10.89.1: the sequence `n ↦ 1 / n` cannot have a single nonzero integer
denominator. -/
lemma one_div_pnat_not_has_common_integer_denominator :
    ¬ has_common_integer_denominator (fun n : ℕ+ ↦ (1 : ℚ) / n) := by
  rintro ⟨a, m, hm, hseq⟩
  let n : ℕ+ := ⟨Int.natAbs m + 1, Nat.succ_pos _⟩
  have hnq : ((n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hmq : (m : ℚ) ≠ 0 := by
    exact_mod_cast hm
  have hvalue : (1 : ℚ) / n = (a n : ℚ) / m := hseq n
  have hcast : (m : ℚ) = (((a n : ℤ) * (n : ℤ) : ℤ) : ℚ) := by
    -- Cross-multiply the claimed denominator identity at the special index `n`.
    have hmul : (1 : ℚ) * (m : ℚ) = (a n : ℚ) * n := by
      exact (div_eq_div_iff hnq hmq).mp hvalue
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdiv : ((n : ℤ) ∣ m) := by
    refine ⟨a n, ?_⟩
    simpa [mul_comm] using (show m = a n * (n : ℤ) by exact_mod_cast hcast)
  have hle' : Int.natAbs ((n : ℤ)) ≤ Int.natAbs m :=
    Int.natAbs_le_of_dvd_ne_zero hdiv hm
  have hleNat : (n : ℕ) ≤ Int.natAbs m := by
    simpa using hle'
  have hle : Int.natAbs m + 1 ≤ Int.natAbs m := by
    simpa [n] using hleNat
  exact Nat.not_succ_le_self _ hle

-- Proof sketch: each tensor product `ℚ ⊗[ℤ] ZMod n` vanishes because `ℚ` is torsion-free and
-- divisible while `ZMod n` is `n`-torsion; hence every component in the product is zero.
/-- Example 10.89.1 (1): for the family `Q_n = ℤ / nℤ` indexed by positive integers, the product
`∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is the zero module. -/
@[stacks 059I]
theorem rat_tensor_pnat_zmod_product_subsingleton :
    Subsingleton ((n : ℕ+) → ℚ ⊗[ℤ] ZMod n) := by
  refine ⟨fun x y ↦ ?_⟩
  -- Each coordinate lives in a subsingleton tensor product.
  ext n
  exact (rat_tensor_zmod_subsingleton n).elim (x n) (y n)

/-- The canonical map from Example 10.89.1 (2) is injective. -/
theorem rat_to_tensor_pnat_zmod_product_injective :
    Function.Injective rat_to_tensor_pnat_zmod_product := by
  have hTensor :
      Function.Injective
        (LinearMap.rTensor ℚ (Algebra.linearMap ℤ ((n : ℕ+) → ZMod n))) := by
    -- Tensor the injective residue map with the flat `ℤ`-module `ℚ`.
    exact Module.Flat.rTensor_preserves_injective_linearMap
      (Algebra.linearMap ℤ ((n : ℕ+) → ZMod n))
      pnat_zmod_residue_map_injective
  -- The target map is obtained by composing with the canonical tensor symmetries.
  exact (TensorProduct.comm ℤ ((n : ℕ+) → ZMod n) ℚ).injective.comp
    (hTensor.comp (TensorProduct.lid ℤ ℚ).symm.injective)

-- Proof sketch: tensor the injective map `ℤ → ∏_{n ≥ 1} ℤ / nℤ`, `m ↦ (m mod n)_n`, with `ℚ`;
-- since `ℚ ⊗[ℤ] ℤ ≃ₗ[ℤ] ℚ`, this yields an injective linear map into
-- `ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ / nℤ)`.
/-- Example 10.89.1 (2): there exists an injective `ℤ`-linear map
`ℚ → ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ / nℤ)`. -/
@[stacks 059I]
theorem exists_injective_rat_to_tensor_pnat_zmod_product :
    ∃ f : ℚ →ₗ[ℤ] ℚ ⊗[ℤ] ((n : ℕ+) → ZMod n), Function.Injective f :=
  ⟨rat_to_tensor_pnat_zmod_product, rat_to_tensor_pnat_zmod_product_injective⟩

-- Proof sketch: the codomain of `piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n)` is subsingleton by the
-- previous vanishing statement, while the domain is nontrivial because it receives an injective
-- map from `ℚ`.
/-- Example 10.89.1 (3): for `Q_n = ℤ / nℤ`, the canonical map
`ℚ ⊗[ℤ] (∏_{n ≥ 1} Q_n) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is not injective. -/
@[stacks 059I]
theorem rat_tensor_pnat_zmod_product_map_not_injective :
    ¬ Function.Injective (piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n)) := by
  intro hpi
  have hcod :
      Subsingleton ((n : ℕ+) → ℚ ⊗[ℤ] ZMod n) :=
    rat_tensor_pnat_zmod_product_subsingleton
  have himage :
      piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n) (rat_to_tensor_pnat_zmod_product 0) =
        piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n) (rat_to_tensor_pnat_zmod_product 1) :=
    hcod.elim _ _
  have hzero_one :
      rat_to_tensor_pnat_zmod_product (0 : ℚ) =
        rat_to_tensor_pnat_zmod_product 1 := hpi himage
  exact zero_ne_one (rat_to_tensor_pnat_zmod_product_injective hzero_one)

-- Proof sketch: identify `ℚ ⊗[ℤ] ℤ` with `ℚ` and unwind the tensor-product map on pure tensors;
-- an element in the image comes from one tensor, so all coordinates share a single nonzero
-- integer denominator, and conversely any such sequence is represented by that tensor.
/-- Example 10.89.1 (4): for the constant family `Q_n = ℤ`, a sequence of rationals lies in the
range of the canonical map `ℚ ⊗[ℤ] (∏_{n ≥ 1} ℤ) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] ℤ)` exactly when it has a
common nonzero integer denominator. -/
@[stacks 059I]
theorem mem_rat_tensor_pnat_int_product_map_range_iff_has_common_integer_denominator
    (x : ℕ+ → ℚ) :
    x ∈ LinearMap.range (piScalarRightHom ℤ ℤ ℚ ℕ+) ↔ has_common_integer_denominator x := by
  constructor
  · rintro ⟨t, rfl⟩
    -- Reduce the range statement to the zero, pure-tensor, and additive cases.
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · refine ⟨0, 1, by decide, fun n ↦ ?_⟩
      simp
    · intro q f
      exact has_common_integer_denominator_piScalarRightHom_tmul q f
    · intro t₁ t₂ ht₁ ht₂
      simpa [map_add] using has_common_integer_denominator_add ht₁ ht₂
  · rintro ⟨a, m, hm, hx⟩
    -- Realize the sequence with common denominator `m` as a single pure tensor.
    refine ⟨(1 / m : ℚ) ⊗ₜ[ℤ] a, ?_⟩
    ext n
    calc
      TensorProduct.piScalarRightHom ℤ ℤ ℚ ℕ+ ((1 / m : ℚ) ⊗ₜ[ℤ] a) n
          = a n • (1 / m : ℚ) := by
            simp [TensorProduct.piScalarRightHom_tmul]
      _ = (a n : ℚ) / m := by
        simp [zsmul_eq_mul, div_eq_mul_inv]
      _ = x n := by simpa [hx n] using (hx n).symm

-- Proof sketch: choose a rational sequence with unbounded reduced denominators, such as
-- `n ↦ 1 / n`; by the range characterization above it cannot come from a single tensor, so the
-- canonical map fails to be surjective.
/-- Example 10.89.1 (5): for the constant family `Q_n = ℤ`, the canonical map
`ℚ ⊗[ℤ] (∏_{n ≥ 1} Q_n) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is not surjective. -/
@[stacks 059I]
theorem rat_tensor_pnat_int_product_map_not_surjective :
    ¬ Function.Surjective (piScalarRightHom ℤ ℤ ℚ ℕ+) := by
  intro hsurj
  obtain ⟨t, ht⟩ := hsurj (fun n : ℕ+ ↦ (1 : ℚ) / n)
  have hmem :
      (fun n : ℕ+ ↦ (1 : ℚ) / n) ∈ LinearMap.range (piScalarRightHom ℤ ℤ ℚ ℕ+) :=
    ⟨t, ht⟩
  exact one_div_pnat_not_has_common_integer_denominator
    ((mem_rat_tensor_pnat_int_product_map_range_iff_has_common_integer_denominator
      (fun n : ℕ+ ↦ (1 : ℚ) / n)).mp hmem)
