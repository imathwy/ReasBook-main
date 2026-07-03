import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_89_1 (from Chap10) -/
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
theorem exists_injective_rat_to_tensor_pnat_zmod_product :
    ∃ f : ℚ →ₗ[ℤ] ℚ ⊗[ℤ] ((n : ℕ+) → ZMod n), Function.Injective f :=
  ⟨rat_to_tensor_pnat_zmod_product, rat_to_tensor_pnat_zmod_product_injective⟩

-- Proof sketch: the codomain of `piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n)` is subsingleton by the
-- previous vanishing statement, while the domain is nontrivial because it receives an injective
-- map from `ℚ`.
/-- Example 10.89.1 (3): for `Q_n = ℤ / nℤ`, the canonical map
`ℚ ⊗[ℤ] (∏_{n ≥ 1} Q_n) → ∏_{n ≥ 1} (ℚ ⊗[ℤ] Q_n)` is not injective. -/
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

/-! ### Proposition_10_89_2 (from Chap10) -/
universe u v w x

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

open scoped TensorProduct

/- Domain triage: this proposition is about the tensor-product comparison map from a tensor with
an arbitrary product to the product of the tensors.
- `source-facing`: the TFAE identifying finite generation of `M` with surjectivity of those
  comparison maps.
- `core/canonical`: the owner maps `TensorProduct.piRightHom` and `TensorProduct.piScalarRightHom`
  from mathlib.
- `bridge/view`: the constant-family and scalar-family clauses are just specializations of those
  owner maps, not separate primitive data.
Primitive data are only the semiring, the module, and the chosen family `Q`. -/

-- Proof sketch: `(1) → (2)` is proved by choosing a surjection from a finite free module onto `M`
-- and comparing the induced commutative square with `TensorProduct.piRight` for the finite free
-- source. The implications `(2) → (3) → (4)` are obtained by specialization. For `(4) → (1)`,
-- apply surjectivity for the index set `M` to the diagonal element `fun x ↦ x : M → M`; a
-- preimage is a finite sum of pure tensors, whose left tensor factors then generate `M`.
/-- Helper for Proposition 10.89.2: a tensor with a finite free module on the left is identified
with a finite tuple by commuting the tensor factors and then applying `piScalarRight`. -/
def fin_free_tensor_equiv (n : ℕ) (X : Type*) [AddCommMonoid X] [Module R X] :
    ((Fin n → R) ⊗[R] X) ≃ₗ[R] Fin n → X :=
  TensorProduct.comm R (Fin n → R) X ≪≫ₗ TensorProduct.piScalarRight R R X (Fin n)

/-- Helper for Proposition 10.89.2: after identifying finite free tensors with tuples,
`TensorProduct.piRightHom` evaluates those tuples coordinatewise. -/
lemma piRightHom_fin_free_tensor_equiv {n : ℕ} {A : Type w} {Q : A → Type x}
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)]
    (t : ((Fin n → R) ⊗[R] (∀ a, Q a))) :
    (fun a ↦ fin_free_tensor_equiv (R := R) n (Q a)
        ((TensorProduct.piRightHom R R (Fin n → R) Q t) a)) =
      fun a i ↦ fin_free_tensor_equiv (R := R) n (∀ a, Q a) t i a := by
  -- Reduce the comparison to pure tensors, where both sides compute directly.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a i
    simp [fin_free_tensor_equiv]
  · intro f q
    ext a i
    simp [fin_free_tensor_equiv, TensorProduct.piRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a i
    simp only [map_add, Pi.add_apply]
    rw [congr_fun (congr_fun ht₁ a) i, congr_fun (congr_fun ht₂ a) i]

/-- Helper for Proposition 10.89.2: for a finite free left tensor factor,
`TensorProduct.piRightHom` is surjective. -/
lemma piRightHom_surjective_fin_free (n : ℕ) (A : Type w) (Q : A → Type x)
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R (Fin n → R) Q) := by
  intro y
  -- Pull the target family back to a tuple of functions on `Fin n`.
  let z : Fin n → ∀ a, Q a := fun i a ↦ fin_free_tensor_equiv (R := R) n (Q a) (y a) i
  refine ⟨(fin_free_tensor_equiv (R := R) n (∀ a, Q a)).symm z, ?_⟩
  ext a
  apply (fin_free_tensor_equiv (R := R) n (Q a)).injective
  -- The comparison lemma identifies the image with the chosen coordinatewise preimage.
  simpa [z] using congr_fun
    (piRightHom_fin_free_tensor_equiv (R := R) (Q := Q)
      ((fin_free_tensor_equiv (R := R) n (∀ a, Q a)).symm z)) a

/-- Helper for Proposition 10.89.2: tensoring a surjection with a product commutes with the
canonical comparison map to the product of the tensor factors. -/
lemma piRightHom_rTensor_apply {n : ℕ} {A : Type w} {Q : A → Type x}
    [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)]
    (f : (Fin n → R) →ₗ[R] M) (t : ((Fin n → R) ⊗[R] (∀ a, Q a))) :
    TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) t) =
      fun a ↦ f.rTensor (Q a) ((TensorProduct.piRightHom R R (Fin n → R) Q t) a) := by
  -- Check the square on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp
  · intro x q
    ext a
    simp [TensorProduct.piRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.2: if a surjective family-valued element lies in the image of
`TensorProduct.piScalarRightHom`, then the left tensor factors of a finite decomposition generate
`M`. -/
lemma module_finite_of_piScalarRightHom_eq_surjective {A : Type w} {d : A → M}
    (hd : Function.Surjective d) {t : M ⊗[R] (A → R)}
    (ht : TensorProduct.piScalarRightHom R R M A t = d) :
    Module.Finite R M := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finsupp_left t
  let generators : Finset M := S.support
  have hx_mem_span : ∀ x : M, x ∈ Submodule.span R (↑generators : Set M) := by
    intro x
    obtain ⟨a, rfl⟩ := hd x
    -- Evaluate the diagonal identity at `x` to obtain an explicit finite linear combination.
    have hx : d a = generators.sum fun m ↦ S m a • m := by
      calc
        d a = (TensorProduct.piScalarRightHom R R M A t) a := by simpa [ht]
        _ = (TensorProduct.piScalarRightHom R R M A (S.sum fun m n ↦ m ⊗ₜ[R] n)) a := by rw [hS]
        _ = generators.sum fun m ↦ S m a • m := by
              simpa [generators, Finsupp.sum]
    refine (Submodule.mem_span_finset).2 ?_
    refine ⟨fun m ↦ S m a, ?_, ?_⟩
    · intro m hm
      by_contra hm_support
      have hzero : S m = 0 := by
        by_contra hne
        exact hm_support (Finsupp.mem_support_iff.mpr hne)
      exact hm (by simp [hzero])
    · simpa using hx.symm
  have htop : ⊤ ≤ Submodule.span R (↑generators : Set M) := by
    intro x hx
    exact hx_mem_span x
  have hspan_top : Submodule.span R (↑generators : Set M) = ⊤ := top_le_iff.mp htop
  letI : Module.Finite R (Submodule.span R (↑generators : Set M)) :=
    Module.Finite.span_of_finite R (Set.toFinite _)
  have hfinite_span : Module.Finite R (Submodule.span R (↑generators : Set M)) := inferInstance
  have hfinite_top : Module.Finite R (⊤ : Submodule R M) := by
    exact hspan_top ▸ hfinite_span
  letI : Module.Finite R (⊤ : Submodule R M) := hfinite_top
  -- Replace `M` by the span of the extracted finite generating set.
  exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M)

/-- Helper for Proposition 10.89.2: replacing the constant family `ULift R` by `R` on the tensor
source is a linear equivalence. -/
def pi_ulift_scalar_domain_equiv (A : Type (max v w)) :
    (M ⊗[R] (A → ULift.{max u x} R)) ≃ₗ[R] (M ⊗[R] (A → R)) :=
  TensorProduct.congr (LinearEquiv.refl R M)
    (LinearEquiv.piCongrRight fun _ ↦ ULift.moduleEquiv)

/-- Helper for Proposition 10.89.2: replacing the constant family `ULift R` by `R` on the target
product is a linear equivalence. -/
def pi_ulift_scalar_codomain_equiv (A : Type (max v w)) :
    (A → M ⊗[R] ULift.{max u x} R) ≃ₗ[R] (A → M) :=
  LinearEquiv.piCongrRight fun _ ↦
    TensorProduct.congr (LinearEquiv.refl R M) ULift.moduleEquiv ≪≫ₗ TensorProduct.rid R M

/-- Helper for Proposition 10.89.2: after transporting the constant family `ULift R` back to `R`,
the canonical map `TensorProduct.piRightHom` becomes `TensorProduct.piScalarRightHom`. -/
lemma piScalarRightHom_eq_piRightHom_ulift (A : Type (max v w))
    (t : M ⊗[R] (A → ULift.{max u x} R)) :
    TensorProduct.piScalarRightHom R R M A ((pi_ulift_scalar_domain_equiv (R := R) (M := M) A) t) =
      pi_ulift_scalar_codomain_equiv (R := R) (M := M) A
        (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
  -- Both sides are linear in `t`, so it suffices to compute on pure tensors.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp [pi_ulift_scalar_domain_equiv, pi_ulift_scalar_codomain_equiv]
  · intro m f
    ext a
    simp [pi_ulift_scalar_domain_equiv, pi_ulift_scalar_codomain_equiv,
      TensorProduct.piRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Proposition 10.89.2: for an `R`-module `M`, the following are equivalent: `M` is finitely
generated; for every family `(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is surjective; for every `R`-module `Q` and every set
`A`, the canonical map `M ⊗[R] (A → Q) → A → (M ⊗[R] Q)` is surjective; and for every set `A`,
the canonical map `M ⊗[R] (A → R) → A → M` is surjective. -/
theorem module_finite_tfae_tensorProduct_pi_surjective :
    List.TFAE
      [ Module.Finite R M,
        ∀ (A : Type (max v w)) (Q : A → Type (max u x))
            [∀ a, AddCommMonoid (Q a)] [∀ a, Module R (Q a)],
          Function.Surjective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type (max v w)) (Q : Type (max u x)) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ (A : Type (max v w)),
          Function.Surjective (TensorProduct.piScalarRightHom R R M A) ] := by
  -- Follow the textbook route `(1) → (2) → (3) → (4) → (1)`.
  tfae_have 1 → 2 := by
    intro hM
    letI : Module.Finite R M := hM
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    intro A Q _ _ y
    -- Pull back each coordinate along the finite free presentation of `M`.
    obtain ⟨y₀, hy₀⟩ := Function.Surjective.piMap
      (fun a ↦ LinearMap.rTensor_surjective (Q a) hf) y
    obtain ⟨t, ht⟩ := piRightHom_surjective_fin_free (R := R) n A Q y₀
    refine ⟨f.rTensor (∀ a, Q a) t, ?_⟩
    ext a
    -- The commutative square transfers the finite-free surjectivity to `M`.
    calc
      TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) t) a
          = f.rTensor (Q a) ((TensorProduct.piRightHom R R (Fin n → R) Q t) a) := by
              simpa using congr_fun
                (piRightHom_rTensor_apply (R := R) (M := M) (Q := Q) f t) a
      _ = f.rTensor (Q a) (y₀ a) := by rw [ht]
      _ = y a := by simpa using congr_fun hy₀ a
  tfae_have 2 → 3 := by
    intro h A Q _ _
    -- This is the constant-family specialization of clause `(2)`.
    simpa using h A (fun _ : A ↦ Q)
  tfae_have 3 → 4 := by
    intro h A
    -- Specialize clause `(3)` to `ULift R` and transport back along the canonical equivalences.
    let y' := (pi_ulift_scalar_codomain_equiv (R := R) (M := M) A).symm
    intro y
    obtain ⟨t, ht⟩ := h A (ULift.{max u x} R) (y' y)
    refine ⟨(pi_ulift_scalar_domain_equiv (R := R) (M := M) A) t, ?_⟩
    calc
      TensorProduct.piScalarRightHom R R M A
          ((pi_ulift_scalar_domain_equiv (R := R) (M := M) A) t)
          = pi_ulift_scalar_codomain_equiv (R := R) (M := M) A
              (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
                  simpa using piScalarRightHom_eq_piRightHom_ulift (R := R) (M := M) A t
      _ = pi_ulift_scalar_codomain_equiv (R := R) (M := M) A (y' y) := by rw [ht]
      _ = y := by simp [y']
  tfae_have 4 → 1 := by
    intro h
    -- Use a preimage of the diagonal element indexed by `ULift M` to extract generators.
    obtain ⟨t, ht⟩ := h (ULift.{max v w} M) ULift.down
    exact module_finite_of_piScalarRightHom_eq_surjective
      (R := R) (M := M) (A := ULift.{max v w} M)
      (d := ULift.down) (fun x ↦ ⟨⟨x⟩, rfl⟩) ht
  tfae_finish

end

/-! ### Proposition_10_89_3 (from Chap10) -/
universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped TensorProduct

/- Domain triage: this proposition is about the tensor-product comparison map from a tensor with
an arbitrary product to the product of the tensors.
- `source-facing`: the TFAE identifying finite presentation of `M` with bijectivity of those
  comparison maps.
- `core/canonical`: the owner maps `TensorProduct.piRightHom` and `TensorProduct.piScalarRightHom`
  from mathlib.
- `bridge/view`: the constant-family and scalar-family clauses are just specializations of those
  owner maps, not separate primitive data.
Primitive data are only the ring, the module, and the chosen family `Q`. -/

/- Route correction: the statement needs the same universe alignment as Proposition `10.89.2`.
The source-faithful proof tests clause `(4)` on `ULift M`, so the product index universe must be
large enough to contain `M`. -/

-- Proof sketch: `(1) → (2)` follows from a finite presentation of `M` and exactness of tensor
-- product, using that finite products commute with tensoring by finite free modules. The
-- implications `(2) → (3) → (4)` are immediate specializations. For `(4) → (1)`, combine
-- Proposition `10.89.2` to obtain finite generation of `M`, choose a surjection from a finite free
-- module onto `M`, and compare kernels after tensoring with `R^A`; surjectivity of the induced map
-- on the kernel then yields finite generation of that kernel, hence finite presentation of `M`.
/-- Helper for Proposition 10.89.3: `TensorProduct.piRightHom` commutes with tensoring a map on
the left. -/
lemma piRightHom_rTensor_apply_linear {X : Type*} [AddCommGroup X] [Module R X] {Y : Type*}
    [AddCommGroup Y] [Module R Y] {A : Type w} {Q : A → Type x}
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] (f : X →ₗ[R] Y)
    (t : X ⊗[R] (∀ a, Q a)) :
    TensorProduct.piRightHom R R Y Q (f.rTensor (∀ a, Q a) t) =
      fun a ↦ f.rTensor (Q a) ((TensorProduct.piRightHom R R X Q t) a) := by
  -- Compute on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp
  · intro x q
    ext a
    simp [TensorProduct.piRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: `TensorProduct.piScalarRightHom` commutes with tensoring a map
on the left. -/
lemma piScalarRightHom_rTensor_apply {X : Type*} [AddCommGroup X] [Module R X] {Y : Type*}
    [AddCommGroup Y] [Module R Y] {A : Type w} (f : X →ₗ[R] Y)
    (t : X ⊗[R] (A → R)) :
    TensorProduct.piScalarRightHom R R Y A (f.rTensor (A → R) t) =
      fun a ↦ f ((TensorProduct.piScalarRightHom R R X A t) a) := by
  -- Compute on pure tensors and extend by tensor induction.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp
  · intro x q
    ext a
    simp [TensorProduct.piScalarRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: after identifying a tensor with a finite free module on the
left with a tuple, `TensorProduct.piScalarRightHom` is just transposition of indices. -/
lemma piScalarRightHom_fin_free_tensor_equiv {n : ℕ} {A : Type w}
    (t : ((Fin n → R) ⊗[R] (A → R))) :
    TensorProduct.piScalarRightHom R R (Fin n → R) A t =
      fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t i a := by
  -- Reduce to pure tensors, where both sides are coordinatewise evaluation.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a i
    simp [fin_free_tensor_equiv]
  · intro f q
    ext a i
    simp [fin_free_tensor_equiv, TensorProduct.piScalarRightHom_tmul, mul_comm]
  · intro t₁ t₂ ht₁ ht₂
    ext a i
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: for a finite free module on the left,
`TensorProduct.piRightHom` is bijective. -/
lemma piRightHom_bijective_fin_free (n : ℕ) (A : Type w) (Q : A → Type x)
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) Q) := by
  constructor
  · intro t₁ t₂ h
    apply (fin_free_tensor_equiv (R := R) n (∀ a, Q a)).injective
    ext i a
    have hcoord :
        fin_free_tensor_equiv (R := R) n (Q a)
          ((TensorProduct.piRightHom R R (Fin n → R) Q t₁) a) =
        fin_free_tensor_equiv (R := R) n (Q a)
          ((TensorProduct.piRightHom R R (Fin n → R) Q t₂) a) := by
      exact congrArg (fin_free_tensor_equiv (R := R) n (Q a)) (congr_fun h a)
    have h₁ := congr_fun (piRightHom_fin_free_tensor_equiv (R := R) (Q := Q) t₁) a
    have h₂ := congr_fun (piRightHom_fin_free_tensor_equiv (R := R) (Q := Q) t₂) a
    calc
      fin_free_tensor_equiv (R := R) n (∀ a, Q a) t₁ i a
          = fin_free_tensor_equiv (R := R) n (Q a)
              ((TensorProduct.piRightHom R R (Fin n → R) Q t₁) a) i := by
                  simpa using (congr_fun h₁ i).symm
      _ = fin_free_tensor_equiv (R := R) n (Q a)
            ((TensorProduct.piRightHom R R (Fin n → R) Q t₂) a) i := by
              simpa using congr_fun hcoord i
      _ = fin_free_tensor_equiv (R := R) n (∀ a, Q a) t₂ i a := by
            simpa using congr_fun h₂ i
  · -- Reuse the finite-generation surjectivity lemma from Proposition `10.89.2`.
    exact piRightHom_surjective_fin_free (R := R) n A Q

/-- Helper for Proposition 10.89.3: for a finite free module on the left,
`TensorProduct.piScalarRightHom` is bijective. -/
lemma piScalarRightHom_bijective_fin_free (n : ℕ) (A : Type w) :
    Function.Bijective (TensorProduct.piScalarRightHom R R (Fin n → R) A) := by
  constructor
  · intro t₁ t₂ h
    apply (fin_free_tensor_equiv (R := R) n (A → R)).injective
    ext i a
    have hswap :
        (fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₁ i a) =
          fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₂ i a := by
      calc
        (fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₁ i a)
            = TensorProduct.piScalarRightHom R R (Fin n → R) A t₁ := by
                symm
                exact piScalarRightHom_fin_free_tensor_equiv (R := R) t₁
        _ = TensorProduct.piScalarRightHom R R (Fin n → R) A t₂ := h
        _ = (fun a i ↦ fin_free_tensor_equiv (R := R) n (A → R) t₂ i a) := by
              exact piScalarRightHom_fin_free_tensor_equiv (R := R) t₂
    exact congr_fun (congr_fun hswap a) i
  · intro y
    let z : Fin n → A → R := fun i a ↦ y a i
    refine ⟨(fin_free_tensor_equiv (R := R) n (A → R)).symm z, ?_⟩
    ext a i
    -- The finite-free tensor identification turns the map into index transposition.
    simpa [z] using congr_fun
      (congr_fun
        (piScalarRightHom_fin_free_tensor_equiv (R := R)
          ((fin_free_tensor_equiv (R := R) n (A → R)).symm z)) a) i

/-- Helper for Proposition 10.89.3: finite modules satisfy surjectivity of
`TensorProduct.piRightHom` for arbitrary index and fiber universes. -/
lemma piRightHom_surjective_of_finite_universe_lift {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] {A : Type w} {Q : A → Type x}
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R N Q) := by
  intro y
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  obtain ⟨y₀, hy₀⟩ := Function.Surjective.piMap
    (fun a ↦ LinearMap.rTensor_surjective (Q a) hf) y
  obtain ⟨t, ht⟩ := piRightHom_surjective_fin_free (R := R) n A Q y₀
  refine ⟨f.rTensor (∀ a, Q a) t, ?_⟩
  ext a
  calc
    TensorProduct.piRightHom R R N Q (f.rTensor (∀ a, Q a) t) a
        = f.rTensor (Q a) ((TensorProduct.piRightHom R R (Fin n → R) Q t) a) := by
            simpa using congr_fun
              (piRightHom_rTensor_apply_linear (R := R) (Q := Q) f t) a
    _ = f.rTensor (Q a) (y₀ a) := by rw [ht]
    _ = y a := by simpa using congr_fun hy₀ a

/-- Helper for Proposition 10.89.3: replacing the constant family `ULift R` by `R` on the tensor
source is a linear equivalence for arbitrary index universes. -/
def pi_ulift_scalar_domain_equiv_univ (A : Type*) :
    (M ⊗[R] (A → ULift.{max u x} R)) ≃ₗ[R] (M ⊗[R] (A → R)) :=
  TensorProduct.congr (LinearEquiv.refl R M)
    (LinearEquiv.piCongrRight fun _ ↦ ULift.moduleEquiv)

/-- Helper for Proposition 10.89.3: replacing the constant family `ULift R` by `R` on the target
product is a linear equivalence for arbitrary index universes. -/
def pi_ulift_scalar_codomain_equiv_univ (A : Type*) :
    (A → M ⊗[R] ULift.{max u x} R) ≃ₗ[R] (A → M) :=
  LinearEquiv.piCongrRight fun _ ↦
    TensorProduct.congr (LinearEquiv.refl R M) ULift.moduleEquiv ≪≫ₗ TensorProduct.rid R M

/-- Helper for Proposition 10.89.3: after transporting the constant family `ULift R` back to `R`
for an arbitrary index universe, the canonical map `TensorProduct.piRightHom` becomes
`TensorProduct.piScalarRightHom`. -/
lemma piScalarRightHom_eq_piRightHom_ulift_univ (A : Type*)
    (t : M ⊗[R] (A → ULift.{max u x} R)) :
    TensorProduct.piScalarRightHom R R M A
        ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) t) =
      pi_ulift_scalar_codomain_equiv_univ (R := R) (M := M) A
        (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
  -- Both sides are linear in `t`, so it suffices to compute on pure tensors.
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · ext a
    simp [pi_ulift_scalar_domain_equiv_univ, pi_ulift_scalar_codomain_equiv_univ]
  · intro m f
    ext a
    simp [pi_ulift_scalar_domain_equiv_univ, pi_ulift_scalar_codomain_equiv_univ,
      TensorProduct.piRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
  · intro t₁ t₂ ht₁ ht₂
    ext a
    simp [ht₁, ht₂]

/-- Helper for Proposition 10.89.3: bijectivity of `TensorProduct.piScalarRightHom` is equivalent
to bijectivity of the constant-family comparison map with coefficients in `ULift R`. -/
lemma piScalarRightHom_bijective_iff_piRightHom_ulift_bijective
    (A : Type (max u v w)) :
    Function.Bijective (TensorProduct.piScalarRightHom R R M A) ↔
      Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R)) := by
  let d := pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A
  let c := pi_ulift_scalar_codomain_equiv_univ (R := R) (M := M) A
  constructor
  · intro hScalar
    constructor
    · intro t₁ t₂ hEq
      have hEq' :
          TensorProduct.piScalarRightHom R R M A (d t₁) =
            TensorProduct.piScalarRightHom R R M A (d t₂) := by
        calc
          TensorProduct.piScalarRightHom R R M A (d t₁)
              = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t₁) := by
                  simpa [d, c] using
                    piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A t₁
          _ = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t₂) := by
                rw [hEq]
          _ = TensorProduct.piScalarRightHom R R M A (d t₂) := by
                simpa [d, c] using
                  (piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A t₂).symm
      exact d.injective (hScalar.1 hEq')
    · intro y
      let y' := c y
      obtain ⟨t, ht⟩ := hScalar.2 y'
      have hd : d (d.symm t) = t := by
        simpa [d] using d.apply_symm_apply t
      have htransport :
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) (d.symm t)) =
            TensorProduct.piScalarRightHom R R M A (d (d.symm t)) := by
        calc
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) (d.symm t))
              = TensorProduct.piScalarRightHom R R M A
                  ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) (d.symm t)) := by
                    simpa [c] using
                      (piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A
                        (d.symm t)).symm
          _ = TensorProduct.piScalarRightHom R R M A (d (d.symm t)) := by rfl
      refine ⟨d.symm t, ?_⟩
      apply c.injective
      calc
        c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) (d.symm t))
            = TensorProduct.piScalarRightHom R R M A (d (d.symm t)) := htransport
        _ = TensorProduct.piScalarRightHom R R M A t := by rw [hd]
        _ = y' := ht
        _ = c y := rfl
  · intro hPi
    constructor
    · intro t₁ t₂ hEq
      let s₁ := d.symm t₁
      let s₂ := d.symm t₂
      have hs₁ : d s₁ = t₁ := by
        simpa [s₁, d] using d.apply_symm_apply t₁
      have hs₂ : d s₂ = t₂ := by
        simpa [s₂, d] using d.apply_symm_apply t₂
      have hs₁_transport :
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁) =
            TensorProduct.piScalarRightHom R R M A (d s₁) := by
        calc
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁)
              = TensorProduct.piScalarRightHom R R M A
                  ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) s₁) := by
                    simpa [c] using
                      (piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A s₁).symm
          _ = TensorProduct.piScalarRightHom R R M A (d s₁) := by rfl
      have hs₂_transport :
          TensorProduct.piScalarRightHom R R M A (d s₂) =
            c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂) := by
        calc
          TensorProduct.piScalarRightHom R R M A (d s₂)
              = TensorProduct.piScalarRightHom R R M A
                  ((pi_ulift_scalar_domain_equiv_univ (R := R) (M := M) A) s₂) := by
                    rfl
          _ = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂) := by
                simpa [c] using
                  piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A s₂
      have hEq' :
          TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁ =
            TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂ := by
        apply c.injective
        calc
          c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₁)
              = TensorProduct.piScalarRightHom R R M A (d s₁) := hs₁_transport
          _ = TensorProduct.piScalarRightHom R R M A t₁ := by rw [hs₁]
          _ = TensorProduct.piScalarRightHom R R M A t₂ := hEq
          _ = TensorProduct.piScalarRightHom R R M A (d s₂) := by rw [hs₂]
          _ = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) s₂) :=
                hs₂_transport
      simpa [s₁, s₂, d] using congrArg d (hPi.1 hEq')
    · intro y
      let y' := c.symm y
      obtain ⟨t, ht⟩ := hPi.2 y'
      refine ⟨d t, ?_⟩
      calc
        TensorProduct.piScalarRightHom R R M A (d t)
            = c (TensorProduct.piRightHom R R M (fun _ : A ↦ ULift.{max u x} R) t) := by
                simpa [d, c] using
                      piScalarRightHom_eq_piRightHom_ulift_univ (R := R) (M := M) A t
        _ = c y' := by rw [ht]
        _ = y := by simp [y']

/-- Helper for Proposition 10.89.3: exactness plus surjectivity on the kernel and bijectivity on
the finite free cover give bijectivity on the quotient module. -/
lemma piRightHom_bijective_of_exact {K : Type*} [AddCommGroup K] [Module R K] {F : Type*}
    [AddCommGroup F] [Module R F] (κ : K →ₗ[R] F) (π : F →ₗ[R] M)
    (hExact : Function.Exact κ π) (hπ : Function.Surjective π) {A : Type w}
    {Q : A → Type x} [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    (hK : Function.Surjective (TensorProduct.piRightHom R R K Q))
    (hF : Function.Bijective (TensorProduct.piRightHom R R F Q)) :
    Function.Bijective (TensorProduct.piRightHom R R M Q) := by
  constructor
  · intro t₁ t₂ hEq
    obtain ⟨u, hu⟩ := LinearMap.rTensor_surjective (∀ a, Q a) hπ (t₁ - t₂)
    have hcoord_zero :
        ∀ a,
          π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q u) a) = 0 := by
      intro a
      calc
        π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q u) a)
            = TensorProduct.piRightHom R R M Q (π.rTensor (∀ a, Q a) u) a := by
                symm
                simpa using congr_fun
                  (piRightHom_rTensor_apply_linear (R := R) (Q := Q) π u) a
        _ = TensorProduct.piRightHom R R M Q (t₁ - t₂) a := by rw [hu]
        _ = (TensorProduct.piRightHom R R M Q t₁) a -
              (TensorProduct.piRightHom R R M Q t₂) a := by
                simp
        _ = 0 := by
              simpa using sub_eq_zero.mpr (congr_fun hEq a)
    have hcoord_range :
        ∀ a, (TensorProduct.piRightHom R R F Q u) a ∈
          LinearMap.range (κ.rTensor (Q a)) := by
      intro a
      rw [← Function.Exact.linearMap_ker_eq (rTensor_exact (Q a) hExact hπ)]
      simpa [LinearMap.mem_ker] using hcoord_zero a
    classical
    choose z hz using hcoord_range
    obtain ⟨s, hs⟩ := hK z
    have hu_eq :
        u = κ.rTensor (∀ a, Q a) s := by
      apply hF.1
      ext a
      calc
        TensorProduct.piRightHom R R F Q u a = κ.rTensor (Q a) (z a) := (hz a).symm
        _ = κ.rTensor (Q a) ((TensorProduct.piRightHom R R K Q s) a) := by rw [hs]
        _ = TensorProduct.piRightHom R R F Q (κ.rTensor (∀ a, Q a) s) a := by
              symm
              simpa using congr_fun
                (piRightHom_rTensor_apply_linear (R := R) (Q := Q) κ s) a
    have hsub : t₁ - t₂ = 0 := by
      calc
        t₁ - t₂ = π.rTensor (∀ a, Q a) u := hu.symm
        _ = π.rTensor (∀ a, Q a) (κ.rTensor (∀ a, Q a) s) := by rw [hu_eq]
        _ = ((π.rTensor (∀ a, Q a)).comp (κ.rTensor (∀ a, Q a))) s := rfl
        _ = ((π.comp κ).rTensor (∀ a, Q a)) s := by
              rw [← LinearMap.rTensor_comp]
        _ = 0 := by
              rw [hExact.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
    exact sub_eq_zero.mp hsub
  · intro y
    -- Lift the target family coordinatewise through `π`, then use bijectivity on `F`.
    obtain ⟨y₀, hy₀⟩ := Function.Surjective.piMap
      (fun a ↦ LinearMap.rTensor_surjective (Q a) hπ) y
    obtain ⟨t, ht⟩ := hF.2 y₀
    refine ⟨π.rTensor (∀ a, Q a) t, ?_⟩
    ext a
    calc
      TensorProduct.piRightHom R R M Q (π.rTensor (∀ a, Q a) t) a
          = π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q t) a) := by
              simpa using congr_fun
                (piRightHom_rTensor_apply_linear (R := R) (Q := Q) π t) a
      _ = π.rTensor (Q a) (y₀ a) := by rw [ht]
      _ = y a := by simpa using congr_fun hy₀ a

/-- Helper for Proposition 10.89.3: if the scalar comparison maps are bijective for a surjection
from a finite free module onto `M`, then the scalar comparison map is surjective on the kernel. -/
lemma piScalarRightHom_surjective_of_exact {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (A : Type w)
    (hF : Function.Bijective (TensorProduct.piScalarRightHom R R F A))
    (hM : Function.Bijective (TensorProduct.piScalarRightHom R R M A)) :
    Function.Surjective (TensorProduct.piScalarRightHom R R (LinearMap.ker π) A) := by
  intro y
  let yF : A → F := fun a ↦ y a
  -- Lift the family of kernel elements to the finite free cover.
  obtain ⟨tF, htF⟩ := hF.2 yF
  have htF_zero : π.rTensor (A → R) tF = 0 := by
    apply hM.1
    ext a
    calc
      TensorProduct.piScalarRightHom R R M A (π.rTensor (A → R) tF) a
          = π ((TensorProduct.piScalarRightHom R R F A tF) a) := by
              simpa using congr_fun
                (piScalarRightHom_rTensor_apply (R := R) (A := A) π tF) a
      _ = π (yF a) := by rw [htF]
      _ = 0 := by
            change π (y a) = 0
            exact (y a).property
  have hmem : tF ∈ LinearMap.range ((LinearMap.ker π).subtype.rTensor (A → R)) := by
    rw [← Function.Exact.linearMap_ker_eq
      (rTensor_exact (A → R) (LinearMap.exact_subtype_ker_map π) hπ)]
    simpa [LinearMap.mem_ker] using htF_zero
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, ?_⟩
  ext a
  calc
    (((TensorProduct.piScalarRightHom R R (LinearMap.ker π) A u) a : LinearMap.ker π) : F)
        = TensorProduct.piScalarRightHom R R F A
            ((LinearMap.ker π).subtype.rTensor (A → R) u) a := by
              symm
              simpa using congr_fun
                (piScalarRightHom_rTensor_apply (R := R) (A := A)
                  (LinearMap.ker π).subtype u) a
    _ = yF a := by rw [hu, htF]
    _ = y a := rfl

/-- Proposition 10.89.3: for an `R`-module `M`, the following are equivalent: `M` is finitely
presented; for every family `(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is bijective; for every `R`-module `Q` and every set `A`,
the canonical map `M ⊗[R] (A → Q) → A → (M ⊗[R] Q)` is bijective; and for every set `A`, the
canonical map `M ⊗[R] (A → R) → A → M` is bijective. -/
theorem module_finitePresentation_tfae_tensorProduct_pi_bijective :
    List.TFAE
      [ Module.FinitePresentation R M,
        ∀ (A : Type (max u v w)) (Q : A → Type (max u x))
            [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Bijective (TensorProduct.piRightHom R R M Q),
        ∀ (A : Type (max u v w)) (Q : Type (max u x)) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)),
        ∀ (A : Type (max u v w)),
          Function.Bijective (TensorProduct.piScalarRightHom R R M A) ] := by
  -- Route correction: align the quantified index universe with the ring universe so clause `(4)`
  -- can be tested on `ULift (LinearMap.ker π)` in the kernel step of the source proof.
  tfae_have 1 → 2 := by
    intro hM
    letI : Module.FinitePresentation R M := hM
    letI : Module.Finite R M := inferInstance
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    letI : Module.Finite R (LinearMap.ker π) := by
      exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker π hπ)
    intro A Q _ _
    -- Compare the exact rows obtained from the finite free cover of `M`.
    exact piRightHom_bijective_of_exact
      (R := R) ((LinearMap.ker π).subtype) π
      (LinearMap.exact_subtype_ker_map π) hπ
      (piRightHom_surjective_of_finite_universe_lift (R := R)
        (N := LinearMap.ker π) (A := A) (Q := Q))
      (piRightHom_bijective_fin_free (R := R) n A Q)
  tfae_have 2 → 3 := by
    intro h A Q _ _
    -- This is the constant-family specialization of clause `(2)`.
    simpa using h A (fun _ : A ↦ Q)
  tfae_have 3 → 4 := by
    intro h A
    -- Transport the constant `ULift R` family back to the scalar comparison map.
    exact (piScalarRightHom_bijective_iff_piRightHom_ulift_bijective
      (R := R) (M := M) A).2 (h A (ULift.{max u x} R))
  tfae_have 4 → 1 := by
    intro h
    have hMfinite : Module.Finite R M := by
      obtain ⟨t, ht⟩ := (h (ULift.{max u v w} M)).2 ULift.down
      exact module_finite_of_piScalarRightHom_eq_surjective
        (R := R) (M := M) (A := ULift.{max u v w} M) (d := ULift.down)
        (fun x ↦ ⟨⟨x⟩, rfl⟩) ht
    letI : Module.Finite R M := hMfinite
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    have hker_surj :
        ∀ (A : Type (max u v w)),
          Function.Surjective
            (TensorProduct.piScalarRightHom R R (LinearMap.ker π) A) := by
      intro A
      -- The second source diagram chase transfers scalar-map surjectivity to the kernel.
      exact piScalarRightHom_surjective_of_exact (R := R) π hπ A
        (piScalarRightHom_bijective_fin_free (R := R) n A) (h A)
    have hker_finite : Module.Finite R (LinearMap.ker π) := by
      obtain ⟨t, ht⟩ := hker_surj (ULift.{max u v w} (LinearMap.ker π)) ULift.down
      exact module_finite_of_piScalarRightHom_eq_surjective
        (R := R) (M := LinearMap.ker π) (A := ULift.{max u v w} (LinearMap.ker π))
        (d := ULift.down) (fun x ↦ ⟨⟨x⟩, rfl⟩) ht
    letI : Module.Finite R (LinearMap.ker π) := hker_finite
    -- Finite generation of the kernel upgrades the finite free cover to a finite presentation.
    exact Module.finitePresentation_of_surjective π hπ Submodule.FG.of_finite
  tfae_finish

end
