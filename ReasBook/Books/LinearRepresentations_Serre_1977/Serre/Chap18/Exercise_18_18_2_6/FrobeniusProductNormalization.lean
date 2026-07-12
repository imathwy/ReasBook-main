import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section

namespace Representation

variable {k : Type*} [Field k]

/-- Helper for Exercise 18-18.2-6: split a product of polynomial powers into the common
residue exponents modulo `p` and the `p`-th power of the quotient-exponent product. -/
lemma polynomial_prod_pow_decompose_mod_char
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k) (m : ι → ℕ) (p : ℕ) :
    (∏ i ∈ s, f i ^ m i) =
      (∏ i ∈ s, f i ^ (m i % p)) * (∏ i ∈ s, f i ^ (m i / p)) ^ p := by
  -- Rewrite each exponent as residue plus characteristic times quotient, then collect the
  -- quotient terms into a single `p`-th power.
  calc
    (∏ i ∈ s, f i ^ m i) =
        ∏ i ∈ s, (f i ^ (m i % p) * (f i ^ (m i / p)) ^ p) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      conv_lhs => rw [← Nat.mod_add_div (m i) p]
      rw [pow_add]
      rw [Nat.mul_comm p (m i / p)]
      rw [pow_mul]
    _ =
        (∏ i ∈ s, f i ^ (m i % p)) *
          ∏ i ∈ s, (f i ^ (m i / p)) ^ p := by
      rw [Finset.prod_mul_distrib]
    _ =
        (∏ i ∈ s, f i ^ (m i % p)) *
          (∏ i ∈ s, f i ^ (m i / p)) ^ p := by
      rw [Finset.prod_pow]

/-- Helper for Exercise 18-18.2-6: a product of powers of constant-term-one polynomials is
nonzero, because its constant coefficient is still `1`. -/
lemma polynomial_prod_pow_ne_zero_of_coeff_zero_eq_one
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k) (e : ι → ℕ)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) :
    ((∏ i ∈ s, f i ^ e i) : Polynomial k) ≠ 0 := by
  intro hzero
  have hc0 : ((∏ i ∈ s, f i ^ e i) : Polynomial k).coeff 0 = 1 := by
    -- Evaluate the constant coefficient factorwise; every factor contributes `1`.
    rw [Polynomial.coeff_zero_prod]
    refine Finset.prod_eq_one ?_
    intro i hi
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      ← Polynomial.coeff_zero_eq_eval_zero, h0 i hi]
    simp
  -- A zero polynomial cannot have constant coefficient `1`.
  have hzcoeff := congrArg (fun q : Polynomial k ↦ q.coeff 0) hzero
  simp [hc0] at hzcoeff

/-- Helper for Exercise 18-18.2-6: in prime characteristic, if two finite products of
constant-term-one polynomial powers are equal and all exponents have the same residue modulo the
characteristic, then the quotient-exponent products are equal. -/
lemma polynomial_prod_pow_div_eq_of_prod_pow_eq_of_cast_eq
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k) (m n : ι → ℕ)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1)
    (hprod : ((∏ i ∈ s, f i ^ m i) : Polynomial k) =
      ((∏ i ∈ s, f i ^ n i) : Polynomial k))
    (hcast : ∀ i ∈ s, (m i : k) = (n i : k)) :
    ((∏ i ∈ s, f i ^ (m i / p)) : Polynomial k) =
      ((∏ i ∈ s, f i ^ (n i / p)) : Polynomial k) := by
  let c : Polynomial k := ∏ i ∈ s, f i ^ (m i % p)
  let qM : Polynomial k := ∏ i ∈ s, f i ^ (m i / p)
  let qN : Polynomial k := ∏ i ∈ s, f i ^ (n i / p)
  have hmod : ∀ i ∈ s, m i % p = n i % p := by
    intro i hi
    -- Equal casts in characteristic `p` are exactly equal residues modulo `p`.
    exact (CharP.cast_eq_iff_mod_eq k p).mp (hcast i hi)
  have hresidue : (∏ i ∈ s, f i ^ (n i % p)) = c := by
    -- Replace the right residues by the left residues, so both sides have the same cancelland.
    dsimp [c]
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [← hmod i hi]
  have hc_ne : c ≠ 0 := by
    -- The common residue product has constant coefficient `1`, hence is cancellable.
    dsimp [c]
    exact
      polynomial_prod_pow_ne_zero_of_coeff_zero_eq_one
        (s := s) (f := f) (e := fun i ↦ m i % p) h0
  have hmnorm : ((∏ i ∈ s, f i ^ m i) : Polynomial k) = c * qM ^ p := by
    -- Put the left product in residue times Frobenius-power normal form.
    dsimp [c, qM]
    exact polynomial_prod_pow_decompose_mod_char (s := s) (f := f) (m := m) p
  have hnnorm : ((∏ i ∈ s, f i ^ n i) : Polynomial k) = c * qN ^ p := by
    -- Put the right product in the same normal form, using the residue equality.
    calc
      ((∏ i ∈ s, f i ^ n i) : Polynomial k) =
          (∏ i ∈ s, f i ^ (n i % p)) *
            (∏ i ∈ s, f i ^ (n i / p)) ^ p := by
        exact polynomial_prod_pow_decompose_mod_char (s := s) (f := f) (m := n) p
      _ = c * qN ^ p := by
        rw [hresidue]
  have hpow : qM ^ p = qN ^ p := by
    -- Cancel the common nonzero residue product from the normalized equality.
    apply mul_left_cancel₀ hc_ne
    calc
      c * qM ^ p = ((∏ i ∈ s, f i ^ m i) : Polynomial k) := hmnorm.symm
      _ = ((∏ i ∈ s, f i ^ n i) : Polynomial k) := hprod
      _ = c * qN ^ p := hnnorm
  have hfrob : (frobenius (Polynomial k) p) qM = (frobenius (Polynomial k) p) qN := by
    -- In characteristic `p`, the Frobenius map is exactly the `p`-th power map.
    rw [frobenius_def, frobenius_def]
    exact hpow
  -- Polynomial rings over fields are reduced, so Frobenius is injective.
  exact (frobenius_inj (Polynomial k) p) hfrob

/-- Helper for Exercise 18-18.2-6: pointwise version of Frobenius division for a family of
constant-term-one polynomial products. -/
lemma prodPowEq_divideCommonResidues_primeChar
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {ι X : Type*} (s : Finset ι) (f : ι → X → Polynomial k) (m n : ι → ℕ)
    (h0 : ∀ i ∈ s, ∀ x, (f i x).coeff 0 = 1)
    (hprod : ∀ x,
      ((∏ i ∈ s, (f i x) ^ m i) : Polynomial k) =
        ((∏ i ∈ s, (f i x) ^ n i) : Polynomial k))
    (hcast : ∀ i ∈ s, (m i : k) = (n i : k)) :
    ∀ x,
      ((∏ i ∈ s, (f i x) ^ (m i / p)) : Polynomial k) =
        ((∏ i ∈ s, (f i x) ^ (n i / p)) : Polynomial k) := by
  intro x
  -- Apply the fixed-polynomial normalization at the chosen parameter.
  exact
    polynomial_prod_pow_div_eq_of_prod_pow_eq_of_cast_eq
      (s := s) (f := fun i ↦ f i x) (m := m) (n := n)
      (fun i hi ↦ h0 i hi x) (hprod x) hcast

/-- Helper for Exercise 18-18.2-6: if a quotient by a prime characteristic is positive, then it
is strictly smaller than the original exponent. -/
lemma nat_div_lt_self_of_prime_of_pos_div {p a : ℕ} (hp : p.Prime) (h : 0 < a / p) :
    a / p < a := by
  -- Prime characteristic gives `1 < p`; multiplying a positive quotient by `p` is therefore
  -- strictly larger than the quotient, while `p * (a / p)` is bounded by `a`.
  have hp_gt : 1 < p := hp.one_lt
  have hmul_le : p * (a / p) ≤ a := Nat.mul_div_le a p
  nlinarith

/-- Helper for Exercise 18-18.2-6: if some quotient exponents differ, then replacing every
exponent by its quotient modulo a prime characteristic strictly lowers the total exponent sum. -/
lemma finset_sum_div_add_lt_sum_of_exists_quotient_diff
    {p : ℕ} (hp : p.Prime) {ι : Type*} (s : Finset ι) (m n : ι → ℕ)
    (hdiff : ∃ i ∈ s, m i / p ≠ n i / p) :
    (∑ i ∈ s, (m i / p + n i / p)) < ∑ i ∈ s, (m i + n i) := by
  refine Finset.sum_lt_sum ?_ ?_
  · intro i hi
    -- Quotienting each exponent can only lower each summand.
    exact Nat.add_le_add (Nat.div_le_self (m i) p) (Nat.div_le_self (n i) p)
  · rcases hdiff with ⟨i, hi, hqdiff⟩
    refine ⟨i, hi, ?_⟩
    -- At the index where the quotients differ, at least one quotient is positive and therefore
    -- strictly decreases its original exponent.
    by_cases hmpos : 0 < m i / p
    · exact Nat.add_lt_add_of_lt_of_le
        (nat_div_lt_self_of_prime_of_pos_div hp hmpos)
        (Nat.div_le_self (n i) p)
    · have hmzero : m i / p = 0 := Nat.eq_zero_of_not_pos hmpos
      have hnpos : 0 < n i / p := by
        exact Nat.pos_of_ne_zero fun hnzero ↦ hqdiff (by rw [hmzero, hnzero])
      exact Nat.add_lt_add_of_le_of_lt
        (Nat.div_le_self (m i) p)
        (nat_div_lt_self_of_prime_of_pos_div hp hnpos)

/-- Helper for Exercise 18-18.2-6: from a nontrivial equality of finite products of
constant-term-one polynomial powers in prime characteristic, repeatedly divide common residues
until some remaining exponent difference is nonzero in the field. -/
lemma exists_normalized_nonzeroWeight_of_prodPowEq_primeChar
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {ι X : Type*} (s : Finset ι) (f : ι → X → Polynomial k) (m n : ι → ℕ)
    (h0 : ∀ i ∈ s, ∀ x, (f i x).coeff 0 = 1)
    (hprod : ∀ x,
      ((∏ i ∈ s, (f i x) ^ m i) : Polynomial k) =
        ((∏ i ∈ s, (f i x) ^ n i) : Polynomial k))
    (hdiff : ∃ i ∈ s, m i ≠ n i) :
    ∃ m' n' : ι → ℕ,
      (∀ x,
        ((∏ i ∈ s, (f i x) ^ m' i) : Polynomial k) =
          ((∏ i ∈ s, (f i x) ^ n' i) : Polynomial k)) ∧
      (∃ i ∈ s, m' i ≠ n' i) ∧
      ∃ i ∈ s, ((m' i : k) - (n' i : k)) ≠ 0 := by
  let motive := fun (m n : ι → ℕ) ↦
    (∀ x,
      ((∏ i ∈ s, (f i x) ^ m i) : Polynomial k) =
        ((∏ i ∈ s, (f i x) ^ n i) : Polynomial k)) →
    (∃ i ∈ s, m i ≠ n i) →
    ∃ m' n' : ι → ℕ,
      (∀ x,
        ((∏ i ∈ s, (f i x) ^ m' i) : Polynomial k) =
          ((∏ i ∈ s, (f i x) ^ n' i) : Polynomial k)) ∧
      (∃ i ∈ s, m' i ≠ n' i) ∧
      ∃ i ∈ s, ((m' i : k) - (n' i : k)) ≠ 0
  have hmain : ∀ N, ∀ m n : ι → ℕ,
      N = ∑ i ∈ s, (m i + n i) → motive m n := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro m n hN hprod hdiff
      by_cases hnonzero : ∃ i ∈ s, ((m i : k) - (n i : k)) ≠ 0
      · -- If a coefficient is already nonzero after casting to `k`, the original exponents are
        -- the required normalized witness.
        exact ⟨m, n, hprod, hdiff, hnonzero⟩
      · have hcast : ∀ i ∈ s, (m i : k) = (n i : k) := by
          intro i hi
          -- Otherwise every supported weight difference vanishes in `k`.
          have hzero : ((m i : k) - (n i : k)) = 0 := by
            by_contra hne
            exact hnonzero ⟨i, hi, hne⟩
          exact sub_eq_zero.mp hzero
        let m₁ : ι → ℕ := fun i ↦ m i / p
        let n₁ : ι → ℕ := fun i ↦ n i / p
        have hprod₁ : ∀ x,
            ((∏ i ∈ s, (f i x) ^ m₁ i) : Polynomial k) =
              ((∏ i ∈ s, (f i x) ^ n₁ i) : Polynomial k) := by
          intro x
          -- Divide the common residues by the Frobenius quotient lemma proved above.
          exact prodPowEq_divideCommonResidues_primeChar
            (s := s) (f := f) (m := m) (n := n) h0 hprod hcast x
        have hdiff₁ : ∃ i ∈ s, m₁ i ≠ n₁ i := by
          rcases hdiff with ⟨i, hi, hneq⟩
          have hmod : m i % p = n i % p :=
            (CharP.cast_eq_iff_mod_eq k p).mp (hcast i hi)
          refine ⟨i, hi, ?_⟩
          intro hdiv
          change m i / p = n i / p at hdiv
          apply hneq
          -- Equal residues and equal quotients would reconstruct equal original exponents.
          calc
            m i = m i % p + p * (m i / p) := (Nat.mod_add_div (m i) p).symm
            _ = n i % p + p * (n i / p) := by rw [hmod, hdiv]
            _ = n i := Nat.mod_add_div (n i) p
        have hsum_lt : (∑ i ∈ s, (m₁ i + n₁ i)) < N := by
          -- The differing quotient exponents strictly lower the strong-induction rank.
          rw [hN]
          exact finset_sum_div_add_lt_sum_of_exists_quotient_diff
            (Fact.out : p.Prime) s m n hdiff₁
        exact ih (∑ i ∈ s, (m₁ i + n₁ i)) hsum_lt m₁ n₁ rfl hprod₁ hdiff₁
  -- Start the descent with the total sum of the two original exponent families.
  exact hmain (∑ i ∈ s, (m i + n i)) m n rfl hprod hdiff

end Representation
