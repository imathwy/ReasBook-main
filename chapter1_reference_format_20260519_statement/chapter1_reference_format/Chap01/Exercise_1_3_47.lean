import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped BigOperators Topology

universe u v

/-- Helper for Exercise 1.3.47: the truncated exponential polynomial
`∑_{i=0}^n X^i / i!` over `ℂ`. -/
noncomputable abbrev truncatedExponential (n : ℕ) : ℂ[X] :=
  Finset.sum (Finset.range (n + 1))
    (fun i ↦ C (((Nat.factorial i : ℂ))⁻¹) * (X : ℂ[X]) ^ i)

/-- Helper for Exercise 1.3.47: differentiating the `(i + 1)`st summand of the truncated
exponential produces the `i`th summand. -/
lemma truncated_exponential_deriv_term (i : ℕ) :
    derivative
        (C (((Nat.factorial (i + 1) : ℂ))⁻¹) * (X : ℂ[X]) ^ (i + 1)) =
      C (((Nat.factorial i : ℂ))⁻¹) * (X : ℂ[X]) ^ i := by
  -- Rewrite the derivative explicitly and cancel the factor `(i + 1)`.
  rw [derivative_C_mul_X_pow]
  have hi : ((i + 1 : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero i
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  simp [hi]

/-- Helper for Exercise 1.3.47: the derivative of the truncated exponential polynomial of order
`n + 1` is the truncated exponential polynomial of order `n`. -/
lemma truncated_exponential_derivative (n : ℕ) :
    derivative (truncatedExponential (n + 1)) = truncatedExponential n := by
  -- Shift the derivative sum by one index so each differentiated term matches the previous jet.
  rw [truncatedExponential, map_sum, Finset.sum_range_succ']
  simp only [derivative_mul, derivative_C, zero_mul, derivative_X_pow_succ, map_add, map_natCast,
    map_one, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    derivative_one, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using truncated_exponential_deriv_term i

/-- Helper for Exercise 1.3.47: the truncated exponential polynomial takes the value `1` at
`0`. -/
lemma truncated_exponential_eval_zero (n : ℕ) :
    (truncatedExponential n).eval 0 = 1 := by
  cases n with
  | zero =>
      simp [truncatedExponential]
  | succ m =>
      -- Split off the constant term and evaluate the positive-degree part at `0`.
      rw [truncatedExponential, Finset.sum_range_succ', eval_add]
      rw [show
        eval 0
            (∑ x ∈ Finset.range (m + 1),
              C (((Nat.factorial (x + 1) : ℂ))⁻¹) * X ^ (x + 1)) =
          ∑ x ∈ Finset.range (m + 1),
            eval 0 (C (((Nat.factorial (x + 1) : ℂ))⁻¹) * X ^ (x + 1)) by
          exact
            map_sum (Polynomial.evalRingHom (R := ℂ) 0)
              (fun k ↦ C (((Nat.factorial (k + 1) : ℂ))⁻¹) * (X : ℂ[X]) ^ (k + 1))
              (Finset.range (m + 1))]
      simp

/-- Helper for Exercise 1.3.47: a common complex root of `X^(m+2) - X + 1` and its derivative
would force an impossible real identity. -/
lemma x_pow_sub_x_add_one_repeated_root_contradiction (m : ℕ) {z : ℂ}
    (hroot : (((X : ℂ[X]) ^ (m + 2) - X + 1 : ℂ[X])).eval z = 0)
    (hderiv : (derivative (((X : ℂ[X]) ^ (m + 2) - X + 1 : ℂ[X]))).eval z = 0) :
    False := by
  -- First rewrite the two root conditions into algebraic equalities for `z`.
  have hrootEq : z ^ (m + 2) = z - 1 := by
    have hroot' : z ^ (m + 2) + (-z + 1) = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hroot
    calc
      z ^ (m + 2) = (z ^ (m + 2) + (-z + 1)) - (-z + 1) := by ring
      _ = 0 - (-z + 1) := by rw [hroot']
      _ = z - 1 := by ring
  have hderivEq : ((m + 2 : ℂ) * z ^ (m + 1)) = 1 := by
    have hderiv' : ((m : ℂ) + (1 + 1)) * z ^ (m + 1) + (-1) = 0 := by
      simpa [Nat.cast_add, derivative_sub, derivative_add, derivative_X_pow, derivative_X,
        derivative_one, eval_add, eval_sub, eval_pow, eval_X, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm] using hderiv
    calc
      (m + 2 : ℂ) * z ^ (m + 1) =
          ((((m : ℂ) + (1 + 1)) * z ^ (m + 1)) + (-1)) - (-1) := by
        ring
      _ = 0 - (-1) := by rw [hderiv']
      _ = 1 := by ring
  -- The two identities force `z` to equal the positive real number `(m + 2) / (m + 1)`.
  have hz_from_deriv : ((m + 2 : ℂ) * z ^ (m + 2)) = z := by
    calc
      ((m + 2 : ℂ) * z ^ (m + 2)) =
          (((m + 2 : ℂ) * z ^ (m + 1)) * z) := by
        rw [pow_succ']
        ring
      _ = z := by
        rw [hderivEq]
        simp
  have hlin : z = (m + 2 : ℂ) * (z - 1) := by
    calc
      z = ((m + 2 : ℂ) * z ^ (m + 2)) := hz_from_deriv.symm
      _ = (m + 2 : ℂ) * (z - 1) := by rw [hrootEq]
  have hzmul : ((m + 1 : ℂ)) * z = (m + 2 : ℂ) := by
    have hlin1 : z + (m + 2 : ℂ) = (m + 2 : ℂ) * z := by
      calc
        z + (m + 2 : ℂ) = (m + 2 : ℂ) * (z - 1) + (m + 2 : ℂ) := by
          conv_lhs => rw [hlin]
        _ = (m + 2 : ℂ) * z := by ring
    calc
      ((m + 1 : ℂ)) * z = ((m + 2 : ℂ) * z) - z := by ring
      _ = (z + (m + 2 : ℂ)) - z := by rw [hlin1]
      _ = (m + 2 : ℂ) := by ring
  have hm1 : ((m + 1 : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  have hz : z = (m + 2 : ℂ) / (m + 1 : ℂ) := by
    apply (eq_div_iff hm1).2
    simpa [mul_comm] using hzmul
  -- Taking norms turns the complex equality into a real inequality contradiction.
  have hrat : ((m + 2 : ℂ) * (((m + 2 : ℂ) / (m + 1 : ℂ)) ^ (m + 1))) = 1 := by
    simpa [hz] using hderivEq
  have hnorm : (m + 2 : ℝ) * (((m + 2 : ℝ) / (m + 1 : ℝ)) ^ (m + 1)) = 1 := by
    have hnorm' := congrArg norm hrat
    have hn2 : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
      simpa [Nat.cast_add] using Complex.norm_natCast (m + 2)
    have hn1 : ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 := by
      simpa [Nat.cast_add] using Complex.norm_natCast (m + 1)
    simpa [hn2, hn1] using hnorm'
  have hm1_pos : (0 : ℝ) < m + 1 := by
    positivity
  have hratio_gt_one : (1 : ℝ) < (m + 2 : ℝ) / (m + 1 : ℝ) := by
    rw [one_lt_div hm1_pos]
    linarith
  have hpow_gt_one : (1 : ℝ) < (((m + 2 : ℝ) / (m + 1 : ℝ)) ^ (m + 1)) := by
    have hmono := pow_right_strictMono₀ hratio_gt_one
    simpa using hmono (Nat.zero_lt_succ m)
  have hm_nonneg : (0 : ℝ) ≤ m := by
    exact_mod_cast Nat.zero_le m
  have hm2_ge_one : (1 : ℝ) ≤ m + 2 := by
    nlinarith
  have hlhs_gt_one : (1 : ℝ) < (m + 2 : ℝ) * (((m + 2 : ℝ) / (m + 1 : ℝ)) ^ (m + 1)) := by
    exact one_lt_mul hm2_ge_one hpow_gt_one
  have : (1 : ℝ) < 1 := by
    rw [hnorm] at hlhs_gt_one
    exact hlhs_gt_one
  exact lt_irrefl _ this

-- Proof sketch: show that the polynomial and its derivative are coprime by computing the
-- derivative explicitly and ruling out common roots, then use `Polynomial.nodup_roots`.
/-- Exercise 1.3.47 (1): for every `n`, the truncated exponential polynomial
`∑_{i=0}^n X^i / i!` has only simple complex roots. -/
theorem truncated_exponential_polynomial_roots_nodup (n : ℕ) :
    ((Finset.sum (Finset.range (n + 1))
        fun i ↦ C (((Nat.factorial i : ℂ))⁻¹) * (X : ℂ[X]) ^ i) : ℂ[X]).roots.Nodup := by
  classical
  cases n with
  | zero =>
      -- The zeroth truncated exponential is the constant polynomial `1`.
      simp
  | succ m =>
      -- A repeated root would have to be a common root of the polynomial and its derivative.
      refine Multiset.nodup_iff_count_le_one.2 ?_
      intro z
      rw [Polynomial.count_roots]
      by_cases hmult : 1 < (truncatedExponential (m + 1)).rootMultiplicity z
      · have hp0 : truncatedExponential (m + 1) ≠ 0 := by
          intro hp
          have hzero : (truncatedExponential (m + 1)).eval 0 = 1 :=
            truncated_exponential_eval_zero (m + 1)
          have : (1 : ℂ) = 0 := by
            simpa [hp] using hzero
          norm_num at this
        have hroot :
            (truncatedExponential (m + 1)).IsRoot z :=
          ((Polynomial.rootMultiplicity_pos').1
            (lt_trans Nat.zero_lt_one hmult)).2
        have hderivMult :
            0 < (derivative (truncatedExponential (m + 1))).rootMultiplicity z := by
          rw [Polynomial.derivative_rootMultiplicity_of_root hroot]
          exact Nat.sub_pos_of_lt hmult
        have hzderiv :
            (derivative (truncatedExponential (m + 1))).IsRoot z :=
          ((Polynomial.rootMultiplicity_pos').1 hderivMult).2
        have hroot : (truncatedExponential (m + 1)).eval z = 0 := hroot
        have hderivRoot : (truncatedExponential m).eval z = 0 := by
          have hzderiv : (derivative (truncatedExponential (m + 1))).eval z = 0 := hzderiv
          rw [truncated_exponential_derivative] at hzderiv
          exact hzderiv
        -- Comparing the polynomial with its derivative isolates the top-degree term.
        have hsum :
            (truncatedExponential (m + 1)).eval z =
              (truncatedExponential m).eval z +
                (C (((Nat.factorial (m + 1) : ℂ))⁻¹) * X ^ (m + 1)).eval z := by
          simp [truncatedExponential, Finset.sum_range_succ, add_assoc]
        have htop : (C (((Nat.factorial (m + 1) : ℂ))⁻¹) * X ^ (m + 1)).eval z = 0 := by
          rw [hroot, hderivRoot, zero_add] at hsum
          exact hsum.symm
        have hfactorial : ((Nat.factorial (m + 1) : ℂ)) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (m + 1)
        have hz0 : z = 0 := by
          simpa [eval_mul, eval_C, eval_X, eval_pow, hfactorial] using htop
        have hzero : (truncatedExponential (m + 1)).eval 0 = 1 :=
          truncated_exponential_eval_zero (m + 1)
        have hroot0 : (truncatedExponential (m + 1)).eval 0 = 0 := by
          simpa [hz0] using hroot
        have : (1 : ℂ) = 0 := by
          calc
            (1 : ℂ) = (truncatedExponential (m + 1)).eval 0 := hzero.symm
            _ = 0 := hroot0
        norm_num at this
      · exact Nat.not_lt.mp hmult

-- Proof sketch: compute the derivative of `X^n - X + 1`, show that a multiple root would have
-- to satisfy both `n * z^(n - 1) = 1` and `z^n - z + 1 = 0`, and derive a contradiction.
/-- Exercise 1.3.47 (2): for every `n`, the polynomial `X^n - X + 1` has only simple
complex roots. -/
theorem X_pow_sub_X_add_one_roots_nodup (n : ℕ) :
    ((((X : ℂ[X]) ^ n) - X + 1) : ℂ[X]).roots.Nodup := by
  classical
  cases n with
  | zero =>
      -- For `n = 0`, the polynomial is the linear polynomial `2 - X`.
      have hpoly : ((((X : ℂ[X]) ^ 0) - X + 1) : ℂ[X]) = -X + C (2 : ℂ) := by
        calc
          ((((X : ℂ[X]) ^ 0) - X + 1) : ℂ[X]) = (1 : ℂ[X]) - X + 1 := by simp
          _ = (2 : ℂ[X]) - X := by ring
          _ = -X + (2 : ℂ[X]) := by ring
          _ = -X + C (2 : ℂ) := by rfl
      have hroots : (-X + C (2 : ℂ) : ℂ[X]).roots = ({(2 : ℂ)} : Multiset ℂ) := by
        simpa [sub_eq_add_neg] using
          (Polynomial.roots_C_mul_X_add_C (a := (-1 : ℂ)) (b := (2 : ℂ)) (by norm_num))
      rw [hpoly]
      rw [hroots]
      simp
  | succ n =>
      cases n with
      | zero =>
          -- For `n = 1`, the polynomial collapses to the constant polynomial `1`.
          simp [pow_one]
      | succ m =>
          -- As in part (1), it suffices to rule out common roots with the derivative.
          refine Multiset.nodup_iff_count_le_one.2 ?_
          intro z
          rw [Polynomial.count_roots]
          by_cases hmult :
              1 < ((((X : ℂ[X]) ^ (m + 2)) - X + 1 : ℂ[X])).rootMultiplicity z
          · have hp0 : ((((X : ℂ[X]) ^ (m + 2)) - X + 1 : ℂ[X]) ≠ 0) := by
              intro hp
              have hconst : ((((X : ℂ[X]) ^ (m + 2)) - X + 1 : ℂ[X])).eval 0 = 1 := by
                simp
              have : (1 : ℂ) = 0 := by
                simpa [hp] using hconst
              norm_num at this
            have hroot :
                ((((X : ℂ[X]) ^ (m + 2)) - X + 1 : ℂ[X])).IsRoot z :=
              ((Polynomial.rootMultiplicity_pos').1
                (lt_trans Nat.zero_lt_one hmult)).2
            have hderivMult :
                0 <
                  (derivative ((((X : ℂ[X]) ^ (m + 2)) - X + 1 : ℂ[X]))).rootMultiplicity z := by
              rw [Polynomial.derivative_rootMultiplicity_of_root hroot]
              exact Nat.sub_pos_of_lt hmult
            have hderiv :
                (derivative ((((X : ℂ[X]) ^ (m + 2)) - X + 1 : ℂ[X]))).IsRoot z :=
              ((Polynomial.rootMultiplicity_pos').1 hderivMult).2
            exact False.elim <|
              x_pow_sub_x_add_one_repeated_root_contradiction m hroot hderiv
          · exact Nat.not_lt.mp hmult

-- Proof sketch: `ℚ` is a perfect field, so every irreducible polynomial over `ℚ` is separable;
-- after mapping to `ℂ`, separability implies that the complex root multiset has no duplicates.
/-- Exercise 1.3.47 (3): every irreducible polynomial over `ℚ` has only simple roots in `ℂ`. -/
theorem irreducible_rat_polynomial_complex_roots_nodup (P : ℚ[X]) (hP : Irreducible P) :
    (P.map (algebraMap ℚ ℂ)).roots.Nodup := by
  simpa using nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr hP.separable)

/-- Helper for Exercise 1.3.47: if `z` is integral over `ℚ`, then the mapped minimal polynomial of
`z` has `z` as a simple complex root. -/
lemma minpoly_rootMultiplicity_eq_one {z : ℂ} (hz : IsIntegral ℚ z) :
    ((minpoly ℚ z).map (algebraMap ℚ ℂ)).rootMultiplicity z = 1 := by
  classical
  -- The mapped minimal polynomial has no repeated roots by part (3).
  have hnodup :
      (((minpoly ℚ z).map (algebraMap ℚ ℂ)).roots).Nodup :=
    irreducible_rat_polynomial_complex_roots_nodup (minpoly ℚ z) (minpoly.irreducible hz)
  have hmap_ne_zero : ((minpoly ℚ z).map (algebraMap ℚ ℂ)) ≠ 0 := by
    exact Polynomial.map_ne_zero (minpoly.ne_zero hz)
  have hmem : z ∈ ((minpoly ℚ z).map (algebraMap ℚ ℂ)).roots := by
    rw [Polynomial.mem_roots hmap_ne_zero]
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using minpoly.aeval ℚ z
  -- Counting the root inside a nodup multiset shows multiplicity one.
  rw [← Polynomial.count_roots]
  exact Multiset.count_eq_one_of_mem hnodup hmem

/-- Helper for Exercise 1.3.47: a root of multiplicity `μ` of `P.map (algebraMap ℚ ℂ)` forces the
`μ`-th power of the minimal polynomial over `ℚ` to divide `P`. -/
lemma minpoly_pow_dvd_of_rootMultiplicity (P : ℚ[X]) {z : ℂ} (hz : IsIntegral ℚ z) :
    (minpoly ℚ z) ^ ((P.map (algebraMap ℚ ℂ)).rootMultiplicity z) ∣ P := by
  -- Route correction: recurse by factoring off one copy of `minpoly ℚ z`, rather than trying to
  -- transport derivative vanishing from `ℂ[X]` back to `ℚ[X]`.
  suffices haux :
      ∀ μ : ℕ, ∀ P : ℚ[X],
        (P.map (algebraMap ℚ ℂ)).rootMultiplicity z = μ →
          (minpoly ℚ z) ^ μ ∣ P by
    exact haux _ P rfl
  intro μ
  induction μ with
  | zero =>
      intro P hμ
      -- Multiplicity zero gives the trivial divisibility.
      simpa [pow_zero] using (one_dvd P)
  | succ n ih =>
      intro P hμ
      -- Positive multiplicity first makes `z` a root of `P`, hence `minpoly ℚ z ∣ P`.
      have hμpos : 0 < (P.map (algebraMap ℚ ℂ)).rootMultiplicity z := by
        rw [hμ]
        exact Nat.succ_pos _
      obtain ⟨hPmap_ne_zero, hroot⟩ := (Polynomial.rootMultiplicity_pos').1 hμpos
      have hrootQ : Polynomial.aeval z P = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hroot
      obtain ⟨Q, hQ⟩ := minpoly.dvd ℚ z hrootQ
      have hQmap_ne_zero : Q.map (algebraMap ℚ ℂ) ≠ 0 := by
        intro hzero
        apply hPmap_ne_zero
        rw [hQ, Polynomial.map_mul, hzero, mul_zero]
      -- The mapped minimal polynomial contributes exactly one to the root multiplicity.
      have hmul :
          (P.map (algebraMap ℚ ℂ)).rootMultiplicity z =
            ((minpoly ℚ z).map (algebraMap ℚ ℂ)).rootMultiplicity z +
              (Q.map (algebraMap ℚ ℂ)).rootMultiplicity z := by
        rw [hQ, Polynomial.map_mul]
        exact Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hz))
          hQmap_ne_zero)
      have hQmult : (Q.map (algebraMap ℚ ℂ)).rootMultiplicity z = n := by
        rw [hμ, minpoly_rootMultiplicity_eq_one hz] at hmul
        omega
      have hQdiv :
          (minpoly ℚ z) ^ n ∣ Q := ih Q hQmult
      rcases hQdiv with ⟨R, hR⟩
      refine ⟨R, ?_⟩
      -- Multiplying the quotient back by one more `minpoly` recovers the required power.
      rw [hQ, hR]
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 1.3.47: any degree-one rational divisor of `P` supplies a rational root of
`P`. -/
lemma exists_rat_root_of_dvd_natDegree_eq_one (P Q : ℚ[X]) (hQ : Q ∣ P) (hQdeg : Q.natDegree = 1) :
    ∃ q : ℚ, P.eval q = 0 := by
  have hQdegree : Q.degree = 1 :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one).2 hQdeg
  obtain ⟨q, hqroot⟩ := Polynomial.exists_root_of_degree_eq_one hQdegree
  rcases hQ with ⟨R, rfl⟩
  refine ⟨q, ?_⟩
  -- Evaluating at a root of the degree-one divisor annihilates the product.
  rw [Polynomial.eval_mul, hqroot, zero_mul]

-- Proof sketch: let `m(X)` be the minimal polynomial of `z` over `ℚ`. Since `m(z) = 0`,
-- `minpoly.dvd` shows that `m(X)^(rootMultiplicity z)` divides `P`; hence
-- `rootMultiplicity z * m.natDegree ≤ P.natDegree`. If `2 * rootMultiplicity z > P.natDegree`,
-- then `m.natDegree = 1`, and `minpoly.natDegree_eq_one_iff` yields that `z` lies in `ℚ`.
/-- Exercise 1.3.47 (4): if a polynomial over `ℚ` has a complex root whose multiplicity
is strictly greater than half of the degree, then that root already lies in `ℚ`. -/
theorem rat_of_rootMultiplicity_gt_half_natDegree (P : ℚ[X]) {z : ℂ}
    (hμ : 2 * (P.map (algebraMap ℚ ℂ)).rootMultiplicity z > P.natDegree) :
    ∃ q : ℚ, algebraMap ℚ ℂ q = z := by
  -- A multiplicity strictly larger than half the degree is automatically positive.
  have hμpos : 0 < (P.map (algebraMap ℚ ℂ)).rootMultiplicity z := by
    omega
  obtain ⟨hPmap_ne_zero, hroot⟩ := (Polynomial.rootMultiplicity_pos').1 hμpos
  have hP_ne_zero : P ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).1 hPmap_ne_zero
  have hzroot : Polynomial.aeval z P = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hroot
  have hz : IsIntegral ℚ z := IsAlgebraic.isIntegral ⟨P, hP_ne_zero, hzroot⟩
  have hdiv := minpoly_pow_dvd_of_rootMultiplicity (P := P) hz
  have hzrange : z ∈ Set.range (algebraMap ℚ ℂ) := by
    by_contra hnot
    have hmin_two : 2 ≤ (minpoly ℚ z).natDegree := (minpoly.two_le_natDegree_iff hz).2 hnot
    have hbound :
        (P.map (algebraMap ℚ ℂ)).rootMultiplicity z * (minpoly ℚ z).natDegree ≤ P.natDegree := by
      calc
        (P.map (algebraMap ℚ ℂ)).rootMultiplicity z * (minpoly ℚ z).natDegree =
            ((minpoly ℚ z) ^ ((P.map (algebraMap ℚ ℂ)).rootMultiplicity z)).natDegree := by
          rw [Polynomial.natDegree_pow]
        _ ≤ P.natDegree := Polynomial.natDegree_le_of_dvd hdiv hP_ne_zero
    have htwo_le :
        2 * (P.map (algebraMap ℚ ℂ)).rootMultiplicity z ≤ P.natDegree := by
      calc
        2 * (P.map (algebraMap ℚ ℂ)).rootMultiplicity z =
            (P.map (algebraMap ℚ ℂ)).rootMultiplicity z * 2 := by ring
        _ ≤ (P.map (algebraMap ℚ ℂ)).rootMultiplicity z * (minpoly ℚ z).natDegree := by
          exact Nat.mul_le_mul_left _ hmin_two
        _ ≤ P.natDegree := hbound
    exact (not_lt_of_ge htwo_le) hμ
  simpa [Set.mem_range] using hzrange

-- Proof sketch: if `z` is nonrational, then its minimal polynomial over `ℚ` has degree at least
-- `2`; since `z` has multiplicity `n`, the divisibility `minpoly ℚ z ^ n ∣ P` forces
-- `2 * n ≤ P.natDegree = 2 * n + 1`, so the complementary factor has degree `1`, giving a
-- rational linear factor. If `z` is rational, we are already done.
/-- Exercise 1.3.47 (5): if a polynomial over `ℚ` has odd degree `2n + 1` and a complex root of
multiplicity `n` with `n ≥ 2`, then it has a rational root. -/
theorem exists_rat_root_of_odd_natDegree_and_large_multiple_root (P : ℚ[X]) (n : ℕ)
    (hdeg : P.natDegree = 2 * n + 1) {z : ℂ}
    (hmult : (P.map (algebraMap ℚ ℂ)).rootMultiplicity z = n) (hn : 2 ≤ n) :
    ∃ q : ℚ, P.eval q = 0 := by
  have hnpos : 0 < n := by omega
  have hμpos : 0 < (P.map (algebraMap ℚ ℂ)).rootMultiplicity z := by
    simpa [hmult] using hnpos
  obtain ⟨hPmap_ne_zero, hroot⟩ := (Polynomial.rootMultiplicity_pos').1 hμpos
  have hP_ne_zero : P ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).1 hPmap_ne_zero
  have hzroot : Polynomial.aeval z P = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hroot
  have hz : IsIntegral ℚ z := IsAlgebraic.isIntegral ⟨P, hP_ne_zero, hzroot⟩
  by_cases hzrat : z ∈ Set.range (algebraMap ℚ ℂ)
  · rcases hzrat with ⟨q, rfl⟩
    refine ⟨q, ?_⟩
    have hq0' : algebraMap ℚ ℂ (P.eval q) = 0 := by
      exact (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (R := ℚ) (A := ℂ) q P).symm.trans
        hzroot
    exact (FaithfulSMul.algebraMap_injective ℚ ℂ) (by simpa using hq0')
  · have hdiv : (minpoly ℚ z) ^ n ∣ P := by
      simpa [hmult] using minpoly_pow_dvd_of_rootMultiplicity (P := P) hz
    rcases hdiv with ⟨Q, hQ⟩
    have hQ_ne_zero : Q ≠ 0 := by
      intro hzero
      apply hP_ne_zero
      rw [hQ, hzero, mul_zero]
    have hmin_two : 2 ≤ (minpoly ℚ z).natDegree := (minpoly.two_le_natDegree_iff hz).2 hzrat
    have hfactor_deg :
        P.natDegree = n * (minpoly ℚ z).natDegree + Q.natDegree := by
      rw [hQ, Polynomial.natDegree_mul (pow_ne_zero _ (minpoly.ne_zero hz)) hQ_ne_zero,
        Polynomial.natDegree_pow]
    have hmin_le_two : (minpoly ℚ z).natDegree ≤ 2 := by
      by_contra hgt
      have hthree : 3 ≤ (minpoly ℚ z).natDegree := by omega
      have hmul_le : 3 * n ≤ P.natDegree := by
        calc
          3 * n ≤ n * (minpoly ℚ z).natDegree := by
            simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hthree
          _ ≤ n * (minpoly ℚ z).natDegree + Q.natDegree := Nat.le_add_right _ _
          _ = P.natDegree := hfactor_deg.symm
      omega
    have hmin_eq_two : (minpoly ℚ z).natDegree = 2 := by omega
    have hQdeg : Q.natDegree = 1 := by
      rw [hdeg, hmin_eq_two] at hfactor_deg
      omega
    have hQdvdP : Q ∣ P := by
      refine ⟨(minpoly ℚ z) ^ n, ?_⟩
      rw [hQ, mul_comm]
    exact exists_rat_root_of_dvd_natDegree_eq_one P Q hQdvdP hQdeg

-- Proof sketch: show that the difference of two candidate polynomials has the prescribed
-- points as roots with the required multiplicities, hence must vanish by the degree bound; then
-- prove existence by solving the corresponding square linear system in the coefficients.
/-- Helper for Exercise 1.3.47: evaluating the `k`th Hasse derivative is the same as evaluating
the `k`th ordinary derivative divided by `k!`. -/
lemma hasseDeriv_eval_eq_iterate_derivative_eval_div_factorial
    {K : Type u} [Field K] [CharZero K] (P : K[X]) (k : ℕ) (a : K) :
    (hasseDeriv k P).eval a = ((derivative^[k]) P).eval a / (k.factorial : K) := by
  -- Evaluate `k! • hasseDeriv k P = derivative^[k] P` at the point `a`.
  have h_eval : (k.factorial : K) * (hasseDeriv k P).eval a = ((derivative^[k]) P).eval a := by
    simpa [nsmul_eq_mul] using
      congrArg (fun Q : K[X] ↦ Q.eval a) (congrFun (factorial_smul_hasseDeriv k) P)
  have hfac : (k.factorial : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  -- Cancel the nonzero factorial to isolate the Hasse jet.
  apply (eq_div_iff hfac).2
  simpa [mul_comm] using h_eval

/-- Helper for Exercise 1.3.47: a polynomial of degree `< ∑ i, m i` whose Hasse jets of orders
`< m i` vanish at each distinct node `x i` must be zero. -/
lemma eq_zero_of_hasse_jets_zero
    {K : Type u} [Field K] [CharZero K] {ι : Type v} [Fintype ι]
    (m : ι → ℕ) (x : ι → K) (hx : Function.Injective x)
    (N : ℕ) (hN : N = ∑ i, m i) (P : Polynomial.degreeLT K N)
    (hP : ∀ i, ∀ k : Fin (m i), (Polynomial.hasseDeriv k.1 (P : K[X])).eval (x i) = 0) :
    (P : K[X]) = 0 := by
  -- Vanishing initial Taylor coefficients at `x i` gives divisibility by `(X - x i)^(m i)`.
  have hi_div : ∀ i, (X - C (x i)) ^ (m i) ∣ (P : K[X]) := by
    intro i
    rw [Polynomial.X_sub_C_pow_dvd_iff]
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    calc
      ((P : K[X]).comp (X + C (x i))).coeff d =
          (Polynomial.hasseDeriv d (P : K[X])).eval (x i) := by
        simpa [Polynomial.taylor_apply] using
          (Polynomial.taylor_coeff (r := x i) (f := (P : K[X])) (n := d))
      _ = 0 := hP i ⟨d, hd⟩
  have hprod_div : (∏ i, (X - C (x i)) ^ (m i)) ∣ (P : K[X]) := by
    -- The linear factors are pairwise coprime because the nodes are distinct.
    refine Fintype.prod_dvd_of_coprime ?_ hi_div
    intro i j hij
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (show IsUnit (x i - x j) by
          exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hx.ne hij)))).pow
  by_contra hne
  have hdegprod : (∏ i, (X - C (x i)) ^ (m i)).natDegree = ∑ i, m i := by
    -- The Hermite product is monic, so its degree is the sum of the multiplicities.
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i hi
      exact (Polynomial.monic_X_sub_C (x i)).pow (m i)
  have hle := Polynomial.natDegree_le_of_dvd hprod_div hne
  rw [hdegprod, ← hN] at hle
  have hlt : (P : K[X]).natDegree < N := by
    have hdeg : ((P : K[X])).degree < N := (Polynomial.mem_degreeLT).1 P.property
    rw [Polynomial.degree_eq_natDegree hne, Nat.cast_lt] at hdeg
    exact hdeg
  exact (Nat.not_lt_of_ge hle) hlt

/-- Exercise 1.3.47 (6): over a characteristic-zero field, prescribed jet data at finitely many
distinct nodes determine a unique Hermite interpolation polynomial of degree below the total jet
order. -/
theorem existsUnique_polynomial_of_jet_values
    {K : Type u} [Field K] [CharZero K] {ι : Type v} [Fintype ι] (m : ι → ℕ)
    (x : ι → K) (hx : Function.Injective x) (y : (i : ι) → Fin (m i) → K) :
    ∃! P : K[X],
      P.degree < ∑ i, m i ∧
        ∀ i, ∀ k : Fin (m i), ((derivative^[k.1]) P).eval (x i) = y i k := by
  -- Route correction: use the canonical Hasse-jet linear map on `K[X]_(∑ i, m i)`.
  let N : ℕ := ∑ i, m i
  let jetMap : Polynomial.degreeLT K N →ₗ[K] ((i : ι) → Fin (m i) → K) :=
    { toFun := fun P i k ↦ (Polynomial.hasseDeriv k.1 (P : K[X])).eval (x i)
      map_add' := by
        intro P Q
        ext i k
        simp
      map_smul' := by
        intro a P
        ext i k
        simp }
  have hjet_injective : Function.Injective jetMap := by
    intro P Q hPQ
    have hdiff : jetMap (P - Q) = 0 := by
      rw [LinearMap.map_sub, hPQ, sub_self]
    have hzero : ((P - Q : Polynomial.degreeLT K N) : K[X]) = 0 := by
      -- The difference has all prescribed Hasse jets equal to zero, hence vanishes.
      apply eq_zero_of_hasse_jets_zero (m := m) (x := x) hx (N := N) (hN := rfl)
      intro i k
      have hk := congrFun (congrFun hdiff i) k
      simpa using hk
    have hsub : (P - Q : Polynomial.degreeLT K N) = 0 := Subtype.ext hzero
    exact sub_eq_zero.mp hsub
  have hdim : Module.finrank K (Polynomial.degreeLT K N) =
      Module.finrank K ((i : ι) → Fin (m i) → K) := by
    -- Domain and codomain both have dimension `∑ i, m i`.
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K N)]
    rw [Module.finrank_eq_card_basis (Pi.basis fun i => Pi.basisFun K (Fin (m i)))]
    simp [N, Fintype.card_sigma]
  have hjet_surjective : Function.Surjective jetMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hjet_injective
  let yH : (i : ι) → Fin (m i) → K := fun i k ↦ y i k / (k.1.factorial : K)
  obtain ⟨P0, hP0⟩ := hjet_surjective yH
  have hP0deg : ((P0 : Polynomial.degreeLT K N) : K[X]).degree < N :=
    (Polynomial.mem_degreeLT).1 P0.property
  have hP0jets : ∀ i, ∀ k : Fin (m i), ((derivative^[k.1]) (P0 : K[X])).eval (x i) = y i k := by
    intro i k
    have hhasse : (Polynomial.hasseDeriv k.1 (P0 : K[X])).eval (x i) = yH i k := by
      exact congrFun (congrFun hP0 i) k
    -- Convert the chosen Hasse jet back to the ordinary derivative value.
    calc
      ((derivative^[k.1]) (P0 : K[X])).eval (x i) =
          (k.1.factorial : K) * (Polynomial.hasseDeriv k.1 (P0 : K[X])).eval (x i) := by
        symm
        simpa [nsmul_eq_mul] using
          congrArg (fun Q : K[X] ↦ Q.eval (x i))
            (congrFun (factorial_smul_hasseDeriv k.1) (P0 : K[X]))
      _ = (k.1.factorial : K) * yH i k := by rw [hhasse]
      _ = y i k := by
        have hfac : (k.1.factorial : K) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero k.1
        dsimp [yH]
        field_simp [hfac]
  refine ⟨(P0 : K[X]), ?_, ?_⟩
  · constructor
    · simpa [N] using hP0deg
    · exact hP0jets
  · intro Q hQ
    have hQmem : Q ∈ Polynomial.degreeLT K N := by
      apply (Polynomial.mem_degreeLT).2
      simpa [N] using hQ.1
    let R : Polynomial.degreeLT K N :=
      ⟨Q - (P0 : K[X]), Submodule.sub_mem _ hQmem P0.property⟩
    have hRzero : (R : K[X]) = 0 := by
      -- The difference polynomial has zero jets at every node.
      apply eq_zero_of_hasse_jets_zero (m := m) (x := x) hx (N := N) (hN := rfl)
      intro i k
      calc
        (Polynomial.hasseDeriv k.1 (R : K[X])).eval (x i) =
            ((derivative^[k.1]) (R : K[X])).eval (x i) / (k.1.factorial : K) := by
          simpa using
            hasseDeriv_eval_eq_iterate_derivative_eval_div_factorial
              (P := (R : K[X])) (k := k.1) (a := x i)
        _ = 0 / (k.1.factorial : K) := by
          congr 1
          calc
            ((derivative^[k.1]) (R : K[X])).eval (x i) =
                (((derivative^[k.1]) Q) - ((derivative^[k.1]) (P0 : K[X]))).eval (x i) := by
              simp [R]
            _ = ((derivative^[k.1]) Q).eval (x i) -
                  ((derivative^[k.1]) (P0 : K[X])).eval (x i) := by
              rw [Polynomial.eval_sub]
            _ = y i k - y i k := by rw [hQ.2 i k, hP0jets i k]
            _ = 0 := sub_self _
        _ = 0 := by simp
    have hRsub : Q - (P0 : K[X]) = 0 := by
      simpa [R] using hRzero
    exact sub_eq_zero.mp hRsub

/-- Helper for Exercise 1.3.47: on a one-dimensional set with unique tangents, iterated
derivatives of a polynomial evaluation agree with iterated polynomial derivatives. -/
lemma iteratedDerivWithin_eval_eq_eval_iterate_derivative
    (s : Set ℝ) (hs : UniqueDiffOn ℝ s) (Q : ℝ[X]) (n : ℕ) :
    Set.EqOn (iteratedDerivWithin n (fun t ↦ Q.eval t) s)
      (fun x ↦ ((Polynomial.derivative^[n]) Q).eval x) s := by
  induction n generalizing Q with
  | zero =>
      intro x hx
      -- At order zero, both sides are just the original polynomial evaluation.
      simp
  | succ n ih =>
      intro x hx
      -- Replace the inner iterated derivative by the inductive polynomial model, then differentiate.
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (ih Q) (ih Q hx)]
      rw [Polynomial.derivWithin ((Polynomial.derivative^[n]) Q) (hs.uniqueDiffWithinAt hx)]
      simp [Function.iterate_succ_apply']

/-- Helper for Exercise 1.3.47: a monic polynomial of degree `n` has `n`th iterated derivative
equal to the constant polynomial `n!`. -/
lemma iterate_derivative_monic_natDegree_eq_factorial (Q : ℝ[X]) (n : ℕ)
    (hQmonic : Q.Monic) (hQdeg : Q.natDegree = n) :
    (Polynomial.derivative^[n]) Q = C ((n.factorial : ℕ) : ℝ) := by
  have hconst :
      (Polynomial.derivative^[n]) Q =
        C (((Polynomial.derivative^[n]) Q).coeff 0) := by
    -- After `n` derivatives, the polynomial has degree at most zero, so it is constant.
    apply Polynomial.eq_C_of_natDegree_le_zero
    simpa [hQdeg] using Polynomial.natDegree_iterate_derivative Q n
  have hcoeff : Q.coeff n = 1 := by
    -- The constant is the leading coefficient transported through the explicit derivative formula.
    simpa [hQdeg] using hQmonic.coeff_natDegree
  rw [hconst]
  rw [Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self]
  simp [hcoeff]

/-- Helper for Exercise 1.3.47: on a closed interval, if the `r`th iterated derivative vanishes
at both endpoints, then the next iterated derivative vanishes at some interior point. -/
lemma iteratedDerivWithin_succ_eq_zero_between_of_eq_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (r : ℕ)
    (hf : ContDiffOn ℝ (r + 1) f (Set.Icc a b))
    (ha : iteratedDerivWithin r f (Set.Icc a b) a = 0)
    (hb : iteratedDerivWithin r f (Set.Icc a b) b = 0) :
    ∃ c ∈ Set.Ioo a b, iteratedDerivWithin (r + 1) f (Set.Icc a b) c = 0 := by
  let F : ℝ → ℝ := iteratedDerivWithin r f (Set.Icc a b)
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    -- The `r`th iterated derivative is continuous on the closed interval.
    simpa [F] using
      hf.continuousOn_iteratedDerivWithin
        (m := r) (by exact_mod_cast Nat.le_succ r) (uniqueDiffOn_Icc hab)
  have hFderiv :
      ∀ x ∈ Set.Ioo a b, HasDerivAt F (iteratedDerivWithin (r + 1) f (Set.Icc a b) x) x := by
    intro x hx
    have hdiff :
        DifferentiableWithinAt ℝ F (Set.Icc a b) x := by
      -- Interior points inherit differentiability of the iterated derivative from `ContDiffOn`.
      simpa [F] using
        (hf.differentiableOn_iteratedDerivWithin
          (m := r) (by exact_mod_cast Nat.lt_succ_self r) (uniqueDiffOn_Icc hab))
          x (Set.Ioo_subset_Icc_self hx)
    have hIcc : HasDerivWithinAt F (derivWithin F (Set.Icc a b) x) (Set.Icc a b) x :=
      hdiff.hasDerivWithinAt
    have hIoo : HasDerivWithinAt F (derivWithin F (Set.Icc a b) x) (Set.Ioo a b) x :=
      hIcc.mono_of_mem_nhdsWithin <|
        Filter.mem_of_superset self_mem_nhdsWithin Set.Ioo_subset_Icc_self
    -- On the open interval, this within-derivative becomes an ordinary derivative.
    simpa [F, iteratedDerivWithin_succ] using hIoo.hasDerivAt (isOpen_Ioo.mem_nhds hx)
  have hEq : F a = F b := by
    -- The endpoint hypotheses put the `r`th iterated derivative at the same value on both ends.
    simpa [F, ha, hb]
  -- Rolle's theorem on the `r`th iterated derivative produces the desired interior zero.
  simpa [F] using exists_hasDerivAt_eq_zero hab hFcont hEq hFderiv

/-- Helper for Exercise 1.3.47: after one differentiation, vanishing jets up to order `r`
become vanishing jets up to order `r - 1` for the first iterated derivative. -/
lemma iteratedDerivWithin_succ_zero_jets_of_zero_jets
    {f : ℝ → ℝ} {s : Set ℝ} {a : ℝ} {r : ℕ}
    (hzero : ∀ k : Fin (r + 1), iteratedDerivWithin k.1 f s a = 0) :
    ∀ k : Fin r, iteratedDerivWithin k.1 (iteratedDerivWithin 1 f s) s a = 0 := by
  intro k
  -- Rewrite the shifted jet of the first derivative as the next jet of the original function.
  simpa [iteratedDerivWithin_one, iteratedDerivWithin_succ'] using
    hzero ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩

/-- Helper for Exercise 1.3.47: the Hermite remainder polynomial
`∏ j, (X - x j)^(m j)` has zero iterated derivatives of orders `< m i` at the node `x i`. -/
lemma iteratedDerivWithin_eval_prod_X_sub_C_pow_eq_zero_of_lt_multiplicity
    (I : Set ℝ) (hIu : UniqueDiffOn ℝ I) {ι : Type v} [Fintype ι]
    (m : ι → ℕ) (x : ι → ℝ) (hxI : ∀ i, x i ∈ I) (i : ι) (k : Fin (m i)) :
    iteratedDerivWithin k.1
      (fun t ↦ (∏ j, ((X - C (x j)) ^ m j : ℝ[X])).eval t) I (x i) = 0 := by
  let W : ℝ[X] := ∏ j, ((X - C (x j)) ^ m j : ℝ[X])
  have hdiv : (X - C (x i)) ^ m i ∣ W := by
    -- One factor of the Hermite product already contributes the full multiplicity at `x i`.
    dsimp [W]
    exact Finset.dvd_prod_of_mem (fun j ↦ ((X - C (x j)) ^ m j : ℝ[X])) (Finset.mem_univ i)
  have hiterdiv : (X - C (x i)) ^ (m i - k.1) ∣ (Polynomial.derivative^[k.1]) W := by
    -- Differentiating fewer than `m i` times leaves at least one copy of the linear factor.
    exact Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k.1 hdiv
  have hlin : X - C (x i) ∣ (Polynomial.derivative^[k.1]) W := by
    have hsubpos : 0 < m i - k.1 := Nat.sub_pos_of_lt k.2
    exact dvd_trans (dvd_pow_self _ (Nat.ne_of_gt hsubpos)) hiterdiv
  have hroot : ((Polynomial.derivative^[k.1]) W).eval (x i) = 0 := by
    -- Evaluating at `x i` kills the remaining linear factor.
    exact (Polynomial.dvd_iff_isRoot.1 hlin)
  calc
    iteratedDerivWithin k.1
        (fun t ↦ (∏ j, ((X - C (x j)) ^ m j : ℝ[X])).eval t) I (x i) =
      ((Polynomial.derivative^[k.1]) W).eval (x i) := by
        -- Convert the analytic iterated derivative back to the polynomial iterate.
        simpa [W] using
          (iteratedDerivWithin_eval_eq_eval_iterate_derivative I hIu W k.1) (x := x i) (hxI i)
    _ = 0 := hroot

/-- Helper for Exercise 1.3.47: after subtracting the interpolation polynomial and normalized
Hermite remainder term, the auxiliary error function has zero jets at every interpolation node. -/
lemma auxiliary_hermite_error_zero_jets
    (I : Set ℝ) (hIu : UniqueDiffOn ℝ I) (f : ℝ → ℝ) {ι : Type v} [Fintype ι]
    (m : ι → ℕ) (hf : ContDiffOn ℝ (∑ i, m i) f I) (x : ι → ℝ) (hxI : ∀ i, x i ∈ I)
    (P W : ℝ[X])
    (hP : ∀ i, ∀ k : Fin (m i),
      ((Polynomial.derivative^[k.1]) P).eval (x i) = iteratedDerivWithin k.1 f I (x i))
    (hWjets : ∀ i, ∀ k : Fin (m i),
      iteratedDerivWithin k.1 (fun t ↦ W.eval t) I (x i) = 0)
    (c : ℝ) (g : ℝ → ℝ) {x0 : ℝ}
    (hg : g = fun t ↦ f t - P.eval t - c * W.eval t)
    (hg0 : g x0 = 0) :
    g x0 = 0 ∧ ∀ i, ∀ k : Fin (m i), iteratedDerivWithin k.1 g I (x i) = 0 := by
  refine ⟨hg0, ?_⟩
  intro i k
  have hmiN : m i ≤ ∑ j, m j := by
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j)) (by simp)
  have hkN : k.1 ≤ ∑ j, m j := le_trans (Nat.le_of_lt k.2) hmiN
  have hfk : ContDiffWithinAt ℝ k.1 f I (x i) := by
    -- Restrict the ambient `C^N` regularity of `f` to the jet order under consideration.
    exact (hf.contDiffWithinAt (hxI i)).of_le (by exact_mod_cast hkN)
  have hPcont : ContDiffWithinAt ℝ k.1 (fun t ↦ P.eval t) I (x i) := by
    -- Polynomial evaluation is smooth of all orders.
    exact (Polynomial.contDiff_aeval P (k.1 : WithTop ℕ∞)).contDiffWithinAt
  have hWcont : ContDiffWithinAt ℝ k.1 (fun t ↦ c * W.eval t) I (x i) := by
    -- The normalized remainder term is also smooth because it is a polynomial multiple.
    exact (contDiff_const.mul (Polynomial.contDiff_aeval W (k.1 : WithTop ℕ∞))).contDiffWithinAt
  have hfgcont : ContDiffWithinAt ℝ k.1 (fun t ↦ f t - P.eval t) I (x i) := hfk.sub hPcont
  have hPjet :
      iteratedDerivWithin k.1 (fun t ↦ P.eval t) I (x i) =
        ((Polynomial.derivative^[k.1]) P).eval (x i) := by
    -- Replace the analytic jet of `P.eval` by the iterated polynomial derivative.
    simpa using
      (iteratedDerivWithin_eval_eq_eval_iterate_derivative I hIu P k.1) (x := x i) (hxI i)
  have hsub :
      iteratedDerivWithin k.1 (fun t ↦ f t - P.eval t) I (x i) =
        iteratedDerivWithin k.1 f I (x i) -
          iteratedDerivWithin k.1 (fun t ↦ P.eval t) I (x i) := by
    -- Separate the interpolation error into its `f` and polynomial parts.
    exact iteratedDerivWithin_sub (hxI i) hIu hfk hPcont
  calc
    iteratedDerivWithin k.1 g I (x i) =
        iteratedDerivWithin k.1 (fun t ↦ f t - P.eval t) I (x i) -
          iteratedDerivWithin k.1 (fun t ↦ c * W.eval t) I (x i) := by
      -- Differentiate the auxiliary error as a difference of the interpolation error and the
      -- normalized remainder term.
      rw [hg]
      exact iteratedDerivWithin_sub (hxI i) hIu hfgcont hWcont
    _ = (iteratedDerivWithin k.1 f I (x i) -
          iteratedDerivWithin k.1 (fun t ↦ P.eval t) I (x i)) -
          (c * iteratedDerivWithin k.1 (fun t ↦ W.eval t) I (x i)) := by
      rw [hsub, iteratedDerivWithin_const_mul_field]
    _ = (iteratedDerivWithin k.1 f I (x i) -
          ((Polynomial.derivative^[k.1]) P).eval (x i)) -
          (c * 0) := by
      rw [hPjet, hWjets i k]
    _ = 0 := by
      rw [← hP i k]
      ring

/-- Helper for Exercise 1.3.47: after taking `N` iterated derivatives, the auxiliary error
`f - P - cW` reduces to the `N`th derivative of `f` minus `c * N!`. -/
lemma iteratedDerivWithin_auxiliary_error_eq
    (I : Set ℝ) (hIu : UniqueDiffOn ℝ I) (f : ℝ → ℝ) (P W : ℝ[X]) (N : ℕ)
    (hf : ContDiffOn ℝ N f I) (hPdeg : P.degree < N)
    (hWtop : (Polynomial.derivative^[N]) W = C ((N.factorial : ℕ) : ℝ))
    (c : ℝ) {ξ : ℝ} (hξ : ξ ∈ I) :
    iteratedDerivWithin N (fun t ↦ f t - P.eval t - c * W.eval t) I ξ =
      iteratedDerivWithin N f I ξ - c * (N.factorial : ℝ) := by
  have hff : ContDiffWithinAt ℝ N f I ξ := hf.contDiffWithinAt hξ
  have hPcont : ContDiffWithinAt ℝ N (fun t ↦ P.eval t) I ξ := by
    exact (Polynomial.contDiff_aeval P (N : WithTop ℕ∞)).contDiffWithinAt
  have hWcont : ContDiffWithinAt ℝ N (fun t ↦ c * W.eval t) I ξ := by
    exact (contDiff_const.mul (Polynomial.contDiff_aeval W (N : WithTop ℕ∞))).contDiffWithinAt
  have hPjet :
      iteratedDerivWithin N (fun t ↦ P.eval t) I ξ = ((Polynomial.derivative^[N]) P).eval ξ := by
    -- Convert the analytic iterated derivative of `P.eval` back to the polynomial iterate.
    simpa using
      (iteratedDerivWithin_eval_eq_eval_iterate_derivative I hIu P N) (x := ξ) hξ
  have hWjet :
      iteratedDerivWithin N (fun t ↦ W.eval t) I ξ = ((Polynomial.derivative^[N]) W).eval ξ := by
    -- The same identification applies to the Hermite product polynomial.
    simpa using
      (iteratedDerivWithin_eval_eq_eval_iterate_derivative I hIu W N) (x := ξ) hξ
  have hsub :
      iteratedDerivWithin N (fun t ↦ f t - P.eval t) I ξ =
        iteratedDerivWithin N f I ξ -
          iteratedDerivWithin N (fun t ↦ P.eval t) I ξ := by
    -- First separate the interpolation error into the `f`-part and the polynomial part.
    exact iteratedDerivWithin_sub hξ hIu hff hPcont
  calc
    iteratedDerivWithin N (fun t ↦ f t - P.eval t - c * W.eval t) I ξ =
        iteratedDerivWithin N (fun t ↦ f t - P.eval t) I ξ -
          iteratedDerivWithin N (fun t ↦ c * W.eval t) I ξ := by
      -- Then differentiate the subtraction of the normalized Hermite product.
      exact iteratedDerivWithin_sub hξ hIu (hff.sub hPcont) hWcont
    _ = (iteratedDerivWithin N f I ξ -
          iteratedDerivWithin N (fun t ↦ P.eval t) I ξ) -
          c * iteratedDerivWithin N (fun t ↦ W.eval t) I ξ := by
      rw [hsub, iteratedDerivWithin_const_mul_field]
    _ = (iteratedDerivWithin N f I ξ - ((Polynomial.derivative^[N]) P).eval ξ) -
          c * ((Polynomial.derivative^[N]) W).eval ξ := by
      rw [hPjet, hWjet]
    _ = iteratedDerivWithin N f I ξ - c * (N.factorial : ℝ) := by
      rw [Polynomial.iterate_derivative_eq_zero_of_degree_lt hPdeg, hWtop]
      simp

/-- Helper for Exercise 1.3.47: at an interior point of a subinterval of `I`, the iterated
derivative computed within that subinterval agrees with the one computed within `I`. -/
lemma iteratedDerivWithin_eq_on_interval_interior
    {f : ℝ → ℝ} {I : Set ℝ} (hI : Set.OrdConnected I) {a b y : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hy : y ∈ Set.Ioo a b) (r : ℕ) :
    iteratedDerivWithin r f (Set.Icc a b) y = iteratedDerivWithin r f I y := by
  have hsets : Set.Icc a b =ᶠ[𝓝 y] I := by
    -- Near an interior point of `[a, b]`, both ambient sets contain the same neighborhood.
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact propext
      ⟨fun hzIcc ↦ hI.out ha hb hzIcc, fun _ ↦ Set.Ioo_subset_Icc_self hz⟩
  -- Transport the one-dimensional iterated derivative through the corresponding Fréchet theorem.
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
  exact congrArg
    (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin r => ℝ) ℝ =>
      (L : (Fin r → ℝ) → ℝ) (fun _ ↦ (1 : ℝ)))
    (iteratedFDerivWithin_congr_set (𝕜 := ℝ) (f := f) hsets r)

/-- Helper for Exercise 1.3.47: a strictly increasing chain of zeros yields one zero of the first
iterated derivative in each adjacent gap. -/
lemma rolle_points_between_sorted_zeros
    {g : ℝ → ℝ} {I : Set ℝ} (hI : Set.OrdConnected I) {n : ℕ}
    (s : Fin (n + 1) → ℝ) (hsmono : StrictMono s) (hsI : ∀ j, s j ∈ I)
    (hg : ContDiffOn ℝ 1 g I) (hzero : ∀ j, g (s j) = 0) :
    ∃ c : Fin n → ℝ,
      (∀ j, c j ∈ Set.Ioo (s (Fin.castSucc j)) (s j.succ)) ∧
      ∀ j, iteratedDerivWithin 1 g I (c j) = 0 := by
  classical
  have hstep :
      ∀ j : Fin n,
        ∃ c, c ∈ Set.Ioo (s (Fin.castSucc j)) (s j.succ) ∧
          iteratedDerivWithin 1 g I c = 0 := by
    intro j
    have hab : s (Fin.castSucc j) < s j.succ := hsmono Fin.castSucc_lt_succ
    have hgIcc : ContDiffOn ℝ 1 g (Set.Icc (s (Fin.castSucc j)) (s j.succ)) := by
      -- Restrict the ambient regularity to the closed interval between the adjacent support points.
      apply hg.mono
      intro y hy
      exact hI.out (hsI (Fin.castSucc j)) (hsI j.succ) hy
    obtain ⟨c, hc, hc0⟩ :=
      iteratedDerivWithin_succ_eq_zero_between_of_eq_zero
        hab 0 hgIcc (by simpa using hzero (Fin.castSucc j)) (by simpa using hzero j.succ)
    refine ⟨c, hc, ?_⟩
    have htransport :=
      iteratedDerivWithin_eq_on_interval_interior
        (f := g) hI (hsI (Fin.castSucc j)) (hsI j.succ) hc 1
    -- Replace the local interval derivative by the ambient interval derivative at the gap point.
    rw [← htransport]
    exact hc0
  choose c hc hc0 using hstep
  exact ⟨c, hc, hc0⟩

/-- Helper for Exercise 1.3.47: the weighted repeated-Rolle induction is organized around a
finite linearly ordered support of distinct points, each carrying a positive zero multiplicity
budget. The order is the one inherited from `ℝ` on the subtype `Z.support`. -/
structure WeightedZeroData
    (I : Set ℝ) {ι : Type v} [Fintype ι] (x : ι → ℝ) {x0 : ℝ} (g : ℝ → ℝ) (r : ℕ) where
  support : Finset ℝ
  weight : support → ℕ
  support_subset : ↑support ⊆ convexHull ℝ (insert x0 (Set.range x))
  weight_pos : ∀ a, 0 < weight a
  weight_sum : ∑ a : support, weight a = r + 1
  jet_zero :
    ∀ a, ∀ k : Fin (weight a), iteratedDerivWithin k.1 g I a.1 = 0

/-- Helper for Exercise 1.3.47: removing the zero-multiplicity nodes does not change the total
multiplicity sum. -/
lemma sum_filter_pos_eq_sum
    {ι : Type v} [Fintype ι] (m : ι → ℕ) :
    Finset.sum (Finset.univ.filter (fun i ↦ 0 < m i)) m = Finset.sum Finset.univ m := by
  -- The filtered-out summands are exactly the zero terms.
  simpa [Nat.pos_iff_ne_zero] using
    (Finset.sum_filter_ne_zero (s := Finset.univ) (f := m))

/-- Helper for Exercise 1.3.47: the distinguished point is disjoint from the positive-multiplicity
support. -/
lemma x0_not_mem_positive_support_image
    {ι : Type v} [Fintype ι] (m : ι → ℕ) (x : ι → ℝ) {x0 : ℝ}
    (hx0_pos : ∀ i, 0 < m i → x0 ≠ x i) :
    x0 ∉ Set.range fun i : {i // 0 < m i} ↦ x i := by
  -- Any point in the positive-multiplicity image contradicts the separation hypothesis at `x0`.
  intro hx0range
  rcases hx0range with ⟨i, hxi⟩
  exact hx0_pos i.1 i.2 hxi.symm

/-- Helper for Exercise 1.3.47: sorting `x₀` together with the positive-multiplicity nodes
produces the initial ordered zero chain for the repeated-Rolle argument. -/
lemma exists_initial_sorted_support
    {ι : Type v} [Fintype ι] (m : ι → ℕ) (x : ι → ℝ) {x0 : ℝ} :
    ∃ l : List ℝ,
      l.Pairwise (· < ·) ∧
      (∀ a, a ∈ l ↔ a ∈ insert x0 ((Finset.univ.filter fun i ↦ 0 < m i).image x)) := by
  let support : Finset ℝ := insert x0 ((Finset.univ.filter fun i ↦ 0 < m i).image x)
  refine ⟨support.sort (· ≤ ·), ?_, ?_⟩
  · -- Sorting the finite support gives a strictly increasing list of distinct points.
    simpa [support] using (Finset.sortedLT_sort support).pairwise
  · intro a
    -- Membership in the sorted list is exactly membership in the underlying finite support.
    simpa [support] using (Finset.mem_sort (s := support) (r := (· ≤ ·)) (a := a))

/-- Helper for Exercise 1.3.47: every support point of a weighted zero chain stays in the ambient
interval because the convex hull of the interpolation nodes is contained in an interval. -/
lemma WeightedZeroData.mem_of_support
    {I : Set ℝ} {ι : Type v} [Fintype ι] {x : ι → ℝ} {x0 : ℝ} {g : ℝ → ℝ} {r : ℕ}
    (Z : WeightedZeroData I x (x0 := x0) g r) (hI : Set.OrdConnected I)
    (hxI : ∀ i, x i ∈ I) (hx0 : x0 ∈ I) :
    ∀ a : Z.support, a.1 ∈ I := by
  intro a
  -- Every support point lies in the convex hull of the interpolation nodes and `x₀`.
  have hahull : a.1 ∈ convexHull ℝ (insert x0 (Set.range x)) := Z.support_subset a.2
  -- An interval contains the convex hull of any subset of it.
  refine convexHull_min ?_ hI.convex hahull
  intro y hy
  rcases hy with rfl | hy
  · exact hx0
  · rcases hy with ⟨i, rfl⟩
    exact hxI i

/-- Helper for Exercise 1.3.47: a weighted zero chain can be enumerated in increasing order,
with the support points staying in the ambient interval and remaining zeros of the function. -/
lemma WeightedZeroData.exists_sorted_support_chain
    {I : Set ℝ} {ι : Type v} [Fintype ι] {x : ι → ℝ} {x0 : ℝ} {g : ℝ → ℝ} {r : ℕ}
    (Z : WeightedZeroData I x (x0 := x0) g r) (hI : Set.OrdConnected I)
    (hxI : ∀ i, x i ∈ I) (hx0 : x0 ∈ I) :
    ∃ n : ℕ, ∃ s : Fin (n + 1) → ℝ,
      StrictMono s ∧
      Set.range s = ↑Z.support ∧
      (∀ j, s j ∈ I) ∧
      (∀ j, s j ∈ convexHull ℝ (insert x0 (Set.range x))) ∧
      (∀ j, g (s j) = 0) := by
  have hsupport_ne : Z.support.card ≠ 0 := by
    have hsum_pos : 0 < ∑ a : Z.support, Z.weight a := by
      rw [Z.weight_sum]
      exact Nat.succ_pos _
    intro h0
    have hsubempty : IsEmpty Z.support := by
      refine ⟨fun a ↦ ?_⟩
      have : (a : ℝ) ∈ (∅ : Finset ℝ) := by
        simpa [Finset.card_eq_zero.mp h0] using a.2
      simpa using this
    letI := hsubempty
    have hsum_zero : (∑ a : Z.support, Z.weight a) = 0 := by simp
    have : 0 < (0 : ℕ) := by simpa [hsum_zero] using hsum_pos
    exact Nat.lt_asymm this this
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hsupport_ne
  let s : Fin (n + 1) → ℝ := Z.support.orderEmbOfFin hn
  refine ⟨n, s, (Z.support.orderEmbOfFin hn).strictMono, ?_, ?_, ?_, ?_⟩
  · -- The sorted enumeration hits every support point exactly once.
    simpa [s] using (Finset.range_orderEmbOfFin (s := Z.support) (h := hn))
  · intro j
    -- Every support point stays in the interval because the interval contains the convex hull.
    exact
      Z.mem_of_support hI hxI hx0
        ⟨s j, by simpa [s] using (Finset.orderEmbOfFin_mem (s := Z.support) (h := hn) j)⟩
  · intro j
    -- The sorted enumeration is still the same support used in the weighted zero data.
    exact Z.support_subset (by simpa [s] using (Finset.orderEmbOfFin_mem (s := Z.support) (h := hn) j))
  · intro j
    -- The order-zero jet at each support point is just the function value.
    let a : Z.support :=
      ⟨s j, by simpa [s] using (Finset.orderEmbOfFin_mem (s := Z.support) (h := hn) j)⟩
    have hpos : 0 < Z.weight a := Z.weight_pos a
    simpa [a] using Z.jet_zero a ⟨0, hpos⟩

/-- Helper for Exercise 1.3.47: the distinguished point together with the positive-multiplicity
nodes already form the initial ordered weighted zero chain for the repeated-Rolle argument. -/
lemma exists_initial_ordered_zero_chain
    (I : Set ℝ) {ι : Type v} [Fintype ι] (m : ι → ℕ) (x : ι → ℝ)
    (hx : Function.Injective x) {x0 : ℝ} {g : ℝ → ℝ}
    (hx0_pos : ∀ i, 0 < m i → x0 ≠ x i)
    (hg0 : g x0 = 0)
    (hgjets : ∀ i, ∀ k : Fin (m i), iteratedDerivWithin k.1 g I (x i) = 0) :
    Nonempty (WeightedZeroData I x (x0 := x0) g (∑ i, m i)) := by
  classical
  let positiveIndex : Type v := {i // 0 < m i}
  let node : Option positiveIndex → ℝ
    | none => x0
    | some i => x i.1
  have hnode_inj : Function.Injective node := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none =>
            rfl
        | some j =>
            exfalso
            exact hx0_pos j.1 j.2 (by simpa [node] using hab)
    | some i =>
        cases b with
        | none =>
            exfalso
            exact hx0_pos i.1 i.2 (by simpa [node] using hab.symm)
        | some j =>
            have hij : i.1 = j.1 := hx (by simpa [node] using hab)
            simpa using congrArg some (Subtype.ext hij)
  let support : Finset ℝ := Finset.univ.image node
  let nodeEquiv : Option positiveIndex ≃ support :=
    { toFun := fun a ↦
        ⟨node a, by
          change node a ∈ Finset.univ.image node
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
      invFun := fun a ↦ Classical.choose (Finset.mem_image.mp a.2)
      left_inv := by
        intro a
        apply hnode_inj
        exact (Classical.choose_spec (Finset.mem_image.mp (by
          change node a ∈ Finset.univ.image node
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))).2
      right_inv := by
        intro a
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp a.2)).2 }
  let weight : support → ℕ := fun a ↦
    match nodeEquiv.symm a with
    | none => 1
    | some i => m i.1
  refine ⟨{
      support := support
      weight := weight
      support_subset := ?_
      weight_pos := ?_
      weight_sum := ?_
      jet_zero := ?_ }⟩
  · intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
    cases b with
    | none =>
        -- The distinguished point is one of the generating vertices of the convex hull.
        simpa [node] using
          (subset_convexHull ℝ (insert x0 (Set.range x)) (by simp : x0 ∈ insert x0 (Set.range x)))
    | some i =>
        -- Each positive-multiplicity node is also one of the generating vertices.
        exact subset_convexHull ℝ _ (by
          right
          exact ⟨i.1, rfl⟩)
  · intro a
    -- Pull the support point back to either `x₀` or a positive-multiplicity node.
    cases hnode : nodeEquiv.symm a with
    | none =>
        simp [weight, hnode]
    | some i =>
        simpa [weight, hnode] using i.2
  · -- Transport the support sum to the explicit source indexing type `Option positiveIndex`.
    calc
      ∑ a : support, weight a =
          ∑ b : Option positiveIndex,
            match b with
            | none => 1
            | some i => m i.1 := by
        refine Fintype.sum_equiv nodeEquiv.symm weight _ ?_
        intro a
        cases hnode : nodeEquiv.symm a <;> simp [weight, hnode]
      _ = 1 + ∑ i : positiveIndex, m i.1 := by
        simpa using
          (Fintype.sum_option
            (fun b : Option positiveIndex ↦
              match b with
              | none => 1
              | some i => m i.1))
      _ = 1 + Finset.sum (Finset.univ.filter (fun i ↦ 0 < m i)) m := by
        rw [← Finset.sum_subtype (s := Finset.univ.filter fun i ↦ 0 < m i)
          (h := by
            intro i
            simp)
          (f := m)]
      _ = (∑ i, m i) + 1 := by
        rw [sum_filter_pos_eq_sum]
        simp [Nat.add_comm]
  · intro a k
    -- Pull the support point back to the distinguished zero or to one interpolation node.
    cases hnode : nodeEquiv.symm a with
    | none =>
        have hk1 : k.1 < 1 := by
          simpa [weight, hnode] using k.2
        have hk0 : k.1 = 0 := by omega
        have ha_eq : a = nodeEquiv none := by
          simpa using congrArg nodeEquiv hnode
        have ha_val : a.1 = x0 := by
          simpa [nodeEquiv, node] using congrArg Subtype.val ha_eq
        simpa [weight, hnode, hk0, ha_val] using hg0
    | some i =>
        have hk : k.1 < m i.1 := by
          simpa [weight, hnode] using k.2
        have ha_eq : a.1 = x i.1 := by
          have hEq : a = nodeEquiv (some i) := by
            simpa using congrArg nodeEquiv hnode
          simpa [nodeEquiv, node] using congrArg Subtype.val hEq
        simpa [ha_eq] using hgjets i.1 ⟨k.1, hk⟩

/-- Helper for Exercise 1.3.47: after subtracting one from each positive weight, the sum over the
retained weights is the original total weight minus the number of support points. -/
lemma sum_decremented_retained_weights_eq_total_sub_length
    {n : ℕ} (w : Fin (n + 1) → ℕ) (hwpos : ∀ j, 0 < w j) :
    ∑ j : {j : Fin (n + 1) // 1 < w j}, (w j.1 - 1) =
      (∑ j : Fin (n + 1), w j) - (n + 1) := by
  have hsubtype :
      ∑ j : {j : Fin (n + 1) // 1 < w j}, (w j.1 - 1) =
        Finset.sum (Finset.univ.filter (fun j : Fin (n + 1) ↦ 1 < w j)) (fun j ↦ w j - 1) := by
    -- Rewrite the subtype sum as a filtered sum on the ambient finite type.
    rw [← Finset.sum_subtype
      (s := Finset.univ.filter fun j : Fin (n + 1) ↦ 1 < w j)
      (h := by
        intro j
        simp)
      (f := fun j : Fin (n + 1) ↦ w j - 1)]
  have hfilter :
      Finset.sum (Finset.univ.filter (fun j : Fin (n + 1) ↦ 1 < w j)) (fun j ↦ w j - 1) =
        ∑ j : Fin (n + 1), (w j - 1) := by
    -- The discarded indices are exactly those with decremented weight equal to zero.
    have hpred : ∀ j : Fin (n + 1), (w j - 1 ≠ 0) ↔ 1 < w j := by
      intro j
      omega
    simpa [hpred] using
      (Finset.sum_filter_ne_zero (s := Finset.univ) (f := fun j : Fin (n + 1) ↦ w j - 1))
  have hsplit :
      ∑ j : Fin (n + 1), w j = (∑ j : Fin (n + 1), (w j - 1)) + (n + 1) := by
    -- Each positive weight splits as its decremented part plus one.
    calc
      ∑ j : Fin (n + 1), w j = ∑ j : Fin (n + 1), ((w j - 1) + 1) := by
        apply Fintype.sum_congr
        intro j
        exact (Nat.sub_add_cancel (Nat.succ_le_of_lt (hwpos j))).symm
      _ = (∑ j : Fin (n + 1), (w j - 1)) + ∑ _j : Fin (n + 1), 1 := by
        simpa using
          (Finset.sum_add_distrib
            (s := Finset.univ) (f := fun j : Fin (n + 1) ↦ w j - 1)
            (g := fun _j : Fin (n + 1) ↦ 1))
      _ = (∑ j : Fin (n + 1), (w j - 1)) + (n + 1) := by
        simp
  rw [hsubtype, hfilter]
  omega

/-- Helper for Exercise 1.3.47: one differentiation lowers the total weighted multiplicity by
one, retaining higher-order zeros at the old support points and inserting a Rolle zero in each
adjacent gap. -/
lemma weighted_zero_data_step
    (I : Set ℝ) (hI : Set.OrdConnected I) {ι : Type v} [Fintype ι]
    (x : ι → ℝ) (hxI : ∀ i, x i ∈ I)
    {g : ℝ → ℝ} {x0 : ℝ} {r : ℕ}
    (Z : WeightedZeroData I x (x0 := x0) g (r + 1)) (hx0 : x0 ∈ I)
    (hg : ContDiffOn ℝ 1 g I) :
    Nonempty (WeightedZeroData I x (x0 := x0) (iteratedDerivWithin 1 g I) r) := by
  classical
  -- Route correction: work on the sorted `Fin`-indexed support chain of `Z`, then package the
  -- derivative-stage support from retained old nodes together with one Rolle zero in each gap.
  obtain ⟨n, s, hsmono, hsrange, hsI, hsHull, hszero⟩ :=
    Z.exists_sorted_support_chain hI hxI hx0
  let oldNode : Fin (n + 1) → Z.support := fun j ↦
    ⟨s j, by
      have hs_mem : s j ∈ Set.range s := ⟨j, rfl⟩
      simpa [hsrange] using hs_mem⟩
  have holdNode_inj : Function.Injective oldNode := by
    intro i j hij
    apply hsmono.injective
    exact congrArg Subtype.val hij
  have holdNode_surj : Function.Surjective oldNode := by
    intro a
    have ha_range : a.1 ∈ Set.range s := by
      simpa [hsrange] using a.2
    rcases ha_range with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    simpa [oldNode] using hj
  let oldEquiv : Fin (n + 1) ≃ Z.support := Equiv.ofBijective oldNode ⟨holdNode_inj, holdNode_surj⟩
  let w : Fin (n + 1) → ℕ := fun j ↦ Z.weight (oldNode j)
  have hwpos : ∀ j, 0 < w j := by
    intro j
    exact Z.weight_pos (oldNode j)
  have hwsum : ∑ j : Fin (n + 1), w j = r + 2 := by
    -- Transport the original weighted sum to the sorted `Fin` indexing.
    calc
      ∑ j : Fin (n + 1), w j = ∑ a : Z.support, Z.weight a := by
        refine Fintype.sum_equiv oldEquiv w Z.weight ?_
        intro j
        rfl
      _ = r + 2 := by
        simpa [Nat.add_assoc] using Z.weight_sum
  obtain ⟨c, hc, hc0⟩ := rolle_points_between_sorted_zeros hI s hsmono hsI hg hszero
  have hcHull : ∀ j : Fin n, c j ∈ convexHull ℝ (insert x0 (Set.range x)) := by
    intro j
    -- Each Rolle point lies on the segment between two consecutive support points in the hull.
    have hseg : c j ∈ segment ℝ (s (Fin.castSucc j)) (s j.succ) := by
      rw [segment_eq_Icc (le_of_lt (hsmono Fin.castSucc_lt_succ))]
      exact Set.Ioo_subset_Icc_self (hc j)
    exact
      (convex_convexHull ℝ (insert x0 (Set.range x))).segment_subset
        (hsHull (Fin.castSucc j)) (hsHull j.succ) hseg
  let retained : Type := {j : Fin (n + 1) // 1 < w j}
  have hretained_sum :
      ∑ j : retained, (w j.1 - 1) = (∑ j : Fin (n + 1), w j) - (n + 1) := by
    simpa [retained] using sum_decremented_retained_weights_eq_total_sub_length w hwpos
  let newNode : Sum retained (Fin n) → ℝ
    | Sum.inl j => s j.1
    | Sum.inr j => c j
  have hnewNode_inj : Function.Injective newNode := by
    intro u v huv
    cases u with
    | inl ju =>
        cases v with
        | inl jv =>
            apply congrArg Sum.inl
            apply Subtype.ext
            exact hsmono.injective (by simpa [newNode] using huv)
        | inr jv =>
            exfalso
            have hEq : s ju.1 = c jv := by
              simpa [newNode] using huv
            have hleft : s (Fin.castSucc jv) < s ju.1 := by
              simpa [hEq] using (hc jv).1
            have hright : s ju.1 < s jv.succ := by
              simpa [hEq] using (hc jv).2
            have hgt : (Fin.castSucc jv : Fin (n + 1)) < ju.1 := by
              by_contra hnot
              exact not_lt_of_ge (hsmono.monotone (le_of_not_gt hnot)) hleft
            have hlt : ju.1 < jv.succ := by
              by_contra hnot
              exact not_lt_of_ge (hsmono.monotone (le_of_not_gt hnot)) hright
            have hgt' : (jv : ℕ) < ju.1 := by
              exact Fin.lt_def.mp hgt
            have hlt' : (ju.1 : ℕ) < jv.1 + 1 := by
              simpa using (Fin.lt_def.mp hlt)
            omega
    | inr ju =>
        cases v with
        | inl jv =>
            exfalso
            have hEq : c ju = s jv.1 := by
              simpa [newNode] using huv
            have hleft : s (Fin.castSucc ju) < s jv.1 := by
              simpa [hEq] using (hc ju).1
            have hright : s jv.1 < s ju.succ := by
              simpa [hEq] using (hc ju).2
            have hgt : (Fin.castSucc ju : Fin (n + 1)) < jv.1 := by
              by_contra hnot
              exact not_lt_of_ge (hsmono.monotone (le_of_not_gt hnot)) hleft
            have hlt : jv.1 < ju.succ := by
              by_contra hnot
              exact not_lt_of_ge (hsmono.monotone (le_of_not_gt hnot)) hright
            have hgt' : (ju : ℕ) < jv.1 := by
              exact Fin.lt_def.mp hgt
            have hlt' : (jv.1 : ℕ) < ju.1 + 1 := by
              simpa using (Fin.lt_def.mp hlt)
            omega
        | inr jv =>
            rcases lt_trichotomy ju jv with hlt | rfl | hgt
            · exfalso
              have hindex : ju.succ ≤ Fin.castSucc jv := by
                exact Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt hlt)
              have hmid : c ju < s (Fin.castSucc jv) := by
                exact lt_of_lt_of_le (hc ju).2 (hsmono.monotone hindex)
              have hlt' : c ju < c jv := by
                exact lt_trans hmid (hc jv).1
              exact (ne_of_lt hlt') (by simpa [newNode] using huv)
            · rfl
            · exfalso
              have hindex : jv.succ ≤ Fin.castSucc ju := by
                exact Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt hgt)
              have hmid : c jv < s (Fin.castSucc ju) := by
                exact lt_of_lt_of_le (hc jv).2 (hsmono.monotone hindex)
              have hlt' : c jv < c ju := by
                exact lt_trans hmid (hc ju).1
              exact (ne_of_lt hlt') (by simpa [newNode] using huv.symm)
  let support : Finset ℝ := Finset.univ.image newNode
  let newEquiv : Sum retained (Fin n) ≃ support :=
    { toFun := fun a ↦
        ⟨newNode a, by
          change newNode a ∈ Finset.univ.image newNode
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
      invFun := fun a ↦ Classical.choose (Finset.mem_image.mp a.2)
      left_inv := by
        intro a
        apply hnewNode_inj
        exact (Classical.choose_spec (Finset.mem_image.mp (by
          change newNode a ∈ Finset.univ.image newNode
          exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))).2
      right_inv := by
        intro a
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp a.2)).2 }
  let weight : support → ℕ := fun a ↦
    match newEquiv.symm a with
    | Sum.inl j => w j.1 - 1
    | Sum.inr _ => 1
  refine ⟨{
      support := support
      weight := weight
      support_subset := ?_
      weight_pos := ?_
      weight_sum := ?_
      jet_zero := ?_ }⟩
  · intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
    cases b with
    | inl j =>
        -- Retained old nodes keep their convex-hull membership.
        exact hsHull j.1
    | inr j =>
        -- Gap points inherit convex-hull membership from the segment between old nodes.
        exact hcHull j
  · intro a
    cases hsrc : newEquiv.symm a with
    | inl j =>
        -- A retained old node had multiplicity at least two, so its decremented weight is still positive.
        have hpos : 0 < w j.1 - 1 := by
          omega
        simpa [weight, hsrc] using hpos
    | inr j =>
        -- Each newly inserted gap zero carries weight one.
        simp [weight, hsrc]
  · -- Transport the weight sum to the explicit source type `Sum retained (Fin n)`.
    have hsplit_w :
        ∑ j : Fin (n + 1), w j = (∑ j : Fin (n + 1), (w j - 1)) + (n + 1) := by
      -- The old total weight is at least the number of support points because every weight is positive.
      calc
        ∑ j : Fin (n + 1), w j = ∑ j : Fin (n + 1), ((w j - 1) + 1) := by
          apply Fintype.sum_congr
          intro j
          exact (Nat.sub_add_cancel (Nat.succ_le_of_lt (hwpos j))).symm
        _ = (∑ j : Fin (n + 1), (w j - 1)) + ∑ _j : Fin (n + 1), 1 := by
          simpa using
            (Finset.sum_add_distrib
              (s := Finset.univ) (f := fun j : Fin (n + 1) ↦ w j - 1)
              (g := fun _j : Fin (n + 1) ↦ 1))
        _ = (∑ j : Fin (n + 1), (w j - 1)) + (n + 1) := by
          simp
    have hcard_le : n + 1 ≤ ∑ j : Fin (n + 1), w j := by
      rw [hsplit_w]
      omega
    calc
      ∑ a : support, weight a =
          ∑ b : Sum retained (Fin n),
            match b with
            | Sum.inl j => w j.1 - 1
            | Sum.inr _ => 1 := by
          refine Fintype.sum_equiv newEquiv.symm weight _ ?_
          intro a
          cases hsrc : newEquiv.symm a <;> simp [weight, hsrc]
      _ = (∑ j : retained, (w j.1 - 1)) + ∑ _j : Fin n, 1 := by
          simpa using
            (Fintype.sum_sum_type
              (fun b : Sum retained (Fin n) ↦
                match b with
                | Sum.inl j => w j.1 - 1
                | Sum.inr _ => 1))
      _ = ((∑ j : Fin (n + 1), w j) - (n + 1)) + n := by
          rw [hretained_sum]
          simp
      _ = r + 1 := by
          have hcard_le' : n + 1 ≤ r + 2 := by
            rw [← hwsum]
            exact hcard_le
          rw [hwsum]
          omega
  · intro a k
    cases hsrc : newEquiv.symm a with
    | inl j =>
        -- At a retained old node, the derivative jets are the shifted old jets.
        have hk : k.1 < w j.1 - 1 := by
          simpa [weight, hsrc] using k.2
        have hwpred : (w j.1 - 1) + 1 = w j.1 := by
          omega
        have holdJets :
            ∀ t : Fin ((w j.1 - 1) + 1), iteratedDerivWithin t.1 g I (s j.1) = 0 := by
          intro t
          have ht : t.1 < w j.1 := by
            simpa [hwpred] using t.2
          simpa [w, oldNode] using Z.jet_zero (oldNode j.1) ⟨t.1, ht⟩
        have hnewJets :
            ∀ t : Fin (w j.1 - 1),
              iteratedDerivWithin t.1 (iteratedDerivWithin 1 g I) I (s j.1) = 0 :=
          iteratedDerivWithin_succ_zero_jets_of_zero_jets
            (s := I) (a := s j.1) (r := w j.1 - 1) holdJets
        have ha_eq : a.1 = s j.1 := by
          have hEq : a = newEquiv (Sum.inl j) := by
            simpa using congrArg newEquiv hsrc
          simpa [newEquiv, newNode] using congrArg Subtype.val hEq
        simpa [weight, hsrc, ha_eq] using hnewJets ⟨k.1, hk⟩
    | inr j =>
        -- At a gap point, only the order-zero jet is required, and it is exactly Rolle's zero.
        have hk1 : k.1 < 1 := by
          simpa [weight, hsrc] using k.2
        have hk0 : k.1 = 0 := by
          omega
        have ha_eq : a.1 = c j := by
          have hEq : a = newEquiv (Sum.inr j) := by
            simpa using congrArg newEquiv hsrc
          simpa [newEquiv, newNode] using congrArg Subtype.val hEq
        simpa [weight, hsrc, hk0, ha_eq] using hc0 j

/-- Helper for Exercise 1.3.47: once the weighted ordered zero chain is available, the remaining
proof is a repeated-Rolle induction on its total multiplicity. -/
lemma exists_iteratedDerivWithin_eq_zero_of_weighted_zero_data
    (I : Set ℝ) (hI : Set.OrdConnected I) {ι : Type v} [Fintype ι]
    (m : ι → ℕ) (x : ι → ℝ) (hxI : ∀ i, x i ∈ I)
    {g : ℝ → ℝ} {x0 : ℝ} {r : ℕ}
    (hIu : UniqueDiffOn ℝ I)
    (Z : WeightedZeroData I x (x0 := x0) g r) (hx0 : x0 ∈ I)
    (hg : ContDiffOn ℝ r g I) :
    ∃ ξ ∈ convexHull ℝ (insert x0 (Set.range x)),
      iteratedDerivWithin r g I ξ = 0 := by
  induction r generalizing g with
  | zero =>
      -- In the base case, any support point is already a zero of the function itself.
      have hsupport_ne : Z.support.card ≠ 0 := by
        have hsum_pos : 0 < ∑ a : Z.support, Z.weight a := by
          rw [Z.weight_sum]
          decide
        intro h0
        have hsubempty : IsEmpty Z.support := by
          refine ⟨fun a ↦ ?_⟩
          have : (a : ℝ) ∈ (∅ : Finset ℝ) := by
            simpa [Finset.card_eq_zero.mp h0] using a.2
          simpa using this
        letI := hsubempty
        have hsum_zero : (∑ a : Z.support, Z.weight a) = 0 := by simp
        have : 0 < (0 : ℕ) := by simpa [hsum_zero] using hsum_pos
        exact Nat.lt_asymm this this
      rcases Finset.card_ne_zero.mp hsupport_ne with ⟨a, ha⟩
      refine ⟨a, Z.support_subset ha, ?_⟩
      let a' : Z.support := ⟨a, ha⟩
      have hpos : 0 < Z.weight a' := Z.weight_pos a'
      simpa [a'] using Z.jet_zero a' ⟨0, hpos⟩
  | succ r ihr =>
      -- Route correction: instead of redesigning the zero-chain invariant again, lower the
      -- multiplicity in one step and recurse on the same `WeightedZeroData` structure.
      have hg1 : ContDiffOn ℝ 1 g I := hg.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
      obtain ⟨Z'⟩ := weighted_zero_data_step I hI x hxI Z hx0 hg1
      have hderiv : ContDiffOn ℝ r (iteratedDerivWithin 1 g I) I := by
        rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hIu]
        constructor
        · intro k hk
          have hcont :=
            hg.continuousOn_iteratedDerivWithin
              (m := k + 1) (by exact_mod_cast Nat.succ_le_succ hk) hIu
          convert hcont using 1
          ext y
          simp [iteratedDerivWithin_one, iteratedDerivWithin_succ']
        · intro k hk
          have hdiff :=
            hg.differentiableOn_iteratedDerivWithin
              (m := k + 1) (by exact_mod_cast Nat.succ_lt_succ hk) hIu
          convert hdiff using 1
          ext y
          simp [iteratedDerivWithin_one, iteratedDerivWithin_succ']
      obtain ⟨ξ, hξhull, hξzero⟩ :=
        ihr Z' hderiv
      refine ⟨ξ, hξhull, ?_⟩
      simpa [iteratedDerivWithin_one, iteratedDerivWithin_succ'] using hξzero

/-- Helper for Exercise 1.3.47: a function on an interval with one distinguished zero and zero
jets of order `< m i` at the interpolation nodes has an `N`th iterated derivative zero somewhere
in the convex hull of those points, where `N = ∑ i, m i`. -/
lemma exists_iteratedDerivWithin_eq_zero_of_zero_jets
    (I : Set ℝ) (hI : Set.OrdConnected I) (hIu : UniqueDiffOn ℝ I) {ι : Type v} [Fintype ι]
    (m : ι → ℕ) (x : ι → ℝ) (hx : Function.Injective x) (hxI : ∀ i, x i ∈ I)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ (∑ i, m i) g I) {x0 : ℝ} (hx0 : x0 ∈ I)
    (hx0_pos : ∀ i, 0 < m i → x0 ≠ x i)
    (hg0 : g x0 = 0)
    (hgjets : ∀ i, ∀ k : Fin (m i), iteratedDerivWithin k.1 g I (x i) = 0) :
    ∃ ξ ∈ convexHull ℝ (insert x0 (Set.range x)),
      iteratedDerivWithin (∑ i, m i) g I ξ = 0 := by
  -- Route correction: the initial chain is now packaged directly as an ordered support subtype,
  -- so the only remaining blocker is the repeated-Rolle induction on `WeightedZeroData`.
  let _ := hIu
  obtain ⟨Z⟩ :
      Nonempty (WeightedZeroData I x (x0 := x0) g (∑ i, m i)) :=
    exists_initial_ordered_zero_chain I m x hx hx0_pos hg0 hgjets
  exact
    exists_iteratedDerivWithin_eq_zero_of_weighted_zero_data
      I hI m x hxI hIu Z hx0 (by simpa using hg)

-- Proof sketch: subtract the Hermite interpolation polynomial from `f`, so the difference has
-- zeros of multiplicity `m i` at each node; apply repeated Rolle's theorem on the minimal
-- interval generated by `x0` and the interpolation nodes, then identify the final derivative with
-- the Hermite remainder term.
/-- Exercise 1.3.47 (7): for a `C^n` real function on an interval, the Hermite interpolation
error equals the `n`-th derivative at a point in the convex hull of `x₀` and the interpolation
nodes times the usual product remainder factor. -/
theorem exists_eq_iteratedDerivWithin_mul_prod_sub_of_hermite_interpolation
    (I : Set ℝ) (hI : Set.OrdConnected I) (f : ℝ → ℝ) {ι : Type v} [Fintype ι] (m : ι → ℕ)
    (hf : ContDiffOn ℝ (∑ i, m i) f I) (x : ι → ℝ)
    (hx : Function.Injective x) (hxI : ∀ i, x i ∈ I) (P : ℝ[X])
    (hP : P.degree < ∑ i, m i ∧
      ∀ i, ∀ k : Fin (m i),
        ((derivative^[k.1]) P).eval (x i) = iteratedDerivWithin k.1 f I (x i))
    {x0 : ℝ} (hx0 : x0 ∈ I) :
    ∃ ξ ∈ convexHull ℝ (insert x0 (Set.range x)),
      f x0 - P.eval x0 =
        iteratedDerivWithin (∑ i, m i) f I ξ / ((∑ i, m i).factorial : ℝ) *
          ∏ i, (x0 - x i) ^ m i :=
    by
  classical
  let N : ℕ := ∑ i, m i
  by_cases hN : N = 0
  · have hm_zero : ∀ i, m i = 0 := by
      intro i
      apply Nat.eq_zero_of_le_zero
      calc
        m i ≤ N := by
          dsimp [N]
          exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j)) (by simp)
        _ = 0 := hN
    have hP0 : P = 0 := by
      -- If the total jet order is zero, the degree bound forces the interpolation polynomial to be
      -- the zero polynomial.
      simpa [N, hN] using hP.1
    refine ⟨x0, subset_convexHull ℝ _ (by simp), ?_⟩
    -- With no interpolation constraints, the formula collapses to the order-zero identity.
    simp [hP0, hm_zero]
  · by_cases hx0node : ∃ i, m i ≠ 0 ∧ x0 = x i
    · rcases hx0node with ⟨i, hm_i, hx0i⟩
      refine ⟨x0, subset_convexHull ℝ _ (by simp), ?_⟩
      have hval : P.eval (x i) = f (x i) := by
        -- The zeroth Hermite jet already matches the value of `f` at a positive-multiplicity node.
        simpa using hP.2 i ⟨0, Nat.pos_of_ne_zero hm_i⟩
      have hleft : f x0 - P.eval x0 = 0 := by
        -- Hence the interpolation error vanishes at `x0` when `x0` is itself a node.
        calc
          f x0 - P.eval x0 = f (x i) - P.eval (x i) := by simp [hx0i]
          _ = 0 := by simp [hval]
      have hprod0 : ∏ j, (x0 - x j) ^ m j = 0 := by
        -- The remainder factor also vanishes because one linear factor is zero with positive power.
        simpa using
          (Finset.prod_eq_zero (s := (Finset.univ : Finset ι)) (i := i) (by simp)
            (by simp [hx0i, hm_i]))
      rw [hleft, hprod0]
      simp
    · let W : ℝ[X] := ∏ i, ((X - C (x i)) ^ m i : ℝ[X])
      have hWmonic : W.Monic := by
        -- The Hermite remainder polynomial is monic because each factor is monic.
        dsimp [W]
        refine Polynomial.monic_prod_of_monic (Finset.univ : Finset ι)
          (fun i ↦ ((X - C (x i)) ^ m i : ℝ[X])) ?_
        intro i hi
        exact (Polynomial.monic_X_sub_C (x i)).pow (m i)
      have hWdeg : W.natDegree = N := by
        -- Its degree is exactly the total multiplicity.
        dsimp [W, N]
        rw [Polynomial.natDegree_prod_of_monic]
        · simp
        · intro i hi
          exact (Polynomial.monic_X_sub_C (x i)).pow (m i)
      have hWtop :
          (Polynomial.derivative^[N]) W = C ((N.factorial : ℕ) : ℝ) := by
        -- This isolates the algebraic top-derivative calculation needed in the endgame.
        exact iterate_derivative_monic_natDegree_eq_factorial W N hWmonic hWdeg
      have hW0_ne : W.eval x0 ≠ 0 := by
        -- Since `x0` is not a positive-multiplicity node, none of the relevant factors vanish.
        dsimp [W]
        simp_rw [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        exact Finset.prod_ne_zero_iff.2 <| fun i hi ↦ by
          by_cases hm : m i = 0
          · simp [hm]
          · exact pow_ne_zero _ <| sub_ne_zero.mpr <| by
              intro hx0i
              exact hx0node ⟨i, hm, hx0i⟩
      let c : ℝ := (f x0 - P.eval x0) / W.eval x0
      let g : ℝ → ℝ := fun t ↦ f t - P.eval t - c * W.eval t
      have hcW : c * W.eval x0 = f x0 - P.eval x0 := by
        -- Clearing the nonzero denominator recovers the chosen normalization constant.
        dsimp [c]
        field_simp [hW0_ne]
      have hg0 : g x0 = 0 := by
        -- The normalization of `c` forces the auxiliary function to vanish at `x0`.
        dsimp [g]
        rw [hcW]
        ring
      have hm_pos : ∃ i, m i ≠ 0 := by
        by_contra hnone
        have hm_zero : ∀ i, m i = 0 := by
          intro i
          by_contra hm
          exact hnone ⟨i, hm⟩
        apply hN
        dsimp [N]
        simp [hm_zero]
      have hIu : UniqueDiffOn ℝ I := by
        obtain ⟨i, hm_i⟩ := hm_pos
        have hx0_ne : x0 ≠ x i := by
          intro hx0i
          exact hx0node ⟨i, hm_i, hx0i⟩
        have hinterior : (interior I).Nonempty := by
          refine ⟨(x0 + x i) / 2, ?_⟩
          refine mem_interior_iff_mem_nhds.2 ?_
          rcases lt_or_gt_of_ne hx0_ne with hlt | hgt
          · have hmid : (x0 + x i) / 2 ∈ Set.Ioo x0 (x i) := by
              constructor <;> nlinarith
            exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmid) <| fun y hy ↦
              hI.out hx0 (hxI i) (Set.Ioo_subset_Icc_self hy)
          · have hmid : (x0 + x i) / 2 ∈ Set.Ioo (x i) x0 := by
              constructor <;> nlinarith
            exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmid) <| fun y hy ↦
              hI.out (hxI i) hx0 (Set.Ioo_subset_Icc_self hy)
        -- A nontrivial interval in `ℝ` has unique tangents everywhere.
        exact uniqueDiffOn_convex hI.convex hinterior
      have hWjets :
          ∀ i, ∀ k : Fin (m i), iteratedDerivWithin k.1 (fun t ↦ W.eval t) I (x i) = 0 := by
        intro i k
        -- The Hermite product contributes the required vanishing multiplicity at each node.
        simpa [W] using
          iteratedDerivWithin_eval_prod_X_sub_C_pow_eq_zero_of_lt_multiplicity
            I hIu m x hxI i k
      have hgjets :
          g x0 = 0 ∧ ∀ i, ∀ k : Fin (m i), iteratedDerivWithin k.1 g I (x i) = 0 := by
        -- Package the zero-jet data for the auxiliary error function before the repeated-Rolle step.
        exact auxiliary_hermite_error_zero_jets
          I hIu f m hf x hxI P W hP.2 hWjets c g rfl hg0
      have hPcontOn : ContDiffOn ℝ (∑ i, m i) (fun t ↦ P.eval t) I := by
        simpa [N] using (Polynomial.contDiff_aeval P (N : WithTop ℕ∞)).contDiffOn
      have hWevalcontOn : ContDiffOn ℝ (∑ i, m i) (fun t ↦ W.eval t) I := by
        simpa [N] using (Polynomial.contDiff_aeval W (N : WithTop ℕ∞)).contDiffOn
      have hWcontOn : ContDiffOn ℝ (∑ i, m i) (fun t ↦ c * W.eval t) I := by
        exact contDiffOn_const.mul hWevalcontOn
      have hgcont : ContDiffOn ℝ (∑ i, m i) g I := by
        -- The auxiliary error inherits the ambient `C^N` regularity from `f` and the polynomial
        -- correction terms.
        rw [show g = fun t ↦ f t - P.eval t - c * W.eval t by rfl]
        exact (hf.sub hPcontOn).sub hWcontOn
      obtain ⟨ξ, hξhull, hξzero⟩ :=
        exists_iteratedDerivWithin_eq_zero_of_zero_jets
          I hI hIu m x hx hxI hgcont hx0
          (fun i hi hx0i ↦ hx0node ⟨i, Nat.ne_of_gt hi, hx0i⟩) hgjets.1 hgjets.2
      have hHullSubset : convexHull ℝ (insert x0 (Set.range x)) ⊆ I := by
        -- The convex hull stays inside the original interval because `I` is convex.
        apply convexHull_min
        · intro y hy
          rcases hy with rfl | hy
          · exact hx0
          · rcases hy with ⟨i, rfl⟩
            exact hxI i
        · exact hI.convex
      have hξI : ξ ∈ I := hHullSubset hξhull
      have haux :
          iteratedDerivWithin N g I ξ =
            iteratedDerivWithin N f I ξ - c * (N.factorial : ℝ) := by
        -- The polynomial part vanishes after `N` derivatives, and `W` contributes exactly `N!`.
        simpa [g, N] using
          iteratedDerivWithin_auxiliary_error_eq
            I hIu f P W N (by simpa [N] using hf) (by simpa [N] using hP.1) hWtop c hξI
      have hzeroeq : iteratedDerivWithin N f I ξ = c * (N.factorial : ℝ) := by
        -- The repeated-Rolle zero converts the auxiliary identity into the target derivative value.
        rw [haux] at hξzero
        linarith
      have hfac_ne : ((N.factorial : ℝ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero N
      have hc : c = iteratedDerivWithin N f I ξ / (N.factorial : ℝ) := by
        -- Solve the scalar normalization from the `N`th-derivative identity.
        apply (eq_div_iff hfac_ne).2
        simpa [mul_comm] using hzeroeq.symm
      have hWeval :
          W.eval x0 = ∏ i, (x0 - x i) ^ m i := by
        -- Evaluating the Hermite product at `x0` gives the standard remainder factor.
        dsimp [W]
        simp [Polynomial.eval_prod, Polynomial.eval_pow]
      refine ⟨ξ, hξhull, ?_⟩
      calc
        f x0 - P.eval x0 = c * W.eval x0 := hcW.symm
        _ = (iteratedDerivWithin N f I ξ / (N.factorial : ℝ)) * W.eval x0 := by rw [hc]
        _ = iteratedDerivWithin N f I ξ / (N.factorial : ℝ) * ∏ i, (x0 - x i) ^ m i := by
          rw [hWeval]
