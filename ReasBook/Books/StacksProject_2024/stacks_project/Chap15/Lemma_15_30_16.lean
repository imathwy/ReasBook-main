import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Regular.Basic
import StacksProject_2024.stacks_project.Chap10.Lemma_10_24_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial
open scoped BigOperators nonZeroDivisors

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Domain triage:
- primary domain: regular elements in multivariable polynomial rings, with the coefficient
  hypothesis organized by the Chapter 10 localization-family owner;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `away_localization_family_map_injective_iff_smul_family_map_injective`,
  `koszulLinearForm`,
  `regular_permutations_subsequences_polynomial_tfae`,
  `IsRegular`;
- best owner abstraction: the canonical injectivity hypothesis is the Chapter 10 owner
  `awayLocalizationFamilyMap R a`; the textbook tuple-multiplication map is only a bridge/view via
  the equivalence theorem from `Lemma_10_24_4`, while the Chapter 15 tuple owner
  `koszulLinearForm` stays auxiliary because this item is about the source-facing polynomial linear
  form itself rather than the Koszul complex owner;
- primitive data: a finite coefficient family `a : Fin n → R`;
- derived API: the regularity of the linear form `∑ i, C (a i) * X i`.

Layering:
- `source-facing`: the regularity of the linear form `∑ i, C (a i) * X i`;
- `core/canonical`: the owner map `awayLocalizationFamilyMap R a`;
- `bridge/view`: `away_localization_family_map_injective_iff_smul_family_map_injective`.
-/

/-- Helper for Lemma 15.30.16: the Chapter 10 localization criterion converts the source-facing
injectivity hypothesis into injectivity of the coordinatewise scalar-multiplication map on `R`. -/
private theorem smul_family_map_injective_of_injective_awayLocalizationFamilyMap
    (a : Fin n → R) (h : Function.Injective (awayLocalizationFamilyMap R a)) :
    Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R R (a i)) := by
  -- Use the earlier equivalence specialized to the ambient module `R`.
  exact (away_localization_family_map_injective_iff_smul_family_map_injective R a).mp h

/-- Helper for Lemma 15.30.16: the coefficient of the linear form `∑ i, a_i t_i` at the monomial
`t_j` is `a_j`. -/
private theorem coeff_linearForm_single (a : Fin n → R) (j : Fin n) :
    ((∑ i, C (a i) * X i : MvPolynomial (Fin n) R)).coeff (Finsupp.single j 1) = a j := by
  -- Rewrite each summand as a monomial and read off the unique degree-one contribution.
  classical
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single j]
  · simp [MvPolynomial.C_mul_X_eq_monomial]
  · intro b _ hbj
    simp [MvPolynomial.C_mul_X_eq_monomial]
    intro hdeg
    have hcoeff := congrArg (fun s : Fin n →₀ ℕ => s b) hdeg
    simp [hbj] at hcoeff
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Helper for Lemma 15.30.16: a scalar annihilator of the linear form annihilates every
coefficient `a_i`. -/
private theorem constant_annihilator_kills_all_coefficients_of_linearForm
    (a : Fin n → R) {r : R}
    (hr :
      C r * (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) = 0) :
    ∀ i, r * a i = 0 := by
  intro i
  -- Compare the coefficient of the monomial `t_i` on both sides.
  have hcoeff :=
    congrArg
      (fun p : MvPolynomial (Fin n) R ↦ p.coeff (Finsupp.single i 1))
      hr
  simpa [coeff_linearForm_single] using hcoeff

/-- Helper for Lemma 15.30.16: under `MvPolynomial.finSuccEquiv`, the linear form in `n + 1`
variables becomes a degree-one polynomial whose constant term is the tail linear form and whose
linear coefficient is the head scalar. -/
private theorem finSuccEquiv_linearForm (a : Fin (n + 1) → R) :
    MvPolynomial.finSuccEquiv R n
      (∑ i, C (a i) * X i : MvPolynomial (Fin (n + 1)) R) =
        Polynomial.C (∑ j, C (a j.succ) * X j : MvPolynomial (Fin n) R) +
          Polynomial.C (C (a 0)) * Polynomial.X := by
  -- Split the transported sum into its head variable and its tail linear form.
  simp [MvPolynomial.finSuccEquiv_apply, Fin.sum_univ_succ, add_comm]

/-- Helper for Lemma 15.30.16: a constant-polynomial annihilator of the transported linear form
annihilates both the tail linear form and the head coefficient. -/
private theorem constant_polynomial_mul_finSucc_linearForm_eq_zero
    (a : Fin (n + 1) → R) (b : MvPolynomial (Fin n) R)
    (h :
      Polynomial.C b * MvPolynomial.finSuccEquiv R n
        (∑ i, C (a i) * X i : MvPolynomial (Fin (n + 1)) R) = 0) :
    b * (∑ j, C (a j.succ) * X j : MvPolynomial (Fin n) R) = 0 ∧
      b * C (a 0) = 0 := by
  -- After rewriting the transported linear form, coefficients `0` and `1` encode the two needed
  -- annihilation relations.
  rw [finSuccEquiv_linearForm] at h
  constructor
  · have h0 := congrArg (fun p : Polynomial (MvPolynomial (Fin n) R) ↦ p.coeff 0) h
    simpa [Polynomial.coeff_C_mul] using h0
  · have h1 := congrArg (fun p : Polynomial (MvPolynomial (Fin n) R) ↦ p.coeff 1) h
    simpa [Polynomial.coeff_C_mul] using h1

/-- Helper for Lemma 15.30.16: if a scalar annihilates every coefficient `a_i`, then its constant
polynomial annihilates the entire linear form. -/
private theorem constant_annihilator_of_linearForm_of_kills_coefficients
    (a : Fin n → R) {r : R} (hr : ∀ i, r * a i = 0) :
    C r * (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) = 0 := by
  -- Multiply termwise through the sum and collapse each summand using the coefficientwise
  -- annihilation hypothesis.
  calc
    C r * (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) =
        ∑ i, C r * (C (a i) * X i) := by
          rw [Finset.mul_sum]
    _ = ∑ i, C (r * a i) * X i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [mul_assoc]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          simp [hr i]

/-- Helper for Lemma 15.30.16: specializing each variable `X i` to `X^(w i)` sends the linear
form to the corresponding sparse one-variable polynomial. -/
private theorem weighted_eval_linearForm_eq_sparse_sum
    (a : Fin n → R) (w : Fin n → ℕ) :
    MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ Polynomial.X ^ (w i))
      (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) =
        ∑ i, Polynomial.C (a i) * Polynomial.X ^ (w i) := by
  -- Specialization respects the finite sum and evaluates each summand termwise.
  simp

/-- Helper for Lemma 15.30.16: any annihilation relation for the multivariable linear form
remains an annihilation relation after the weighted specialization to `Polynomial R`. -/
private theorem weighted_eval_mul_linearForm_eq_zero
    (a : Fin n → R) (w : Fin n → ℕ) {q : MvPolynomial (Fin n) R}
    (hq :
      q * (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) = 0) :
    MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ Polynomial.X ^ (w i)) q *
      (∑ i, Polynomial.C (a i) * Polynomial.X ^ (w i)) = 0 := by
  -- Apply the specialization hom to the product equation and rewrite the image of the linear form.
  simpa [weighted_eval_linearForm_eq_sparse_sum, map_mul] using
    congrArg (MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ Polynomial.X ^ (w i))) hq

/-- Helper for Lemma 15.30.16: a degree-one polynomial annihilator can be replaced by a nonzero
scalar from the coefficient ring that kills both coefficients. -/
private theorem Polynomial.exists_nonzero_scalar_annihilator_of_mul_C_add_C_mul_X_eq_zero
    {A : Type u} [CommRing A] (u v : A) {Q : Polynomial A} (hQ : Q ≠ 0)
    (hMul : Q * (Polynomial.C u + Polynomial.C v * Polynomial.X) = 0) :
    ∃ b : A, b ≠ 0 ∧ b * u = 0 ∧ b * v = 0 := by
  -- Interpret the degree-one factor as a zerodivisor, then use the polynomial McCoy bridge and
  -- read coefficients `0` and `1` of the resulting scalar-annihilation equation.
  have hzero : Polynomial.C u + Polynomial.C v * Polynomial.X ∉ nonZeroDivisors (Polynomial A) := by
    rw [notMem_nonZeroDivisors_iff_right]
    exact ⟨Q, hMul, hQ⟩
  rcases (Polynomial.notMem_nonZeroDivisors_iff.mp hzero) with ⟨b, hb0, hbMul⟩
  refine ⟨b, hb0, ?_, ?_⟩
  · have hcoeff := congrArg (fun p : Polynomial A ↦ p.coeff 0) hbMul
    simpa [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul] using hcoeff
  · have hcoeff := congrArg (fun p : Polynomial A ↦ p.coeff 1) hbMul
    simpa [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X] using hcoeff

/-- Helper for Lemma 15.30.16: if a nonzero multivariable polynomial annihilates a constant
polynomial `C z`, then some nonzero coefficient of that polynomial annihilates `z`. -/
private theorem exists_nonzero_scalar_annihilator_of_constant_from_mul_eq_zero
    {σ : Type*} [DecidableEq σ] {z : R} {q : MvPolynomial σ R} (hq : q ≠ 0)
    (hz : q * C z = 0) :
    ∃ c : R, c ≠ 0 ∧ c * z = 0 := by
  classical
  -- Pick a nonzero coefficient of `q` from its support and read the same coefficient from
  -- `q * C z = 0`.
  have hsupport : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hq
  rcases hsupport with ⟨d, hd⟩
  refine ⟨q.coeff d, MvPolynomial.mem_support_iff.mp hd, ?_⟩
  have hz' : C z * q = 0 := by
    simpa [mul_comm] using hz
  have hcoeff : (C z * q).coeff d = 0 := by
    simpa using congrArg (fun p : MvPolynomial σ R ↦ p.coeff d) hz'
  have hzcoeff : z * q.coeff d = 0 := by
    simpa [MvPolynomial.coeff_C_mul] using hcoeff
  simpa [mul_comm] using hzcoeff

/-- Helper for Lemma 15.30.16: one nonzero coefficient of `q` simultaneously kills every
constant in a finite family once `q` annihilates each corresponding constant polynomial. -/
private theorem exists_nonzero_scalar_annihilator_of_constants_from_mul_eq_zero_family
    {σ : Type*} [DecidableEq σ] {k : ℕ} (zs : Fin k → R) {q : MvPolynomial σ R} (hq : q ≠ 0)
    (hz : ∀ j, q * C (zs j) = 0) :
    ∃ c : R, c ≠ 0 ∧ ∀ j, c * zs j = 0 := by
  classical
  -- Pick one nonzero coefficient of `q` and read the same coefficient from every product
  -- equation `q * C (zs j) = 0`.
  have hsupport : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hq
  rcases hsupport with ⟨d, hd⟩
  refine ⟨q.coeff d, MvPolynomial.mem_support_iff.mp hd, ?_⟩
  intro j
  have hz' : C (zs j) * q = 0 := by
    simpa [mul_comm] using hz j
  have hcoeff : (C (zs j) * q).coeff d = 0 := by
    simpa using congrArg (fun p : MvPolynomial σ R ↦ p.coeff d) hz'
  have hzcoeff : zs j * q.coeff d = 0 := by
    simpa [MvPolynomial.coeff_C_mul] using hcoeff
  simpa [mul_comm] using hzcoeff

/-- Helper for Lemma 15.30.16: `MvPolynomial.finSuccEquiv` sends constant multivariable
polynomials to constant one-variable polynomials with the same coefficient. -/
private theorem finSuccEquiv_C {m : ℕ} (z : R) :
    MvPolynomial.finSuccEquiv R m (C z : MvPolynomial (Fin (m + 1)) R) =
      Polynomial.C (C z) := by
  -- The fin-splitting equivalence preserves coefficients and sends every variable-free term to a
  -- constant polynomial.
  simp [MvPolynomial.finSuccEquiv_apply]

/-- Helper for Lemma 15.30.16: a scalar annihilates the degree-one polynomial `C u + C v * X`
exactly when it annihilates both coefficients `u` and `v`. -/
private theorem Polynomial.smul_C_add_C_mul_X_eq_zero_iff
    {A : Type u} [CommRing A] (r u v : A) :
    r • (Polynomial.C u + Polynomial.C v * Polynomial.X) = 0 ↔ r * u = 0 ∧ r * v = 0 := by
  constructor
  · intro h
    constructor
    · -- Read the constant coefficient of the scalar-annihilation relation.
      have h0 := congrArg (fun p : Polynomial A ↦ p.coeff 0) h
      simpa [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul] using h0
    · -- Read the linear coefficient of the scalar-annihilation relation.
      have h1 := congrArg (fun p : Polynomial A ↦ p.coeff 1) h
      simpa [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul_X] using h1
  · rintro ⟨hu, hv⟩
    -- Coefficients above degree `1` vanish automatically, so coefficients `0` and `1` suffice.
    ext n
    cases n with
    | zero =>
        simpa [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul] using hu
    | succ n =>
        cases n with
        | zero =>
            simpa [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_C_mul_X] using hv
        | succ n =>
            simp [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul,
              Polynomial.coeff_C_mul_X]

/-- Helper for Lemma 15.30.16: a constant factor killed by `Q` is also killed by the leading
coefficient of `Q`. -/
private theorem Polynomial.leadingCoeff_mul_eq_zero_of_mul_C_eq_zero
    {A : Type u} [CommRing A] {Q : Polynomial A} {z : A}
    (h : Q * Polynomial.C z = 0) :
    Q.leadingCoeff * z = 0 := by
  -- Read the coefficient at `Q.natDegree`, where multiplication by a constant preserves degrees.
  have hcoeff := congrArg (fun p : Polynomial A ↦ p.coeff Q.natDegree) h
  simpa [Polynomial.coeff_natDegree, Polynomial.coeff_mul_C] using hcoeff

/-- Helper for Lemma 15.30.16: the one-variable McCoy cancellation argument can carry along a
finite family of constant equations `Q * C (zs j) = 0`. -/
private theorem Polynomial.eq_zero_of_mul_eq_zero_of_smul_with_constants
    {A : Type u} [CommRing A] {k : ℕ} (P : Polynomial A) (zs : Fin k → A)
    (hP : ∀ r : A, r • P = 0 → (∀ j, r * zs j = 0) → r = 0) (Q : Polynomial A)
    (hMul : P * Q = 0) (hConst : ∀ j, Q * Polynomial.C (zs j) = 0) :
    Q = 0 := by
  suffices hCoeff : ∀ i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    -- Apply the scalar criterion to the leading coefficient of `Q`.
    apply hP
    · simpa [ext_iff, mul_comm Q.leadingCoeff] using
        fun i ↦ congrArg (fun p : Polynomial A ↦ p.coeff Q.natDegree) (hCoeff i)
    · intro j
      exact Polynomial.leadingCoeff_mul_eq_zero_of_mul_C_eq_zero (hConst j)
  -- Follow mathlib's strong decreasing induction and thread the constant equations recursively.
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi, zero_smul]
  intro l IH
  obtain hlt | hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · -- The recursive branch keeps the same source polynomial `P` and rescales the annihilator `Q`.
    apply Polynomial.eq_zero_of_mul_eq_zero_of_smul_with_constants P zs hP (P.coeff l • Q)
    · calc
        P * (P.coeff l • Q) = Polynomial.C (P.coeff l) * (P * Q) := by
          simp [Polynomial.smul_eq_C_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = 0 := by simp [hMul]
    · intro j
      calc
        (P.coeff l • Q) * Polynomial.C (zs j) =
            Polynomial.C (P.coeff l) * (Q * Polynomial.C (zs j)) := by
              simp [Polynomial.smul_eq_C_mul, mul_assoc, mul_left_comm, mul_comm]
        _ = 0 := by simp [hConst j]
  · suffices P.coeff l * Q.leadingCoeff = 0 by
      rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
    let m := Q.natDegree
    suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by
      rw [← this, hMul, coeff_zero]
    rw [coeff_mul]
    apply Finset.sum_eq_single (l, m) _ (by simp)
    simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
    intro i j hij hneq
    obtain hi | rfl | hi := lt_trichotomy i l
    · have him : i + m < l + m := Nat.add_lt_add_right hi m
      have hij' : i + m < i + j := by simpa [hij] using him
      have hj : m < j := Nat.add_lt_add_iff_left.mp hij'
      rw [coeff_eq_zero_of_natDegree_lt hj, mul_zero]
    · exfalso
      exact hneq rfl (Nat.add_left_cancel hij)
    · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q.natDegree

/-- Helper for Lemma 15.30.16: the degree-one McCoy step with extra constant equations should
produce one common nonzero coefficient-ring scalar killing both coefficients and every carried
constant. -/
private theorem Polynomial.exists_nonzero_scalar_annihilator_of_mul_C_add_C_mul_X_eq_zero_with_constants
    {A : Type u} [CommRing A] {k : ℕ} (u v : A) (zs : Fin k → A) {Q : Polynomial A} (hQ : Q ≠ 0)
    (hMul : Q * (Polynomial.C u + Polynomial.C v * Polynomial.X) = 0)
    (hConst : ∀ j, Q * Polynomial.C (zs j) = 0) :
    ∃ b : A, b ≠ 0 ∧ b * u = 0 ∧ b * v = 0 ∧ ∀ j, b * zs j = 0 := by
  -- Route correction: the old one-scalar invariant lost the previously carried constants at the
  -- successor step. The intended replacement is the McCoy proof with the extra equations
  -- `Q * C (zs j) = 0` threaded through the same induction on `Q.natDegree`.
  by_contra hNoScalar
  have hScalarCriterion :
      ∀ r : A, r • (Polynomial.C u + Polynomial.C v * Polynomial.X) = 0 →
        (∀ j, r * zs j = 0) → r = 0 := by
    intro r hr hzs
    have hruv := (Polynomial.smul_C_add_C_mul_X_eq_zero_iff r u v).mp hr
    -- Any nonzero scalar satisfying these equations would contradict the negated conclusion.
    by_contra hr0
    exact hNoScalar ⟨r, hr0, hruv.1, hruv.2, hzs⟩
  have hMul' : (Polynomial.C u + Polynomial.C v * Polynomial.X) * Q = 0 := by
    -- Commute the given annihilation relation into the orientation expected by the McCoy helper.
    simpa only [mul_comm] using hMul
  have hQzero :
      Q = 0 :=
    Polynomial.eq_zero_of_mul_eq_zero_of_smul_with_constants
      (P := Polynomial.C u + Polynomial.C v * Polynomial.X) (zs := zs)
      hScalarCriterion Q hMul' hConst
  exact hQ hQzero

/-- Helper for Lemma 15.30.16: strengthen the source-faithful induction by carrying a finite
family of auxiliary constants through `MvPolynomial.finSuccEquiv`. -/
private theorem exists_constant_annihilator_of_linearForm_with_aux_constants :
    ∀ {m k : ℕ} (a : Fin m → R) (zs : Fin k → R) {q : MvPolynomial (Fin m) R},
      q ≠ 0 →
      q * (∑ i, C (a i) * X i : MvPolynomial (Fin m) R) = 0 →
      (∀ j, q * C (zs j) = 0) →
      ∃ r : R, r ≠ 0 ∧
        C r * (∑ i, C (a i) * X i : MvPolynomial (Fin m) R) = 0 ∧
          ∀ j, r * zs j = 0
  | 0, k, a, zs, q, hq, hlin, hConst => by
      -- In zero variables the linear form is zero, so one nonzero coefficient of `q` already
      -- yields the common scalar annihilator for the auxiliary constants.
      obtain ⟨r, hr0, hrzs⟩ :=
        exists_nonzero_scalar_annihilator_of_constants_from_mul_eq_zero_family zs hq hConst
      refine ⟨r, hr0, ?_, hrzs⟩
      simp
  | m + 1, k, a, zs, q, hq, hlin, hConst => by
      -- Rewrite the relation through `MvPolynomial.finSuccEquiv`, use the degree-one McCoy step
      -- in the head variable, and recurse on the tail while carrying both the old constants and
      -- the new head coefficient.
      let Q : Polynomial (MvPolynomial (Fin m) R) := MvPolynomial.finSuccEquiv R m q
      have hQ : Q ≠ 0 := by
        intro hQ0
        apply hq
        exact (MvPolynomial.finSuccEquiv R m).injective hQ0
      have hlinQ :
          Q *
              (Polynomial.C (∑ j, C (a (Fin.succ j)) * X j : MvPolynomial (Fin m) R) +
                Polynomial.C (C (a 0)) * Polynomial.X) = 0 := by
        -- Transport the annihilation relation to the one-variable polynomial side.
        have hmap :
            Q *
                MvPolynomial.finSuccEquiv R m
                  (∑ i, C (a i) * X i : MvPolynomial (Fin (m + 1)) R) = 0 := by
          simpa [Q, map_mul] using congrArg (MvPolynomial.finSuccEquiv R m) hlin
        rw [finSuccEquiv_linearForm] at hmap
        exact hmap
      have hConstQ : ∀ j, Q * Polynomial.C (C (zs j)) = 0 := by
        intro j
        -- The transported annihilator polynomial still kills each carried constant.
        have hmap :
            Q * MvPolynomial.finSuccEquiv R m
                (C (zs j) : MvPolynomial (Fin (m + 1)) R) = 0 := by
          simpa [Q, map_mul] using congrArg (MvPolynomial.finSuccEquiv R m) (hConst j)
        simpa [finSuccEquiv_C] using hmap
      obtain ⟨b, hb0, hbTail, hbHead, hbzs⟩ :=
        Polynomial.exists_nonzero_scalar_annihilator_of_mul_C_add_C_mul_X_eq_zero_with_constants
          (u := (∑ j, C (a (Fin.succ j)) * X j : MvPolynomial (Fin m) R))
          (v := C (a 0)) (zs := fun j ↦ C (zs j)) hQ hlinQ hConstQ
      let zs' : Fin (k + 1) → R := Fin.snoc zs (a 0)
      have hbSnoc : ∀ j : Fin (k + 1), b * C (zs' j) = 0 := by
        intro j
        refine Fin.lastCases ?_ ?_ j
        · simpa [zs'] using hbHead
        · intro j
          simpa [zs'] using hbzs j
      obtain ⟨r, hr0, hrTail, hrSnoc⟩ :=
        exists_constant_annihilator_of_linearForm_with_aux_constants
          (a := fun j ↦ a (Fin.succ j)) (zs := zs')
          (q := b) hb0 hbTail hbSnoc
      have hrHead : r * a 0 = 0 := by
        simpa [zs'] using hrSnoc (Fin.last k)
      have hrTailCoeff : ∀ j : Fin m, r * a j.succ = 0 :=
        constant_annihilator_kills_all_coefficients_of_linearForm (a := fun j ↦ a j.succ) hrTail
      refine ⟨r, hr0, ?_, ?_⟩
      · -- Reassemble the coefficientwise annihilation into the full linear-form equation.
        apply constant_annihilator_of_linearForm_of_kills_coefficients
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hrHead
        · intro j
          simpa using hrTailCoeff j
      · intro j
        simpa [zs'] using hrSnoc j.castSucc

/-- Helper for Lemma 15.30.16: if the linear form is a zerodivisor, then a nonzero scalar from the
base ring annihilates it. -/
private theorem exists_constant_annihilator_of_zero_divisor_linearForm
    (a : Fin n → R)
    (hzero :
      (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) ∉
        nonZeroDivisors (MvPolynomial (Fin n) R)) :
    ∃ r : R, r ≠ 0 ∧
      C r * (∑ i, C (a i) * X i : MvPolynomial (Fin n) R) = 0 := by
  -- Convert the zerodivisor hypothesis into a nonzero annihilator polynomial and then invoke the
  -- strengthened finite-family induction with no auxiliary constants.
  rcases (notMem_nonZeroDivisors_iff_right.mp hzero) with ⟨q, hqMul, hq0⟩
  obtain ⟨r, hr0, hrLin, _⟩ :=
    exists_constant_annihilator_of_linearForm_with_aux_constants
      (a := a) (zs := Fin.elim0) (q := q) hq0 hqMul (by intro j; exact Fin.elim0 j)
  exact ⟨r, hr0, hrLin⟩

/-- Lemma 15.30.16: if the canonical map from `R` to the family of away localizations at the
coefficients `a_i` is injective, equivalently if the map `R → R^n`, `x ↦ (x a_i)_i`, is
injective, then the linear form `∑ i, a_i t_i` is a nonzerodivisor in the polynomial ring
`R[t_0, ..., t_{n-1}]`. -/
theorem isRegular_linearForm_of_injective_awayLocalizationFamilyMap (a : Fin n → R)
    (h : Function.Injective (awayLocalizationFamilyMap R a)) :
    IsRegular (∑ i, C (a i) * X i) := by
  -- Rewrite regularity as the nonzerodivisor condition in the polynomial ring.
  rw [isRegular_iff_mem_nonZeroDivisors]
  by_contra hreg
  have hsmul :
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R R (a i)) :=
    smul_family_map_injective_of_injective_awayLocalizationFamilyMap a h
  obtain ⟨r, hr0, hrLin⟩ :=
    exists_constant_annihilator_of_zero_divisor_linearForm a hreg
  have hkills : ∀ i, r * a i = 0 :=
    constant_annihilator_kills_all_coefficients_of_linearForm a hrLin
  have hrEq : r = 0 := by
    apply hsmul
    ext i
    simpa [mul_comm] using hkills i
  exact hr0 hrEq

end
