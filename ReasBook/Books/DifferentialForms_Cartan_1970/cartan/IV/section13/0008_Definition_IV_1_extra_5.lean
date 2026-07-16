import DifferentialForms_Cartan_1970.cartan.IV.section13.«0001_Definition_IV_1_extra_1»
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.MvPowerSeries.Trunc

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling:
-- * owner pattern for formal differentiation in one variable:
--   public operator `PowerSeries.derivativeFun`, with the bundled derivation
--   `PowerSeries.derivative` as a stronger bridge
-- * owner pattern for multivariable formal partial differentiation:
--   `MvPolynomial.pderiv`
-- * chapter owner for the source-facing two-variable ambient algebra:
--   `K⟦X,Y⟧`
--
-- Primitive data here is the coefficient-shift operator itself. The bundled derivation is the
-- stronger bridge/view layer under commutativity, while the `X`/`Y` cases are source-facing
-- notation specializations of the operator.

universe u

noncomputable section

open scoped MvPowerSeries

namespace MvPowerSeries

open Finsupp

section Semiring

variable {σ : Type u} {R : Type*} [Semiring R]

/-- The formal partial derivative of a multivariate power series with respect to the variable `i`,
defined coefficientwise by shifting the exponent of `i` down by one and multiplying by the former
exponent. -/
def partialDerivative (i : σ) (S : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ ((d i + 1 : ℕ) : R) * coeff (d + single i 1) S

scoped notation "∂[" i "]" => partialDerivative i
scoped notation "∂X" => partialDerivative (0 : Fin 2)
scoped notation "∂Y" => partialDerivative (1 : Fin 2)

/-- The coefficients of `partialDerivative` are obtained by the expected exponent shift and
scalar multiplication by the old exponent. -/
theorem coeff_partialDerivative (i : σ) (S : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (∂[i] S) = ((d i + 1 : ℕ) : R) * coeff (d + single i 1) S :=
  rfl

theorem partialDerivative_add (i : σ) (S T : MvPowerSeries σ R) :
    ∂[i] (S + T) = ∂[i] S + ∂[i] T := by
  funext d
  change ((d i + 1 : ℕ) : R) * coeff (d + single i 1) (S + T) =
      ((d i + 1 : ℕ) : R) * coeff (d + single i 1) S +
        ((d i + 1 : ℕ) : R) * coeff (d + single i 1) T
  simp [mul_add]

theorem partialDerivative_one (i : σ) : ∂[i] (1 : MvPowerSeries σ R) = 0 := by
  ext d
  classical
  have h : d + single i 1 ≠ 0 := by
    intro hd
    have : d i + 1 = 0 := by
      simpa using congrArg (fun e : σ →₀ ℕ ↦ e i) hd
    exact Nat.succ_ne_zero (d i) this
  change ((d i + 1 : ℕ) : R) * coeff (d + single i 1) (1 : MvPowerSeries σ R) = 0
  simp [coeff_one, h]

/-- Definition IV.1-extra-5 (1): the coefficients of `∂X S` are `p a_{p,q}` after shifting the
`X`-exponent down by one. -/
theorem coeff_partialDerivativeX (S : R⟦X,Y⟧) (d : Fin 2 →₀ ℕ) :
    coeff d (∂X S) = ((d 0 + 1 : ℕ) : R) * coeff (d + single 0 1) S :=
  rfl

/-- Definition IV.1-extra-5 (2): the coefficients of `∂Y S` are `q a_{p,q}` after shifting the
`Y`-exponent down by one. -/
theorem coeff_partialDerivativeY (S : R⟦X,Y⟧) (d : Fin 2 →₀ ℕ) :
    coeff d (∂Y S) = ((d 1 + 1 : ℕ) : R) * coeff (d + single 1 1) S :=
  rfl

end Semiring

section CommSemiring

variable {σ : Type u} {R : Type*} [CommSemiring R]

namespace MvPolynomial

open Finsupp

/-- Helper for Definition IV.1-extra-5: the coefficient of a polynomial partial derivative is
determined by the coefficient one step higher in the differentiated variable. -/
theorem coeff_pderiv (i : σ) (P : MvPolynomial σ R) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i P) =
      ((d i + 1 : ℕ) : R) * MvPolynomial.coeff (d + single i 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
      -- Compute the derivative of a monomial directly and compare the shifted exponent.
      by_cases hs : s i = 0
      · have hs_ne : s ≠ d + single i 1 := by
          intro h
          have hsi : s i = d i + 1 := by
            simpa [h] using congrArg (fun e : σ →₀ ℕ ↦ e i) h
          have hzero : 0 = d i + 1 := by simpa [hs] using hsi
          exact Nat.succ_ne_zero (d i) hzero.symm
        simp [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, hs, hs_ne]
      · by_cases hsd : s - single i 1 = d
        · have hs_eq : s = d + single i 1 := by
            rw [← hsd, Finsupp.sub_add_single_one_cancel hs]
          have hsi : s i = d i + 1 := by
            simpa [hs_eq] using congrArg (fun e : σ →₀ ℕ ↦ e i) hs_eq
          simp [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, hsd, hs_eq, hsi,
            mul_comm]
        · have hs_ne : s ≠ d + single i 1 := by
            intro hs_eq
            apply hsd
            simpa [hs_eq] using add_tsub_cancel_right d (single i 1)
          simp [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, hsd, hs_ne]
  | add P Q hP hQ =>
      -- The coefficient identity is additive, so the monomial computation extends by linearity.
      simp [hP, hQ, left_distrib]

end MvPolynomial

/-- Helper for Definition IV.1-extra-5: once the truncation level contains `d + single i 1`, the
`d`-coefficient of the polynomial partial derivative of a truncation agrees with the
`d`-coefficient of the power-series partial derivative. -/
theorem coeff_pderiv_trunc'_eq_coeff_partialDerivative (i : σ) (d n : σ →₀ ℕ)
    [DecidableEq σ] (h : d + single i 1 ≤ n) (S : MvPowerSeries σ R) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i (MvPowerSeries.trunc' R n S)) =
      MvPowerSeries.coeff d (∂[i] S) := by
  classical
  -- Rewrite both sides to the same shifted coefficient of `S`.
  rw [MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_partialDerivative, MvPowerSeries.coeff_trunc']
  simp [h]

/-- Helper for Definition IV.1-extra-5: truncating `∂[i] S` at degree `d` matches the polynomial
partial derivative of the truncation one step higher in the `i`-direction. -/
theorem trunc'_partialDerivative_eq_pderiv_trunc'_succ (i : σ) (d : σ →₀ ℕ)
    [DecidableEq σ] (S : MvPowerSeries σ R) :
    MvPowerSeries.trunc' R d (∂[i] S) =
      MvPolynomial.pderiv i (MvPowerSeries.trunc' R (d + single i 1) S) := by
  classical
  ext m
  by_cases hm : m ≤ d
  · have hm' : m + single i 1 ≤ d + single i 1 := by
        intro a
        exact Nat.add_le_add_right (hm a) ((single i 1) a)
    -- Inside the truncation range, both polynomials read the same coefficient of `∂[i] S`.
    rw [MvPowerSeries.coeff_trunc', if_pos hm,
      coeff_pderiv_trunc'_eq_coeff_partialDerivative (i := i) (d := m)
        (n := d + single i 1) hm']
  · have hm' : ¬ m + single i 1 ≤ d + single i 1 := by
      intro hmd
      exact hm <| by
        intro a
        exact Nat.le_of_add_le_add_right (hmd a)
    -- Outside the truncation range, both sides vanish.
    rw [MvPowerSeries.coeff_trunc', if_neg hm, MvPolynomial.coeff_pderiv,
      MvPowerSeries.coeff_trunc', if_neg hm']
    simp

/-- Helper for Definition IV.1-extra-5: the `d`-coefficient of the polynomial product
`pderiv i (trunc' S) * trunc' T` is the `d`-coefficient of `∂[i] S * T`. -/
theorem coeff_pderiv_trunc'_mul_eq_coeff_partialDerivative_mul
    (i : σ) [DecidableEq σ] (d : σ →₀ ℕ) (S T : MvPowerSeries σ R) :
    MvPolynomial.coeff d
        (MvPolynomial.pderiv i (MvPowerSeries.trunc' R (d + single i 1) S) *
          MvPowerSeries.trunc' R (d + single i 1) T) =
      MvPowerSeries.coeff d (∂[i] S * T) := by
  classical
  -- Compare the two products coefficientwise over the same antidiagonal decomposition of `d`.
  rw [MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx₁ : x.1 ≤ d := Finset.antidiagonal.fst_le hx
  have hx₂ : x.2 ≤ d := Finset.antidiagonal.snd_le hx
  have hx₁' : x.1 + single i 1 ≤ d + single i 1 := by
    intro a
    exact Nat.add_le_add_right (hx₁ a) ((single i 1) a)
  have hd : d ≤ d + single i 1 := by
    intro a
    exact Nat.le_add_right (d a) ((single i 1) a)
  have hx₂' : x.2 ≤ d + single i 1 := le_trans hx₂ hd
  rw [coeff_pderiv_trunc'_eq_coeff_partialDerivative (i := i) (d := x.1)
      (n := d + single i 1) hx₁']
  rw [MvPowerSeries.coeff_trunc', if_pos hx₂']

theorem partialDerivative_smul (i : σ) (a : R) (S : MvPowerSeries σ R) :
    ∂[i] (a • S) = a • ∂[i] S := by
  ext d
  change ((d i + 1 : ℕ) : R) * coeff (d + single i 1) (a • S) =
      a * (((d i + 1 : ℕ) : R) * coeff (d + single i 1) S)
  rw [coeff_smul]
  ac_rfl

theorem partialDerivative_mul (i : σ) (S T : MvPowerSeries σ R) :
    ∂[i] (S * T) = S * ∂[i] T + T * ∂[i] S := by
  classical
  ext d
  let n : σ →₀ ℕ := d + single i 1
  have hd : d ≤ n := by
    dsimp [n]
    intro a
    exact Nat.le_add_right (d a) ((single i 1) a)
  -- Reduce the target coefficient to polynomial partial differentiation on the truncation window
  -- that controls degree `d`.
  calc
    MvPowerSeries.coeff d (∂[i] (S * T))
        = MvPolynomial.coeff d (MvPolynomial.pderiv i (MvPowerSeries.trunc' R n (S * T))) := by
            rw [MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_partialDerivative,
              MvPowerSeries.coeff_trunc']
            simp [n]
    _ = ((d i + 1 : ℕ) : R) * MvPowerSeries.coeff n (S * T) := by
          rw [MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_trunc', if_pos le_rfl]
    _ = ((d i + 1 : ℕ) : R) *
          MvPolynomial.coeff n (MvPowerSeries.trunc' R n S * MvPowerSeries.trunc' R n T) := by
            rw [← MvPowerSeries.coeff_trunc'_mul_trunc'_eq_coeff_mul (n := n) S T (m := n) le_rfl]
    _ = MvPolynomial.coeff d
          (MvPolynomial.pderiv i (MvPowerSeries.trunc' R n S * MvPowerSeries.trunc' R n T)) := by
            rw [MvPolynomial.coeff_pderiv]
    _ = MvPolynomial.coeff d
          (MvPolynomial.pderiv i (MvPowerSeries.trunc' R n S) * MvPowerSeries.trunc' R n T +
            MvPowerSeries.trunc' R n S * MvPolynomial.pderiv i (MvPowerSeries.trunc' R n T)) := by
            rw [MvPolynomial.pderiv_mul]
    _ = MvPowerSeries.coeff d (T * ∂[i] S) + MvPowerSeries.coeff d (S * ∂[i] T) := by
            -- Translate the polynomial Leibniz rule back to the two power-series summands.
            rw [MvPolynomial.coeff_add]
            congr 1
            · calc
                MvPolynomial.coeff d
                    (MvPolynomial.pderiv i (MvPowerSeries.trunc' R n S) *
                      MvPowerSeries.trunc' R n T)
                    = MvPowerSeries.coeff d (∂[i] S * T) := by
                        simpa [n] using
                          coeff_pderiv_trunc'_mul_eq_coeff_partialDerivative_mul (i := i) (d := d) S T
                _ = MvPowerSeries.coeff d (T * ∂[i] S) := by rw [mul_comm]
            · calc
                MvPolynomial.coeff d
                    (MvPowerSeries.trunc' R n S *
                      MvPolynomial.pderiv i (MvPowerSeries.trunc' R n T))
                    = MvPolynomial.coeff d
                        (MvPolynomial.pderiv i (MvPowerSeries.trunc' R n T) *
                          MvPowerSeries.trunc' R n S) := by
                            rw [mul_comm]
                _ = MvPowerSeries.coeff d (∂[i] T * S) := by
                      simpa [n] using
                        coeff_pderiv_trunc'_mul_eq_coeff_partialDerivative_mul (i := i) (d := d) T S
                _ = MvPowerSeries.coeff d (S * ∂[i] T) := by rw [mul_comm]
    _ = MvPowerSeries.coeff d (T * ∂[i] S + S * ∂[i] T) := by
          rfl
    _ = MvPowerSeries.coeff d (S * ∂[i] T + T * ∂[i] S) := by
          rw [add_comm]

/-- The source-facing partial-derivative operator, packaged as a derivation over a commutative
semiring. -/
def partialDerivativeDerivation (i : σ) :
    Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toLinearMap :=
    { toFun := partialDerivative i
      map_add' := partialDerivative_add i
      map_smul' := partialDerivative_smul i }
  map_one_eq_zero' := partialDerivative_one i
  leibniz' := partialDerivative_mul i

end CommSemiring

end MvPowerSeries
