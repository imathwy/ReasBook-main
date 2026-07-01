import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

variable {K : Type u} [Field K]

/-- Helper for Proposition 7.1: substituting a series with zero constant term preserves the
constant coefficient. -/
-- The constant term of `S.subst T` is the `d = 0` contribution in the substitution formula,
-- because every higher power of `T` still has zero constant coefficient.
lemma constantCoeff_subst_of_constantCoeff_zero {S T : K⟦X⟧} (hT0 : T.constantCoeff = 0) :
    (S.subst T).constantCoeff = S.constantCoeff := by
  let hT : PowerSeries.HasSubst T := PowerSeries.HasSubst.of_constantCoeff_zero' hT0
  rw [PowerSeries.constantCoeff_subst hT]
  rw [finsum_eq_single 0]
  · simp
  · intro d hd
    simp [PowerSeries.constantCoeff_eq_coeff_zero, hT0, hd]

/-- Helper for Proposition 7.1: after substituting a series with zero constant term, the linear
coefficient is the product of the two linear coefficients. -/
-- The source proof compares the linear terms in `S(T(X))`. Here the substitution coefficient
-- formula shows that only the `d = 1` summand survives.
lemma coeff_one_subst_of_constantCoeff_zero {S T : K⟦X⟧} (hT0 : T.constantCoeff = 0) :
    coeff 1 (S.subst T) = coeff 1 S * coeff 1 T := by
  let hT : PowerSeries.HasSubst T := PowerSeries.HasSubst.of_constantCoeff_zero' hT0
  rw [PowerSeries.coeff_subst' hT S 1]
  rw [finsum_eq_single 1]
  · simp [PowerSeries.coeff_one_pow, hT0]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with hlt | hgt
    · have hd0 : d = 0 := Nat.eq_zero_of_lt_one hlt
      subst hd0
      simp
    · have hd1 : d - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hgt
      simp [PowerSeries.coeff_one_pow, hT0, hd1]

/-- Helper for Proposition 7.1: a substitution left inverse and a substitution right inverse must
agree. -/
-- This is the associativity computation from the source proof: start from `T`, insert `X`,
-- rewrite `X` as `U ∘ S`, and then reassociate through the known right inverse relation.
lemma subst_right_inverse_unique {S T U : K⟦X⟧}
    (hS0 : S.constantCoeff = 0) (hT0 : T.constantCoeff = 0)
    (hleft : U.subst S = X) (hright : S.subst T = X) :
    T = U := by
  let hS : PowerSeries.HasSubst S := PowerSeries.HasSubst.of_constantCoeff_zero' hS0
  let hT : PowerSeries.HasSubst T := PowerSeries.HasSubst.of_constantCoeff_zero' hT0
  calc
    T = X.subst T := by
      symm
      exact PowerSeries.subst_X hT
    _ = (U.subst S).subst T := by rw [hleft]
    _ = U.subst (S.subst T) := by
      rw [← PowerSeries.subst_comp_subst_apply hS hT U]
    _ = U.subst X := by rw [hright]
    _ = U := PowerSeries.X_subst U

/-- Proposition 7.1: a formal power series over a field admits a right inverse for substitution
with vanishing constant term if and only if its constant term is zero and its linear coefficient
is nonzero. -/
-- Proof sketch: for the forward implication, compare the constant and linear coefficients in the
-- identity `S.subst T = X`; for the reverse implication, apply the canonical construction
-- `S.substInvOfIsUnit` using `S.constantCoeff = 0` and `isUnit_iff_ne_zero` for `coeff 1 S`.
theorem powerSeries_exists_subst_right_inverse_iff
    {S : K⟦X⟧} :
    (∃ T : K⟦X⟧, T.constantCoeff = 0 ∧ S.subst T = X) ↔
      S.constantCoeff = 0 ∧ coeff 1 S ≠ 0 := by
  constructor
  · rintro ⟨T, hT0, hcomp⟩
    -- Compare constant coefficients in `S.subst T = X` to recover `S(0) = 0`.
    have hS0 : S.constantCoeff = 0 := by
      have hconst := congrArg constantCoeff hcomp
      simpa [constantCoeff_subst_of_constantCoeff_zero hT0] using hconst
    -- Compare linear coefficients to recover that the first coefficient of `S` is invertible.
    have hcoeff1 : coeff 1 S * coeff 1 T = 1 := by
      have hcoeff := congrArg (coeff 1) hcomp
      simpa [coeff_one_subst_of_constantCoeff_zero hT0] using hcoeff
    refine ⟨hS0, ?_⟩
    intro hS1
    have : (0 : K) = 1 := by
      simpa [hS1] using hcoeff1
    exact zero_ne_one this
  · rintro ⟨hS0, hS1⟩
    -- Use mathlib's canonical substitution inverse, which packages the coefficient recursion.
    refine ⟨S.substInvOfIsUnit (isUnit_iff_ne_zero.2 hS1), ?_, ?_⟩
    · simpa using
        S.constantCoeff_substInvOfIsUnit (hP' := isUnit_iff_ne_zero.2 hS1)
    · simpa using
        S.subst_substInvOfIsUnit_right hS0 (isUnit_iff_ne_zero.2 hS1)

/-- A formal power series admitting a substitution right inverse with vanishing constant term has
nonvanishing linear coefficient. -/
-- Proof sketch: first recover `S.constantCoeff = 0` and `coeff 1 S ≠ 0` from
-- `powerSeries_exists_subst_right_inverse_iff`; then use associativity of substitution and the
-- canonical left-inverse identity for `S.substInvOfIsUnit`.
theorem powerSeries_subst_right_inverse_coeff_one_ne_zero
    {S T : K⟦X⟧} (hT0 : T.constantCoeff = 0) (hcomp : S.subst T = X) :
    coeff 1 S ≠ 0 := by
  -- This is the forward implication of Proposition 7.1 applied to the given witness `T`.
  exact ((powerSeries_exists_subst_right_inverse_iff (S := S)).1 ⟨T, hT0, hcomp⟩).2

/-- Any substitution right inverse of a formal power series with vanishing constant term and
nonvanishing linear coefficient coincides with the canonical substitution inverse
`S.substInvOfIsUnit`. -/
-- Proof sketch: recover `S.constantCoeff = 0` from
-- `powerSeries_exists_subst_right_inverse_iff`, derive `coeff 1 S ≠ 0` via
-- `powerSeries_subst_right_inverse_coeff_one_ne_zero`, and compare `T` with the canonical
-- inverse using associativity of substitution and `S.subst_substInvOfIsUnit_left`.
theorem powerSeries_subst_right_inverse_eq_substInvOfIsUnit
    {S T : K⟦X⟧}
    (hT0 : T.constantCoeff = 0) (hcomp : S.subst T = X) :
    T = S.substInvOfIsUnit
      (isUnit_iff_ne_zero.2 (powerSeries_subst_right_inverse_coeff_one_ne_zero hT0 hcomp)) := by
  -- First recover the vanishing constant coefficient required by the canonical inverse theorem.
  have hS0 : S.constantCoeff = 0 :=
    ((powerSeries_exists_subst_right_inverse_iff (S := S)).1 ⟨T, hT0, hcomp⟩).1
  -- Then compare the given right inverse with the canonical left inverse by associativity.
  exact subst_right_inverse_unique hS0 hT0
    (U := S.substInvOfIsUnit
      (isUnit_iff_ne_zero.2 (powerSeries_subst_right_inverse_coeff_one_ne_zero hT0 hcomp)))
    (by
      simpa using S.subst_substInvOfIsUnit_left hS0
        (isUnit_iff_ne_zero.2 (powerSeries_subst_right_inverse_coeff_one_ne_zero hT0 hcomp)))
    hcomp
