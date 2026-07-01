import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

variable {K : Type u} [Field K]

/-- Helper for Proposition 7.1: substituting a series with vanishing constant term preserves the
constant coefficient. -/
lemma powerSeries_constantCoeff_subst_eq_constantCoeff
    {S T : K⟦X⟧} (hT0 : T.constantCoeff = 0) :
    constantCoeff (S.subst T) = S.constantCoeff := by
  have hT : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  -- Only the zeroth contribution survives in the coefficient formula for substitution.
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' hT, finsum_eq_single (a := 0)]
  · simp [smul_eq_mul, coeff_zero_eq_constantCoeff]
  · intro n hn
    cases n with
    | zero =>
        exact (hn rfl).elim
    | succ n =>
        simp [smul_eq_mul, coeff_zero_eq_constantCoeff, hT0]

/-- Helper for Proposition 7.1: the linear coefficient of a substituted series is the product of
the linear coefficients when the substituted series has vanishing constant term. -/
lemma powerSeries_coeff_one_subst_eq_mul_coeff_one
    {S T : K⟦X⟧} (hT0 : T.constantCoeff = 0) :
    coeff 1 (S.subst T) = coeff 1 S * coeff 1 T := by
  have hT : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  -- For the first coefficient, only the linear term of `S` contributes.
  rw [coeff_subst' hT, finsum_eq_single (a := 1)]
  · simp [smul_eq_mul]
  · intro n hn
    cases n with
    | zero =>
        simp [smul_eq_mul]
    | succ n =>
        cases n with
        | zero =>
            exact (hn rfl).elim
        | succ n =>
            simp [smul_eq_mul, coeff_one_pow, hT0]

/-- Helper for Proposition 7.1: the constant coefficient of the derivative is the linear
coefficient of the original series. -/
lemma powerSeries_derivative_constantCoeff_ne_zero_iff_coeff_one_ne_zero
    {S : K⟦X⟧} :
    constantCoeff (d⁄dX K S) ≠ 0 ↔ coeff 1 S ≠ 0 := by
  -- The derivative shifts coefficients down by one.
  rw [← coeff_zero_eq_constantCoeff, coeff_derivative]
  simp

/-- Proposition 7.1 (1): a formal power series admits a substitution right inverse with vanishing
constant term if and only if its constant term vanishes and its formal derivative at `0` is
nonzero. -/
theorem powerSeries_exists_subst_right_inverse_iff
    {S : K⟦X⟧} :
    (∃ T : K⟦X⟧, T.constantCoeff = 0 ∧ S.subst T = X) ↔
      S.constantCoeff = 0 ∧ constantCoeff (d⁄dX K S) ≠ 0 := by
  constructor
  · rintro ⟨T, hT0, hST⟩
    constructor
    · -- Compare constant coefficients in `S ∘ T = X`.
      calc
        S.constantCoeff = constantCoeff (S.subst T) :=
          (powerSeries_constantCoeff_subst_eq_constantCoeff hT0).symm
        _ = constantCoeff (X : K⟦X⟧) := by rw [hST]
        _ = 0 := by simp
    · -- Compare linear coefficients in `S ∘ T = X` to force `coeff 1 S ≠ 0`.
      have hmul : coeff 1 S * coeff 1 T = 1 := by
        calc
          coeff 1 S * coeff 1 T = coeff 1 (S.subst T) := by
            symm
            exact powerSeries_coeff_one_subst_eq_mul_coeff_one hT0
          _ = coeff 1 (X : K⟦X⟧) := by rw [hST]
          _ = 1 := coeff_one_X
      have hS1 : coeff 1 S ≠ 0 := by
        intro hcoeff1
        rw [hcoeff1, zero_mul] at hmul
        exact zero_ne_one hmul
      exact
        (powerSeries_derivative_constantCoeff_ne_zero_iff_coeff_one_ne_zero).2 hS1
  · rintro ⟨hS0, hD⟩
    have hS1 : IsUnit (coeff 1 S) := by
      -- The derivative condition is exactly the nonvanishing of the linear coefficient.
      refine isUnit_iff_ne_zero.mpr ?_
      exact
        (powerSeries_derivative_constantCoeff_ne_zero_iff_coeff_one_ne_zero).1 hD
    refine Exists.intro (S.substInvOfIsUnit hS1) ?_
    constructor
    · -- The canonical inverse from mathlib has vanishing constant term.
      exact S.constantCoeff_substInvOfIsUnit hS1
    · -- Mathlib packages the recursive inverse construction from the textbook.
      exact S.subst_substInvOfIsUnit_right hS0 hS1

/-- Any substitution right inverse with vanishing constant term forces the linear coefficient of
the original series to be a unit. -/
theorem powerSeries_subst_right_inverse_coeff_one_isUnit
    {S T : K⟦X⟧}
    (hT0 : T.constantCoeff = 0) (hST : S.subst T = X) :
    IsUnit (coeff 1 S) := by
  have hS := powerSeries_exists_subst_right_inverse_iff.mp ⟨T, hT0, hST⟩
  refine isUnit_iff_ne_zero.mpr fun hcoeff1 ↦ ?_
  exact hS.2 <| by rw [← coeff_zero_eq_constantCoeff, coeff_derivative, hcoeff1, zero_mul]

/-- Bridge to the canonical substitution inverse from mathlib: any substitution right inverse with
vanishing constant term agrees with `PowerSeries.substInvOfIsUnit`; the unit hypothesis on the
linear coefficient is derived from the right-inverse data. -/
theorem powerSeries_subst_right_inverse_eq_substInvOfIsUnit
    {S T : K⟦X⟧}
    (hT0 : T.constantCoeff = 0) (hST : S.subst T = X) :
    T = S.substInvOfIsUnit (powerSeries_subst_right_inverse_coeff_one_isUnit hT0 hST) := by
  have hS0 : S.constantCoeff = 0 :=
    (powerSeries_exists_subst_right_inverse_iff.mp ⟨T, hT0, hST⟩).1
  have hS1 : IsUnit (coeff 1 S) :=
    powerSeries_subst_right_inverse_coeff_one_isUnit hT0 hST
  have hS : HasSubst S := HasSubst.of_constantCoeff_zero' hS0
  have hT : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  calc
    T = PowerSeries.subst T (X : K⟦X⟧) := by simpa using (PowerSeries.subst_X hT).symm
    _ = PowerSeries.subst T (PowerSeries.subst S (S.substInvOfIsUnit hS1)) := by
      rw [(S.subst_substInvOfIsUnit_left hS0 hS1).symm]
    _ = PowerSeries.subst (PowerSeries.subst T S) (S.substInvOfIsUnit hS1) := by
      simpa using PowerSeries.subst_comp_subst_apply hS hT (S.substInvOfIsUnit hS1)
    _ = PowerSeries.subst (X : K⟦X⟧) (S.substInvOfIsUnit hS1) := by rw [hST]
    _ = S.substInvOfIsUnit hS1 := PowerSeries.X_subst (S.substInvOfIsUnit hS1)

/-- Proposition 7.1 (2): a substitution right inverse with vanishing constant term is unique. -/
theorem powerSeries_subst_right_inverse_unique
    {S T₁ T₂ : K⟦X⟧}
    (hT₁0 : T₁.constantCoeff = 0) (hT₂0 : T₂.constantCoeff = 0)
    (hST₁ : S.subst T₁ = X) (hST₂ : S.subst T₂ = X) :
    T₁ = T₂ := by
  have hInv :
      S.substInvOfIsUnit (powerSeries_subst_right_inverse_coeff_one_isUnit hT₁0 hST₁) =
        S.substInvOfIsUnit (powerSeries_subst_right_inverse_coeff_one_isUnit hT₂0 hST₂) := by
    exact congrArg (S.substInvOfIsUnit) <| Subsingleton.elim _ _
  calc
    T₁ = S.substInvOfIsUnit (powerSeries_subst_right_inverse_coeff_one_isUnit hT₁0 hST₁) :=
      powerSeries_subst_right_inverse_eq_substInvOfIsUnit hT₁0 hST₁
    _ = S.substInvOfIsUnit (powerSeries_subst_right_inverse_coeff_one_isUnit hT₂0 hST₂) :=
      hInv
    _ = T₂ :=
      (powerSeries_subst_right_inverse_eq_substInvOfIsUnit hT₂0 hST₂).symm

/-- Proposition 7.1 (3): a substitution right inverse with vanishing constant term is also a left
inverse. -/
theorem powerSeries_subst_right_inverse_is_left_inverse
    {S T : K⟦X⟧}
    (hT0 : T.constantCoeff = 0) (hST : S.subst T = X) :
    T.subst S = X := by
  have hS0 : S.constantCoeff = 0 :=
    (powerSeries_exists_subst_right_inverse_iff.mp ⟨T, hT0, hST⟩).1
  rw [powerSeries_subst_right_inverse_eq_substInvOfIsUnit hT0 hST]
  have hS1 : IsUnit (coeff 1 S) :=
    powerSeries_subst_right_inverse_coeff_one_isUnit hT0 hST
  simpa using S.subst_substInvOfIsUnit_left hS0 hS1
