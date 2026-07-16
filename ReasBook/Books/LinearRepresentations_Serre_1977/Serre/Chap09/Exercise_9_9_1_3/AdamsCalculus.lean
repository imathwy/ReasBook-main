import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.AdamsOperatorSeries

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k] [Algebra ℚ k]
variable {G : Type u} [Group G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

local instance : CharZero k := algebraRat.charZero (R := k)

theorem eval_psiGeneratingSeries_coeff_succ
    (ρ : Representation k G V) (s : G) (m : ℕ) :
    PowerSeries.coeff (m + 1)
      (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) =
        algebraMap ℚ k ((m + 1 : ℚ)⁻¹) * LinearMap.trace k V ((ρ s) ^ (m + 1)) := by
  -- Evaluate the coefficient first, then unfold the Adams operator into the power map on `G`.
  rw [PowerSeries.coeff_map, coeff_psiGeneratingSeries_succ]
  -- The evaluated character of `s^(m+1)` is the trace of `(ρ s)^(m+1)`.
  simp [smul_eq_mul, Representation.adamsOperator, Representation.character, map_pow]

/-- Helper for Exercise 9-9.1-3: evaluating the degree-`m+1` coefficient of the alternating Adams
logarithmic series at `s` rewrites it as the signed scaled trace of `(ρ s)^(m+1)`. -/
theorem eval_alternatingPsiGeneratingSeries_coeff_succ
    (ρ : Representation k G V) (s : G) (m : ℕ) :
    PowerSeries.coeff (m + 1)
      (PowerSeries.map (Pi.evalRingHom _ s) (alternatingPsiGeneratingSeries ρ.character)) =
        algebraMap ℚ k (((-1 : ℚ) ^ m) * (m + 1 : ℚ)⁻¹) *
          LinearMap.trace k V ((ρ s) ^ (m + 1)) := by
  -- Evaluate the coefficient first, then unfold the Adams operator into the power map on `G`.
  rw [PowerSeries.coeff_map, coeff_alternatingPsiGeneratingSeries_succ]
  -- The remaining pointwise term is the same trace-power expression as in the non-alternating case.
  simp [smul_eq_mul, Representation.adamsOperator, Representation.character, map_pow]

/-- Helper for Exercise 9-9.1-3: differentiating the Adams logarithmic series removes the
`1/(m+1)` weight in degree `m`. -/
theorem coeff_derivative_psiGeneratingSeries
    (ρ : Representation k G V) (m : ℕ) :
    PowerSeries.coeff m (d⁄dX (G → k) (psiGeneratingSeries ρ.character)) =
      Ψ^m.succPNat(ρ.character) := by
  -- Differentiate coefficientwise and rewrite the degree-`m+1` coefficient of the logarithmic
  -- series.
  rw [PowerSeries.coeff_derivative, coeff_psiGeneratingSeries_succ]
  -- Pointwise, the factor `(m+1)` cancels the rational weight `(m+1)⁻¹`.
  ext s
  have hne : (m + 1 : k) ≠ 0 := by
    simpa [Nat.succ_eq_add_one] using (Nat.cast_ne_zero (R := k).mpr (Nat.succ_ne_zero m))
  simp [smul_eq_mul, mul_assoc]
  field_simp [hne]

/-- Helper for Exercise 9-9.1-3: differentiating the alternating Adams logarithmic series removes
the denominator while preserving the expected sign `(-1)^m`. -/
theorem coeff_derivative_alternatingPsiGeneratingSeries
    (ρ : Representation k G V) (m : ℕ) :
    PowerSeries.coeff m (d⁄dX (G → k) (alternatingPsiGeneratingSeries ρ.character)) =
      ((-1 : k) ^ m) • Ψ^m.succPNat(ρ.character) := by
  -- Differentiate coefficientwise and rewrite the degree-`m+1` coefficient of the alternating
  -- logarithmic series.
  rw [PowerSeries.coeff_derivative, coeff_alternatingPsiGeneratingSeries_succ]
  -- Pointwise, the factor `(m+1)` cancels the denominator and leaves the sign `(-1)^m`.
  ext s
  have hne : (m + 1 : k) ≠ 0 := by
    simpa [Nat.succ_eq_add_one] using (Nat.cast_ne_zero (R := k).mpr (Nat.succ_ne_zero m))
  simp [smul_eq_mul, mul_assoc]
  field_simp [hne]

/-- Helper for Exercise 9-9.1-3: the symmetric Adams logarithmic series has zero constant term, so
it can be substituted into `exp`. -/
theorem hasSubst_psiGeneratingSeries
    (ρ : Representation k G V) :
    PowerSeries.HasSubst (psiGeneratingSeries ρ.character) := by
  -- The constant coefficient was built to vanish, which is the exact substitution criterion.
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp [psiGeneratingSeries, weightedPsiGeneratingSeries]

/-- Helper for Exercise 9-9.1-3: the alternating Adams logarithmic series also has zero constant
term, so it can be substituted into `exp`. -/
theorem hasSubst_alternatingPsiGeneratingSeries
    (ρ : Representation k G V) :
    PowerSeries.HasSubst (alternatingPsiGeneratingSeries ρ.character) := by
  -- As in the non-alternating case, substitution is allowed because degree `0` vanishes.
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp [alternatingPsiGeneratingSeries, weightedPsiGeneratingSeries]

/-- Helper for Exercise 9-9.1-3: rescaling the alternating Adams logarithmic series by `-1`
turns the alternating signs into the global minus sign of the ordinary Adams logarithmic series. -/
theorem rescale_neg_alternatingPsiGeneratingSeries_eq_neg_psiGeneratingSeries
    (ρ : Representation k G V) :
    PowerSeries.rescale (-1 : G → k) (alternatingPsiGeneratingSeries ρ.character) =
      - psiGeneratingSeries ρ.character := by
  -- Compare coefficients after rescaling; the factor `(-1)^n` cancels the alternating sign in
  -- degree `n = m + 1`.
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_rescale, psiGeneratingSeries, alternatingPsiGeneratingSeries,
        weightedPsiGeneratingSeries]
  | succ m =>
      simp [PowerSeries.coeff_rescale, smul_eq_mul]
      ring_nf
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 9-9.1-3: a power series with constant term `1` and logarithmic derivative
matching a zero-constant-term series `g` is the exponential substituted at `g`. -/
theorem eq_exp_subst_of_derivative_eq_mul
    (f g : PowerSeries k) (hg : PowerSeries.HasSubst g)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hconst : PowerSeries.constantCoeff f = 1)
    (hderiv : d⁄dX k f = f * d⁄dX k g) :
    f = (exp k).subst g := by
  let h : PowerSeries k := (exp k).subst (-g)
  have hgneg : PowerSeries.HasSubst (-g) := by
    simpa using (PowerSeries.HasSubst.smul' (-1 : k) hg)
  have hconst_h : PowerSeries.constantCoeff h = 1 := by
    -- The substituted exponential keeps constant coefficient `1` because `g` has no constant term.
    dsimp [h]
    rw [show PowerSeries.constantCoeff ((exp k).subst (-g)) =
        ∑ᶠ d : ℕ, PowerSeries.coeff d (exp k) * PowerSeries.constantCoeff ((-g) ^ d) by
        simpa [smul_eq_mul] using (PowerSeries.constantCoeff_subst hgneg (exp k))]
    rw [finsum_eq_single (a := 0)]
    · simp [PowerSeries.constantCoeff_exp]
    · intro d hd
      simp [hd, hg0]
  have hmul_exp : ((exp k).subst g) * h = 1 := by
    -- Substitute `g` into the universal identity `exp(X) * exp(-X) = 1`.
    calc
      ((exp k).subst g) * h
          = ((exp k) * PowerSeries.evalNegHom (exp k)).subst g := by
              dsimp [h]
              have hneg := subst_evalNeg_eq_subst_neg (f := exp k) (g := g) hg
              rw [PowerSeries.subst_mul hg, hneg]
      _ = (1 : PowerSeries k).subst g := by
            exact congrArg (fun F : PowerSeries k => F.subst g)
              (PowerSeries.exp_mul_exp_neg_eq_one (A := k))
      _ = 1 := by
            rw [← PowerSeries.coe_substAlgHom hg, map_one]
  have hderiv_h : d⁄dX k h = h * -(d⁄dX k g) := by
    -- Differentiate the substituted exponential and absorb the derivative of `-g`.
    dsimp [h]
    rw [PowerSeries.derivative_subst (A := k) (hg := hgneg)]
    rw [PowerSeries.derivative_exp]
    simp [mul_assoc]
  have hderiv_mul : d⁄dX k (f * h) = 0 := by
    -- The two logarithmic-derivative contributions cancel after multiplying by `exp (-g)`.
    calc
      d⁄dX k (f * h) = f * d⁄dX k h + h * d⁄dX k f := by
        simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using (PowerSeries.derivative k).leibniz f h
      _ = f * (h * -(d⁄dX k g)) + h * (f * d⁄dX k g) := by rw [hderiv_h, hderiv]
      _ = 0 := by ring
  have hmul : f * h = 1 := by
    -- Equal derivative and constant term identify the product with the constant series `1`.
    apply PowerSeries.derivative.ext
    · simpa using hderiv_mul
    · simp [hconst, hconst_h]
  have hmul_exp' : h * ((exp k).subst g) = 1 := by
    simpa [mul_comm] using hmul_exp
  -- Multiply by the common inverse `exp(-g)` to recover the desired series.
  calc
    f = f * 1 := by simp
    _ = f * (h * ((exp k).subst g)) := by rw [hmul_exp']
    _ = (f * h) * ((exp k).subst g) := by ring
    _ = (exp k).subst g := by simp [hmul]

/-- Helper for Exercise 9-9.1-3: the `exp`-substituted Adams series and its negated companion are
multiplicative inverses. -/
theorem exp_subst_mul_exp_subst_neg_eq_one
    (ρ : Representation k G V) :
    ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) *
      ((exp (G → k)).subst (- psiGeneratingSeries ρ.character)) = 1 := by
  -- Substitute the Adams series into the universal identity `exp(X) * exp(-X) = 1`.
  calc
    ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) *
        ((exp (G → k)).subst (- psiGeneratingSeries ρ.character))
        = ((exp (G → k)) * PowerSeries.evalNegHom (exp (G → k))).subst
            (psiGeneratingSeries ρ.character) := by
              have hneg :=
                subst_evalNeg_eq_subst_neg (f := exp (G → k))
                  (g := psiGeneratingSeries ρ.character) (hasSubst_psiGeneratingSeries ρ)
              rw [PowerSeries.subst_mul (hasSubst_psiGeneratingSeries ρ)]
              rw [hneg]
    _ = (1 : PowerSeries (G → k)).subst (psiGeneratingSeries ρ.character) := by
          exact congrArg (fun f : PowerSeries (G → k) =>
            f.subst (psiGeneratingSeries ρ.character))
            (PowerSeries.exp_mul_exp_neg_eq_one (A := G → k))
    _ = 1 := by
          rw [← PowerSeries.coe_substAlgHom (hasSubst_psiGeneratingSeries ρ), map_one]

end

end Representation
