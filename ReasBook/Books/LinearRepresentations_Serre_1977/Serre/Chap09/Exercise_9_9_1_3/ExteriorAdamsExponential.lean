import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.NewtonIdentities

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

theorem coeff_derivative_alternating_trace_series
    (A : V →ₗ[k] V) (m : ℕ) :
    PowerSeries.coeff m
      (d⁄dX k (PowerSeries.mk fun
        | 0 => 0
        | n + 1 =>
            algebraMap ℚ k (((-1 : ℚ) ^ n) * (n + 1 : ℚ)⁻¹) *
              LinearMap.trace k V (A ^ (n + 1)))) =
        ((-1 : k) ^ m) * LinearMap.trace k V (A ^ (m + 1)) := by
  -- Differentiate coefficientwise; the factor `(m + 1)` cancels the rational denominator.
  rw [PowerSeries.coeff_derivative]
  have hne : (m + 1 : k) ≠ 0 := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.cast_ne_zero (R := k).mpr (Nat.succ_ne_zero m))
  simp [mul_assoc]
  field_simp [hne]

/-- Helper for Exercise 9-9.1-3: the scalar determinant series `det (1 + A T)` is the exponential
of the alternating trace logarithm. -/
theorem derivative_neg_charpoly_reverse_eq_mul_alternating_trace_series
    (A : V →ₗ[k] V) :
    d⁄dX k (((( -A).charpoly.reverse : Polynomial k) : PowerSeries k)) =
      ((((-A).charpoly.reverse : Polynomial k) : PowerSeries k)) *
        d⁄dX k (PowerSeries.mk fun
          | 0 => 0
          | m + 1 =>
              algebraMap ℚ k (((-1 : ℚ) ^ m) * (m + 1 : ℚ)⁻¹) *
                LinearMap.trace k V (A ^ (m + 1))) := by
  let p : PowerSeries k := ((((-A).charpoly.reverse : Polynomial k) : PowerSeries k))
  let g : PowerSeries k := PowerSeries.mk fun
    | 0 => 0
    | m + 1 =>
        algebraMap ℚ k (((-1 : ℚ) ^ m) * (m + 1 : ℚ)⁻¹) *
          LinearMap.trace k V (A ^ (m + 1))
  -- Compare the coefficient of degree `n` on both sides; Newton's coefficient recurrence is
  -- exactly the resulting scalar identity.
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul]
  rw [mul_comm]
  have hnewton := neg_charpoly_reverse_coeff_newton (A := A) n
  calc
    (n + 1 : k) * PowerSeries.coeff (n + 1) p
        = Finset.sum (Finset.antidiagonal n) fun x ↦
            PowerSeries.coeff x.1 p *
              (((-1 : k) ^ x.2) * LinearMap.trace k V (A ^ (x.2 + 1))) := by
              simpa [p] using hnewton
    _ = Finset.sum (Finset.antidiagonal n) fun x ↦
          PowerSeries.coeff x.1 p *
            PowerSeries.coeff x.2 (d⁄dX k g) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [coeff_derivative_alternating_trace_series (A := A) (m := x.2)]

/-- Helper for Exercise 9-9.1-3: after evaluating at `s`, the exterior-power series is the scalar
exponential attached to the alternating Adams trace series. -/
theorem exteriorPowerCharacterSeries_eq_exp_subst_aux
    (ρ : Representation k G V) :
    λ_T(ρ) =
      (exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character) := by
  -- Evaluate at each `s : G`, identify the scalar determinant series, and then use the
  -- logarithmic-derivative uniqueness lemma.
  ext n s
  let gEval : PowerSeries k :=
    PowerSeries.map (Pi.evalRingHom _ s) (alternatingPsiGeneratingSeries ρ.character)
  let gTrace : PowerSeries k := PowerSeries.mk fun
    | 0 => 0
    | m + 1 =>
        algebraMap ℚ k (((-1 : ℚ) ^ m) * (m + 1 : ℚ)⁻¹) *
          LinearMap.trace k V ((ρ s) ^ (m + 1))
  have hgEval_eq : gEval = gTrace := by
    -- Compare coefficients: the evaluated Adams coefficients are exactly the expected traces.
    ext m
    cases m with
    | zero =>
        simp [gEval, gTrace]
    | succ m =>
        simpa [gEval, gTrace] using
          eval_alternatingPsiGeneratingSeries_coeff_succ (ρ := ρ) (s := s) m
  have hg0 : PowerSeries.constantCoeff gEval = 0 := by
    -- The alternating Adams logarithm has vanishing constant coefficient even after evaluation.
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp
  have hg : PowerSeries.HasSubst gEval := by
    exact PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hdet :
      PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) =
        (((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
    exact exteriorPowerCharacterSeries_eval_eq_det_aux (ρ := ρ) s
  have hscalar :
      PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) =
        (exp k).subst gEval := by
    -- The evaluated determinant series is determined by its constant coefficient and
    -- logarithmic derivative.
    apply eq_exp_subst_of_derivative_eq_mul
      (f := PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ))
      (g := gEval)
      hg hg0
    · rw [hdet]
      simpa using constantCoeff_charpoly_reverse_powerSeries (A := -ρ s)
    · rw [hdet, hgEval_eq]
      simpa [gTrace] using
        derivative_neg_charpoly_reverse_eq_mul_alternating_trace_series (A := ρ s)
  have hmap :
      PowerSeries.map (Pi.evalRingHom _ s)
          ((exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character)) =
        (exp k).subst gEval := by
    -- Evaluation commutes with substitution into `exp`.
    simpa [gEval] using
      (PowerSeries.map_subst (ha := hasSubst_alternatingPsiGeneratingSeries ρ)
        (h := Pi.evalRingHom _ s) (f := exp (G → k)))
  calc
    PowerSeries.coeff n λ_T(ρ) s
        = (Pi.evalRingHom _ s) (PowerSeries.coeff n λ_T(ρ)) := by
            rfl
    _ = PowerSeries.coeff n (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ)) := by
            rw [PowerSeries.coeff_map]
    _ = PowerSeries.coeff n ((exp k).subst gEval) := by rw [hscalar]
    _ = PowerSeries.coeff n
          (PowerSeries.map (Pi.evalRingHom _ s)
            ((exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character))) := by
            rw [hmap]
    _ = (Pi.evalRingHom _ s)
          (PowerSeries.coeff n
            ((exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character))) := by
            rw [PowerSeries.coeff_map]
    _ = PowerSeries.coeff n
          ((exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character)) s := by
            rfl

/-- Helper for Exercise 9-9.1-3: after evaluating at `s`, the Adams exponential multiplied by the
rescaled exterior series is already `1`. -/
theorem map_eval_exp_subst_psi_mul_rescale_neg_exterior_eq_one
    (ρ : Representation k G V) (s : G) :
    (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) *
      PowerSeries.rescale (-1 : k)
        (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ)) = 1 := by
  -- Rewrite the rescaled evaluated exterior series via the exterior exponential formula and then
  -- use the universal identity `exp(X) * exp(-X) = 1`.
  let altEval : PowerSeries k :=
    PowerSeries.map (Pi.evalRingHom _ s) (alternatingPsiGeneratingSeries ρ.character)
  have hAltEval : PowerSeries.HasSubst altEval := by
    refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp [altEval]
  have hsLam :
      PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) = (exp k).subst altEval := by
    have hAux :=
      congrArg (PowerSeries.map (Pi.evalRingHom _ s))
        (exteriorPowerCharacterSeries_eq_exp_subst_aux (ρ := ρ))
    have hMap :
        PowerSeries.map (Pi.evalRingHom _ s)
            ((exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character)) =
          (exp k).subst altEval := by
      simpa [altEval] using
        (PowerSeries.map_subst (ha := hasSubst_alternatingPsiGeneratingSeries ρ)
          (h := Pi.evalRingHom _ s) (f := exp (G → k)))
    exact hAux.trans hMap
  have hrescale :
      PowerSeries.rescale (-1 : k) altEval =
        - PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character) := by
    -- Evaluating after rescaling matches rescaling after evaluation, and the alternating signs
    -- collapse to the global minus sign.
    calc
      PowerSeries.rescale (-1 : k) altEval
          = PowerSeries.map (Pi.evalRingHom _ s)
              (PowerSeries.rescale (-1 : G → k)
                (alternatingPsiGeneratingSeries ρ.character)) := by
                symm
                simpa [altEval] using
                  map_eval_rescale (f := alternatingPsiGeneratingSeries ρ.character) (-1) s
      _ = PowerSeries.map (Pi.evalRingHom _ s) (- psiGeneratingSeries ρ.character) := by
            rw [rescale_neg_alternatingPsiGeneratingSeries_eq_neg_psiGeneratingSeries]
      _ = - PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character) := by
            simp
  rw [hsLam]
  rw [PowerSeries.rescale_eq_subst]
  rw [PowerSeries.subst_comp_subst_apply
    (ha := hAltEval) (hb := PowerSeries.HasSubst.smul_X' (-1 : k))]
  rw [show PowerSeries.subst ((-1 : k) • X) altEval = PowerSeries.rescale (-1 : k) altEval by
    rw [PowerSeries.rescale_eq_subst]]
  rw [hrescale]
  have hpsi :
      PowerSeries.map (Pi.evalRingHom _ s)
          ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) =
        (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) := by
    simpa using
      (PowerSeries.map_subst (ha := hasSubst_psiGeneratingSeries ρ)
        (h := Pi.evalRingHom _ s) (f := exp (G → k)))
  have hneg :
      PowerSeries.map (Pi.evalRingHom _ s)
          ((exp (G → k)).subst (- psiGeneratingSeries ρ.character)) =
        (exp k).subst (-(PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character))) := by
    simpa [map_neg] using
      (PowerSeries.map_subst
        (ha := PowerSeries.HasSubst.smul' (-1 : G → k) (hasSubst_psiGeneratingSeries ρ))
        (h := Pi.evalRingHom _ s) (f := exp (G → k)))
  have hexp :=
    congrArg (PowerSeries.map (Pi.evalRingHom _ s)) (exp_subst_mul_exp_subst_neg_eq_one ρ)
  calc
    (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) *
        (exp k).subst (-(PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character))) =
          PowerSeries.map (Pi.evalRingHom _ s)
            ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) *
              PowerSeries.map (Pi.evalRingHom _ s)
                ((exp (G → k)).subst (- psiGeneratingSeries ρ.character)) := by
                  rw [hpsi, hneg]
    _ = 1 := by simpa using hexp

end

end Representation
