import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.ExteriorAdamsExponential

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

theorem symmetricPowerCharacterSeries_eq_exp_subst_aux (ρ : Representation k G V) :
    σ_T(ρ) =
      (exp (G → k)).subst (psiGeneratingSeries ρ.character) := by
  -- Compare both sides after evaluating at `s : G`; over the scalar coefficient field `k`, both
  -- series are the inverse of the same rescaled exterior series.
  ext n s
  let q : PowerSeries k :=
    PowerSeries.rescale (-1 : k) (PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ))
  have hqeq :
      q = (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
    -- The exterior determinant formula identifies the common inverse after the sign change
    -- `T ↦ -T`.
    calc
      q = PowerSeries.rescale (-1 : k)
            (((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
              simp [q, exteriorPowerCharacterSeries_eval_eq_det_aux]
      _ = (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) := by
            simpa using rescale_neg_charpoly_reverse (A := ρ s)
  have hq : PowerSeries.constantCoeff q ≠ 0 := by
    rw [hqeq]
    rw [constantCoeff_charpoly_reverse_powerSeries (A := ρ s)]
    simp
  have hσmul :
      PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) * q = 1 := by
    -- The symmetric determinant formula says the evaluated symmetric series is the inverse of `q`.
    have hchar :
        PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) *
          ((((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)) = 1 := by
      rw [symmetricPowerCharacterSeries_eval_eq_det_inv_aux]
      exact (PowerSeries.eq_inv_iff_mul_eq_one
        (by
          rw [constantCoeff_charpoly_reverse_powerSeries (A := ρ s)]
          simp)).1 rfl
    simpa [hqeq] using hchar
  have hexpmul :
      (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) *
        q = 1 := by
    -- The Adams exponential has the same inverse because the exterior exponential identity is
    -- already known pointwise.
    simpa [q] using map_eval_exp_subst_psi_mul_rescale_neg_exterior_eq_one (ρ := ρ) s
  have hσeq :
      PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) =
        (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) := by
    -- Over the field `k`, a series with nonzero constant coefficient has a unique inverse.
    have hσinv :
        PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) = q⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one hq).2 hσmul
    have hexpinv :
        (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) =
          q⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one hq).2 hexpmul
    exact hσinv.trans hexpinv.symm
  have hmap :
      PowerSeries.map (Pi.evalRingHom _ s)
          ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) =
        (exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character)) := by
    -- Evaluation commutes with substitution into `exp`.
    simpa using
      (PowerSeries.map_subst (ha := hasSubst_psiGeneratingSeries ρ)
        (h := Pi.evalRingHom _ s) (f := exp (G → k)))
  calc
    PowerSeries.coeff n σ_T(ρ) s
        = (Pi.evalRingHom _ s) (PowerSeries.coeff n σ_T(ρ)) := by
            rfl
    _ = PowerSeries.coeff n (PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ)) := by
            rw [PowerSeries.coeff_map]
    _ = PowerSeries.coeff n
          ((exp k).subst (PowerSeries.map (Pi.evalRingHom _ s) (psiGeneratingSeries ρ.character))) := by
            rw [hσeq]
    _ = PowerSeries.coeff n
          (PowerSeries.map (Pi.evalRingHom _ s)
            ((exp (G → k)).subst (psiGeneratingSeries ρ.character))) := by
            rw [hmap]
    _ = (Pi.evalRingHom _ s)
          (PowerSeries.coeff n
            ((exp (G → k)).subst (psiGeneratingSeries ρ.character))) := by
            rw [PowerSeries.coeff_map]
    _ = PowerSeries.coeff n
          ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) s := by
            rfl

/-- The exterior-power generating series is the exponential of the alternating Adams-operation
series. -/
theorem exteriorPowerCharacterSeries_eq_exp_subst_public_aux (ρ : Representation k G V) :
    λ_T(ρ) =
      (exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character) := by
  -- The heavy work is the pointwise scalar computation, already isolated in the auxiliary lemma.
  exact exteriorPowerCharacterSeries_eq_exp_subst_aux (ρ := ρ)

/-- Helper for Exercise 9-9.1-3: once the exterior exponential formula is available, the Adams
exponential series multiplied by the rescaled exterior series is already `1`. -/
theorem exp_subst_psi_mul_rescale_neg_exterior_eq_one
    (ρ : Representation k G V) :
    ((exp (G → k)).subst (psiGeneratingSeries ρ.character)) *
      PowerSeries.rescale (-1 : G → k) λ_T(ρ) = 1 := by
  -- Rewrite the rescaled exterior series as the exponential substituted at the negated Adams
  -- logarithm.
  rw [exteriorPowerCharacterSeries_eq_exp_subst_aux]
  rw [PowerSeries.rescale_eq_subst]
  rw [PowerSeries.subst_comp_subst_apply
    (ha := hasSubst_alternatingPsiGeneratingSeries ρ)
    (hb := PowerSeries.HasSubst.smul_X' (-1 : G → k))]
  -- The inner rescaling turns the alternating Adams logarithm into the negated ordinary one.
  rw [show
      PowerSeries.subst ((-1 : G → k) • X)
        (alternatingPsiGeneratingSeries ρ.character) =
        PowerSeries.rescale (-1 : G → k)
          (alternatingPsiGeneratingSeries ρ.character) by
      rw [PowerSeries.rescale_eq_subst]]
  rw [rescale_neg_alternatingPsiGeneratingSeries_eq_neg_psiGeneratingSeries ρ]
  exact exp_subst_mul_exp_subst_neg_eq_one ρ

/-- Helper for Exercise 9-9.1-3: once the symmetric series is written as `exp` of the Adams
logarithmic series, differentiating gives the product of the original series with the Adams trace
series. -/
theorem derivative_symmetricPowerCharacterSeries
    (ρ : Representation k G V) :
    d⁄dX (G → k) σ_T(ρ) =
      σ_T(ρ) * d⁄dX (G → k) (psiGeneratingSeries ρ.character) := by
  -- Route correction: separate the power-series chain-rule step from the unresolved scalar
  -- determinant identity, so the Newton recursion depends only on formal calculus here.
  rw [symmetricPowerCharacterSeries_eq_exp_subst_aux]
  rw [PowerSeries.derivative_subst (A := G → k) (hg := hasSubst_psiGeneratingSeries ρ)]
  rw [PowerSeries.derivative_exp]

/-- Helper for Exercise 9-9.1-3: differentiating the alternating exponential identity factors the
derivative of `λ_T(ρ)` through the alternating Adams trace series. -/
theorem derivative_exteriorPowerCharacterSeries
    (ρ : Representation k G V) :
    d⁄dX (G → k) λ_T(ρ) =
      λ_T(ρ) * d⁄dX (G → k) (alternatingPsiGeneratingSeries ρ.character) := by
  -- The exterior case uses the same chain-rule argument with the alternating logarithmic series.
  rw [exteriorPowerCharacterSeries_eq_exp_subst_aux]
  rw [PowerSeries.derivative_subst (A := G → k)
      (hg := hasSubst_alternatingPsiGeneratingSeries ρ)]
  rw [PowerSeries.derivative_exp]

end

end Representation
