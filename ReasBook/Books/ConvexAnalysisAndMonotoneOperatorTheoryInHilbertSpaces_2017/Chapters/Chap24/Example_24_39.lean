import Mathlib
import BauschkeLean.Chap09.Example_9_36
import BauschkeLean.Chap09.Example_9_41
import BauschkeLean.Chap13.Example_13_2
import BauschkeLean.Chap16.Proposition_16_37
import BauschkeLean.Chap17.Proposition_17_32
import BauschkeLean.Chap24.Proposition_24_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

noncomputable section

open Real

private theorem negativeBoltzmannShannonEntropy_eq_boltzmannEntropy_asEReal :
    negativeBoltzmannShannonEntropy = boltzmannEntropy.asEReal := by
  funext u
  by_cases hu : 0 < u
  · simp [negativeBoltzmannShannonEntropy, boltzmannEntropy, hu]
  · by_cases h0 : u = 0
    · simp [negativeBoltzmannShannonEntropy, boltzmannEntropy, h0]
    · simp [negativeBoltzmannShannonEntropy, boltzmannEntropy, hu, h0]

private theorem exp_subdifferential_eq_singleton (x : ℝ) :
    (∂ exp.toEReal) x = ({exp x} : Set ℝ) := by
  rw [scalar_subdifferential_toEReal_eq_singleton_deriv
    exp strictConvexOn_exp.convexOn differentiableAt_exp]
  simp [Real.deriv_exp]

/-- Example 24.39 (1): the negative Boltzmann--Shannon entropy
`φ(ξ) = ξ log ξ - ξ` for `ξ > 0`, `φ(0) = 0`, and `φ(ξ) = +∞` for `ξ < 0`
has Fenchel conjugate `exp`. -/
theorem boltzmannEntropy_conjugate_eq_exp :
    boltzmannEntropy∗[boltzmannEntropy_mem_gammaZero] = exp.toEReal := by
  have hconj_exp :
      exp.toEReal.asEReal∗ = boltzmannEntropy.asEReal := by
    funext u
    rw [conjugate_exp]
    simp [negativeBoltzmannShannonEntropy_eq_boltzmannEntropy_asEReal]
  have hconj_boltz :
      boltzmannEntropy.asEReal∗ = exp.toEReal.asEReal := by
    calc
      boltzmannEntropy.asEReal∗ = exp.toEReal.asEReal∗∗ := by
        simp [hconj_exp]
      _ = exp.toEReal.asEReal := biconjugate_eq_of_mem_gammaZero exp_mem_gammaZero
  funext u
  apply Subtype.ext
  simpa [gammaZeroConjugate_apply] using congrFun hconj_boltz u

private theorem prox_boltzmannEntropy_eq_iff_eq_exp_sub
    (ξ p : ℝ) :
    p = Prox[boltzmannEntropy, boltzmannEntropy_mem_gammaZero] ξ ↔
      p = exp (ξ - p) := by
  constructor
  · intro hp
    have hsub :
        ξ - p ∈ (∂ boltzmannEntropy) p :=
      (eq_proximityOperator_iff_sub_mem_subdifferential
        boltzmannEntropy boltzmannEntropy_mem_gammaZero).1 hp
    have hconj_sub :
        p ∈ (∂ (boltzmannEntropy∗[boltzmannEntropy_mem_gammaZero])) (ξ - p) := by
      rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
        boltzmannEntropy boltzmannEntropy_mem_gammaZero]
      simpa [SetValuedOperator.mem_inverse_iff] using hsub
    rw [boltzmannEntropy_conjugate_eq_exp, exp_subdifferential_eq_singleton] at hconj_sub
    simpa using hconj_sub
  · intro hp
    have hconj_sub :
        p ∈ (∂ (boltzmannEntropy∗[boltzmannEntropy_mem_gammaZero])) (ξ - p) := by
      rw [boltzmannEntropy_conjugate_eq_exp, exp_subdifferential_eq_singleton]
      rw [Set.mem_singleton_iff]
      exact hp
    have hsub :
        ξ - p ∈ (∂ boltzmannEntropy) p :=
      mem_subdifferential_of_mem_subdifferential_gammaZeroConjugate
        boltzmannEntropy boltzmannEntropy_mem_gammaZero hconj_sub
    exact (eq_proximityOperator_iff_sub_mem_subdifferential
      boltzmannEntropy boltzmannEntropy_mem_gammaZero).2 hsub

/-- Example 24.39 (2): for real `ξ` and `p`, the proximal value `p = Prox_φ ξ` is exactly the
positive solution of `p = exp (ξ - p)`; equivalently, `p = W(exp ξ)` when Lambert `W` is
available. -/
theorem prox_boltzmannEntropy_eq_iff_pos_eq_exp_sub
    (ξ p : ℝ) :
    p = Prox[boltzmannEntropy, boltzmannEntropy_mem_gammaZero] ξ ↔
      0 < p ∧ p = exp (ξ - p) := by
  rw [prox_boltzmannEntropy_eq_iff_eq_exp_sub]
  constructor
  · intro hp
    exact ⟨hp.symm ▸ exp_pos (ξ - p), hp⟩
  · rintro ⟨_, hp⟩
    exact hp

/-- Example 24.39 (3): the proximity operator of `exp` is the residual
`ξ - Prox_φ ξ = ξ - W(exp ξ)`. -/
theorem prox_exp_eq_sub_prox_boltzmannEntropy (ξ : ℝ) :
    Prox[exp.toEReal, exp_mem_gammaZero] ξ =
      ξ - Prox[boltzmannEntropy, boltzmannEntropy_mem_gammaZero] ξ := by
  let q := Prox[exp.toEReal, exp_mem_gammaZero] ξ
  have hsub :
      ξ - q ∈ (∂ exp.toEReal) q :=
    (eq_proximityOperator_iff_sub_mem_subdifferential exp.toEReal exp_mem_gammaZero).1 rfl
  rw [exp_subdifferential_eq_singleton] at hsub
  have hboltz :
      ξ - q = Prox[boltzmannEntropy, boltzmannEntropy_mem_gammaZero] ξ :=
    (prox_boltzmannEntropy_eq_iff_eq_exp_sub ξ (ξ - q)).2 <| by simpa using hsub
  calc
    Prox[exp.toEReal, exp_mem_gammaZero] ξ = q := rfl
    _ = ξ - Prox[boltzmannEntropy, boltzmannEntropy_mem_gammaZero] ξ := by
      calc
        q = ξ - (ξ - q) := by abel_nf
        _ = ξ - Prox[boltzmannEntropy, boltzmannEntropy_mem_gammaZero] ξ := by rw [hboltz]

end

end ERealFunction
