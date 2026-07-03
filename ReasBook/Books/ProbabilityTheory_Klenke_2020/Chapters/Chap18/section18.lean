

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_18_18 (from Items/Chap18) -/
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- The neighbor-interaction sum
`∑_{j : j ∼ i} (1_{x(j) ≠ σ} - 1 / 2)` appearing in the single-site Ising conditional law. -/
def isingNeighborBias (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) : ℝ :=
  ∑ j, if G.Adj i j then ((if x j ≠ σ then (1 : ℝ) else 0) - (1 / 2 : ℝ)) else 0

/-- The single-site conditional probability of resetting the spin at `i` to `σ` in the finite
Ising model with inverse temperature `β`. -/
def isingConditionalProbability (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) : ℝ :=
  (1 + Real.exp (2 * β * isingNeighborBias G x i σ))⁻¹

omit [DecidableEq Λ] in
/-- The single-site Ising conditional law is the logistic expression determined by the neighboring
spins. -/
theorem isingConditionalProbability_eq_logistic
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) :
    isingConditionalProbability β G x i σ =
      (1 + Real.exp (2 * β * ∑ j, if G.Adj i j then
        ((if x j ≠ σ then (1 : ℝ) else 0) - (1 / 2 : ℝ)) else 0))⁻¹ :=
  rfl

private def positiveIsingSpin : ising_spin :=
  ⟨1, by decide⟩

omit [DecidableEq Λ] in
private theorem isingBoltzmannPMF_tsum_ne_zero
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) :
    (∑' x : ising_configuration Λ, ising_boltzmann_weight G β x) ≠ 0 := by
  classical
  let x : ising_configuration Λ := fun _ ↦ positiveIsingSpin
  have hx : ising_boltzmann_weight G β x ≠ 0 := by
    simp [ising_boltzmann_weight, ENNReal.ofReal_eq_zero, Real.exp_pos]
  have hle : ising_boltzmann_weight G β x ≤
      ∑' y : ising_configuration Λ, ising_boltzmann_weight G β y := by
    simpa [tsum_fintype] using
      Finset.single_le_sum (fun y hy ↦ bot_le) (Finset.mem_univ x)
  intro hsum
  exact hx (le_antisymm (hsum ▸ hle) bot_le)

omit [DecidableEq Λ] in
private theorem isingBoltzmannPMF_tsum_ne_top
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) :
    (∑' x : ising_configuration Λ, ising_boltzmann_weight G β x) ≠ ∞ := by
  classical
  simpa [tsum_fintype] using
    (ENNReal.sum_ne_top.2 fun x hx ↦ by simp [ising_boltzmann_weight] :
      ∑ x ∈ (Finset.univ : Finset (ising_configuration Λ)), ising_boltzmann_weight G β x ≠
        ∞)

/-- The finite Ising Boltzmann distribution at inverse temperature `β`, obtained by normalizing
the Boltzmann weight `x ↦ exp (-β H(x))`. -/
def isingBoltzmannPMF
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) : PMF (ising_configuration Λ) :=
  PMF.normalize (ising_boltzmann_weight G β)
    (isingBoltzmannPMF_tsum_ne_zero G β)
    (isingBoltzmannPMF_tsum_ne_top G β)

section GibbsSampler

variable [Nonempty Λ]
variable (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]

omit [Nonempty Λ] [DecidableEq Λ] in
private theorem isingBoltzmannPMF_apply_ne_zero (x : ising_configuration Λ) :
    isingBoltzmannPMF G β x ≠ 0 := by
  rw [isingBoltzmannPMF, PMF.normalize_apply]
  refine mul_ne_zero ?_ ?_
  · simp [ising_boltzmann_weight, ENNReal.ofReal_eq_zero, Real.exp_pos]
  · simp [ENNReal.inv_eq_zero, isingBoltzmannPMF_tsum_ne_top G β]

omit [Nonempty Λ] [DecidableEq Λ] in
private theorem isingBoltzmannPMF_hasPositiveGibbsCoordinateMarginals :
    HasPositiveGibbsCoordinateMarginals (isingBoltzmannPMF G β) := by
  apply hasPositiveGibbsCoordinateMarginals_of_apply_ne_zero
  intro x
  exact isingBoltzmannPMF_apply_ne_zero β G x

/- Example 18.18: the finite Ising Gibbs sampler is the Chapter 18 Gibbs sampler specialized to
the Ising Boltzmann distribution and the uniform site law on `Λ`. -/
#check (gibbsSamplerMatrix
  (PMF.uniformOfFintype Λ)
  (isingBoltzmannPMF G β) :
  ising_configuration Λ → ising_configuration Λ → ℝ≥0∞)

-- Proof sketch: rewrite with `gibbsSamplerMatrix_apply`, use that `PMF.uniformOfFintype Λ` gives
-- mass `(card Λ)⁻¹` to each site, and simplify the resulting single-site Gibbs ratio to the
-- logistic conditional law using positivity of the Ising Boltzmann weights.
/-- Evaluating the Ising specialization of `gibbsSamplerMatrix` reproduces the site-averaged
single-site conditional-probability formula. -/
theorem isingGibbsTransitionMatrix_apply
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x y : ising_configuration Λ) :
    gibbsSamplerMatrix
        (PMF.uniformOfFintype Λ)
        (isingBoltzmannPMF G β)
        x y =
      (Fintype.card Λ : ℝ≥0∞)⁻¹ *
        ∑ i : Λ,
          if y = gibbsCoordinateReplace x i (y i) then
            ENNReal.ofReal (isingConditionalProbability β G x i (y i))
          else
            0 := sorry

end GibbsSampler

end ProbabilityTheory
