import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Definition_15_40
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

open RealRandomVariableArray

/-- The three-point law of the rare jump variable `Z_{n+1}`: it is `0` with probability
`1 - (n + 1)⁻²` and takes the values `± (n + 1)` with probability `(2 (n + 1)²)⁻¹` each. -/
def rareJumpLaw (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
    ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ) +
      ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (-(n + 1 : ℝ))

/-- The rare-jump law is the sum of the Dirac masses at `0` and `± (n + 1)` with the stated
weights. -/
theorem rareJumpLaw_def (n : ℕ) :
    rareJumpLaw n =
      ENNReal.ofReal (1 - 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) • Measure.dirac 0 +
        ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) • Measure.dirac (n + 1 : ℝ) +
          ENNReal.ofReal (1 / (2 * ((n + 1 : ℝ) ^ (2 : ℕ)))) •
            Measure.dirac (-(n + 1 : ℝ)) :=
  rfl

section RareJumpPerturbedArray

variable (Y Z : ℕ → Ω → ℝ)
variable (hY_meas : ∀ n, Measurable (Y n)) (hZ_meas : ∀ n, Measurable (Z n))

/- Exercise 15.5.2 is `source-facing`: it studies the perturbed normalized sums
`n^{-1/2} ∑_{k < n} (Y_k + Z_k)`. The chapter's `core/canonical` owner for rowwise CLT and
Lindeberg data is `RealRandomVariableArray Ω`; the array below is the `bridge/view` packaging of
those source sums as row sums of an owner object. -/
/-- The `n`-th row consists of the first `n` perturbed summands `Y_k + Z_k`, each scaled by
`(√n)⁻¹`, so its row sum is the normalized textbook sum `n^{-1/2} ∑_{k < n} (Y_k + Z_k)`. -/
def rareJumpPerturbedStandardizedArray : RealRandomVariableArray Ω where
  rowLength n := n
  entry n i ω := (Y i.1 ω + Z i.1 ω) / Real.sqrt (n : ℝ)
  measurable_entry n i := by
    simpa using ((hY_meas i.1).add (hZ_meas i.1)).div_const (Real.sqrt (n : ℝ))

/-- The entries of the rare-jump perturbed standardized array are the scaled perturbed summands. -/
theorem rareJumpPerturbedStandardizedArray_apply (n : ℕ) (i : Fin n) (ω : Ω) :
    rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas n i ω =
      (Y i.1 ω + Z i.1 ω) / Real.sqrt (n : ℝ) :=
  rfl

/-- The entries of the rare-jump perturbed standardized array are measurable. -/
theorem measurable_rareJumpPerturbedStandardizedArray_entry (n : ℕ) (i : Fin n) :
    Measurable (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas n i) :=
  (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).measurable_entry n i

end RareJumpPerturbedArray

-- Proof sketch: the source hypotheses require not only that `Y` is i.i.d., but also that the
-- perturbation sequence `Z` is independent and independent of the whole sequence `Y`. The
-- rare-jump law `rareJumpLaw n` gives `∑ n, P[Z n ≠ 0] < ∞`, so Borel--Cantelli yields only
-- finitely many nonzero jumps almost surely. Hence the perturbation is asymptotically negligible
-- after dividing by `√n`, the row sums still converge weakly to the standard Gaussian law by the
-- iid CLT for `Y` and Slutsky, and the exceptional summands still violate the chapter-owner
-- Lindeberg condition.
/-- Exercise 15.5.2: for a `0`-based Lean model of the textbook sequences `Y₁, Y₂, ...` and
`Z₁, Z₂, ...`, the laws of the row sums of
`rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas`, equivalently of the normalized sums
`n^{-1/2} ∑_{k < n} (Y_k + Z_k)`, converge weakly to the standard Gaussian law `𝒩(0, 1)` when
`Y` is i.i.d., the perturbations `Z_k` are independent with laws `rareJumpLaw k`, and `Z` is
independent of the whole sequence `Y`; but the associated standardized array does not satisfy the
chapter-owner Lindeberg condition. -/
theorem rareLargeJumps_clt_but_not_lindeberg
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : ℕ → Ω → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hZ_meas : ∀ n, Measurable (Z n))
    (hY_iid : IsIID Y P)
    (hZ_indep : iIndepFun Z P)
    (hYZ_indep : IndepFun (fun ω ↦ fun n : ℕ ↦ Y n ω) (fun ω ↦ fun n : ℕ ↦ Z n ω) P)
    (hY_mean : P[Y 0] = 0)
    (hY_var : Var[Y 0; P] = 1)
    (hZ_law : ∀ n, HasLaw (Z n) (rareJumpLaw n) P) :
    Tendsto
      (fun n ↦ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).rowSumLaw P n)
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) ∧
    ¬ (rareJumpPerturbedStandardizedArray Y Z hY_meas hZ_meas).SatisfiesLindebergCondition P :=
  sorry

end
