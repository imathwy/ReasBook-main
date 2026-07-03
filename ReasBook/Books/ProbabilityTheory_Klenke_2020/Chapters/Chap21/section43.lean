import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_21_43 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Y : ℕ → Ω → ℝ}

local notation "BrownianPathSpace" => C(NNReal, ℝ)

/-- The Brownian path space `C([0, ∞), ℝ)` carries its Borel `σ`-algebra in this item. -/
local instance brownianPathSpaceMeasurableSpace : MeasurableSpace BrownianPathSpace :=
  borel BrownianPathSpace

/-- The Brownian path space is a Borel space for its compact-open topology. -/
local instance brownianPathSpaceBorelSpace : BorelSpace BrownianPathSpace :=
  ⟨rfl⟩

/-- The normalized linearly interpolated partial-sum path built from the `0`-based increment
sequence `Y 0, Y 1, ...`, corresponding to the textbook process `\bar S^n`. -/
def donskerInterpolatedPathFun
    (Y : ℕ → Ω → ℝ) (variance : ℝ) (n : ℕ) (ω : Ω) : NNReal → ℝ :=
  fun t ↦
    let x : ℝ := (n : ℝ) * (t : ℝ);
    let k : ℕ := Nat.floor x;
    (Real.sqrt ((n : ℝ) * variance))⁻¹ *
      (Finset.sum (Finset.range k) (fun i ↦ Y i ω) + (x - k) * Y k ω)

-- Proof sketch: unfold `donskerInterpolatedPathFun`; the displayed formula is exactly the
-- definition of the linear interpolation between the normalized partial sums at mesh `1 / n`.
/-- Expanding `donskerInterpolatedPathFun` gives the textbook interpolation formula. -/
theorem donskerInterpolatedPathFun_apply
    (Y : ℕ → Ω → ℝ) (variance : ℝ) (n : ℕ) (ω : Ω) (t : NNReal) :
    donskerInterpolatedPathFun Y variance n ω t =
      let x : ℝ := (n : ℝ) * (t : ℝ);
      let k : ℕ := Nat.floor x;
      (Real.sqrt ((n : ℝ) * variance))⁻¹ *
        (Finset.sum (Finset.range k) (fun i ↦ Y i ω) + (x - k) * Y k ω) := sorry

-- Proof sketch: on each interval `[k / n, (k + 1) / n]` the displayed formula is affine in `t`,
-- and the endpoint values of neighboring pieces agree because both recover the same normalized
-- partial sum.
/-- For each sample point `ω`, the interpolated partial-sum formula defines a continuous path. -/
theorem continuous_donskerInterpolatedPathFun
    (Y : ℕ → Ω → ℝ) (variance : ℝ) (n : ℕ) (ω : Ω) :
    Continuous (donskerInterpolatedPathFun Y variance n ω) := sorry

/-- The path-valued random variable on `C([0, ∞), ℝ)` corresponding to the normalized linearly
interpolated partial sums. -/
def donskerInterpolatedPath
    (Y : ℕ → Ω → ℝ) (variance : ℝ) (n : ℕ) : Ω → BrownianPathSpace :=
  fun ω ↦ ⟨donskerInterpolatedPathFun Y variance n ω, continuous_donskerInterpolatedPathFun Y variance n ω⟩

-- Proof sketch: `donskerInterpolatedPath` is defined by packaging
-- `donskerInterpolatedPathFun Y variance n ω` with its continuity theorem.
/-- Evaluating the path-valued interpolation at time `t` recovers the scalar interpolation
formula. -/
theorem donskerInterpolatedPath_apply
    (Y : ℕ → Ω → ℝ) (variance : ℝ) (n : ℕ) (ω : Ω) (t : NNReal) :
    donskerInterpolatedPath Y variance n ω t = donskerInterpolatedPathFun Y variance n ω t := sorry

-- Proof sketch: measurability of the path-valued map follows from coordinate measurability on the
-- Borel path space, using Theorem 21.31 to identify the coordinate-generated `σ`-algebra with the
-- Borel `σ`-algebra on `C([0, ∞), ℝ)`.
/-- The normalized interpolated partial-sum path is almost everywhere measurable as a
Brownian-path-valued random variable. -/
theorem aemeasurable_donskerInterpolatedPath
    (hY_meas : ∀ k : ℕ, AEMeasurable (Y k) P) (variance : ℝ) (n : ℕ) :
    AEMeasurable (donskerInterpolatedPath Y variance n) P := sorry

/-- The probability law of the normalized linearly interpolated partial-sum path. -/
def donskerInterpolatedPathLaw
    (Y : ℕ → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (variance : ℝ) (hY_meas : ∀ k : ℕ, AEMeasurable (Y k) P) (n : ℕ) :
    ProbabilityMeasure BrownianPathSpace :=
  ProbabilityMeasure.map ⟨P, inferInstance⟩
    (aemeasurable_donskerInterpolatedPath hY_meas variance n)

-- Proof sketch: unfold `donskerInterpolatedPathLaw`; it is the pushforward of `P` by the
-- Brownian-path-valued random variable `donskerInterpolatedPath Y variance n`.
/-- Coercing the interpolated path law to a measure gives the corresponding pushforward measure. -/
theorem donskerInterpolatedPathLaw_toMeasure
    (hY_meas : ∀ k : ℕ, AEMeasurable (Y k) P) (variance : ℝ) (n : ℕ) :
    (donskerInterpolatedPathLaw Y P variance hY_meas n : Measure BrownianPathSpace) =
      P.map (donskerInterpolatedPath Y variance n) := sorry

-- Proof sketch: use Theorem 21.38 to reduce weak convergence on path space to finite-dimensional
-- convergence plus tightness, obtain the finite-dimensional convergence from the preceding
-- chapter results, and verify tightness by the Kolmogorov criterion after truncating the
-- increments as in the textbook proof.
/-- Theorem 21.43: Donsker's theorem. If `Y 0, Y 1, ...` are iid centered real random variables
with positive variance under `P`, then the laws of the normalized linearly interpolated partial-sum
paths converge weakly on `C([0, ∞), ℝ)` to any Brownian path law `μW` started from `0`. -/
theorem donskerInterpolatedPathLaw_tendsto_brownianPathLaw
    (μW : ProbabilityMeasure BrownianPathSpace)
    (hWstart :
      (μW : Measure BrownianPathSpace) ((fun ω : BrownianPathSpace ↦ ω 0) ⁻¹' {(0 : ℝ)}) = 1)
    (hWindep :
      HasIndepIncrements (fun t (ω : BrownianPathSpace) ↦ ω t)
        (μW : Measure BrownianPathSpace))
    (hWstationary :
      ∀ r s t : NNReal,
        IdentDistrib
          (fun ω : BrownianPathSpace ↦ ω ((s + t) + r) - ω (t + r))
          (fun ω : BrownianPathSpace ↦ ω (s + r) - ω r)
          (μW : Measure BrownianPathSpace) (μW : Measure BrownianPathSpace))
    (hWgaussian :
      ∀ ⦃t : NNReal⦄, 0 < t →
        HasLaw (fun ω : BrownianPathSpace ↦ ω t) (gaussianReal 0 t)
          (μW : Measure BrownianPathSpace))
    (hY_meas : ∀ k : ℕ, AEMeasurable (Y k) P)
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ k : ℕ, IdentDistrib (Y k) (Y 0) P P)
    (hmean : ∫ ω, Y 0 ω ∂P = 0)
    (hvar : 0 < Var[Y 0; P]) :
    Tendsto
      (fun n ↦ donskerInterpolatedPathLaw Y P (Var[Y 0; P]) hY_meas n)
      atTop
      (𝓝 μW) := sorry

end ProbabilityTheory
