import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The first-moment map on probability measures supported on a finite alphabet `α`, computed from
the coordinate realization `v : α → Fin d → ℝ`. -/
def finiteAlphabetFirstMoment {d : ℕ} [Fintype α]
    (v : α → Fin d → ℝ) (ν : ProbabilityMeasure α) :
    Fin d → ℝ :=
  fun i ↦ ∑ a, ((ν {a} : NNReal) : ℝ) * v a i

/-- The fiber of the first-moment map above the vector `x`. -/
def finiteAlphabetMomentFiber {d : ℕ} [Fintype α]
    (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    Set (ProbabilityMeasure α) :=
  {ν | finiteAlphabetFirstMoment v ν = x}

/-- The contraction rate obtained from Sanov's theorem by minimizing relative entropy over all
probability measures on `α` with prescribed first moment `x`. -/
def finiteAlphabetSanovRateFunction {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) : ENNReal :=
  sInf ((fun ν : ProbabilityMeasure α ↦
    InformationTheory.klDiv (ν : Measure α) (μ : Measure α)) '' finiteAlphabetMomentFiber v x)

/-- The logarithmic moment generating function `Λ` of a finite-alphabet law `μ` pushed forward by
the coordinate realization `v`. -/
def finiteAlphabetLogMomentGeneratingFunction {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (t : Fin d → ℝ) : ℝ :=
  Real.log <| ∑ a, ((μ {a} : NNReal) : ℝ) * Real.exp (∑ i, t i * v a i)

/-- The Legendre-transform rate function `Λ*` attached to the finite-alphabet law `μ`. -/
def finiteAlphabetLegendreRateFunction {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) : ENNReal :=
  ((sSup (Set.range fun t : Fin d → ℝ ↦
    (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) : EReal)))).toENNReal

-- Proof sketch: unfold `finiteAlphabetLegendreRateFunction`; the right-hand side is exactly the
-- Legendre-transform supremum defining `Λ*`, viewed in `ENNReal`.
/-- Expanding `finiteAlphabetLegendreRateFunction μ v x` gives the Legendre-transform supremum of
`⟨t, x⟩ - Λ(t)` over all `t ∈ ℝ^d`, encoded as `Fin d → ℝ`. -/
theorem finiteAlphabetLegendreRateFunction_def {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    finiteAlphabetLegendreRateFunction μ v x =
      ((sSup
        (Set.range fun t : Fin d → ℝ ↦
          (((∑ i, t i * x i) - finiteAlphabetLogMomentGeneratingFunction μ v t : ℝ) :
            EReal)))).toENNReal := sorry

/-- The `0`-based partial sum of the vectors `v (X 0), …, v (X n)`. -/
def finiteAlphabetPartialSum {d : ℕ}
    (v : α → Fin d → ℝ) (X : ℕ → Ω → α) (n : ℕ) : Ω → Fin d → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range (n + 1), v (X i ω)

/-- The empirical mean of the first `n + 1` variables in the chapter's `0`-based indexing. -/
def finiteAlphabetEmpiricalMean {d : ℕ}
    (v : α → Fin d → ℝ) (X : ℕ → Ω → α) (n : ℕ) : Ω → Fin d → ℝ :=
  fun ω ↦ (n + 1 : ℝ)⁻¹ • finiteAlphabetPartialSum v X n ω

-- Proof sketch: unfold `finiteAlphabetEmpiricalMean` and `finiteAlphabetPartialSum`; the result is
-- the displayed normalized finite sum.
/-- Expanding `finiteAlphabetEmpiricalMean v X n` gives the normalized `0`-based partial sum
`(n + 1)⁻¹ ∑_{i=0}^n v (X i)`. -/
theorem finiteAlphabetEmpiricalMean_apply {d : ℕ}
    (v : α → Fin d → ℝ) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    finiteAlphabetEmpiricalMean v X n ω =
      (n + 1 : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), v (X i ω) := sorry

-- Proof sketch: each coordinate `ω ↦ v (X i ω)` is a.e.-measurable because `X i` is; finite sums
-- and scalar multiples preserve a.e.-measurability, giving measurability of the empirical mean.
/-- The empirical mean map of a finite-alphabet sequence is a.e.-measurable under the reference
probability measure. -/
theorem finiteAlphabetEmpiricalMean_aemeasurable {d : ℕ}
    (P : ProbabilityMeasure Ω) (v : α → Fin d → ℝ) (X : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω)) (n : ℕ) :
    AEMeasurable (finiteAlphabetEmpiricalMean v X n) (P : Measure Ω) := sorry

/-- The law of the empirical mean of the first `n + 1` variables. -/
def finiteAlphabetEmpiricalMeanLaw {d : ℕ}
    (P : ProbabilityMeasure Ω) (v : α → Fin d → ℝ) (X : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω)) (n : ℕ) :
    ProbabilityMeasure (Fin d → ℝ) :=
  P.map (finiteAlphabetEmpiricalMean_aemeasurable P v X hXmeas n)

-- Proof sketch: apply Sanov's theorem to the empirical measures of the finite-alphabet sequence,
-- push the resulting LDP forward along the continuous first-moment map, and identify the
-- contraction rate with the Legendre transform `Λ*`.
/-- Example 23.15: let `μ` be a probability measure on a finite alphabet `α`, let `X 0, X 1, …`
be independent `α`-valued random variables with common law `μ`, and let `v : α → Fin d → ℝ`
realize the alphabet as a finite subset of `ℝ^d`. Then the laws of the empirical means of the
vectors `v (X n)` satisfy a large deviations principle at speed `n + 1` with rate function `Λ*`,
the Legendre transform of the finite-alphabet log moment generating function. This is the chapter's
`0`-based version of the book's statement about `S_n / n`. -/
theorem finiteAlphabetEmpiricalMean_hasLargeDeviationsPrinciple {d : ℕ} [Fintype α]
    (P : ProbabilityMeasure Ω) (μ : ProbabilityMeasure α)
    (v : α → Fin d → ℝ) (X : ℕ → Ω → α)
    (hXmeas : ∀ n, AEMeasurable (X n) (P : Measure Ω))
    (hindep : iIndepFun X (P : Measure Ω))
    (hLaw : ∀ n, Measure.map (X n) (P : Measure Ω) = (μ : Measure α)) :
    HasLargeDeviationsPrincipleAlong
      (finiteAlphabetEmpiricalMeanLaw P v X hXmeas)
      (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by positivity⟩)
      atTop
      (finiteAlphabetLegendreRateFunction μ v) := sorry

-- Proof sketch: the contraction rate from Sanov is the infimum of relative entropy over the moment
-- fiber `m⁻¹({x})`; optimize the dual variational problem by exponential tilting and use Jensen's
-- inequality to identify that infimum with the Legendre transform `Λ*`.
/-- The Sanov contraction rate at a prescribed first moment `x` coincides with the
Legendre-transform rate function `Λ*`. -/
theorem finiteAlphabetSanovRateFunction_eq_legendreRateFunction {d : ℕ} [Fintype α]
    (μ : ProbabilityMeasure α) (v : α → Fin d → ℝ) (x : Fin d → ℝ) :
    finiteAlphabetSanovRateFunction μ v x = finiteAlphabetLegendreRateFunction μ v x := sorry

end ProbabilityTheory
