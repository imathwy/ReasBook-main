import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {τ : Ω → Ω} {X₀ : Ω → ℝ} {p : ℝ≥0∞}

section Lp

variable [Fact (1 ≤ p)]

local notation "ℐ" => MeasurableSpace.invariants τ

/- Theorem 20.16 is `source-facing`: it asserts `L^p(P)` convergence of Birkhoff averages. The
Chapter 7 owner abstraction for this notion is `TendstoInLp`, while raw `eLpNorm` convergence is
only the derived `bridge/view` supplied by `TendstoInLp.tendsto_eLpNorm`. The main public
statements therefore use `TendstoInLp`, and the seminorm formulations remain thin companions. -/

-- Proof sketch: combine the almost-sure convergence from Birkhoff's ergodic theorem with the
-- uniform integrability of the `p`th powers from Lemma 20.15, then apply the Vitali-type
-- `L¹` convergence criterion to the error sequence `|Aₙ - P[X₀ | MeasurableSpace.invariants τ]|^p`.
/-- Theorem 20.16 (1): for a probability-preserving transformation `τ` and a real-valued
`L^p(P)` observable `X₀` with `1 ≤ p < ∞`, the Birkhoff averages of `X₀` along the orbit of `τ`
converge in `L^p(P)` to the conditional expectation of `X₀` onto the invariant σ-algebra
`MeasurableSpace.invariants τ`. -/
theorem birkhoffAverage_tendsto_condExp_invariants
    (hp_top : p ≠ ∞) (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    TendstoInLp p P (fun n ↦ birkhoffAverage ℝ τ X₀ n) P[X₀ | ℐ] := sorry

/-- Bridge companion to Theorem 20.16 (1): the owner-level `L^p` convergence statement rewritten
as convergence of the corresponding `eLpNorm` errors. -/
theorem birkhoffAverage_tendsto_condExp_invariants_eLpNorm
    (hp_top : p ≠ ∞) (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    Tendsto
      (fun n ↦
        eLpNorm (birkhoffAverage ℝ τ X₀ n - P[X₀ | ℐ]) p P)
      atTop (𝓝 0) :=
  (birkhoffAverage_tendsto_condExp_invariants hp_top hτ hX₀).tendsto_eLpNorm

-- Proof sketch: apply the first part and use ergodicity to identify the conditional expectation
-- onto the invariant σ-algebra with the constant function equal to `P[X₀]`.
/-- Theorem 20.16 (2): if `τ` is ergodic, then the same Birkhoff averages converge in `L^p(P)`
to the constant expectation `P[X₀]`. -/
theorem birkhoffAverage_tendsto_expectation_of_ergodic
    (hp_top : p ≠ ∞) (hτ : Ergodic τ P) (hX₀ : MemLp X₀ p P) :
    TendstoInLp p P (fun n ↦ birkhoffAverage ℝ τ X₀ n) (fun _ ↦ P[X₀]) := sorry

/-- Bridge companion to Theorem 20.16 (2): the owner-level `L^p` convergence statement rewritten
as convergence of the corresponding `eLpNorm` errors. -/
theorem birkhoffAverage_tendsto_expectation_of_ergodic_eLpNorm
    (hp_top : p ≠ ∞) (hτ : Ergodic τ P) (hX₀ : MemLp X₀ p P) :
    Tendsto
      (fun n ↦ eLpNorm (birkhoffAverage ℝ τ X₀ n - fun _ ↦ P[X₀]) p P)
      atTop (𝓝 0) :=
  (birkhoffAverage_tendsto_expectation_of_ergodic hp_top hτ hX₀).tendsto_eLpNorm

end Lp
