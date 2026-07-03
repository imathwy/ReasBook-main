import ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_1
import ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_5
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Example 19.4:
- `source-facing`: `firstEntranceValueFunction`, the boundary-value extension defined from the
  first entrance law.
- `core/canonical`: `MeasureTheory.hittingAfter` for the entrance time, `IsHarmonicOutside` for
  harmonicity, and `SolvesDirichletProblem` for the combined boundary-value package.
- `bridge/view`: the Dirichlet-problem theorem below uses the canonical ambient extension of the
  subtype datum `g : A → ℝ` by `0` off `A`; this does not change the source semantics because the
  owner predicate only records boundary agreement on `A`. -/

/-- The boundary reward obtained by stopping `X` at the canonical first entrance time
`hittingAfter X A 1` and evaluating the boundary datum `g`; it is set to `0` on paths that never
enter `A`. -/
private def firstEntranceReward (X : ℕ → Ω → E) (A : Set E) (g : A → ℝ) : Ω → ℝ :=
  fun ω ↦
    if hτ : hittingAfter X A 1 ω < ⊤ then
      g ⟨stoppedValue X (hittingAfter X A 1) ω, by
        simpa [stoppedValue] using
          (hittingAfter_mem_set_of_ne_top hτ.ne)⟩
    else
      0

/-- The function obtained from boundary data `g` on `A` by taking the expected boundary value at
the first entrance into `A` when the initial state lies outside `A`. -/
def firstEntranceValueFunction (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (A : Set E) (g : A → ℝ) : E → ℝ :=
  fun x ↦
    if hx : x ∈ A then
      g ⟨x, hx⟩
    else
      ∫ ω, firstEntranceReward X A g ω ∂(P x : Measure Ω)

-- Proof sketch: unfold `firstEntranceValueFunction`; on `A` the definition uses the first branch
-- of the `if`, so the boundary-value extension agrees with `g`.
/-- On the boundary set `A`, the first-entrance value function agrees with the prescribed boundary
data. -/
theorem firstEntranceValueFunction_eq_of_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : A → ℝ) {x : E}
    (hx : x ∈ A) :
    firstEntranceValueFunction P X A g x = g ⟨x, hx⟩ := sorry

-- Proof sketch: unfold `firstEntranceValueFunction`; outside `A` the definition uses the
-- expectation of the stopped boundary reward.
/-- Outside `A`, the first-entrance value function is the expected boundary reward at the first
entrance into `A`. -/
theorem firstEntranceValueFunction_eq_of_not_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : A → ℝ) {x : E}
    (hx : x ∉ A) :
    firstEntranceValueFunction P X A g x =
      ∫ ω, firstEntranceReward X A g ω ∂(P x : Measure Ω) := sorry

section

variable {κ : Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ κ ^ n) P X]

-- Proof sketch: apply the Markov property at time `1` and then at the first entrance time into
-- `A` to identify the outside values of `firstEntranceValueFunction` with their one-step kernel
-- averages. The assumption that the first entrance time is almost surely finite from every
-- starting state outside `A`, expressed in the canonical `∀ᵐ` stopping-time form, ensures the
-- stopped boundary reward represents the boundary data seen at the entrance point, and boundedness
-- of `g` on `A` provides the needed integrability.
/-- Example 19.4: if the first entrance time into `A` is almost surely finite from every starting
state outside `A`, and `f` is defined by the boundary data `g` on `A` and by the expected boundary
value at the first entrance into `A` on `E \ A`, then `f` is harmonic on `E \ A`. -/
theorem firstEntranceValueFunction_isHarmonicOutside
    (A : Set E) (g : A → ℝ)
    (hg_bdd : ∃ C : ℝ, ∀ a : A, |g a| ≤ C)
    (hτ : ∀ x : E, x ∉ A → ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω ≠ ⊤) :
    IsHarmonicOutside κ A (firstEntranceValueFunction P X A g) := sorry

-- Proof sketch: combine `firstEntranceValueFunction_isHarmonicOutside` with
-- `firstEntranceValueFunction_eq_of_mem`. The ambient boundary datum is the canonical bridge
-- `x ↦ if hx : x ∈ A then g ⟨x, hx⟩ else 0`, whose values on `A` are definitionally the original
-- subtype datum `g`.
/-- The first-entrance value function solves the Chapter 19 Dirichlet problem for the ambient
boundary extension of `g` obtained by setting the value to `0` off `A`. -/
theorem firstEntranceValueFunction_solvesDirichletProblem
    (A : Set E) (g : A → ℝ)
    (hg_bdd : ∃ C : ℝ, ∀ a : A, |g a| ≤ C)
    (hτ : ∀ x : E, x ∉ A → ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω ≠ ⊤) :
    SolvesDirichletProblem κ A
      (fun x ↦ if hx : x ∈ A then g ⟨x, hx⟩ else 0)
      (firstEntranceValueFunction P X A g) := sorry

end

end ProbabilityTheory
