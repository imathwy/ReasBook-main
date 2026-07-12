import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

/-
Exercise 11.2.5 is `source-facing`: it compares the textbook pathwise properties usually denoted
`C`, `A⁺`, `A⁻`, and `F` for a real-valued martingale. Here the primitive data are only the
martingale `X` and the bounded-difference hypothesis. The `core/canonical` owner for the fourth
event is the chapter square-variation process `⟨X⟩[ℱ, μ]`, while formula-level identities such as
Theorem 10.4 are only `bridge/view` statements. The public theorem below therefore keeps the
owner event itself in the fourth clause instead of a parallel increment-sum presentation.
-/

-- Proof sketch: apply the canonical martingale Borel-Cantelli comparison between pathwise upper
-- and lower boundedness and convergence for bounded-difference martingales. The fourth clause is
-- stated directly in the owner shape from Chapter 10, so no parallel local square-variation API
-- survives in the public statement.
/-- Exercise 11.2.5: for a real-valued martingale with bounded differences, the textbook events
`C`, `A^+`, `A^-`, and `F` are almost surely equivalent. Equivalently, for almost every sample
point, the following are equivalent: the path converges in `ℝ`, its values are bounded above, its
values are bounded below, and the canonical square variation `n ↦ ⟨X⟩[ℱ, μ] n` is bounded above.
-/
theorem martingale_convergence_tfae_of_bdd_difference
    [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      List.TFAE [
        ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c),
        BddAbove (Set.range fun n ↦ X n ω),
        BddBelow (Set.range fun n ↦ X n ω),
        BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω)
      ] := sorry

end
