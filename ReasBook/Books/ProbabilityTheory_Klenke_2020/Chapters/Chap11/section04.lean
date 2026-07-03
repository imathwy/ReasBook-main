import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_11_4 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsFiniteMeasure μ]

/- Theorem 11.4 is `source-facing`: its hypothesis is the textbook boundedness of the positive
parts. The `core/canonical` owner layer is the `Submartingale` API for `ℱ.limitProcess`. The only
local `bridge/view` needed here is the passage from bounded positive-part expectations to the
owner hypothesis `∀ n, eLpNorm (X n) 1 μ ≤ R`. -/

-- Proof sketch: bounded positive-part expectations and monotonicity of submartingale expectations
-- give a uniform `L¹` bound on `X`, which is exactly the owner input for the canonical
-- `limitProcess` convergence and integrability theorems.
private theorem submartingale_eLpNorm_one_bounded_of_bdd_pos_part {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (Set.range fun n ↦ μ[fun ω ↦ (X n ω)⁺])) :
    ∃ R : NNReal, ∀ n, eLpNorm (X n) 1 μ ≤ R := sorry

/-- Theorem 11.4: if a real-valued discrete submartingale has uniformly bounded expectations of
its positive parts, then its canonical limit process is integrable and the submartingale converges
to it almost surely. -/
theorem submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (Set.range fun n ↦ μ[fun ω ↦ (X n ω)⁺])) :
    Integrable (ℱ.limitProcess X μ) μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω)) := by
  obtain ⟨R, hR⟩ := submartingale_eLpNorm_one_bounded_of_bdd_pos_part hX hpos
  refine ⟨(hX.memLp_limitProcess hR).integrable le_rfl, hX.ae_tendsto_limitProcess hR⟩

-- Proof sketch: the canonical limit object in the previous theorem is `ℱ.limitProcess X μ`; its
-- `⨆ n, ℱ n`-strong measurability is exactly the owner-level `limitProcess` regularity theorem,
-- so no local wrapper is needed here.
/- The canonical limit process of an `L¹`-bounded submartingale is measurable with respect to the
terminal σ-algebra `⨆ n, ℱ n`; the project uses the stronger owner declaration asserting
`StronglyMeasurable[⨆ n, ℱ n]`. -/
recall MeasureTheory.Filtration.stronglyMeasurable_limitProcess
