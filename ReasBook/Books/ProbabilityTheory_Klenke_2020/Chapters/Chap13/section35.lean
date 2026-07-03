

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_13_35 (from Items/Chap13) -/
open Filter MeasureTheory Set Topology

universe u

namespace MeasureTheory
namespace FiniteMeasure

section

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
  [LocallyCompactSpace E] [PolishSpace E]

-- Proof sketch: reduce finite measures to subprobabilities by normalizing total mass, apply the
-- locally compact Polish vague-convergence clauses in
-- `FiniteMeasure.portmanteau_subprobability_tfae`, and use Prokhorov tightness for the final
-- tightness formulation.
/-- Theorem 13.35: for finite measures on a locally compact Polish space, weak convergence is
equivalent to vague convergence together with either convergence of total masses, one-sided limsup
mass control, or tightness of the sequence. -/
theorem weak_vague_mass_tight_tfae (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) :
    List.TFAE
      [ Tendsto μs atTop (𝓝 μ)
      , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
          Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)
      , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
          limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass
      , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
          IsTightMeasureSet (Set.range fun n ↦ (μs n : Measure E))
      ] := sorry

end

end FiniteMeasure
end MeasureTheory
