import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_6
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

/- Example 17.5 is `source-facing`: it identifies the path-space law of an i.i.d.-increment walk
and the Markov property of the canonical coordinate process under that law. The relevant
`core/canonical` owner in this chapter is `HasNaturalMarkovProperty` for the canonical process on
path space. The primitive data here is the random-walk path map and its pushforward law; the
natural filtration and coordinate measurability are derived from the owner abstraction, so the file
does not keep parallel wrapper lemmas for those pieces. -/

/-- The partial-sum path of the `ℝ^d`-valued increment sequence `Y`, started at the point `x`.
At time `n`, this path is `x + ∑_{i < n} Y_i`. -/
def randomWalkPath (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ) : Ω → ℕ → Fin d → ℝ :=
  fun ω n ↦ x + Finset.sum (Finset.range n) (fun i ↦ Y i ω)

-- Proof sketch: use measurability of each increment coordinate `Y n`, then assemble the finite
-- partial sums coordinatewise and finally apply measurability into the product space on
-- `(ℕ → Fin d → ℝ)`.
/-- The partial-sum path map associated with a measurable increment sequence is almost everywhere
measurable as a random element of path space. -/
theorem aemeasurable_randomWalkPath (P : ProbabilityMeasure Ω)
    (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) :
    AEMeasurable (randomWalkPath x Y) P := sorry

/-- The path-space law of the random walk with starting point `x`, obtained by pushing the
underlying probability measure forward along the partial-sum path map. -/
def randomWalkLaw (P : ProbabilityMeasure Ω)
    (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) : ProbabilityMeasure (ℕ → Fin d → ℝ) :=
  P.map (aemeasurable_randomWalkPath P x Y hY_meas)

-- Proof sketch: identify `randomWalkLaw P x Y hY_meas` with the pushforward law of the i.i.d.
-- increment sequence under the partial-sum map. Then verify the one-step transition law depends
-- only on the present coordinate, so the coordinate process satisfies the chapter owner
-- abstraction `HasNaturalMarkovProperty`.
/-- Example 17.5: if `Y` is an i.i.d. sequence of `ℝ^d`-valued random variables under `P`, then
for every starting point `x` the canonical process on path space, under the pushforward law
`randomWalkLaw P x Y hY_meas`, has the Markov property with respect to its natural filtration.
This is the random walk on `ℝ^d` with initial value `x`; in Lean indexing, the textbook increments
`Y₁, Y₂, ...` are encoded by `Y 0, Y 1, ...`. -/
theorem canonicalProcess_hasNaturalMarkovProperty_randomWalkLaw
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n))
    (hY_indep : iIndepFun Y (P : Measure Ω))
    (hY_ident : ∀ n : ℕ, IdentDistrib (Y n) (Y 0) (P : Measure Ω) (P : Measure Ω))
    (x : Fin d → ℝ) :
    HasNaturalMarkovProperty
      (randomWalkLaw P x Y hY_meas : Measure (ℕ → Fin d → ℝ))
      (Function.eval : ℕ → (ℕ → Fin d → ℝ) → Fin d → ℝ) := sorry

end ProbabilityTheory
