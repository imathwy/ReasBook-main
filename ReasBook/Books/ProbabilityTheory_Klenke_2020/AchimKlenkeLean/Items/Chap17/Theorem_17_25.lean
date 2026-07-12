import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_23
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- A kernel family `κ` has generator matrix `q` if each singleton transition probability has
right derivative `q x y` at time `0`, measured relative to the time-zero row `κ 0 x`. For a
Markov semigroup, this is exactly the discrete-state Q-matrix derivative condition at `t = 0`
because `κ 0 = Kernel.id`. -/
def HasGeneratorMatrix (κ : NNReal → Kernel E E) (q : E → E → ℝ) : Prop :=
  ∀ x y : E,
    Filter.Tendsto
      (fun t : NNReal ↦ ((((κ t) x).real {y}) - (((κ 0) x).real {y})) / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (nhds (q x y))

-- Proof sketch: this is just the defining right-derivative condition for the singleton transition
-- probabilities, unpacked from `HasGeneratorMatrix`.
/-- Unfolding `HasGeneratorMatrix` gives the pointwise right-derivative formula for singleton
transition probabilities, relative to the time-zero row. -/
theorem hasGeneratorMatrix_iff
    (κ : NNReal → Kernel E E) (q : E → E → ℝ) :
    HasGeneratorMatrix κ q ↔
      ∀ x y : E,
        Filter.Tendsto
          (fun t : NNReal ↦ ((((κ t) x).real {y}) - (((κ 0) x).real {y})) / (t : ℝ))
          (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (nhds (q x y)) :=
  Iff.rfl

section

variable [DiscreteMeasurableSpace E]
variable (q : E → E → ℝ)

-- Proof sketch: use the bounded diagonal hypothesis to choose a uniform jump rate `λ`, build the
-- discrete-time stochastic matrix `p = q / λ + I`, realize the chain with transition matrix `p`,
-- Poissonize it to obtain a continuous-time semigroup, and then show uniqueness by the forward
-- equation together with a Gronwall-type contraction estimate.
/-- Theorem 17.25: if `q` is a Q-matrix on the discrete state space `E` and its diagonal entries
are uniformly bounded in absolute value, then there exists a unique Markov semigroup `κ` whose
generator matrix is `q`. Equivalently, `q` is the Q-matrix of a unique continuous-time Markov
process, up to the transition semigroup and hence up to finite-dimensional distributions. -/
theorem existsUnique_markovSemigroup_of_bounded_qMatrix
    (hq : IsQMatrix q)
    (hbounded : BddAbove (Set.range fun x : E ↦ |q x x|))
    :
    ∃! κ : NNReal → Kernel E E, IsMarkovSemigroup κ ∧ HasGeneratorMatrix κ q := sorry

-- Proof sketch: obtain the unique semigroup `κ` from
-- `existsUnique_markovSemigroup_of_bounded_qMatrix`, then apply
-- `exists_markovProcessRealization_of_markovSemigroup` to realize `κ` by a Markov process on a
-- path space.
variable [StandardBorelSpace E]

/-- A bounded Q-matrix admits a realization by a continuous-time Markov process whose transition
semigroup has generator matrix `q`. -/
theorem exists_markovProcessRealization_of_bounded_qMatrix
    (hq : IsQMatrix q)
    (hbounded : BddAbove (Set.range fun x : E ↦ |q x x|))
    :
    ∃ κ : NNReal → Kernel E E,
      HasGeneratorMatrix κ q ∧
        ∃ (Ω' : Type v), ∃ _ : MeasurableSpace Ω', ∃ X : NNReal → Ω' → E,
          ∃ P : E → ProbabilityMeasure Ω', IsMarkovProcessRealization κ P X := sorry

end

end ProbabilityTheory
