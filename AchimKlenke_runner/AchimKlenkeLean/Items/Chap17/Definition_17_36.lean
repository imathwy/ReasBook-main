import AchimKlenkeLean.Items.Chap17.Definition_17_33
import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/-
Layering for Definition 17.36:
- `IsIrreducibleMarkovChain` and `IsWeaklyIrreducibleMarkovChain` remain the source-facing
  Chapter 17 positivity predicates for `F[P, X]`.
- `Kernel.IsIrreducible (Measure.count) _` is the core/canonical owner notion for discrete kernels;
  its `n = 0` case explains why off-diagonal communication is often the right bridge formulation.
- `greenFunctionFrom` is the owner abstraction for positive-time visit counts; its `N = 1`
  specialization is used only in the realization-scoped bridge theorem below.
-/

/-- Definition 17.36: a discrete Markov chain is irreducible if every state `y` is reached from
every starting state `x` with strictly positive ever-hit probability `F(x,y)`. -/
def IsIrreducibleMarkovChain (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x y : E, 0 < (F[P, X]) x y

/-- A discrete Markov chain is weakly irreducible if for every pair of states at least one of the
two directed ever-hit probabilities is strictly positive. -/
def IsWeaklyIrreducibleMarkovChain
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x y : E, 0 < (F[P, X]) x y + (F[P, X]) y x

section MeasurableState

variable [MeasurableSpace E] [MeasurableSingletonClass E]

-- Proof sketch: under the realization semantics, off-diagonal communication is the kernel-style
-- notion; convert it pointwise to `G[P, X; 1]` via
-- `greenFunctionFrom_one_pos_iff_everHitsProbability_pos`.
/-- Auxiliary bridge: for a measurable Markov-process realization started from its initial state,
the source-facing irreducibility predicate is equivalent to strict positivity of the positive-time
Green function `G[P, X; 1] x y` on off-diagonal pairs. -/
theorem isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
    {κ : ℕ → Kernel E E} (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization κ P X] :
    IsIrreducibleMarkovChain P X ↔
      ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y := sorry

end MeasurableState

-- Proof sketch: if every directed ever-hit probability is positive, then for each pair `(x, y)`
-- the sum `F(x,y) + F(y,x)` is positive as well.
/-- Every irreducible Markov chain is weakly irreducible. -/
theorem isWeaklyIrreducibleMarkovChain_of_isIrreducibleMarkovChain
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (h : IsIrreducibleMarkovChain P X) :
    IsWeaklyIrreducibleMarkovChain P X := sorry

end ProbabilityTheory
