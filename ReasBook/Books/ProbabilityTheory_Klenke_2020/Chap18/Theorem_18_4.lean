import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_1

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- A family `C : ZMod d → Set E` is a cyclic class decomposition for the period-`d` discrete
Markov kernel `p` when the textbook classes `E_i = C i` are nonempty, pairwise disjoint, cover
the whole state space, and one-step transitions move from class `i` to class `i + 1`. -/
def IsPeriodicClassFamily (p : Kernel E E) {d : ℕ+} (C : ZMod d → Set E) : Prop :=
  (∀ i : ZMod d, (C i).Nonempty) ∧
    Pairwise fun i j ↦ Disjoint (C i) (C j) ∧
    (⋃ i, C i) = Set.univ ∧
    ∀ ⦃x y : E⦄ ⦃i : ZMod d⦄, (p x) {y} > 0 → x ∈ C i → y ∈ C (i + 1)

section

variable (p : Kernel E E) [IsMarkovKernel p]
variable [Kernel.IsIrreducible (Measure.count : Measure E) p]

-- Proof sketch: choose a reference state `x₀`, define `E_i` by the congruence class modulo `d`
-- of the length of a path from `x₀` to `x`, and use irreducibility together with the period
-- condition to show that this is well defined, covers all states, and is advanced by one-step
-- transitions.
/-- Theorem 18.4 (1): if a discrete Markov kernel on a nonempty discrete state space is
irreducible and has period `d`, then its state space admits a cyclic decomposition into `d`
pairwise disjoint classes that are advanced by one-step transitions. -/
theorem exists_periodicClassDecomposition
    [Nonempty E] (d : ℕ+) (hperiod : HasPeriod p d) :
    ∃ C : ZMod d → Set E, IsPeriodicClassFamily p C := sorry

-- Proof sketch: fix one state and compare any two decompositions by the class containing that
-- state. Irreducibility forces every other state to lie in the class predicted by the path length
-- modulo `d`, so the two decompositions can differ only by one global cyclic shift.
/-- Theorem 18.4 (2): for an irreducible discrete Markov kernel, any two cyclic decompositions of
the state space indexed by `ZMod d` differ by a cyclic permutation of the class labels. -/
theorem periodicClassDecomposition_unique_up_to_cyclicShift
    (d : ℕ+) (C₁ C₂ : ZMod d → Set E)
    (hC₁ : IsPeriodicClassFamily p C₁) (hC₂ : IsPeriodicClassFamily p C₂) :
    ∃ k : ZMod d, ∀ i : ZMod d, C₁ i = C₂ (i + k) := sorry

end

end ProbabilityTheory
