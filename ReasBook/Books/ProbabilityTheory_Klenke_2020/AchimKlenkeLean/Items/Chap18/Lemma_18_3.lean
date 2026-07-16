import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Definition_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- `HasEventualPeriodResidue κ x y L` means that, from some threshold on, every sufficiently
large integer in the residue class `L` modulo `statePeriod κ x` belongs to the transition-time set
`positiveTransitionStepSet κ x y`. -/
def HasEventualPeriodResidue (κ : Kernel E E) (x y : E) (L : ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, n * statePeriod κ x + L ∈ positiveTransitionStepSet κ x y

-- Proof sketch: this is just the definition of `HasEventualPeriodResidue`.
/-- Unfolding `HasEventualPeriodResidue` gives the threshold after which the whole residue class
lies in `positiveTransitionStepSet κ x y`. -/
theorem hasEventualPeriodResidue_iff (κ : Kernel E E) (x y : E) (L : ℕ) :
    HasEventualPeriodResidue κ x y L ↔
      ∃ n₀ : ℕ, ∀ n ≥ n₀, n * statePeriod κ x + L ∈ positiveTransitionStepSet κ x y := sorry

section

variable (κ : Kernel E E) [IsMarkovKernel κ]
variable [Kernel.IsIrreducible (Measure.count : Measure E) κ]

-- Proof sketch: choose connecting times in `positiveTransitionStepSet κ x y` and
-- `positiveTransitionStepSet κ y x`, compose them with large return multiples at `x` and `y`, and
-- deduce each period divides the other by the same argument as in the textbook proof.
/-- Lemma 18.3 (1): assertion (i), namely that in the irreducible setting all state periods
coincide. -/
theorem statePeriod_eq (x y : E) :
    statePeriod κ x = statePeriod κ y := sorry

-- Proof sketch: pick one time `m ∈ positiveTransitionStepSet κ x y` from irreducibility, divide
-- `m` by the common period, and compose with sufficiently large return multiples at `x` to see
-- that one residue class modulo `statePeriod κ x` eventually lies in
-- `positiveTransitionStepSet κ x y`.
/-- Lemma 18.3 (2): assertion (ii), namely that for every pair of states there is an eventual
residue class modulo the common period describing `positiveTransitionStepSet κ x y`. -/
theorem exists_eventual_period_residue (x y : E) :
    ∃ Lxy : ℕ, Lxy < statePeriod κ x ∧ HasEventualPeriodResidue κ x y Lxy := sorry

-- Proof sketch: if two residues in `{0, ..., statePeriod κ x - 1}` both occur eventually in
-- `positiveTransitionStepSet κ x y`, compose them with an eventual return class from
-- `positiveTransitionStepSet κ y x` and use divisibility by the period to force the two residues
-- to be equal.
/-- Lemma 18.3 (3): the residue from assertion (ii) is uniquely determined in
`{0, ..., statePeriod κ x - 1}`. -/
theorem eventual_period_residue_unique
    {x y : E} {L L' : ℕ}
    (hL_lt : L < statePeriod κ x)
    (hL'_lt : L' < statePeriod κ x)
    (hL : HasEventualPeriodResidue κ x y L)
    (hL' : HasEventualPeriodResidue κ x y L') :
    L = L' := sorry

-- Proof sketch: combine eventual representatives for `(x,y)`, `(y,z)`, and `(z,x)` using kernel
-- composition; the resulting large return times from `x` to itself are divisible by the common
-- period, so the sum of the three residues is `0` modulo that period.
/-- Lemma 18.3 (4): the eventual residues satisfy the cocycle relation
`L_xy + L_yz + L_zx ≡ 0 [MOD d]`. -/
theorem eventual_period_residue_cocycle
    {x y z : E} {Lxy Lyz Lzx : ℕ}
    (hxy_lt : Lxy < statePeriod κ x)
    (hyz_lt : Lyz < statePeriod κ y)
    (hzx_lt : Lzx < statePeriod κ z)
    (hxy : HasEventualPeriodResidue κ x y Lxy)
    (hyz : HasEventualPeriodResidue κ y z Lyz)
    (hzx : HasEventualPeriodResidue κ z x Lzx) :
    Nat.ModEq (statePeriod κ x) (Lxy + Lyz + Lzx) 0 := sorry

end

end ProbabilityTheory
