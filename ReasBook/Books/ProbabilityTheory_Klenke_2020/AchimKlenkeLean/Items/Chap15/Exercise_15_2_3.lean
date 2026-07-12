import Mathlib

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

namespace Measure

/-- A real law is lattice distributed when it is concentrated on some affine lattice `a + d ℤ`. -/
def IsLatticeDistributed (μ : Measure ℝ) : Prop :=
  ∃ a d : ℝ, μ (Set.range fun n : ℤ ↦ a + (n : ℝ) * d) = 1

-- Proof sketch: for the forward direction, write the support condition `μ[a + d ℤ] = 1` and
-- evaluate the characteristic function at a nonzero frequency annihilating the lattice increments.
-- For the converse, equality in the triangle inequality for the oscillatory integral forces the
-- phase `exp (i u x)` to be `μ`-almost surely constant, which implies concentration on an affine
-- lattice.
/-- A real zero-or-probability law is lattice distributed if and only if there exists a nonzero
frequency at which the modulus of its characteristic function is equal to `1`. The probability-law
case is the textbook criterion, while the zero measure handles non-measurable pushforwards
canonically. -/
theorem isLatticeDistributed_iff_exists_ne_zero_norm_charFun_eq_one
    (μ : Measure ℝ) [IsZeroOrProbabilityMeasure μ] :
    IsLatticeDistributed μ ↔
      ∃ u : ℝ, u ≠ 0 ∧ ‖charFun μ u‖ = 1 := sorry

end Measure

/-- A real random variable is lattice distributed when its law is lattice distributed. -/
def IsLatticeDistributed (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measure.IsLatticeDistributed (P.map X)

/-- Exercise 15.2.3: a real random variable is lattice distributed if and only if there exists a
nonzero frequency at which the modulus of its characteristic function is equal to `1`. -/
theorem is_lattice_distributed_iff_exists_ne_zero_norm_charFun_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) :
    IsLatticeDistributed P X ↔
      ∃ u : ℝ, u ≠ 0 ∧ ‖charFun (P.map X) u‖ = 1 := by
  simpa [IsLatticeDistributed] using
    Measure.isLatticeDistributed_iff_exists_ne_zero_norm_charFun_eq_one (P.map X)
