import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory MeasurableEquiv ProbabilityTheory Preorder
open ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The state space at time `i`, represented by the finite set `{0, ..., n + i}`. -/
abbrev polyaUrnState (n : ℕ) (i : ℕ) := Fin (n + i + 1)

/-- The deterministic initial red-count state `k` at time `0`. -/
def polyaUrnInitialState (n k : ℕ) (hk : k ≤ n) : polyaUrnState n 0 :=
  ⟨k, Nat.lt_succ_of_le hk⟩

/-- The one-step state-space transition kernel of the Pólya urn from time `i` to time `i + 1`. -/
noncomputable def polyaUrnTransitionKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    Kernel (polyaUrnState n i) (polyaUrnState n (i + 1)) where
  toFun current :=
  let _ : NeZero (n + i : ℝ≥0∞) :=
    ⟨by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hn (Nat.le_add_right n i))⟩
  let p : ℝ≥0∞ := ((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞)
  p • Measure.dirac current.succ + (1 - p) • Measure.dirac current.castSucc
  measurable' := Measurable.of_discrete

/-- The stage-`i` transition kernel of the Pólya-urn trajectory, obtained from the state-space
kernel by reading the current count from the last coordinate of the prefix. -/
noncomputable def polyaUrnStepKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    Kernel (Π j : Finset.Iic i, polyaUrnState n j) (polyaUrnState n (i + 1)) :=
  Kernel.comap
    (polyaUrnTransitionKernel n hn i)
    (fun x : Π j : Finset.Iic i, polyaUrnState n j ↦ x ⟨i, mem_Iic.2 le_rfl⟩)
    Measurable.of_discrete

-- Proof sketch: for a current state `xᵢ`, the transition measure is supported on the two
-- states `xᵢ.castSucc` and `xᵢ.succ`. Its total mass is
-- `xᵢ / (n + i) + (1 - xᵢ / (n + i)) = 1`.
instance polyaUrnTransitionKernel_isMarkovKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    IsMarkovKernel (polyaUrnTransitionKernel n hn i) := sorry

instance polyaUrnStepKernel_isMarkovKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    IsMarkovKernel (polyaUrnStepKernel n hn i) := by
  dsimp [polyaUrnStepKernel]
  infer_instance

section

variable (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)

/-- Example 14.38: the path-space law of Pólya's urn with `n > 0` initial balls, `k` of them
red, and reinforcement by returning the sampled ball together with one additional ball of the same
color. Here `Ωᵢ = {0, ..., n + i}` is represented by `Fin (n + i + 1)`. -/
noncomputable def polyaUrnTrajectoryMeasure :
    Measure (∀ i : ℕ, polyaUrnState n i) :=
  trajMeasure (Measure.dirac (polyaUrnInitialState n k hk)) (polyaUrnStepKernel n hn)

/-- The finite-dimensional law up to time `i`, obtained as the marginal of the full Pólya-urn
trajectory law on the first `i + 1` coordinates. -/
noncomputable def polyaUrnFiniteLawUpTo (i : ℕ) :
    Measure (Π j : Finset.Iic i, polyaUrnState n j) :=
  (polyaUrnTrajectoryMeasure n k hn hk).map (frestrictLe i)

/-- The Pólya-urn trajectory law is a probability measure. -/
theorem polyaUrnTrajectoryMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (polyaUrnTrajectoryMeasure n k hn hk) := by
  dsimp [polyaUrnTrajectoryMeasure]
  infer_instance

/-- The finite-dimensional laws `Pᵢ` are the marginals of the full Pólya-urn trajectory law on the
first `i + 1` coordinates. -/
theorem polyaUrnFiniteLawUpTo_eq_map_trajectoryMeasure
    (i : ℕ) :
    polyaUrnFiniteLawUpTo n k hn hk i =
      (polyaUrnTrajectoryMeasure n k hn hk).map (frestrictLe i) :=
  rfl

/-- The finite-dimensional marginal law agrees with the iterated textbook kernel construction from
the deterministic initial state. -/
theorem polyaUrnFiniteLawUpTo_eq_partialTraj_comp_initialMeasure
    (i : ℕ) :
    polyaUrnFiniteLawUpTo n k hn hk i =
      (partialTraj (polyaUrnStepKernel n hn) 0 i) ∘ₘ
        (Measure.dirac (polyaUrnInitialState n k hk)).map (piUnique _).symm := by
  simpa [polyaUrnFiniteLawUpTo, polyaUrnTrajectoryMeasure] using
    (trajMeasure_map_frestrictLe
      (Measure.dirac (polyaUrnInitialState n k hk))
      (polyaUrnStepKernel n hn) i)

end

end
