import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped BigOperators
open Preorder Finset

noncomputable section

universe u

section

variable {d n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The kernel family driving the random walk with increment laws `μ`, viewed as a family on
finite prefix trajectories. -/
private def convolutionTrajectoryKernel (μ : Fin n → ProbabilityMeasure E) :
    (k : ℕ) → Kernel ((i : Finset.Iic k) → E) E
  | k =>
      if hk : k < n then
        let current : Finset.Iic k := ⟨k, Finset.mem_Iic.2 le_rfl⟩
        (dirac_convolution_kernel (μ ⟨k, hk⟩ : Measure E)).comap
          (fun x : (i : Finset.Iic k) → E ↦ x current)
          (measurable_pi_apply current)
      else
        Kernel.const ((i : Finset.Iic k) → E) (Measure.dirac (0 : E))

-- Proof sketch: first identify the left-hand side with the `Kernel.partialTraj`-generated law of
-- the finite path `(S₁, ..., Sₙ)` through the canonical kernel on starting states obtained from
-- `Kernel.partialTraj` by forgetting time `0`. Then rewrite that law as the pushforward of the
-- product law of the increments under the cumulative-sum map. Next use independence and the law
-- assumptions to identify that product law with the joint law of `(X₀, ..., Xₙ₋₁)`, and finally
-- push forward by `Fin.partialSum` along the source-facing index set `{1, ..., n}`.
/-- Theorem 14.28: for independent `ℝ^d`-valued increments with laws `μ i`, the path law generated
by the convolution kernels and started at `0` agrees with the joint law of the partial sums. Here
the owner kernel is the finite-step `Kernel.partialTraj` law, restricted from `Iic n` to the
source-facing index set `Finset.Ioc 0 n` representing the textbook partial sums `S₁, …, Sₙ`. -/
theorem convolutionTrajectoryLaw_eq_jointLaw_partialSums
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → E} {μ : Fin n → ProbabilityMeasure E}
    (hX_indep : iIndepFun X P) (hX_law : ∀ i, HasLaw (X i) (μ i) P) :
    let state : ℕ → Type _ := fun _ ↦ E
    let κstep : (k : ℕ) → Kernel ((i : Finset.Iic k) → state i) (state (k + 1)) :=
      convolutionTrajectoryKernel μ
    let e : state 0 ≃ᵐ ((i : Finset.Iic 0) → state i) :=
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ state i)).symm
    let κpath : Kernel (state 0) ((i : Finset.Ioc 0 n) → state i) :=
      Kernel.comap
        ((partialTraj κstep 0 n).map (restrict₂ Ioc_subset_Iic_self))
        (fun x : state 0 ↦ e x)
        (by simpa using e.measurable)
    κpath ∘ₘ Measure.dirac (0 : state 0) =
      Measure.map
        (fun ω (i : Finset.Ioc 0 n) ↦
          Fin.partialSum (fun j ↦ X j ω)
            ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 i.2).2⟩)
        P := sorry

end
