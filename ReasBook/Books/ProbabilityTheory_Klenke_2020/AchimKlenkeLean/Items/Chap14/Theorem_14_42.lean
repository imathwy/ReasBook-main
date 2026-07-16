import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap14.Definition_14_39

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel
open scoped ProbabilityTheory

noncomputable section

universe u v

section FiniteDimensional

variable {I : Type u} [Preorder I]
variable {E : Type v} [MeasurableSpace E]

/-- The projection of a path in `I → E` to the finite chain of times encoded by `j`. -/
def finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    (I → E) → Π _ : Finset.Iic n, E :=
  fun ω k ↦ ω (j k)

-- Proof sketch: each coordinate of `finiteCoordinateProjection j` is an evaluation map on the
-- product measurable space, so measurability follows coordinatewise.
/-- The projection to a finite chain of coordinates is measurable. -/
theorem measurable_finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    Measurable (finiteCoordinateProjection j : (I → E) → Π _ : Finset.Iic n, E) := sorry

private def historyHead {n : ℕ} : (Π _ : Finset.Iic n, E) → E :=
  fun x ↦ x ⟨0, mem_Iic.2 (Nat.zero_le n)⟩

private theorem measurable_historyHead {n : ℕ} :
    Measurable (historyHead : (Π _ : Finset.Iic n, E) → E) := sorry

private def historyLast {n : ℕ} : (Π _ : Finset.Iic n, E) → E :=
  fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩

private theorem measurable_historyLast {n : ℕ} :
    Measurable (historyLast : (Π _ : Finset.Iic n, E) → E) := sorry

private def initialHistory : E → Π _ : Finset.Iic 0, E :=
  fun x _ ↦ x

private theorem measurable_initialHistory :
    Measurable (initialHistory : E → Π _ : Finset.Iic 0, E) := sorry

private noncomputable def consistentFamilyHistoryKernels
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E :=
  fun m ↦
    if hm : m < n then
      Kernel.comap
        (κ (hj (show (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
        historyLast measurable_historyLast
    else
      Kernel.deterministic historyHead measurable_historyHead

private noncomputable def consistentFamilyHistoryTraj {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E) :
    Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E) :=
  ((@partialTraj (fun _ : ℕ ↦ E) _ κhist 0 n) :
    Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E))

/-- The finite-dimensional kernel attached to the ordered chain of kernels picked out by `j`,
viewed as a stochastic kernel in the initial state. This is the owner construction over
`Kernel.partialTraj`; the measure-valued finite-dimensional laws are obtained from it by
composition with an initial law. -/
noncomputable def consistentFamilyFiniteDimensionalKernel
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    Kernel E (Π _ : Finset.Iic n, E) :=
  consistentFamilyHistoryTraj (consistentFamilyHistoryKernels κ j hj) ∘ₖ
    Kernel.deterministic initialHistory measurable_initialHistory

/-- The finite-dimensional law attached to an initial measure `μ` and the ordered chain of kernels
picked out by `j`. This is the bridge/view API obtained from
`consistentFamilyFiniteDimensionalKernel` by composing with the initial law. -/
noncomputable def consistentFamilyFiniteDimensionalMeasure
    (μ : Measure E) (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    Measure (Π _ : Finset.Iic n, E) :=
  consistentFamilyFiniteDimensionalKernel κ j hj ∘ₘ μ

-- Proof sketch: unfold `consistentFamilyFiniteDimensionalMeasure`; when `n = 0`,
-- `partialTraj ... 0 0` is the identity kernel, so only the pushforward along the unique
-- one-point-history equivalence remains.
/-- At level `n = 0`, the finite-dimensional law is just the initial law viewed on the
one-point-history space. -/
theorem consistentFamilyFiniteDimensionalMeasure_zero
    (μ : Measure E) (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (j : Π _ : Finset.Iic 0, I) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalMeasure μ κ j hj =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm := sorry

/-- Evaluating the finite-dimensional kernel at `x` recovers the finite-dimensional law with
initial distribution `δ_x`. -/
theorem consistentFamilyFiniteDimensionalKernel_apply
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) (x : E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalKernel κ j hj x =
      consistentFamilyFiniteDimensionalMeasure (Measure.dirac x) κ j hj := sorry

end FiniteDimensional

section

variable {E : Type v} [MeasurableSpace E]
variable {I : Set NNReal}
variable [StandardBorelSpace E]
variable (h0I : (0 : NNReal) ∈ I)

-- Proof sketch: for each initial state `x`, the measures
-- `consistentFamilyFiniteDimensionalKernel K j hj x` form a projective family by the
-- consistency hypothesis. Apply Kolmogorov's extension theorem on the product space `I → E`, then
-- verify measurability in `x` on finite cylinders and extend to all measurable sets.
/-- Theorem 14.42: a consistent family of stochastic kernels on the standard Borel state space `E`
produces a kernel on the path space `E^I` whose finite-dimensional marginals along every strictly
increasing chain `⊥ = j₀ < j₁ < ··· < jₙ` are the iterated kernel laws
`δ_x ⊗ \bigotimes_{k=0}^{n-1} κ_{j_k,j_{k+1}}`. -/
theorem exists_kernel_on_path_space_of_consistent_family
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K) :
    letI : OrderBot I := Subtype.orderBot h0I
    ∃ κ : Kernel E (I → E),
      IsMarkovKernel κ ∧
        ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j),
          j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
          (κ x).map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel K j hj x := sorry

end
