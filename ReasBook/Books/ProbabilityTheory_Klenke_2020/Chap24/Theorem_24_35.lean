import ProbabilityTheory_Klenke_2020.Chap24.Definition_24_34

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace ProbabilityTheory

/-- The finite type `Nat.Partition n` carries the discrete measurable structure. -/
instance partitionMeasurableSpace (n : ℕ) : MeasurableSpace (Nat.Partition n) := ⊤

/-- The parts of a finite integer partition, listed in decreasing order. -/
def partitionPartsDescending {n : ℕ} (π : Nat.Partition n) : List ℕ :=
  (π.parts.sort (· ≤ ·)).reverse

/-- The normalized ranked block-size function associated with a finite integer partition. -/
def normalizedPartitionSequenceFun {n : ℕ} (π : Nat.Partition n) : ℕ → NNReal :=
  fun k ↦ (((partitionPartsDescending π).getD k 0 : ℕ) : NNReal) / n

-- Proof sketch: the parts of `π` are listed in decreasing order, padded by zeros, and normalized
-- by the positive scalar `n`; hence the resulting sequence is antitone, summable, and has total
-- mass `1`.
/-- For `n > 0`, the normalized ranked block-size function is a mass partition. -/
theorem normalizedPartitionSequenceFun_isMassPartition {n : ℕ} (π : Nat.Partition n) (hn : n ≠ 0) :
    Antitone (normalizedPartitionSequenceFun π) ∧
      Summable (normalizedPartitionSequenceFun π) ∧
      ∑' k, normalizedPartitionSequenceFun π k = 1 := sorry

/-- The normalized block-size mass partition associated with a finite integer partition. For
`n = 0` this uses the singleton mass partition as a harmless convention. -/
def normalizedPartitionSequence {n : ℕ} (π : Nat.Partition n) : MassPartition :=
  if hn : n = 0 then
    singletonMassPartition
  else
    ⟨normalizedPartitionSequenceFun π, normalizedPartitionSequenceFun_isMassPartition π hn⟩

/-- The Ewens--Pitman sampling weight assigned to a ranked partition of `n` in the
Chinese-restaurant law with parameters `(α, θ)`. -/
def chineseRestaurantPartitionWeight (α θ : ℝ) {n : ℕ} (π : Nat.Partition n) : ℝ :=
  let k := π.parts.card
  let tableFactor : ℝ :=
    Finset.prod (Finset.range k) (fun j ↦ θ + (j : ℝ) * α)
  let blockFactor : ℝ :=
    (π.parts.map fun m ↦
      Finset.prod (Finset.Icc (1 : ℕ) (m - 1)) (fun j ↦ (j : ℝ) - α)).prod
  let normalizer : ℝ :=
    Finset.prod (Finset.range n) (fun j ↦ θ + (j : ℝ))
  tableFactor * blockFactor / normalizer

/-- A family `μ n` of laws on ranked partitions of `n` is the Chinese-restaurant law sequence with
parameters `(α, θ)` when every singleton mass is given by the Ewens--Pitman sampling formula. -/
def IsChineseRestaurantPartitionLawSequence (α θ : ℝ)
    (μ : ∀ n : ℕ, ProbabilityMeasure (Nat.Partition n)) : Prop :=
  ∀ n (π : Nat.Partition n),
    ((μ n : Measure (Nat.Partition n)) {π}) =
      ENNReal.ofReal (chineseRestaurantPartitionWeight α θ π)

/-- The law of the normalized ranked block-size sequence obtained from a law on partitions of
`n`. This is the formal version of the textbook notation `P_{N^n / n}`. -/
def normalizedChineseRestaurantPartitionLaw
    (μ : ∀ n : ℕ, ProbabilityMeasure (Nat.Partition n)) (n : ℕ) :
    ProbabilityMeasure MassPartition :=
  (μ n).map
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (normalizedPartitionSequence : Nat.Partition n → MassPartition) ↑(μ n))

-- Proof sketch: identify `partitionLaws n` with the ranked block-size law of the
-- `(α, θ)`-Chinese restaurant process via the Ewens--Pitman sampling formula, view
-- `normalizedChineseRestaurantPartitionLaw partitionLaws n` as the law of `N^n / n`, realize the
-- Poisson--Dirichlet law from Definition 24.34, and then invoke the classical convergence theorem
-- for normalized block sizes.
/-- Theorem 24.35: if `partitionLaws n` is the law of the ranked block-size partition `N^n` of the
Chinese restaurant process with parameters `(α, θ)`, then the normalized laws `P_{N^n / n}`
converge weakly to the Poisson--Dirichlet law `PD_{α,θ}` from Definition 24.34. -/
theorem normalizedChineseRestaurantPartitionLaw_tendsto_poissonDirichlet
    (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ)
    (partitionLaws : ∀ n : ℕ, ProbabilityMeasure (Nat.Partition n))
    (hpartitionLaws : IsChineseRestaurantPartitionLawSequence α θ partitionLaws) :
    Tendsto (normalizedChineseRestaurantPartitionLaw partitionLaws) atTop
      (𝓝 (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα)) := sorry

end ProbabilityTheory
