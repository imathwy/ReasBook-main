import AchimKlenkeLean.Items.Chap24.Definition_24_31
import AchimKlenkeLean.Items.Chap24.Theorem_24_33

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

-- Proof sketch: since `α ∈ [0, 1)` and `θ > -α`, the quantity `θ + (n + 1) * α` is bounded below
-- by `θ + α`, which is positive; this is the positivity needed for the second Beta parameter.
/-- The second Beta shape parameter in the GEM construction is positive in every coordinate. -/
private theorem gemBetaSecondShape_pos (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hθα : -α < θ) (n : ℕ) :
    0 < θ + ((n : ℝ) + 1) * α := by
  have hn : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  linarith [mul_nonneg hn hα_nonneg]

/-- The `n`th independent Beta coordinate used in the GEM stick-breaking construction. -/
private noncomputable def gemBetaCoordinateLaw (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨betaMeasure (1 - α) (θ + ((n : ℝ) + 1) * α),
    isProbabilityMeasureBeta (sub_pos.mpr hα_lt_one)
      (gemBetaSecondShape_pos α θ hα_nonneg hθα n)⟩

/-- The infinite product law of the independent Beta coordinates appearing in the GEM
stick-breaking construction. -/
private noncomputable def gemBetaProductLaw (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨Measure.infinitePi fun n ↦ (gemBetaCoordinateLaw α θ hα_nonneg hα_lt_one hθα n : Measure ℝ),
    inferInstance⟩

-- Proof sketch: measurability into the product space reduces to measurability of each coordinate;
-- each coordinate is a finite product of measurable coordinate projections and measurable algebraic
-- operations.
/-- The stick-breaking map from Beta coordinates to GEM weights is measurable. -/
theorem measurable_gemStickBreaking :
    Measurable (gemStickBreaking : (ℕ → ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  simp [gemStickBreaking]
  measurability

/-- The mass partition with a single block of mass `1`. -/
def singletonMassPartition : MassPartition :=
  ⟨fun n ↦ if n = 0 then 1 else 0, by
    constructor
    · intro i j hij
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · simp [hj]
        · simp [hj]
      · have hj : j ≠ 0 := by
          intro hj
          apply hi
          exact Nat.eq_zero_of_le_zero (hj ▸ hij)
        simp [hi, hj]
    constructor
    · exact (hasSum_ite_eq 0 (1 : NNReal)).summable
    · exact (hasSum_ite_eq 0 (1 : NNReal)).tsum_eq⟩

/-- A mass partition `x` is a ranked rearrangement of `z` when its coordinates are obtained from
`z` by a permutation of `ℕ`. -/
def IsRankedRearrangement (x : MassPartition) (z : ℕ → ℝ) : Prop :=
  ∃ e : Equiv.Perm ℕ, (fun n ↦ (x n : ℝ)) = z ∘ e

/-- Any sequence that admits a ranked rearrangement has a unique such rearrangement. -/
private theorem existsUnique_rankedRearrangement (z : ℕ → ℝ)
    (hz : ∃ x : MassPartition, IsRankedRearrangement x z) :
    ∃! x : MassPartition, IsRankedRearrangement x z := sorry

/-- The canonical ranked rearrangement of a sequence, as a mass partition when one exists;
otherwise the singleton mass partition. -/
noncomputable def rankedRearrangement (z : ℕ → ℝ) : MassPartition :=
  if hz : ∃ x : MassPartition, IsRankedRearrangement x z then
    (existsUnique_rankedRearrangement z hz).choose
  else
    singletonMassPartition

/-- If a sequence admits a ranked rearrangement, then `rankedRearrangement` returns it. -/
theorem isRankedRearrangement_rankedRearrangement {z : ℕ → ℝ}
    (hz : ∃ x : MassPartition, IsRankedRearrangement x z) :
    IsRankedRearrangement (rankedRearrangement z) z := by
  rw [rankedRearrangement, dif_pos hz]
  exact (existsUnique_rankedRearrangement z hz).choose_spec.1

/-- A ranked rearrangement is uniquely determined by the source sequence. -/
theorem rankedRearrangement_eq_of_isRankedRearrangement {x : MassPartition} {z : ℕ → ℝ}
    (hx : IsRankedRearrangement x z) :
    rankedRearrangement z = x := by
  let hz : ∃ y : MassPartition, IsRankedRearrangement y z := ⟨x, hx⟩
  rw [rankedRearrangement, dif_pos hz]
  exact (ExistsUnique.choose_eq_iff (existsUnique_rankedRearrangement z hz)).2 hx

-- Proof sketch: the ranked rearrangement is characterized pointwise by the unique decreasing mass
-- partition equidistributed with the input sequence, and this mass-partition-valued selection is
-- measurable on the product space.
/-- The canonical ranked-rearrangement map on real sequences, valued in `MassPartition`, is
measurable. -/
theorem measurable_rankedRearrangement :
    Measurable rankedRearrangement := sorry

/-- Definition 24.34: for `α ∈ [0,1)` and `θ > -α`, the GEM distribution with parameters
`(α, θ)` is the law of the stick-breaking sequence built from independent Beta variables with
shapes `(1 - α, θ + (n + 1) * α)`. -/
noncomputable def gemDistribution (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  (gemBetaProductLaw α θ hα_nonneg hα_lt_one hθα).map measurable_gemStickBreaking.aemeasurable

-- Proof sketch: unfold `gemDistribution` as the pushforward of `gemBetaProductLaw` by
-- `gemStickBreaking`, then apply `ProbabilityMeasure.map_apply`.
/-- The GEM law evaluates measurable sets by pulling them back along the stick-breaking map. -/
theorem gemDistribution_apply (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    gemDistribution α θ hα_nonneg hα_lt_one hθα A =
      gemBetaProductLaw α θ hα_nonneg hα_lt_one hθα (gemStickBreaking ⁻¹' A) := by
  simpa [gemDistribution] using
    (gemBetaProductLaw α θ hα_nonneg hα_lt_one hθα).map_apply
      measurable_gemStickBreaking.aemeasurable hA

/-- Definition 24.34: the Poisson--Dirichlet distribution `PD_{α,θ}` is the law of the ranked
rearrangement of a `GEM_{α,θ}` stick-breaking sequence. -/
noncomputable def poissonDirichletDistribution (α θ : ℝ) (hα_nonneg : 0 ≤ α)
    (hα_lt_one : α < 1) (hθα : -α < θ) : ProbabilityMeasure MassPartition :=
  (gemDistribution α θ hα_nonneg hα_lt_one hθα).map measurable_rankedRearrangement.aemeasurable

-- Proof sketch: unfold `poissonDirichletDistribution` as the pushforward of `gemDistribution` by
-- `rankedRearrangement`, then apply `ProbabilityMeasure.map_apply`.
/-- The Poisson--Dirichlet law evaluates measurable sets by pulling them back along the canonical
ranked-rearrangement map. -/
theorem poissonDirichletDistribution_apply (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1)
    (hθα : -α < θ) {A : Set MassPartition} (hA : MeasurableSet A) :
    poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα A =
      gemDistribution α θ hα_nonneg hα_lt_one hθα (rankedRearrangement ⁻¹' A) := by
  simpa [poissonDirichletDistribution] using
    (gemDistribution α θ hα_nonneg hα_lt_one hθα).map_apply
      measurable_rankedRearrangement.aemeasurable hA

-- Proof sketch: use the uniqueness of ranked rearrangements to identify `X` almost everywhere with
-- `rankedRearrangement ∘ Z`, then push forward the `GEM_{α,θ}` law along
-- `rankedRearrangement`.
/-- Any random ranked rearrangement of a `GEM_{α,θ}` sequence has the canonical
`PD_{α,θ}` law. -/
theorem hasLaw_poissonDirichletDistribution_of_hasLaw_gemDistribution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → MassPartition} {Z : Ω → ℕ → ℝ}
    (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ)
    (hZ : HasLaw Z (gemDistribution α θ hα_nonneg hα_lt_one hθα : Measure (ℕ → ℝ)) P)
    (hX_ranked : ∀ᵐ ω ∂P, IsRankedRearrangement (X ω) (Z ω)) :
    HasLaw X (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα : Measure MassPartition) P :=
  sorry

end ProbabilityTheory
