module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

public section

open Set
open scoped Topology

/-- The family of singleton sets `{(n + 1)⁻¹}` that witnesses the quantifier error in the
purported proof. -/
def reciprocalSingletons (n : ℕ) : Set ℝ := {((n + 1 : ℕ) : ℝ)⁻¹}

/-- Every neighborhood of `0` meets some member of `reciprocalSingletons`. -/
theorem exists_reciprocalSingleton_inter_nhds (U : Set ℝ) (hU : U ∈ 𝓝 0) :
    ∃ n, (U ∩ reciprocalSingletons n).Nonempty := by
  -- Convergence makes the reciprocal sequence eventually enter the chosen neighborhood.
  have hTendsto :
      Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) Filter.atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0))
  have hEventually : ∀ᶠ n in Filter.atTop, ((n + 1 : ℕ) : ℝ)⁻¹ ∈ U :=
    hTendsto.eventually hU
  obtain ⟨n, hn⟩ := hEventually.exists
  -- The corresponding sequence value witnesses the required intersection.
  refine ⟨n, ((n + 1 : ℕ) : ℝ)⁻¹, hn, ?_⟩
  simp only [reciprocalSingletons, mem_singleton_iff]

/-- No fixed member of `reciprocalSingletons` meets every neighborhood of `0`. -/
theorem no_reciprocalSingleton_inter_all_nhds :
    ¬ ∃ n, ∀ U ∈ 𝓝 (0 : ℝ), (U ∩ reciprocalSingletons n).Nonempty := by
  rintro ⟨n, hn⟩
  -- The reciprocal is positive, so its singleton complement is a neighborhood of zero.
  have hPositive : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have hNeighborhood : {(((n + 1 : ℕ) : ℝ)⁻¹)}ᶜ ∈ 𝓝 (0 : ℝ) :=
    compl_singleton_mem_nhds hPositive.ne
  -- That neighborhood is disjoint from the fixed singleton, contradicting the assumption.
  obtain ⟨x, hxComplement, hxSingleton⟩ :=
    hn {(((n + 1 : ℕ) : ℝ)⁻¹)}ᶜ hNeighborhood
  have hxValue : x = (((n + 1 : ℕ) : ℝ)⁻¹) := by
    simpa only [reciprocalSingletons, mem_singleton_iff] using hxSingleton
  exact hxComplement hxValue

/-- Exercise 17.7: For the family `reciprocalSingletons`, the true statement that every
neighborhood `U` of `0` meets some member of the family does not imply that one fixed member
meets every such `U`. This is the invalid quantifier exchange in the purported proof. -/
theorem reciprocalSingletons_quantifier_exchange_invalid :
    ¬ ((∀ U ∈ 𝓝 (0 : ℝ), ∃ n, (U ∩ reciprocalSingletons n).Nonempty) →
      ∃ n, ∀ U ∈ 𝓝 (0 : ℝ), (U ∩ reciprocalSingletons n).Nonempty) := by
  intro hExchange
  -- Apply the claimed exchange to the valid neighborhood-dependent choice of index.
  have hUniform := hExchange (fun U hU ↦ exists_reciprocalSingleton_inter_nhds U hU)
  -- No fixed singleton can satisfy the resulting uniform neighborhood statement.
  exact no_reciprocalSingleton_inter_all_nhds hUniform

/-- Consequently, the closure of an infinite union need not be contained in the union of
the individual closures. -/
theorem closure_iUnion_reciprocalSingletons_not_subset :
    ¬ (closure (⋃ n : ℕ, reciprocalSingletons n) ⊆
      ⋃ n : ℕ, closure (reciprocalSingletons n)) := by
  intro hSubset
  -- Every neighborhood of zero meets the union because it meets one family member.
  have hZeroClosure : (0 : ℝ) ∈ closure (⋃ n : ℕ, reciprocalSingletons n) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨n, x, hxU, hxSingleton⟩ := exists_reciprocalSingleton_inter_nhds U hU
    exact ⟨x, hxU, Set.mem_iUnion.2 ⟨n, hxSingleton⟩⟩
  -- The assumed inclusion puts zero in one singleton closure, which is impossible.
  have hZeroIndividualClosure := hSubset hZeroClosure
  simp only [reciprocalSingletons, closure_singleton, mem_iUnion,
    mem_singleton_iff] at hZeroIndividualClosure
  obtain ⟨n, hn⟩ := hZeroIndividualClosure
  have hPositive : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  exact hPositive.ne' hn.symm
