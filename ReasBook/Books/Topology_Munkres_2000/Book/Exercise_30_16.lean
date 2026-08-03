module

public import Topology_Munkres_2000.Book.Exercise_30_16.Instances
public import Mathlib.Analysis.Real.Cardinality

public section

universe u

/- Exercise 30.16 (1): The product `ℝ^[0,1]`, represented by the function space
`unitInterval → ℝ` with the product topology, has a countable dense subset. -/
#synth TopologicalSpace.SeparableSpace (unitInterval → ℝ)

/-- Helper for Exercise 30.16: a dense subset of a real product contains a point
whose values at two distinct coordinates are separated by the interval `Set.Ioo 0 1`. -/
private lemma denseRealPi_exists_coordinateSeparator {J : Type u} {D : Set (J → ℝ)}
    (hD : Dense D) {α β : J} (hαβ : α ≠ β) :
    ∃ d : D, d.1 α ∈ Set.Ioo (0 : ℝ) 1 ∧ d.1 β ∉ Set.Ioo (0 : ℝ) 1 := by
  classical
  -- Use an open cylinder that puts the two coordinates in disjoint intervals.
  let U : Set (J → ℝ) :=
    (fun f ↦ f α) ⁻¹' Set.Ioo (0 : ℝ) 1 ∩ (fun f ↦ f β) ⁻¹' Set.Ioo (1 : ℝ) 3
  have hUOpen : IsOpen U := by
    exact (isOpen_Ioo.preimage (continuous_apply α)).inter
      (isOpen_Ioo.preimage (continuous_apply β))
  have hUNonempty : U.Nonempty := by
    have hβα : β ≠ α := Ne.symm hαβ
    refine ⟨fun γ ↦ if γ = α then (1 / 2 : ℝ) else 2, ?_⟩
    simp only [U, Set.mem_inter_iff, Set.mem_preimage, if_pos, hβα]
    norm_num
  -- Density supplies a point of `D` in this cylinder.
  obtain ⟨f, hfD, hfU⟩ := hD.exists_mem_open hUOpen hUNonempty
  refine ⟨⟨f, hfD⟩, hfU.1, ?_⟩
  intro hfβ
  exact (not_lt_of_ge hfU.2.1.le) hfβ.2

/-- Helper for Exercise 30.16: recording membership in one coordinate interval
embeds the coordinate type into the powerset of any dense subset. -/
private lemma coordinateIntervalTrace_injective {J : Type u} {D : Set (J → ℝ)}
    (hD : Dense D) :
    Function.Injective (fun α : J ↦ {d : D | d.1 α ∈ Set.Ioo (0 : ℝ) 1}) := by
  intro α β htrace
  -- A separator contradicts equality of the two traces unless the coordinates agree.
  by_contra hαβ
  obtain ⟨d, hdα, hdβ⟩ := denseRealPi_exists_coordinateSeparator hD hαβ
  have hdTrace : d ∈ {d : D | d.1 β ∈ Set.Ioo (0 : ℝ) 1} := by
    exact (Set.ext_iff.mp htrace d).mp hdα
  exact hdβ hdTrace

/-- Helper for Exercise 30.16: the powerset of a countable subtype has cardinality
at most the continuum. -/
private lemma cardinalMk_set_le_continuum_of_countable {X : Type u} {D : Set X}
    (hD : D.Countable) : Cardinal.mk (Set D) ≤ Cardinal.continuum := by
  have hTwo : (2 : Cardinal) ≠ 0 := by
    norm_num
  -- Rewrite powerset cardinality as exponentiation and use countability of `D`.
  rw [Cardinal.mk_set, ← Cardinal.two_power_aleph0]
  exact Cardinal.power_le_power_left hTwo hD.le_aleph0

/-- Exercise 30.16 (2): A separable product of real lines has at most continuum
many coordinates. -/
theorem cardinalMk_le_continuum_of_realPi_separable (J : Type u)
    [TopologicalSpace.SeparableSpace (J → ℝ)] :
    Cardinal.mk J ≤ Cardinal.continuum := by
  -- Choose a countable dense set, embed coordinates into its powerset, and bound that powerset.
  obtain ⟨D, hDCountable, hDDense⟩ := TopologicalSpace.exists_countable_dense (α := J → ℝ)
  calc
    Cardinal.mk J ≤ Cardinal.mk (Set D) :=
      Cardinal.mk_le_of_injective (coordinateIntervalTrace_injective hDDense)
    _ ≤ Cardinal.continuum := cardinalMk_set_le_continuum_of_countable hDCountable

/-- The large-index nonseparability conclusion of Exercise 30.16 (2). -/
theorem realPiNotSeparableOfLargeIndex {J : Type u}
    (hJ : Cardinal.continuum < Cardinal.mk J) :
    ¬ TopologicalSpace.SeparableSpace (J → ℝ) := by
  intro
  exact hJ.2 (cardinalMk_le_continuum_of_realPi_separable J)
