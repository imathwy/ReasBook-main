import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BoundedContinuousFunction CompactlySupported

private abbrev IciNN := Set.Ici (0 : ℝ)

/-- Compactly supported bounded continuous functions whose support is contained in `[0,n]`. -/
private def compactSupportLayer (n : ℕ) : Set C_cb(IciNN, ℝ) :=
  {f | tsupport (f.1 : IciNN →ᵇ ℝ) ⊆ {x | (x : ℝ) ≤ n}}

/-- Restriction of a function in the `n`th support layer to the compact interval `[0,n]`. -/
private def compactSupportLayerRestrict (n : ℕ) :
    compactSupportLayer n → C(Set.Icc (0 : ℝ) n, ℝ) :=
  fun f ↦
    ⟨fun x ↦ (f.1.1 : IciNN →ᵇ ℝ) ⟨x, x.2.1⟩,
      (f.1.1 : IciNN →ᵇ ℝ).continuous.comp
        (continuous_subtype_val.subtype_mk fun x ↦ x.2.1)⟩

private theorem compactSupportLayerRestrict_isometry (n : ℕ) :
    Isometry (compactSupportLayerRestrict n) := by
  refine Isometry.of_dist_eq ?_
  intro f g
  apply le_antisymm
  · apply (ContinuousMap.dist_le dist_nonneg).2
    intro x
    exact BoundedContinuousFunction.dist_coe_le_dist
      (⟨(x : ℝ), x.2.1⟩ : IciNN)
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).2
    intro x
    by_cases hx : (x : ℝ) ≤ n
    · exact ContinuousMap.dist_apply_le_dist
        (f := compactSupportLayerRestrict n f) (g := compactSupportLayerRestrict n g)
        (⟨(x : ℝ), x.2, hx⟩ : Set.Icc (0 : ℝ) n)
    · have hxf : x ∉ tsupport (f.1.1 : IciNN →ᵇ ℝ) := fun h ↦ hx (f.2 h)
      have hxg : x ∉ tsupport (g.1.1 : IciNN →ᵇ ℝ) := fun h ↦ hx (g.2 h)
      simp [image_eq_zero_of_notMem_tsupport hxf,
        image_eq_zero_of_notMem_tsupport hxg]

private theorem compactSupportLayer_separable (n : ℕ) :
    TopologicalSpace.SeparableSpace (compactSupportLayer n) :=
  (compactSupportLayerRestrict_isometry n).isEmbedding.separableSpace

private theorem iUnion_compactSupportLayer :
    (⋃ n : ℕ, compactSupportLayer n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro f
  have hcompact : IsCompact (tsupport (f.1 : IciNN →ᵇ ℝ)) :=
    (mem_compactlySupported.mp f.2).isCompact
  rcases hcompact.bddAbove with ⟨a, ha⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (a : ℝ)
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  intro x hx
  change (x : ℝ) ≤ n
  exact (show (x : ℝ) ≤ (a : ℝ) from ha hx).trans hn

/-- Exercise 13.1.1 (1): the supremum-norm space `C([0,1], ℝ)` is separable. -/
-- This is the canonical owner instance for continuous maps on a locally compact second-countable
-- domain.
theorem continuousMap_Icc_zero_one_separable :
    TopologicalSpace.SeparableSpace (C(Set.Icc (0 : ℝ) 1, ℝ)) := by
  infer_instance

/-- Exercise 13.1.1 (2): the supremum-norm space of bounded continuous real-valued functions on
`[0, ∞)` is not separable. -/
-- Proof sketch: produce an uncountable family of bounded continuous functions that are pairwise
-- separated by a fixed positive distance in the supremum norm.
theorem boundedContinuousFunction_Ici_not_separable :
    ¬ TopologicalSpace.SeparableSpace ((Set.Ici (0 : ℝ)) →ᵇ ℝ) := sorry

/-- Exercise 13.1.1 (3): the supremum-norm space `C_c([0, ∞), ℝ)` is separable. -/
-- `C_cb` is the canonical uniform-norm owner: unlike the bare compact-support structure `C_c`,
-- it is a subtype of bounded continuous functions and therefore carries the intended metric.
theorem compactlySupportedContinuousMap_Ici_separable :
    TopologicalSpace.SeparableSpace (C_cb(Set.Ici (0 : ℝ), ℝ)) := by
  rw [← TopologicalSpace.isSeparable_univ_iff, ← iUnion_compactSupportLayer]
  exact TopologicalSpace.IsSeparable.iUnion fun n ↦ by
    letI := compactSupportLayer_separable n
    exact TopologicalSpace.IsSeparable.of_subtype (compactSupportLayer n)
