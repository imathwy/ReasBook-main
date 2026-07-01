import SmoothManifoldsLee.Chap01.Sec01_02.Definition_1_2_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ChartedSpace OpenPartialHomeomorph
open scoped ContDiff Manifold

universe u v w x

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type x} [TopologicalSpace M]
variable {I : ModelWithCorners 𝕜 E H}

/-- Proposition 1.17 (1): a smooth atlas is contained in the maximal smooth atlas it determines.
That maximal atlas is again smooth, and a chart belongs to it exactly when it is smoothly
compatible with every chart of the original atlas. The source-facing owner is
`OpenPartialHomeomorph.IsSmoothAtlas`, while the core/canonical bridge is
`StructureGroupoid.maximalAtlas`. -/
theorem smooth_structure_determined_by_atlas
    (c : ChartedSpace H M) (hc : IsSmoothAtlas I c.atlas) :
    letI := c
    c.atlas ⊆ (contDiffGroupoid (∞ : ℕ∞ω) I).maximalAtlas M ∧
      IsSmoothAtlas I ((contDiffGroupoid (∞ : ℕ∞ω) I).maximalAtlas M) ∧
      ∀ {e : OpenPartialHomeomorph M H},
        e ∈ (contDiffGroupoid (∞ : ℕ∞ω) I).maximalAtlas M ↔
          ∀ e' ∈ c.atlas, e.symm ≫ₕ e' ∈ contDiffGroupoid (∞ : ℕ∞ω) I := by
  let G := contDiffGroupoid (∞ : ℕ∞ω) I
  letI := c
  letI : HasGroupoid M G := (isSmoothAtlas_atlas_iff.mp hc)
  constructor
  · exact G.subset_maximalAtlas
  · constructor
    · refine ⟨?_, ?_⟩
      · intro x
        exact ⟨chartAt H x, G.chart_mem_maximalAtlas x, mem_chart_source H x⟩
      · intro e e' he he'
        exact G.compatible_of_mem_maximalAtlas he he'
    · intro e
      constructor
      · intro he e' he'
        exact mem_maximalAtlas_iff.1 he e' he' |>.1
      · intro he
        rw [mem_maximalAtlas_iff]
        intro e' he'
        have hleft : e.symm ≫ₕ e' ∈ G := he e' he'
        exact ⟨hleft, by simpa using G.symm hleft⟩

/-- Proposition 1.17 (2): two smooth atlases determine the same smooth structure exactly when
their union is again a smooth atlas. The source-facing statement is expressed by
`OpenPartialHomeomorph.IsSmoothAtlas`, and the bridge to "same smooth structure" is equality of
the corresponding maximal smooth atlases. -/
theorem same_smooth_structure_iff_union_is_smooth_atlas
    (c c' : ChartedSpace H M)
    (hc : IsSmoothAtlas I c.atlas)
    (hc' : IsSmoothAtlas I c'.atlas) :
    (letI := c
     (contDiffGroupoid (∞ : ℕ∞ω) I).maximalAtlas M) =
      (letI := c'
       (contDiffGroupoid (∞ : ℕ∞ω) I).maximalAtlas M) ↔
        IsSmoothAtlas I (c.atlas ∪ c'.atlas) := by
  let G := contDiffGroupoid (∞ : ℕ∞ω) I
  let A : Set (OpenPartialHomeomorph M H) := by
    letI := c
    exact G.maximalAtlas M
  let A' : Set (OpenPartialHomeomorph M H) := by
    letI := c'
    exact G.maximalAtlas M
  have hsubsetA : c.atlas ⊆ A := by
    simpa [A, G] using (smooth_structure_determined_by_atlas c hc).1
  have hsubsetA' : c'.atlas ⊆ A' := by
    simpa [A', G] using (smooth_structure_determined_by_atlas c' hc').1
  have hA : IsSmoothAtlas I A := by
    simpa [A, G] using (smooth_structure_determined_by_atlas c hc).2.1
  have hA' : IsSmoothAtlas I A' := by
    simpa [A', G] using (smooth_structure_determined_by_atlas c' hc').2.1
  have hmemA {e : OpenPartialHomeomorph M H} :
      e ∈ A ↔ ∀ e' ∈ c.atlas, e.symm ≫ₕ e' ∈ G := by
    simpa [A, G] using (smooth_structure_determined_by_atlas c hc).2.2
  have hmemA' {e : OpenPartialHomeomorph M H} :
      e ∈ A' ↔ ∀ e' ∈ c'.atlas, e.symm ≫ₕ e' ∈ G := by
    simpa [A', G] using (smooth_structure_determined_by_atlas c' hc').2.2
  change A = A' ↔ IsSmoothAtlas I (c.atlas ∪ c'.atlas)
  constructor
  · intro hAA'
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨e, he, hx⟩ := hc.cover x
      exact ⟨e, Or.inl he, hx⟩
    · intro e e' he he'
      rcases he with he | he
      · rcases he' with he' | he'
        · exact hc.compatible he he'
        · have hem : e ∈ A := hsubsetA he
          have he'm : e' ∈ A' := hsubsetA' he'
          have he'A : e' ∈ A := by simpa [hAA'] using he'm
          exact hA.compatible hem he'A
      · rcases he' with he' | he'
        · have hem : e ∈ A' := hsubsetA' he
          have hemA : e ∈ A := by simpa [hAA'] using hem
          have he'm : e' ∈ A := hsubsetA he'
          exact hA.compatible hemA he'm
        · exact hc'.compatible he he'
  · intro hunion
    have hchart_c'_A : c'.atlas ⊆ A := by
      intro e he
      rw [hmemA]
      intro e' he'
      exact hunion.compatible (Or.inr he) (Or.inl he')
    have hchart_c_A' : c.atlas ⊆ A' := by
      intro e he
      rw [hmemA']
      intro e' he'
      exact hunion.compatible (Or.inl he) (Or.inr he')
    apply Set.Subset.antisymm
    · intro e he
      rw [hmemA']
      intro e' he'
      exact hA.compatible he (hchart_c'_A he')
    · intro e he
      rw [hmemA]
      intro e' he'
      exact hA'.compatible he (hchart_c_A' he')
