import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Exercise_6_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set
open scoped ContDiff Manifold

-- Semantic Lean search tool unavailable in this environment; this proposition now reuses the
-- local Section 6.38 owner `has_measure_zero_in_manifold` instead of restating its chartwise
-- criterion.

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddHaarMeasure]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Helper for Proposition 6.8: a manifold measure-zero set has zero `volume` in the preferred
chart normal form `target ∩ extChartAt.symm ⁻¹' A`. -/
lemma extChartAtPreimageVolumeEqZero {A : Set M} (hA : has_measure_zero_in_manifold I A) (x : M) :
    volume ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' A) = 0 := by
  -- Rewrite the preferred-chart image statement into the target/preimage normal form used later.
  rw [← (extChartAt I x).image_source_inter_eq' A]
  simpa [inter_comm] using has_measure_zero_in_manifold.extChartAt_volume_eq_zero I hA x

/-- Proposition 6.8: if `A ⊆ M` has measure zero in the smooth manifold `M`, then its complement
`Aᶜ = M \ A` is dense in `M`. -/
theorem has_measure_zero_in_manifold.dense_compl {A : Set M}
    (hA : has_measure_zero_in_manifold I A) :
    Dense (Aᶜ : Set M) := by
  -- Rewrite density of the complement as emptiness of the interior.
  rw [← interior_eq_empty_iff_dense_compl]
  by_contra hInterior
  obtain ⟨x, hx⟩ : (interior A).Nonempty := Set.nonempty_iff_ne_empty.mpr hInterior
  let s : Set E := (extChartAt I x).symm ⁻¹' A ∩ (extChartAt I x).target
  -- The preferred-chart representative has zero ambient volume.
  have hzero : volume ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' A) = 0 :=
    extChartAtPreimageVolumeEqZero (I := I) hA x
  -- But an interior point of `A` maps into the closure of the interior of that chart-side set.
  have hclosure : extChartAt I x x ∈ closure (interior s) := by
    exact extChartAt_mem_closure_interior (I := I) (s := A) (x₀ := x) (x := x)
      (subset_closure hx) (mem_extChartAt_source (I := I) x)
  have hempty : interior s = ∅ :=
    Measure.interior_eq_empty_of_null (μ := volume) (by simpa [s, inter_comm] using hzero)
  rw [hempty, closure_empty] at hclosure
  exact hclosure.elim
