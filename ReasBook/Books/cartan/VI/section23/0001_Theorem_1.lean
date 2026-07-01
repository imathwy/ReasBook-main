import Mathlib
import cartan.III.section07.«0002_Theorem_III_1_extra_2»
import cartan.VI.section22.«0006_Definition_VI_1_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Metric Set

/-- Helper for Theorem 1: if a holomorphic isomorphism is defined on all of `ℂ`, then every value
of its underlying map lies in the target set. -/
lemma HolomorphicIsomorph.range_subset_target_of_source_univ {D : Set ℂ}
    (e : HolomorphicIsomorph (univ : Set ℂ) D) :
    Set.range (e : ℂ → ℂ) ⊆ D := by
  -- Any point in the range is the image of a source point, and the source is all of `ℂ`.
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simp [HolomorphicIsomorph.source_eq]
  simpa [HolomorphicIsomorph.target_eq] using
    (e : OpenPartialHomeomorph ℂ ℂ).map_source hz

/-- Helper for Theorem 1: if the target of a holomorphic isomorphism from `ℂ` is bounded, then the
range of its underlying entire map is bounded. -/
lemma HolomorphicIsomorph.isBounded_range_of_source_univ {D : Set ℂ}
    (e : HolomorphicIsomorph (univ : Set ℂ) D) (hD : Bornology.IsBounded D) :
    Bornology.IsBounded (Set.range (e : ℂ → ℂ)) := by
  -- The range is contained in the bounded target, so boundedness descends by inclusion.
  exact hD.subset e.range_subset_target_of_source_univ

/-- Helper for Theorem 1: a holomorphic isomorphism with source `ℂ` cannot be constant, because
its underlying partial homeomorphism is injective on all of `ℂ`. -/
lemma HolomorphicIsomorph.ne_const_of_source_univ {D : Set ℂ}
    (e : HolomorphicIsomorph (univ : Set ℂ) D) (c : ℂ) :
    (e : ℂ → ℂ) ≠ Function.const ℂ c := by
  intro hconst
  -- Source equality upgrades injectivity-on-source to injectivity on the whole plane.
  have hinj : Set.InjOn (e : ℂ → ℂ) univ := by
    simpa [HolomorphicIsomorph.source_eq] using
      (e : OpenPartialHomeomorph ℂ ℂ).injOn
  have hEq : e 0 = e 1 := by
    simp [hconst]
  have h01 : (0 : ℂ) = 1 := hinj (by simp) (by simp) hEq
  norm_num at h01

/-- Theorem 1. The complex plane `ℂ` and the open disc `|z| < 1` are not biholomorphically
isomorphic. -/
theorem complex_plane_not_biholomorphic_to_open_unit_disc :
    ¬ Nonempty (HolomorphicIsomorph (univ : Set ℂ) (ball (0 : ℂ) 1)) := by
  rintro ⟨e⟩
  -- The source proof controls the global image: the disc target makes the entire map bounded.
  have hbounded : Bornology.IsBounded (Set.range (e : ℂ → ℂ)) := by
    have hball : Bornology.IsBounded (ball (0 : ℂ) 1) := by
      simpa using Metric.isBounded_ball (x := (0 : ℂ)) (r := (1 : ℝ))
    exact e.isBounded_range_of_source_univ hball
  -- Liouville turns a bounded entire map into a constant one.
  obtain ⟨c, hc⟩ := exists_eq_const_of_bounded_of_analyticOnNhd_univ
    (hf := e.analyticOn_toFun) (hb := hbounded)
  -- A biholomorphic map on all of `ℂ` cannot be constant, so we get the contradiction.
  exact e.ne_const_of_source_univ c hc
