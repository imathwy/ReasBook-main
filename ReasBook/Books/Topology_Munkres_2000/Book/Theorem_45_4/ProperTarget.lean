module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.ProperSpace

import Mathlib.Topology.MetricSpace.Bounded

public section

universe u v

namespace BoundedContinuousFunction

/-- Helper for Theorem 45.4: total boundedness in the uniform metric makes the underlying
family of functions equicontinuous. -/
private lemma equicontinuous_coe_of_totallyBounded
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    {𝓕 : Set (X →ᵇ Y)} (h_totallyBounded : TotallyBounded 𝓕) :
    Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hε3 : 0 < ε / 3 := by
    linarith
  obtain ⟨t, ht_finite, ht_cover⟩ :=
    Metric.totallyBounded_iff.mp h_totallyBounded (ε / 3) hε3
  classical
  letI : Fintype t := ht_finite.fintype
  have h_centers : EquicontinuousAt (fun g : t ↦ (g.val : X → Y)) x₀ := by
    rw [equicontinuousAt_finite]
    exact fun g ↦ g.val.continuous.continuousAt
  have h_centers_near :
      ∀ᶠ x in nhds x₀, ∀ g : t, dist (g.val x₀) (g.val x) < ε / 3 :=
    Metric.equicontinuousAt_iff_right.mp h_centers (ε / 3) hε3
  -- Approximate each family member by one finite center and transfer its local estimate.
  filter_upwards [h_centers_near] with x hx
  intro f
  rcases Set.mem_iUnion.mp (ht_cover f.property) with ⟨g, hg⟩
  rcases Set.mem_iUnion.mp hg with ⟨hgt, hfg⟩
  have h_left : dist (f.val x₀) (g x₀) < ε / 3 :=
    (dist_coe_le_dist x₀).trans_lt hfg
  have hgf : dist g f.val < ε / 3 := by
    rw [dist_comm]
    exact hfg
  have h_right : dist (g x) (f.val x) < ε / 3 :=
    (dist_coe_le_dist x).trans_lt hgf
  calc
    dist (f.val x₀) (f.val x) ≤
        dist (f.val x₀) (g x₀) + dist (g x₀) (g x) + dist (g x) (f.val x) :=
      dist_triangle4 _ _ _ _
    _ < ε := by
      linarith [h_left, hx ⟨g, hgt⟩, h_right]

/-- Helper for Theorem 45.4: an equicontinuous, pointwise bounded family on a compact
domain has a bounded union of ranges. -/
private lemma isBounded_iUnion_range_of_equicontinuous_of_pointwiseBounded
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    {𝓕 : Set (X →ᵇ Y)}
    (h_equicontinuous : Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)))
    (h_pointwise : PointwiseBounded (fun f : 𝓕 ↦ (f : X → Y))) :
    Bornology.IsBounded (⋃ f : 𝓕, Set.range (f : X → Y)) := by
  let U : X → Set X := fun a ↦ {x | ∀ f : 𝓕, dist (f.val a) (f.val x) < 1}
  have hU : ∀ a, U a ∈ nhds a := by
    intro a
    exact Metric.equicontinuousAt_iff_right.mp (h_equicontinuous a) 1 zero_lt_one
  obtain ⟨t, ht_cover⟩ := finite_cover_nhds hU
  have h_center_values :
      Bornology.IsBounded (⋃ a ∈ t, Set.range (fun f : 𝓕 ↦ f.val a)) := by
    rw [Bornology.isBounded_biUnion_finset]
    exact fun a _ ↦ pointwiseBounded_iff.mp h_pointwise a
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp h_center_values
  refine Metric.isBounded_iff.mpr ⟨C + 2, ?_⟩
  intro y hy z hz
  rcases Set.mem_iUnion.mp hy with ⟨f, hf⟩
  rcases hf with ⟨x, rfl⟩
  rcases Set.mem_iUnion.mp hz with ⟨g, hg⟩
  rcases hg with ⟨x', rfl⟩
  have hx_cover : x ∈ ⋃ a ∈ t, U a := by
    rw [ht_cover]
    exact Set.mem_univ x
  have hx'_cover : x' ∈ ⋃ a ∈ t, U a := by
    rw [ht_cover]
    exact Set.mem_univ x'
  rcases Set.mem_iUnion.mp hx_cover with ⟨a, hxa⟩
  rcases Set.mem_iUnion.mp hxa with ⟨hat, hxaU⟩
  rcases Set.mem_iUnion.mp hx'_cover with ⟨b, hxb⟩
  rcases Set.mem_iUnion.mp hxb with ⟨hbt, hxbU⟩
  have hfa : f.val a ∈ ⋃ c ∈ t, Set.range (fun k : 𝓕 ↦ k.val c) :=
    Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨hat, Set.mem_range_self f⟩⟩
  have hgb : g.val b ∈ ⋃ c ∈ t, Set.range (fun k : 𝓕 ↦ k.val c) :=
    Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨hbt, Set.mem_range_self g⟩⟩
  -- Route both arbitrary values through bounded values at finite cover centers.
  calc
    dist (f.val x) (g.val x') ≤
        dist (f.val x) (f.val a) + dist (f.val a) (g.val b) +
          dist (g.val b) (g.val x') :=
      dist_triangle4 _ _ _ _
    _ ≤ C + 2 := by
      have hfx : dist (f.val x) (f.val a) < 1 := by
        simpa [dist_comm] using hxaU f
      have hgx : dist (g.val b) (g.val x') < 1 := hxbU g
      linarith [hC hfa hgb]

/-- For a proper metric target, a family of continuous maps from a compact space has compact
closure in the uniform topology exactly when it is equicontinuous and pointwise bounded. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseBounded
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] [ProperSpace Y] (𝓕 : Set (X →ᵇ Y)) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) ∧
        PointwiseBounded (fun f : 𝓕 ↦ (f : X → Y)) := by
  constructor
  · intro h_compact
    have h_totallyBounded : TotallyBounded 𝓕 :=
      h_compact.totallyBounded.subset subset_closure
    have h_bounded : Bornology.IsBounded 𝓕 := h_compact.isBounded.subset subset_closure
    refine ⟨equicontinuous_coe_of_totallyBounded h_totallyBounded,
      pointwiseBounded_iff.mpr fun x ↦ ?_⟩
    -- Evaluation is Lipschitz, so boundedness of the compact closure gives each pointwise bound.
    have h_image := (lipschitz_eval_const x).isBounded_image h_bounded
    simpa only [Set.image_eq_range] using h_image
  · rintro ⟨h_equicontinuous, h_pointwise⟩
    let R : Set Y := ⋃ f : 𝓕, Set.range (f : X → Y)
    have hR_bounded : Bornology.IsBounded R :=
      isBounded_iUnion_range_of_equicontinuous_of_pointwiseBounded
        h_equicontinuous h_pointwise
    have hR_compact : IsCompact (closure R) := hR_bounded.isCompact_closure
    -- The compact closure of the common range is the target set for Arzelà--Ascoli.
    refine arzela_ascoli (closure R) hR_compact 𝓕 ?_ h_equicontinuous
    intro f x hf
    exact subset_closure (Set.mem_iUnion.2
      ⟨⟨f, hf⟩, Set.mem_range_self x⟩)

end BoundedContinuousFunction
