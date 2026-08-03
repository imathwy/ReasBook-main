module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Equicontinuity

public section

universe u v

open scoped UniformConvergence
open Filter Topology Uniformity

/-- Helper for Lemma 45.2: a uniform function in the range of a continuous family is continuous. -/
private lemma continuous_toFun_of_mem_uniformRange
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] {ι : Type*}
    {F : ι → X → Y} (hF : ∀ i, Continuous (F i)) {g : X →ᵤ Y}
    (hg : g ∈ Set.range (fun i ↦ UniformFun.ofFun (F i))) :
    Continuous (UniformFun.toFun g) := by
  -- Recover the original family member and hence its continuity.
  obtain ⟨i, rfl⟩ := hg
  simpa only [UniformFun.toFun_ofFun] using hF i

/-- Helper for Lemma 45.2: a totally bounded uniform family admits finite pointwise-uniform
approximations whose centers belong to the family. -/
private lemma existsFiniteUniformApproximation
    {X : Type u} {Y : Type v} [MetricSpace Y] {ι : Type*} (F : ι → X → Y)
    (hT : TotallyBounded (Set.range (fun i ↦ UniformFun.ofFun (F i))))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : Set (X →ᵤ Y), t.Finite ∧
      t ⊆ Set.range (fun i ↦ UniformFun.ofFun (F i)) ∧
      ∀ i, ∃ g : t, ∀ x, dist (F i x) (UniformFun.toFun g x) < δ := by
  -- Lift the metric δ-entourage to uniform convergence on the whole domain.
  have h_entourage :
      UniformFun.gen X Y {p : Y × Y | dist p.1 p.2 < δ} ∈ 𝓤 (X →ᵤ Y) := by
    exact (UniformFun.hasBasis_uniformity_of_basis X Y Metric.uniformity_basis_dist).mem_of_mem hδ
  obtain ⟨t, ht_range, ht_finite, ht_cover⟩ := hT.exists_subset h_entourage
  refine ⟨t, ht_finite, ht_range, ?_⟩
  intro i
  have hi : UniformFun.ofFun (F i) ∈ Set.range (fun j ↦ UniformFun.ofFun (F j)) :=
    Set.mem_range_self i
  rcases Set.mem_iUnion.mp (ht_cover hi) with ⟨g, hg⟩
  rcases Set.mem_iUnion.mp hg with ⟨hgt, h_near⟩
  refine ⟨⟨g, hgt⟩, ?_⟩
  -- Membership in the lifted entourage is exactly uniform pointwise δ-closeness.
  intro x
  exact UniformFun.mem_gen.mp h_near x

/-- Helper for Lemma 45.2: every pointwise-continuous family that is totally bounded for
uniform convergence is equicontinuous. -/
private lemma equicontinuous_of_totallyBounded_uniformFun
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] {ι : Type*}
    {F : ι → X → Y} (hF : ∀ i, Continuous (F i))
    (hT : TotallyBounded (Set.range (fun i ↦ UniformFun.ofFun (F i)))) :
    Equicontinuous F := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hδ : 0 < ε / 3 := by
    linarith
  obtain ⟨t, ht_finite, ht_range, ht_approx⟩ :=
    existsFiniteUniformApproximation F hT hδ
  classical
  letI : Fintype t := ht_finite.fintype
  have h_centers_continuous : ∀ g : t, Continuous (UniformFun.toFun g.val) := by
    intro g
    exact continuous_toFun_of_mem_uniformRange hF (ht_range g.property)
  have h_centers_equicontinuous :
      EquicontinuousAt (fun g : t ↦ UniformFun.toFun g.val) x₀ := by
    rw [equicontinuousAt_finite]
    exact fun g ↦ (h_centers_continuous g).continuousAt
  have h_centers_near :
      ∀ᶠ x in 𝓝 x₀, ∀ g : t,
        dist (UniformFun.toFun g.val x₀) (UniformFun.toFun g.val x) < ε / 3 :=
    Metric.equicontinuousAt_iff_right.mp h_centers_equicontinuous (ε / 3) hδ
  -- Transfer the finite centers' common local estimate through the two uniform approximations.
  filter_upwards [h_centers_near] with x hx
  intro i
  obtain ⟨g, hg⟩ := ht_approx i
  calc
    dist (F i x₀) (F i x) ≤
        dist (F i x₀) (UniformFun.toFun g.val x₀) +
          dist (UniformFun.toFun g.val x₀) (UniformFun.toFun g.val x) +
            dist (UniformFun.toFun g.val x) (F i x) :=
      dist_triangle4 _ _ _ _
    _ < ε := by
      rw [dist_comm (UniformFun.toFun g.val x) (F i x)]
      linarith [hg x₀, hx g, hg x]

/-- Lemma 45.2. A totally bounded family of continuous maps under the uniform
metric is equicontinuous. -/
theorem equicontinuous_of_totallyBounded_uniform
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] {𝓕 : Set C(X, Y)}
    (h_totallyBounded : TotallyBounded
      (Set.range (fun f : 𝓕 ↦ UniformFun.ofFun (f : X → Y)))) :
    Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) := by
  -- Continuous maps provide the pointwise continuity required by the indexed-family result.
  exact equicontinuous_of_totallyBounded_uniformFun
    (fun f ↦ f.val.continuous) h_totallyBounded
