module

public import Topology_Munkres_2000.Book.Definition_46_3.CompactBall
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

public section

open Filter Set
open scoped CompactConvergence

universe u v

namespace Metric

variable {X : Type u} {Y : Type v} [PseudoMetricSpace Y]

/-- Helper for Exercise 46.1: membership in a uniform ball bounds every pointwise
distance by the radius. -/
private lemma uniformBallOn_subset_pointwise_lt
    {C : Set X} {f : X → Y} {ε : ℝ} :
    uniformBallOn C f ε ⊆ {g | ∀ x ∈ C, dist (f x) (g x) < ε} := by
  intro g hg x hx
  rw [mem_uniformBallOn] at hg
  -- Compare the selected pointwise distance with the defining supremum.
  have hPointwise :
      dist (f x) (g x) ≤ sSup ((fun z ↦ dist (f z) (g z)) '' C) :=
    le_csSup hg.1 ⟨x, hx, rfl⟩
  have hPointwise' : dist (f x) (g x) ≤ supDistOn C f g := by
    rwa [supDistOn_eq_sSup]
  exact hPointwise'.trans_lt hg.2

/-- Helper for Exercise 46.1: a nonnegative common pointwise bound strictly below
the radius places a function in the corresponding uniform ball. -/
private lemma pointwise_le_subset_uniformBallOn
    {C : Set X} {f : X → Y} {r ε : ℝ} (hr : 0 ≤ r) (hrε : r < ε) :
    {g | ∀ x ∈ C, dist (f x) (g x) ≤ r} ⊆ uniformBallOn C f ε := by
  intro g hg
  rw [mem_uniformBallOn]
  -- Package the common bound as both boundedness and an upper bound for the supremum.
  have hUpper : r ∈ upperBounds ((fun x ↦ dist (f x) (g x)) '' C) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  refine ⟨⟨r, hUpper⟩, ?_⟩
  have hSup : sSup ((fun x ↦ dist (f x) (g x)) '' C) ≤ r :=
    Real.sSup_le (fun _ hx ↦ hUpper hx) hr
  rw [supDistOn_eq_sSup]
  exact hSup.trans_lt hrε

/-- Helper for Exercise 46.1: the supremum of pointwise distances is nonnegative,
including when the indexing set is empty. -/
private lemma supDistOn_nonneg (C : Set X) (f g : X → Y) :
    0 ≤ supDistOn C f g := by
  rw [supDistOn_eq_sSup]
  -- Every value in the distance image is nonnegative.
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, hx, rfl⟩
  exact dist_nonneg

/-- Helper for Exercise 46.1: a uniform ball can be recentered at any of its members
after shrinking its radius. -/
private lemma exists_uniformBallOn_subset
    {C : Set X} {f g : X → Y} {ε : ℝ} (hg : g ∈ uniformBallOn C f ε) :
    ∃ δ > 0, uniformBallOn C g δ ⊆ uniformBallOn C f ε := by
  have hgData :
      BddAbove ((fun x ↦ dist (f x) (g x)) '' C) ∧ supDistOn C f g < ε :=
    mem_uniformBallOn.mp hg
  let δ := (ε - supDistOn C f g) / 2
  have hδ : 0 < δ := half_pos (uniformBallOn_radius_pos hg)
  refine ⟨δ, hδ, ?_⟩
  -- The triangle inequality gives the common bound `supDistOn C f g + δ`.
  have hHalf : δ < ε - supDistOn C f g := by
    exact half_lt_self (uniformBallOn_radius_pos hg)
  have hRadius : supDistOn C f g + δ < ε := by
    have hSum : δ + supDistOn C f g < ε :=
      (lt_sub_iff_add_lt).mp hHalf
    simpa [add_comm] using hSum
  intro h hh
  apply pointwise_le_subset_uniformBallOn (C := C) (f := f)
    (r := supDistOn C f g + δ) (ε := ε)
    (add_nonneg (supDistOn_nonneg C f g) hδ.le) hRadius
  intro x hx
  have hfg : dist (f x) (g x) ≤ supDistOn C f g := by
    rw [supDistOn_eq_sSup]
    exact le_csSup hgData.1 ⟨x, hx, rfl⟩
  have hgh : dist (g x) (h x) < δ :=
    uniformBallOn_subset_pointwise_lt hh x hx
  exact (dist_triangle (f x) (g x) (h x)).trans
    (add_le_add hfg hgh.le)

end Metric

namespace UniformOnFun

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- Helper for Exercise 46.1: compact-set uniform balls centered at a function form
a neighborhood basis for compact convergence at that function. -/
private lemma hasBasis_nhds_compactBalls
    (f : UniformOnFun X Y {C : Set X | IsCompact C}) :
    (nhds f).HasBasis
      (fun Cε : Set X × ℝ ↦ IsCompact Cε.1 ∧ 0 < Cε.2)
      (fun Cε ↦ B_[Cε.1](f, Cε.2)) := by
  have hPointwise :
      (nhds f).HasBasis
        (fun Cε : Set X × ℝ ↦ IsCompact Cε.1 ∧ 0 < Cε.2)
        (fun Cε ↦
          {g | ∀ x ∈ Cε.1,
            dist (toFun _ f x) (toFun _ g x) < Cε.2}) := by
    -- Specialize the general uniform-on-sets basis to compact sets and metric entourages.
    simpa [UniformOnFun.gen, dist_comm] using
      UniformOnFun.hasBasis_nhds_of_basis X Y {C : Set X | IsCompact C} f
        ⟨∅, isCompact_empty⟩ (directedOn_of_sup_mem fun _ _ ↦ IsCompact.union)
        Metric.uniformity_basis_dist
  -- The pointwise basis and the uniform-ball basis refine one another.
  refine hPointwise.to_hasBasis ?_ ?_
  · rintro ⟨C, ε⟩ ⟨hC, hε⟩
    exact ⟨⟨C, ε⟩, ⟨hC, hε⟩,
      Metric.uniformBallOn_subset_pointwise_lt⟩
  · rintro ⟨C, ε⟩ ⟨hC, hε⟩
    refine ⟨⟨C, ε / 2⟩, ⟨hC, half_pos hε⟩, ?_⟩
    intro g hg
    exact Metric.pointwise_le_subset_uniformBallOn
      (half_pos hε).le (half_lt_self hε) fun x hx ↦ (hg x hx).le

/-- Exercise 46.1: The compact-set uniform balls form a basis for the topology of
uniform convergence on compact subsets of `X`. -/
theorem isTopologicalBasis_compactBalls :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (UniformOnFun X Y {K : Set X | IsCompact K}) |
        ∃ C : Set X, IsCompact C ∧
          ∃ f : UniformOnFun X Y {K : Set X | IsCompact K},
            ∃ ε > 0, U = B_[C](f, ε)} := by
  -- Reindex the centered local bases by all compact balls containing the base point.
  refine TopologicalSpace.IsTopologicalBasis.of_hasBasis_nhds fun f ↦ ?_
  have hBasis := hasBasis_nhds_compactBalls f
  refine hBasis.to_hasBasis ?_ ?_
  · rintro ⟨C, ε⟩ ⟨hC, hε⟩
    refine ⟨B_[C](f, ε), ⟨?_, ?_⟩, Subset.rfl⟩
    · exact ⟨C, hC, f, ε, hε, rfl⟩
    · exact mem_of_mem_nhds (hBasis.mem_of_mem ⟨hC, hε⟩)
  · rintro _ ⟨⟨C, hC, g, ε, hε, rfl⟩, hf⟩
    -- Recenter the given global ball at `f` to obtain a centered basis ball below it.
    obtain ⟨δ, hδ, hsub⟩ := Metric.exists_uniformBallOn_subset hf
    exact ⟨⟨C, δ⟩, ⟨hC, hδ⟩, hsub⟩

end UniformOnFun
