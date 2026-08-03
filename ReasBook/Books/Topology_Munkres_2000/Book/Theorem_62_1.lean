module

public import Topology_Munkres_2000.Book.Theorem_62_1.Index
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Maps.Basic

public section

/-- Helper for Theorem 62.1: an injective map into a subsingleton space is an open
embedding. -/
private lemma isOpenEmbedding_of_injective_subsingleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Subsingleton Y] (f : X → Y) (hf : Function.Injective f) :
    Topology.IsOpenEmbedding f := by
  -- Injectivity transfers the subsingleton property to the source, so both topologies are discrete.
  letI : Subsingleton X := hf.subsingleton
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    continuous_of_discreteTopology hf ?_
  -- Every image is open in the discrete codomain.
  intro s _
  exact isOpen_discrete (f '' s)

/-- Helper for Theorem 62.1: openness of images of sufficiently small restricted balls
implies that a map from an open metric subspace is open. -/
private lemma isOpenMap_of_open_restricted_ball_images {E F : Type*} [PseudoMetricSpace E]
    [TopologicalSpace F] {U : Set E} (hU : IsOpen U) (f : U → F)
    (hball : ∀ (c : E) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ U →
      IsOpen (f '' {x : U | (x : E) ∈ Metric.ball c r})) : IsOpenMap f := by
  intro s hs
  -- Regard the open subset of `U` as an open subset of the ambient metric space.
  have hsAmbient : IsOpen (Subtype.val '' s) := hU.isOpenMap_subtype_val s hs
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro y hy
  obtain ⟨x, hxs, rfl⟩ := hy
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hsAmbient x.1 ⟨x, hxs, rfl⟩
  have hrHalf : 0 < r / 2 := half_pos hr
  have hclosed : Metric.closedBall x.1 (r / 2) ⊆ U := by
    intro z hz
    obtain ⟨w, _, hw⟩ := hrs (Metric.closedBall_subset_ball (half_lt_self hr) hz)
    rw [← hw]
    exact w.property
  -- The half-radius ball has closed ball in `U`, and its image is the required neighborhood.
  refine ⟨f '' {z : U | (z : E) ∈ Metric.ball x.1 (r / 2)}, ?_,
    hball x.1 (r / 2) hrHalf hclosed, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨w', hw's, hww'⟩ := hrs (Metric.ball_subset_ball (half_le_self hr.le) hw)
    have hwEq : w' = w := Subtype.ext hww'
    exact ⟨w, hwEq ▸ hw's, rfl⟩
  · exact ⟨x, Metric.mem_ball_self hrHalf, rfl⟩

/-- Theorem 62.1. Brouwer's invariance of domain theorem: a continuous injective map
from an open subset of `EuclideanSpace ℝ (Fin n)` into the same Euclidean space is an
open embedding. Thus its range is open, and `f` is a homeomorphism onto its range. -/
theorem invarianceOfDomain {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (f : U → EuclideanSpace ℝ (Fin n)) (hf_continuous : Continuous f)
    (hf_injective : Function.Injective f) : Topology.IsOpenEmbedding f := by
  -- Dimension zero is discrete because the Euclidean codomain is a subsingleton.
  by_cases hn : n = 0
  · subst n
    exact isOpenEmbedding_of_injective_subsingleton f hf_injective
  · refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf_continuous
      hf_injective ?_
    -- Route correction: the stalled Alexander endpoint comparison is replaced
    -- by the normalized-boundary-displacement obstruction on every positive dimension.
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    refine isOpenMap_of_open_restricted_ball_images hU f ?_
    intro c r hr hclosed
    exact InvarianceOfDomainSupport.isOpen_image_restricted_euclidean_ball hnPos f
      hf_continuous hf_injective c r hr hclosed

end
