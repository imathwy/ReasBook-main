module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Instances.Irrational

public section

open Set

universe u

/-- Helper for Exercise 43.6: a point of a countable intersection belongs to each open factor. -/
private lemma mem_openOf_mem_iInter {X : Type u} [MetricSpace X] {s : Set X}
    (V : ℕ → TopologicalSpace.Opens X) (hs : s = ⋂ n, (V n : Set X)) (x : s) (n : ℕ) :
    x.1 ∈ V n := by
  -- Rewrite the subtype membership as membership in every open factor.
  have hx : x.1 ∈ ⋂ n, (V n : Set X) := by
    rw [← hs]
    exact x.2
  exact Set.mem_iInter.mp hx n

/-- Helper for Exercise 43.6: the diagonal map into the complete copies of the open factors. -/
private def gDeltaDiagonal {X : Type u} [MetricSpace X] {s : Set X}
    (V : ℕ → TopologicalSpace.Opens X) (hs : s = ⋂ n, (V n : Set X)) :
    s → ∀ n, (V n).CompleteCopy :=
  fun x n ↦ ⟨x.1, mem_openOf_mem_iInter V hs x n⟩

/-- Helper for Exercise 43.6: a family with constant underlying point determines a point of the
intersection of its open factors. -/
private lemma constantUnderlying_mem_iInter {X : Type u} [MetricSpace X] {s : Set X}
    (V : ℕ → TopologicalSpace.Opens X) (hs : s = ⋂ n, (V n : Set X))
    (y : ∀ n, (V n).CompleteCopy) (hy : ∀ n, (y n).1 = (y 0).1) :
    (y 0).1 ∈ s := by
  -- Check membership factorwise, replacing the zeroth coordinate by the relevant coordinate.
  rw [hs, Set.mem_iInter]
  intro n
  rw [← hy n]
  exact (y n).2

/-- Helper for Exercise 43.6: the range of the diagonal consists exactly of families with constant
underlying point. -/
private lemma range_gDeltaDiagonal {X : Type u} [MetricSpace X] {s : Set X}
    (V : ℕ → TopologicalSpace.Opens X) (hs : s = ⋂ n, (V n : Set X)) :
    Set.range (gDeltaDiagonal V hs) = {y | ∀ n, (y n).1 = (y 0).1} := by
  -- Compare both descriptions pointwise and reconstruct the source point from coordinate zero.
  ext y
  constructor
  · rintro ⟨x, rfl⟩ n
    rfl
  · intro hy
    refine ⟨⟨(y 0).1, constantUnderlying_mem_iInter V hs y hy⟩, ?_⟩
    funext n
    apply Subtype.ext
    exact (hy n).symm

/-- Helper for Exercise 43.6: the diagonal into complete open copies is a closed embedding. -/
private lemma gDeltaDiagonal_isClosedEmbedding {X : Type u} [MetricSpace X] {s : Set X}
    (V : ℕ → TopologicalSpace.Opens X) (hs : s = ⋂ n, (V n : Set X)) :
    Topology.IsClosedEmbedding (gDeltaDiagonal V hs) := by
  -- Establish continuity coordinatewise and recover the source topology through coordinate zero.
  have hcontinuous : Continuous (gDeltaDiagonal V hs) := by
    exact continuous_pi fun n ↦ continuous_subtype_val.subtype_mk _
  have hprojection : Continuous (fun y : ∀ n, (V n).CompleteCopy ↦ (y 0).1) := by
    exact continuous_subtype_val.comp (continuous_apply 0)
  have hcomp :
      (fun y : ∀ n, (V n).CompleteCopy ↦ (y 0).1) ∘ gDeltaDiagonal V hs =
        fun x : s ↦ x.1 := by
    rfl
  have hembedding : Topology.IsEmbedding (gDeltaDiagonal V hs) := by
    refine Topology.IsEmbedding.of_comp hcontinuous hprojection ?_
    rw [hcomp]
    exact Topology.IsEmbedding.subtypeVal
  refine ⟨hembedding, ?_⟩
  -- The range is a countable intersection of closed equalizers in the Hausdorff metric space `X`.
  rw [range_gDeltaDiagonal]
  have hcoordinate (n : ℕ) :
      Continuous (fun y : ∀ k, (V k).CompleteCopy ↦ (y n).1) := by
    exact continuous_subtype_val.comp (continuous_apply n)
  rw [Set.setOf_forall]
  exact isClosed_iInter fun n ↦ isClosed_eq (hcoordinate n) (hcoordinate 0)

/-- Exercise 43.6: A `Gδ` subspace of a completely metrizable space is completely metrizable. -/
theorem IsGδ.isCompletelyMetrizableSpace {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] {s : Set X} (hs : IsGδ s) :
    TopologicalSpace.IsCompletelyMetrizableSpace s := by
  -- Choose a compatible complete metric and express the `Gδ` set as a countable open intersection.
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  obtain ⟨U, hUopen, hsU⟩ := hs.eq_iInter_nat
  let V : ℕ → TopologicalSpace.Opens X := fun n ↦ ⟨U n, hUopen n⟩
  have hsV : s = ⋂ n, (V n : Set X) := hsU
  -- Transfer complete metrizability from the complete product along the closed diagonal embedding.
  exact (gDeltaDiagonal_isClosedEmbedding V hsV).IsCompletelyMetrizableSpace

/-- An open subspace of a completely metrizable space is completely metrizable. -/
theorem IsOpen.isCompletelyMetrizableSpace {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] {s : Set X} (hs : IsOpen s) :
    TopologicalSpace.IsCompletelyMetrizableSpace s :=
  hs.isGδ.isCompletelyMetrizableSpace

namespace Irrational

/-- The subtype of irrational real numbers is completely metrizable. -/
instance instIsCompletelyMetrizableSpace :
    TopologicalSpace.IsCompletelyMetrizableSpace {x : ℝ // Irrational x} :=
  IsGδ.setOf_irrational.isCompletelyMetrizableSpace

end Irrational
