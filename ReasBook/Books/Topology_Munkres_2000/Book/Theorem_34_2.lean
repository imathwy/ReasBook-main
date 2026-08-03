module

public import Topology_Munkres_2000.Book.Definition_34_1.Separation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Basic

public section

open scoped Topology

universe u v

namespace SeparatesPointsFromClosedSets

/-- Helper for Theorem 34.2: every neighborhood contains the inverse image of a
neighborhood of the evaluation vector. -/
lemma exists_evaluation_nhds_preimage_subset {X : Type u} {J : Type v}
    [TopologicalSpace X] {f : J → C(X, ℝ)} (h : SeparatesPointsFromClosedSets f)
    (x : X) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set (J → ℝ), V ∈ 𝓝 (fun j ↦ f j x) ∧
      (fun y j ↦ f j y) ⁻¹' V ⊆ U := by
  -- Choose a coordinate that detects `x` while vanishing off the interior of `U`.
  have hxU : x ∈ interior U := mem_interior_iff_mem_nhds.2 hU
  have hxComplement : x ∉ (interior U)ᶜ := by
    simpa using hxU
  obtain ⟨j, hjx, hjU⟩ :=
    h.closedSet x (interior U)ᶜ isOpen_interior.isClosed_compl hxComplement
  refine ⟨{z | 0 < z j}, ?_, ?_⟩
  · -- The positive-coordinate cylinder is a neighborhood of the evaluation vector.
    exact (isOpen_Ioi.preimage (continuous_apply j)).mem_nhds hjx
  · -- Positivity in this coordinate forces the source point to lie in `U`.
    intro y hy
    by_contra hyU
    have hyInterior : y ∉ interior U := fun hy ↦ hyU (interior_subset hy)
    simp [hjU y hyInterior] at hy

/-- Helper for Theorem 34.2: the coordinate evaluation map induces the original
topology whenever the coordinates separate points from closed sets. -/
theorem isInducing_evaluation {X : Type u} {J : Type v} [TopologicalSpace X]
    {f : J → C(X, ℝ)} (h : SeparatesPointsFromClosedSets f) :
    Topology.IsInducing (fun x j ↦ f j x) := by
  rw [Topology.isInducing_iff_nhds]
  intro x
  apply le_antisymm
  · -- Coordinatewise continuity gives the forward neighborhood inequality.
    exact (continuous_pi fun j ↦ (f j).continuous).continuousAt.le_comap
  · -- The cylinder lemma recovers each source neighborhood from the product.
    rw [Filter.le_def]
    intro U hU
    obtain ⟨V, hV, hVU⟩ := h.exists_evaluation_nhds_preimage_subset x hU
    exact Filter.mem_comap.2 ⟨V, hV, hVU⟩

end SeparatesPointsFromClosedSets

/-- Theorem 34.2 (1): A `T₁` space with enough continuous real-valued functions
that are positive at a chosen point and vanish outside a prescribed neighborhood
embeds into the corresponding product of copies of `ℝ`. -/
theorem isEmbedding_pi_of_neighborhood_functions {X : Type u} {J : Type v}
    [TopologicalSpace X] [T1Space X] (f : J → C(X, ℝ))
    (h : SeparatesPointsFromClosedSets f) :
    Topology.IsEmbedding (fun x j ↦ f j x) := by
  -- A `T₁` space is `T₀`, so an inducing evaluation map is an embedding.
  exact h.isInducing_evaluation.isEmbedding

/-- Theorem 34.2 (2): If the coordinate functions also take values in
`Set.Icc (0 : ℝ) 1`, their evaluation map embeds the space into the product of
unit intervals. -/
theorem isEmbedding_piIcc_of_neighborhood_functions {X : Type u} {J : Type v}
    [TopologicalSpace X] [T1Space X] (f : J → C(X, ℝ))
    (h : SeparatesPointsFromClosedSets f)
    (h_range : ∀ j x, f j x ∈ Set.Icc (0 : ℝ) 1) :
    Topology.IsEmbedding
      (fun x j ↦ (⟨f j x, h_range j x⟩ : Set.Icc (0 : ℝ) 1)) := by
  -- Coordinatewise subtype inclusion embeds the interval product into the real product.
  have h_inclusion : Topology.IsEmbedding
      (Pi.map (fun _ : J ↦ (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))) :=
    Topology.IsEmbedding.piMap (fun _ ↦ Topology.IsEmbedding.subtypeVal)
  -- After inclusion, the interval-valued evaluation map is the real-valued one.
  have h_comp :
      Pi.map (fun _ : J ↦ (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)) ∘
          (fun x j ↦ (⟨f j x, h_range j x⟩ : Set.Icc (0 : ℝ) 1)) =
        (fun x j ↦ f j x) := by
    funext x j
    rfl
  -- Cancel the embedding of the interval product after identifying the composite.
  apply h_inclusion.of_comp_iff.mp
  rw [h_comp]
  exact isEmbedding_pi_of_neighborhood_functions f h
