module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.Equicontinuity

public section

universe u v

/-- Helper for Lemma 45.3: the uniform-function representation is uniformly inducing on
every subtype of continuous maps from a compact space. -/
private lemma isUniformInducing_uniformFunOfContinuousMapSubtype
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] {𝓕 : Set C(X, Y)} :
    IsUniformInducing (fun f : 𝓕 ↦ UniformFun.ofFun (f : X → Y)) := by
  -- Restrict the canonical isometry from continuous maps to uniform functions to the subtype.
  simpa only [Function.comp_def, UniformFun.instPseudoEMetricSpace] using
    (UniformFun.isometry_ofFun_continuousMap.comp isometry_subtype_coe).isUniformInducing

/-- Helper for Lemma 45.3: an equicontinuous subtype of maps into a compact metric space is
totally bounded in its induced uniform structure. -/
private lemma totallyBounded_univ_continuousMapSubtype_of_equicontinuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y] {𝓕 : Set C(X, Y)}
    (h_equicontinuous : Equicontinuous (fun f : 𝓕 ↦ (f : X → Y))) :
    TotallyBounded (Set.univ : Set 𝓕) := by
  -- Ascoli identifies uniform convergence with pointwise convergence on this family.
  have h_uniform :
      IsUniformInducing (UniformFun.ofFun ∘ fun f : 𝓕 ↦ (f : X → Y)) := by
    simpa only [Function.comp_def] using
      (isUniformInducing_uniformFunOfContinuousMapSubtype (𝓕 := 𝓕))
  have h_pointwise : IsUniformInducing (fun f : 𝓕 ↦ (f : X → Y)) :=
    h_equicontinuous.isUniformInducing_uniformFun_iff_pi.mp h_uniform
  -- Pull total boundedness back from the compact product of copies of `Y`.
  have h_product : TotallyBounded (Set.univ : Set (X → Y)) :=
    isCompact_univ.totallyBounded
  simpa only [Set.preimage_univ] using totallyBounded_preimage h_pointwise h_product

/-- Lemma 45.3 (1). An equicontinuous family of continuous maps from a compact
space to a compact metric space is totally bounded for uniform convergence. -/
theorem totallyBounded_uniform_of_equicontinuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y] {𝓕 : Set C(X, Y)}
    (h_equicontinuous : Equicontinuous (fun f : 𝓕 ↦ (f : X → Y))) :
    TotallyBounded
      (Set.range (fun f : 𝓕 ↦ UniformFun.ofFun (f : X → Y))) := by
  -- Transport the shared subtype invariant through the uniform-function embedding.
  have h_image : TotallyBounded
      ((fun f : 𝓕 ↦ UniformFun.ofFun (f : X → Y)) '' (Set.univ : Set 𝓕)) :=
    (totallyBounded_image_iff
      (isUniformInducing_uniformFunOfContinuousMapSubtype (𝓕 := 𝓕))).mpr
        (totallyBounded_univ_continuousMapSubtype_of_equicontinuous h_equicontinuous)
  -- The image of the whole subtype is the range appearing in the statement.
  simpa only [Set.image_univ] using h_image

/-- Lemma 45.3 (2). An equicontinuous family of continuous maps from a compact
space to a compact metric space is totally bounded in the supremum metric on
`C(X, Y)`. -/
theorem totallyBounded_sup_of_equicontinuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y] {𝓕 : Set C(X, Y)}
    (h_equicontinuous : Equicontinuous (fun f : 𝓕 ↦ (f : X → Y))) :
    TotallyBounded 𝓕 := by
  -- Transport the shared subtype invariant through the canonical subtype inclusion.
  have h_image : TotallyBounded
      ((fun f : 𝓕 ↦ (f : C(X, Y))) '' (Set.univ : Set 𝓕)) :=
    (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing).mpr
      (totallyBounded_univ_continuousMapSubtype_of_equicontinuous h_equicontinuous)
  -- The range of the subtype inclusion is exactly the original family.
  simpa only [Set.image_univ, Subtype.range_coe] using h_image
