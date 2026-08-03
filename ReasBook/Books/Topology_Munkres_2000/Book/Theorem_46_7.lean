module

public import Topology_Munkres_2000.Book.Proposition_46_1.Topologies

public section

universe u v

namespace FunctionTopology

/-- Theorem 46.7 (1). On `X → Y`, the topology of uniform convergence is finer than
the topology of compact convergence. -/
theorem uniform_le_compact {X : Type u} {Y : Type v} [TopologicalSpace X] [UniformSpace Y] :
    uniform X Y ≤ compact X Y := by
  -- Uniform convergence continuously maps to uniform convergence on every compact subset.
  have hcont : Continuous (fun f : UniformFun X Y ↦
      UniformOnFun.ofFun {K : Set X | IsCompact K} (UniformFun.toFun f)) :=
    (UniformOnFun.uniformContinuous_ofUniformFun Y
      {K : Set X | IsCompact K}).continuous
  -- Induce this comparison along the common raw-function carrier.
  rw [uniform, compact]
  calc
    TopologicalSpace.induced UniformFun.ofFun (UniformFun.topologicalSpace X Y) ≤
        TopologicalSpace.induced UniformFun.ofFun
          (TopologicalSpace.induced
            (fun f : UniformFun X Y ↦
              UniformOnFun.ofFun {K : Set X | IsCompact K} (UniformFun.toFun f))
            (UniformOnFun.topologicalSpace X Y {K : Set X | IsCompact K})) :=
      induced_mono hcont.le_induced
    _ = TopologicalSpace.induced (UniformOnFun.ofFun {K : Set X | IsCompact K})
          (UniformOnFun.topologicalSpace X Y {K : Set X | IsCompact K}) := by
      rw [induced_compose]
      rfl

/-- Theorem 46.7 (2). On `X → Y`, the topology of compact convergence is finer than
the topology of pointwise convergence. -/
theorem compact_le_pointwise {X : Type u} {Y : Type v} [TopologicalSpace X] [UniformSpace Y] :
    compact X Y ≤ (Pi.topologicalSpace : TopologicalSpace (X → Y)) := by
  -- Every finite subset is compact, so compact convergence maps continuously to finite convergence.
  have hfinite : {K : Set X | K.Finite} ⊆ {K : Set X | IsCompact K} :=
    fun _ hK ↦ hK.isCompact
  have hcont : Continuous
      (UniformOnFun.ofFun {K : Set X | K.Finite} ∘
        UniformOnFun.toFun {K : Set X | IsCompact K} :
          UniformOnFun X Y {K : Set X | IsCompact K} →
            UniformOnFun X Y {K : Set X | K.Finite}) :=
    (UniformOnFun.uniformContinuous_ofFun_toFun_of_subset Y
      {K : Set X | K.Finite} {K : Set X | IsCompact K} hfinite).continuous
  -- The finite-convergence bundle embeds into the Pi topology on raw functions.
  have hfiniteTopology :
      UniformOnFun.topologicalSpace X Y {K : Set X | K.Finite} =
        TopologicalSpace.induced (UniformOnFun.toFun {K : Set X | K.Finite})
          (Pi.topologicalSpace : TopologicalSpace (X → Y)) :=
    (UniformOnFun.isEmbedding_toFun_finite X Y).isInducing.eq_induced
  rw [compact]
  calc
    TopologicalSpace.induced (UniformOnFun.ofFun {K : Set X | IsCompact K})
        (UniformOnFun.topologicalSpace X Y {K : Set X | IsCompact K}) ≤
      TopologicalSpace.induced (UniformOnFun.ofFun {K : Set X | IsCompact K})
        (TopologicalSpace.induced
          (UniformOnFun.ofFun {K : Set X | K.Finite} ∘
            UniformOnFun.toFun {K : Set X | IsCompact K})
          (UniformOnFun.topologicalSpace X Y {K : Set X | K.Finite})) :=
      induced_mono hcont.le_induced
    _ = TopologicalSpace.induced (UniformOnFun.ofFun {K : Set X | K.Finite})
          (UniformOnFun.topologicalSpace X Y {K : Set X | K.Finite}) := by
      rw [induced_compose]
      rfl
    _ = Pi.topologicalSpace := by
      rw [hfiniteTopology, induced_compose]
      exact induced_fun_id

/-- Helper for Theorem 46.7: in a discrete space, compact subsets are exactly finite subsets. -/
lemma compactSets_eq_finiteSets {X : Type u} [TopologicalSpace X] [DiscreteTopology X] :
    {K : Set X | IsCompact K} = {K : Set X | K.Finite} := by
  -- Extensionality reduces the indexing-family equality to compactness in a discrete space.
  ext K
  exact isCompact_iff_finite

/-- Theorem 46.7 (3). If `X` is compact, uniform convergence and compact convergence
define the same topology on `X → Y`. -/
theorem uniform_eq_compact_of_compact {X : Type u} {Y : Type v} [TopologicalSpace X]
    [CompactSpace X] [UniformSpace Y] :
    uniform X Y = compact X Y := by
  -- Since `univ` is compact, compact convergence is uniformly equivalent to uniform convergence.
  let comparison := UniformOnFun.uniformEquivUniformFun Y
    {K : Set X | IsCompact K} isCompact_univ
  have hcomparison :
      UniformOnFun.topologicalSpace X Y {K : Set X | IsCompact K} =
        TopologicalSpace.induced comparison
          (UniformFun.topologicalSpace X Y) :=
    comparison.isUniformInducing.isInducing.eq_induced
  -- Transport the inducing equality back to the common raw-function carrier.
  symm
  rw [compact, uniform, hcomparison, induced_compose]
  rfl

/-- Theorem 46.7 (4). If `X` is discrete, compact convergence and pointwise convergence
define the same topology on `X → Y`. -/
theorem compact_eq_pointwise_of_discrete {X : Type u} {Y : Type v} [TopologicalSpace X]
    [DiscreteTopology X] [UniformSpace Y] :
    compact X Y = (Pi.topologicalSpace : TopologicalSpace (X → Y)) := by
  -- Replace the compact indexing family by the finite indexing family.
  rw [compact, compactSets_eq_finiteSets]
  -- Finite convergence induces exactly the Pi topology on the raw function space.
  rw [(UniformOnFun.isEmbedding_toFun_finite X Y).isInducing.eq_induced,
    induced_compose]
  exact induced_fun_id

end FunctionTopology
