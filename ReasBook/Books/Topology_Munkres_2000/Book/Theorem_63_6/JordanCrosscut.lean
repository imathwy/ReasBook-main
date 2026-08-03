module

public import Topology_Munkres_2000.Book.Definition_61_2.Arc
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

open Set
open scoped Topology

universe u

namespace Topology.IsSimpleClosedCurve

/-- Helper for Theorem 63.6: every simple closed curve in a Hausdorff space is the
union of two closed connected arcs meeting exactly at two prescribed distinct endpoints. -/
theorem existsTwoArcDecomposition
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (D : Set X) [Topology.IsSimpleClosedCurve D]
    (p q : D) (hpq : p ≠ q) :
    ∃ D₁ D₂ : Set X,
      D = D₁ ∪ D₂ ∧ D₁ ∩ D₂ = {(p : X), (q : X)} ∧
        IsClosed D₁ ∧ IsClosed D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧
        Topology.IsArc D₁ ∧ Topology.IsArc D₂ := by
  classical
  -- Transport the two canonical circle paths between the selected endpoints into the curve.
  obtain ⟨e⟩ := Topology.IsSimpleClosedCurve.homeomorphic_circle (X := D)
  let f : Circle → X := fun z ↦ (e.symm z : X)
  let D₁ : Set X := Set.range (f ∘ Circle.path (e p) (e q))
  let D₂ : Set X := Set.range (f ∘ Circle.path (e q) (e p))
  have hfContinuous : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hfInjective : Function.Injective f :=
    Subtype.val_injective.comp e.symm.injective
  have hepq : e p ≠ e q := fun h ↦ hpq (e.injective h)
  have hRange : Set.range f = D := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, rfl⟩
      exact (e.symm y).property
    · intro x hx
      have hfx : f (e ⟨x, hx⟩) = x := by
        simp [f]
      exact ⟨e ⟨x, hx⟩, hfx⟩
  have hpath₁Continuous : Continuous (f ∘ Circle.path (e p) (e q)) :=
    hfContinuous.comp (Circle.path (e p) (e q)).continuous
  have hpath₂Continuous : Continuous (f ∘ Circle.path (e q) (e p)) :=
    hfContinuous.comp (Circle.path (e q) (e p)).continuous
  have hpath₁Injective : Function.Injective (f ∘ Circle.path (e p) (e q)) :=
    hfInjective.comp (Circle.path_injective_of_ne hepq)
  have hpath₂Injective : Function.Injective (f ∘ Circle.path (e q) (e p)) :=
    hfInjective.comp (Circle.path_injective_of_ne hepq.symm)
  -- Compact-domain embeddings identify each path range with the unit interval.
  have hD₁Arc : Topology.IsArc D₁ := by
    let hEmbedding : Topology.IsEmbedding (f ∘ Circle.path (e p) (e q)) :=
      hpath₁Continuous.isClosedEmbedding hpath₁Injective |>.isEmbedding
    exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩
  have hD₂Arc : Topology.IsArc D₂ := by
    let hEmbedding : Topology.IsEmbedding (f ∘ Circle.path (e q) (e p)) :=
      hpath₂Continuous.isClosedEmbedding hpath₂Injective |>.isEmbedding
    exact ⟨⟨hEmbedding.toHomeomorph.symm⟩⟩
  have hD₁image : D₁ = f '' Set.range (Circle.path (e p) (e q)) := by
    simp [D₁, Set.range_comp]
  have hD₂image : D₂ = f '' Set.range (Circle.path (e q) (e p)) := by
    simp [D₂, Set.range_comp]
  -- The complementary circle paths cover the circle and meet only at endpoints.
  have hUnion : D = D₁ ∪ D₂ := by
    rw [hD₁image, hD₂image, ← Set.image_union,
      Circle.range_path_union_range_path hepq, Set.image_univ]
    exact hRange.symm
  have hInter : D₁ ∩ D₂ = {(p : X), (q : X)} := by
    rw [hD₁image, hD₂image, ← Set.image_inter hfInjective,
      Circle.range_path_inter_range_path hepq, Set.image_pair]
    simp [f]
  -- Continuity from the compact interval supplies closedness and connectedness.
  refine ⟨D₁, D₂, hUnion, hInter, ?_, ?_, ?_, ?_, hD₁Arc, hD₂Arc⟩
  · exact (isCompact_range hpath₁Continuous).isClosed
  · exact (isCompact_range hpath₂Continuous).isClosed
  · exact isConnected_range hpath₁Continuous
  · exact isConnected_range hpath₂Continuous

end Topology.IsSimpleClosedCurve

/-- Helper for Theorem 63.6: a Jordan crosscut is a parametrized arc in a domain
closure whose only frontier points are its two ambient endpoints. -/
structure JordanCrosscut {X : Type u} [TopologicalSpace X]
    (U : Set X) (p q : X) where
  carrier : Set X
  parameterization : unitInterval ≃ₜ carrier
  source_eq : (parameterization (0 : unitInterval) : X) = p
  target_eq : (parameterization (1 : unitInterval) : X) = q
  carrier_subset_closure : carrier ⊆ closure U
  carrier_inter_frontier : carrier ∩ frontier U = {p, q}

namespace JordanCrosscut

/-- Helper for Theorem 63.6: both endpoints of a Jordan crosscut lie on its carrier. -/
theorem endpoints_mem {X : Type u} [TopologicalSpace X]
    {U : Set X} {p q : X} (γ : JordanCrosscut U p q) :
    p ∈ γ.carrier ∧ q ∈ γ.carrier := by
  -- Read both endpoint memberships from the chosen interval parametrization.
  constructor
  · simpa only [γ.source_eq] using (γ.parameterization (0 : unitInterval)).property
  · simpa only [γ.target_eq] using (γ.parameterization (1 : unitInterval)).property

/-- Helper for Theorem 63.6: both endpoints of a Jordan crosscut lie on the frontier. -/
theorem endpoints_mem_frontier {X : Type u} [TopologicalSpace X]
    {U : Set X} {p q : X} (γ : JordanCrosscut U p q) :
    p ∈ frontier U ∧ q ∈ frontier U := by
  -- Rewrite the carrier-frontier intersection and use the endpoint carrier facts.
  constructor
  · have : p ∈ γ.carrier ∩ frontier U := by
      rw [γ.carrier_inter_frontier]
      exact Set.mem_insert p {q}
    exact this.2
  · have : q ∈ γ.carrier ∩ frontier U := by
      rw [γ.carrier_inter_frontier]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton q))
    exact this.2

end JordanCrosscut
