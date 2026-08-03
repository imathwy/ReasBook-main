module

public import Topology_Munkres_2000.Book.Exercise_32_7.Separation
public import Topology_Munkres_2000.Book.Example_32_2.Separation
public import Topology_Munkres_2000.Book.Exercise_29_7.Compactification
public import Mathlib.Logic.Small.Basic
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Topology.Order.T5
import Topology_Munkres_2000.Book.Example_31_3.Separation

public section

universe u

section

variable {X : Type u}

/- Exercise 32.7 (1): Every subspace of a completely normal space is completely
normal. Here `T5Space` expresses the book's `T₁` convention. -/
#check fun [TopologicalSpace X] [T5Space X] (p : X → Prop) ↦
  (inferInstance : T5Space {x // p x})

/- Exercise 32.7 (2): Products of completely normal spaces need not be completely
normal; the Sorgenfrey plane is a counterexample. -/
theorem sorgenfreyPlane_not_completelyNormal :
    ¬ T5Space (SorgenfreyLine × SorgenfreyLine) := by
  intro h
  exact SorgenfreyPlane.notT4 {
    toT1Space := h.toT1Space
    toNormalSpace := h.toCompletelyNormalSpace.toNormalSpace
  }

/- Exercise 32.7 (3): Every well-ordered set with the order topology is completely
normal in the book's `T₁` convention. -/
#check fun [LinearOrder X] [WellFoundedLT X] [TopologicalSpace X] [OrderTopology X] ↦
  (inferInstance : T5Space X)

/- Exercise 32.7 (4): Every metrizable space is completely normal in the book's
`T₁` convention. -/
#check fun [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] ↦
  (inferInstance : T5Space X)

/-- Helper for Exercise 32.7: the closed first-uncountable ordinal has a copy in
the universe of its ordinal representatives. -/
private noncomputable instance closedOmegaOneSmall : Small.{u} ClosedOmegaOne.{u} := by
  -- Identify the space with the small closed ordinal interval used in its definition.
  change Small.{u} (Set.Iic (Ordinal.omega 1 : Ordinal.{u}))
  infer_instance

/-- Helper for Exercise 32.7: the deleted ordinal plank embeds in the closed
first-uncountable ordinal square. -/
private lemma isEmbedding_openOmegaOne_prodClosedOmegaOne :
    Topology.IsEmbedding (fun p : OpenOmegaOne.{u} × ClosedOmegaOne.{u} ↦
      (OpenOmegaOne.toClosed p.1, p.2)) := by
  -- Express the coordinatewise inclusion as the standard product map.
  change Topology.IsEmbedding (Prod.map OpenOmegaOne.toClosed id)
  exact OpenOmegaOne.isEmbedding_toClosed.prodMap Topology.IsEmbedding.id

/-- Helper for Exercise 32.7: the closed first-uncountable ordinal square is
not completely normal in the `T₁` convention. -/
private lemma closedOmegaOneSquare_notT5 :
    ¬ T5Space (ClosedOmegaOne.{u} × ClosedOmegaOne.{u}) := by
  intro h
  -- Complete normality descends to the embedded deleted ordinal plank.
  letI : T5Space (ClosedOmegaOne.{u} × ClosedOmegaOne.{u}) := h
  have hPlank : T5Space (OpenOmegaOne.{u} × ClosedOmegaOne.{u}) :=
    isEmbedding_openOmegaOne_prodClosedOmegaOne.t5Space
  -- Its induced normality contradicts the established deleted-plank example.
  exact OpenOmegaOne.prodClosedOmegaOne_notT4 hPlank.toT4Space

/-- Helper for Exercise 32.7: a universe-lowered copy of the closed ordinal
square is still not completely normal. -/
private lemma shrinkClosedOmegaOneSquare_notT5 :
    ¬ T5Space (Shrink.{u} (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})) := by
  intro h
  -- Transfer the assumed separation property back across the shrinking homeomorphism.
  letI : T5Space (Shrink.{u} (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})) := h
  have hSquare : T5Space (ClosedOmegaOne.{u} × ClosedOmegaOne.{u}) :=
    (Shrink.homeomorph (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})).symm.t5Space
  exact closedOmegaOneSquare_notT5 hSquare

/-- Exercise 32.7 (5): Compact Hausdorff spaces need not be completely normal. -/
theorem compactT2_not_always_completelyNormal :
    ¬ ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      T5Space X := by
  intro h
  -- Transfer compactness and Hausdorffness to a copy living in the target universe.
  letI : CompactSpace (Shrink.{u} (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})) :=
    (Shrink.homeomorph (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})).compactSpace
  letI : T2Space (Shrink.{u} (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})) :=
    (Shrink.homeomorph (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})).t2Space
  -- Specialize the universal claim to this compact Hausdorff copy.
  exact shrinkClosedOmegaOneSquare_notT5
    (h (Shrink.{u} (ClosedOmegaOne.{u} × ClosedOmegaOne.{u})))

/- Exercise 32.7 (6): Every regular space with a countable basis is completely
normal. Here `T3Space` and `T5Space` express the book's separation conventions. -/
#check fun [TopologicalSpace X] [T3Space X] [SecondCountableTopology X] ↦
  (inferInstance : T5Space X)

/- Exercise 32.7 (7): The Sorgenfrey line `SorgenfreyLine` is completely normal. -/
#check SorgenfreyLine.instT5Space

end
