module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Example_28_3
public import Topology_Munkres_2000.Book.Exercise_34_7
public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Topology_Munkres_2000.Book.Exercise_30_7
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Regular

public section

universe u

/- Source recovery for Exercise 4.99.3: the original Munkres second-edition scan,
book page 228, explicitly prints the antecedent list in this exact order: connected,
path connected, locally connected, locally path connected, compact, limit point
compact, locally compact Hausdorff, Hausdorff, regular, completely regular, normal,
first-countable, second-countable, Lindelöf, having a countable dense subset, locally
metrizable, and metrizable. The 17 entries below classify precisely that list. -/

/-- Exercise 4.99.3 (1): A compact Hausdorff space need not be connected. -/
theorem compactT2_not_always_connected :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      ConnectedSpace X := by
  -- Lift the discrete two-point space into the quantified universe and pull connectedness back.
  intro h
  have hLift : ConnectedSpace (ULift.{max u 1, 0} Bool) :=
    h (ULift.{max u 1, 0} Bool)
  have hBool : ConnectedSpace Bool := Homeomorph.ulift.connectedSpace_iff.mp hLift
  letI : ConnectedSpace Bool := hBool
  have hEq : false = true :=
    isPreconnected_univ.subsingleton (Set.mem_univ false) (Set.mem_univ true)
  exact Bool.false_ne_true hEq

/-- Exercise 4.99.3 (2): A compact Hausdorff space need not be path connected. -/
theorem compactT2_not_always_pathConnected :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      PathConnectedSpace X := by
  -- Path connectedness on the lifted two-point space implies the impossible
  -- connectedness of `Bool`.
  intro h
  letI : PathConnectedSpace (ULift.{max u 1, 0} Bool) := h (ULift.{max u 1, 0} Bool)
  have hBool : ConnectedSpace Bool := Homeomorph.ulift.connectedSpace_iff.mp inferInstance
  letI : ConnectedSpace Bool := hBool
  have hEq : false = true :=
    isPreconnected_univ.subsingleton (Set.mem_univ false) (Set.mem_univ true)
  exact Bool.false_ne_true hEq

/-- Exercise 4.99.3 (3): A compact Hausdorff space need not be locally connected. -/
theorem compactT2_not_always_locallyConnected :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      LocallyConnectedSpace X := by
  -- Pull local connectedness back to Cantor space, where it would force a
  -- discrete compact topology.
  intro h
  letI : LocallyConnectedSpace (ULift.{max u 1, 0} (ℕ → Bool)) :=
    h (ULift.{max u 1, 0} (ℕ → Bool))
  letI : LocallyConnectedSpace (ℕ → Bool) := Homeomorph.ulift.symm.locallyConnectedSpace
  have hOpen : ∀ x : ℕ → Bool, IsOpen ({x} : Set (ℕ → Bool)) := by
    intro x
    rw [← connectedComponent_eq_singleton x]
    exact isOpen_connectedComponent
  letI : DiscreteTopology (ℕ → Bool) := discreteTopology_iff_isOpen_singleton.mpr hOpen
  letI : Finite (ℕ → Bool) := finite_of_compact_of_discrete
  exact Infinite.false (α := ℕ → Bool) inferInstance

/-- Exercise 4.99.3 (4): A compact Hausdorff space need not be locally path connected. -/
theorem compactT2_not_always_locallyPathConnected :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      LocallyPathConnectedSpace X := by
  -- Local path connectedness gives local connectedness on the lifted Cantor space.
  intro h
  letI : LocallyPathConnectedSpace (ULift.{max u 1, 0} (ℕ → Bool)) :=
    h (ULift.{max u 1, 0} (ℕ → Bool))
  letI : LocallyConnectedSpace (ℕ → Bool) := Homeomorph.ulift.symm.locallyConnectedSpace
  have hOpen : ∀ x : ℕ → Bool, IsOpen ({x} : Set (ℕ → Bool)) := by
    intro x
    rw [← connectedComponent_eq_singleton x]
    exact isOpen_connectedComponent
  letI : DiscreteTopology (ℕ → Bool) := discreteTopology_iff_isOpen_singleton.mpr hOpen
  letI : Finite (ℕ → Bool) := finite_of_compact_of_discrete
  exact Infinite.false (α := ℕ → Bool) inferInstance

/- Exercise 4.99.3 (5): Every compact Hausdorff space is compact. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : CompactSpace X)

/- Exercise 4.99.3 (6): Every compact Hausdorff space is limit point compact. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : LimitPointCompactSpace X)

/- Exercise 4.99.3 (7): Every compact Hausdorff space is locally compact Hausdorff. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (⟨inferInstance, inferInstance⟩ : LocallyCompactSpace X ∧ T2Space X)

/- Exercise 4.99.3 (8): Every compact Hausdorff space is Hausdorff. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : T2Space X)

/- Exercise 4.99.3 (9): Every compact Hausdorff space is regular. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : T3Space X)

/- Exercise 4.99.3 (10): Every compact Hausdorff space is completely regular. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : T35Space X)

/- Exercise 4.99.3 (11): Every compact Hausdorff space is normal. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : T4Space X)

/-- Exercise 4.99.3 (12): A compact Hausdorff space need not be first countable. -/
theorem compactT2_not_always_firstCountable :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      FirstCountableTopology X := by
  -- Pull first countability from the lifted ordinal space back along its canonical homeomorphism.
  intro h
  letI : FirstCountableTopology (ULift.{u, 1} ClosedOmegaOne) := h (ULift.{u, 1} ClosedOmegaOne)
  exact ClosedOmegaOne.notFirstCountable Homeomorph.ulift.symm.isEmbedding.firstCountableTopology

/-- Exercise 4.99.3 (13): A compact Hausdorff space need not be second countable. -/
theorem compactT2_not_always_secondCountable :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      SecondCountableTopology X := by
  -- Pull second countability from the lifted ordinal space back to `ClosedOmegaOne`.
  intro h
  letI : SecondCountableTopology (ULift.{u, 1} ClosedOmegaOne) := h (ULift.{u, 1} ClosedOmegaOne)
  exact ClosedOmegaOne.notSecondCountable Homeomorph.ulift.symm.secondCountableTopology

/- Exercise 4.99.3 (14): Every compact Hausdorff space is Lindelöf. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] ↦
  (inferInstance : LindelofSpace X)

/-- Exercise 4.99.3 (15): A compact Hausdorff space need not be separable. -/
theorem compactT2_not_always_separable :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      TopologicalSpace.SeparableSpace X := by
  -- A separable lifted ordinal space would make its homeomorphic base space separable.
  intro h
  letI : TopologicalSpace.SeparableSpace (ULift.{u, 1} ClosedOmegaOne) :=
    h (ULift.{u, 1} ClosedOmegaOne)
  exact ClosedOmegaOne.notSeparable Homeomorph.ulift.isQuotientMap.separableSpace

/-- Exercise 4.99.3 (16): A compact Hausdorff space need not be locally metrizable. -/
theorem compactT2_not_always_locallyMetrizable :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      LocallyMetrizableSpace X := by
  -- Compact local metrizability makes the lifted ordinal space metrizable, hence so is its base.
  intro h
  letI : LocallyMetrizableSpace (ULift.{u, 1} ClosedOmegaOne) := h (ULift.{u, 1} ClosedOmegaOne)
  letI : TopologicalSpace.MetrizableSpace (ULift.{u, 1} ClosedOmegaOne) :=
    LocallyMetrizableSpace.metrizableSpace_of_compact
  exact ClosedOmegaOne.notMetrizable Homeomorph.ulift.symm.isEmbedding.metrizableSpace

/-- Exercise 4.99.3 (17): A compact Hausdorff space need not be metrizable. -/
theorem compactT2_not_always_metrizable :
    ¬ ∀ (X : Type (max u 1)) [TopologicalSpace X] [CompactSpace X] [T2Space X],
      TopologicalSpace.MetrizableSpace X := by
  -- Pull a hypothetical metric topology on the lifted ordinal space back to `ClosedOmegaOne`.
  intro h
  letI : TopologicalSpace.MetrizableSpace (ULift.{u, 1} ClosedOmegaOne) :=
    h (ULift.{u, 1} ClosedOmegaOne)
  exact ClosedOmegaOne.notMetrizable Homeomorph.ulift.symm.isEmbedding.metrizableSpace
