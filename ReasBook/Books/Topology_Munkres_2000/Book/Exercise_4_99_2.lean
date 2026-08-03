module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.RatLemmas
public import Mathlib.Topology.Separation.CompletelyRegular

public section

universe u

/-- Helper for Exercise 4.99.2: an infinite discrete space is not compact. -/
private lemma infiniteDiscrete_not_compact (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [Infinite X] : ¬ CompactSpace X := by
  -- Compactness would make the discrete carrier finite.
  intro h
  letI : CompactSpace X := h
  letI : Finite X := finite_of_compact_of_discrete
  exact Infinite.false (α := X) inferInstance

/-- Helper for Exercise 4.99.2: an infinite discrete space is not limit point compact. -/
private lemma infiniteDiscrete_not_limitPointCompact (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [Infinite X] : ¬ LimitPointCompactSpace X := by
  -- The whole carrier is infinite, but a singleton neighborhood rules out accumulation points.
  intro h
  obtain ⟨x, hx⟩ := h.exists_accPt (Set.univ : Set X) Set.infinite_univ
  rw [accPt_iff_nhds] at hx
  obtain ⟨y, hy, hne⟩ := hx {x} (discreteTopology_iff_singleton_mem_nhds.mp inferInstance x)
  have hyx : y = x := by
    simpa using hy.1
  exact hne hyx

/-- Helper for Exercise 4.99.2: a totally disconnected space with a non-isolated point
is not locally connected. -/
private lemma not_locallyConnectedSpace_of_totallyDisconnected_of_nonisolated
    {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (x : X) [Filter.NeBot (nhdsWithin x {x}ᶜ)] : ¬ LocallyConnectedSpace X := by
  -- Local connectedness would make the singleton connected component of `x` open.
  intro h
  letI : LocallyConnectedSpace X := h
  apply not_isOpen_singleton x
  rw [← connectedComponent_eq_singleton x]
  exact isOpen_connectedComponent

namespace Rat

/-- Helper for Exercise 4.99.2: the rational line is not locally compact. -/
private lemma not_locallyCompactSpace : ¬ LocallyCompactSpace ℚ := by
  -- A compact neighborhood of zero would have nonempty interior, unlike every compact set in `ℚ`.
  intro h
  letI : LocallyCompactSpace ℚ := h
  obtain ⟨K, hK, hKzero⟩ := exists_compact_mem_nhds (0 : ℚ)
  have hzero : (0 : ℚ) ∈ interior K := mem_interior_iff_mem_nhds.mpr hKzero
  rw [interior_compact_eq_empty hK] at hzero
  exact hzero

end Rat

/-- Helper for Exercise 4.99.2: an uncountable discrete space is not second-countable. -/
private lemma not_secondCountableTopology_of_uncountable_discrete
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X]
    (hX : ¬ Countable X) : ¬ SecondCountableTopology X := by
  -- A second-countable space is separable, and a separable discrete space is countable.
  intro h
  letI : SecondCountableTopology X := h
  exact hX (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/- Exercise 4.99.2 refers, in order, to the following list printed at the start of the
supplementary exercises: connected, path connected, locally connected, locally path
connected, compact, limit point compact, locally compact Hausdorff, Hausdorff,
regular, completely regular, normal, first-countable, second-countable, Lindelöf,
having a countable dense subset, locally metrizable, and metrizable. -/

/-- Helper for Exercise 4.99.2 (1): a metric space need not be connected. -/
theorem not_every_metricSpace_connected :
    ¬ ∀ (X : Type u) [MetricSpace X], ConnectedSpace X := by
  -- The lifted natural numbers are discrete and nontrivial, so they cannot be connected.
  intro h
  letI : ConnectedSpace (ULift.{u} ℕ) := h (ULift.{u} ℕ)
  have heq : (ULift.up 0 : ULift.{u} ℕ) = ULift.up 1 :=
    isPreconnected_univ.subsingleton (Set.mem_univ _) (Set.mem_univ _)
  exact Nat.zero_ne_one (ULift.up_injective heq)

/-- Helper for Exercise 4.99.2 (2): a metric space need not be path connected. -/
theorem not_every_metricSpace_pathConnected :
    ¬ ∀ (X : Type u) [MetricSpace X], PathConnectedSpace X := by
  -- Universal path connectedness would imply the already refuted universal connectedness.
  intro h
  apply not_every_metricSpace_connected
  intro X _
  letI : PathConnectedSpace X := h X
  infer_instance

/-- Helper for Exercise 4.99.2 (3): a metric space need not be locally connected. -/
theorem not_every_metricSpace_locallyConnected :
    ¬ ∀ (X : Type u) [MetricSpace X], LocallyConnectedSpace X := by
  -- Pull the assumed local connectedness of lifted rationals back to the rational line.
  intro h
  letI : LocallyConnectedSpace (ULift.{u} ℚ) := h (ULift.{u} ℚ)
  have hRat : LocallyConnectedSpace ℚ := Homeomorph.ulift.symm.locallyConnectedSpace
  exact not_locallyConnectedSpace_of_totallyDisconnected_of_nonisolated (0 : ℚ) hRat

/-- Helper for Exercise 4.99.2 (4): a metric space need not be locally path connected. -/
theorem not_every_metricSpace_locallyPathConnected :
    ¬ ∀ (X : Type u) [MetricSpace X], LocallyPathConnectedSpace X := by
  -- Universal local path connectedness would imply universal local connectedness.
  intro h
  apply not_every_metricSpace_locallyConnected
  intro X _
  letI : LocallyPathConnectedSpace X := h X
  infer_instance

/-- Helper for Exercise 4.99.2 (5): a metric space need not be compact. -/
theorem not_every_metricSpace_compact :
    ¬ ∀ (X : Type u) [MetricSpace X], CompactSpace X := by
  -- Lift the infinite discrete natural numbers into the quantified universe.
  intro h
  exact infiniteDiscrete_not_compact (ULift.{u} ℕ) (h (ULift.{u} ℕ))

/-- Helper for Exercise 4.99.2 (6): a metric space need not be limit point compact. -/
theorem not_every_metricSpace_limitPointCompact :
    ¬ ∀ (X : Type u) [MetricSpace X], LimitPointCompactSpace X := by
  -- The same lifted discrete space has no accumulation point of its infinite carrier.
  intro h
  exact infiniteDiscrete_not_limitPointCompact (ULift.{u} ℕ) (h (ULift.{u} ℕ))

/-- Helper for Exercise 4.99.2 (7): a metric space need not be locally compact Hausdorff. -/
theorem not_every_metricSpace_locallyCompactHausdorff :
    ¬ ∀ (X : Type u) [MetricSpace X], LocallyCompactSpace X ∧ T2Space X := by
  -- Pull the local-compactness component for lifted rationals back along the homeomorphism.
  intro h
  letI : LocallyCompactSpace (ULift.{u} ℚ) := (h (ULift.{u} ℚ)).1
  have hRat : LocallyCompactSpace ℚ :=
    Homeomorph.ulift.symm.isClosedEmbedding.locallyCompactSpace
  exact Rat.not_locallyCompactSpace hRat

/-- A metric space need not be locally compact. -/
theorem not_every_metricSpace_locallyCompact :
    ¬ ∀ (X : Type u) [MetricSpace X], LocallyCompactSpace X := by
  intro h
  exact not_every_metricSpace_locallyCompactHausdorff fun X ↦ ⟨h X, inferInstance⟩

/- Exercise 4.99.2 (8): Every metric space is Hausdorff. -/
#check fun (X : Type u) [MetricSpace X] ↦ (inferInstance : T2Space X)

/- Exercise 4.99.2 (9): Every metric space is regular. -/
#check fun (X : Type u) [MetricSpace X] ↦ (inferInstance : T3Space X)

/- Exercise 4.99.2 (10): Every metric space is completely regular. -/
#check fun (X : Type u) [MetricSpace X] ↦ (inferInstance : T35Space X)

/- Exercise 4.99.2 (11): Every metric space is normal. -/
#check fun (X : Type u) [MetricSpace X] ↦ (inferInstance : T4Space X)

/- Exercise 4.99.2 (12): Every metric space is first-countable. -/
#check fun (X : Type u) [MetricSpace X] ↦
  (inferInstance : FirstCountableTopology X)

/-- Helper for Exercise 4.99.2 (13): a metric space need not be second-countable. -/
theorem not_every_metricSpace_secondCountable :
    ¬ ∀ (X : Type u) [MetricSpace X], SecondCountableTopology X := by
  -- Give an uncountable discrete carrier a metric compatible with its discrete topology.
  intro h
  let X := WithDiscreteTopology (ULift.{u} ℝ)
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hX : ¬ Countable X := by
    -- Countability would transport first through `WithTopology` and then through `ULift` to `ℝ`.
    intro hcountable
    have hLift : Countable (ULift.{u} ℝ) :=
      (WithTopology.equiv (ULift.{u} ℝ) ⊥).countable_iff.mp hcountable
    have hReal : Countable ℝ := Equiv.ulift.countable_iff.mp hLift
    exact not_countable hReal
  exact not_secondCountableTopology_of_uncountable_discrete X hX (h X)

/-- Helper for Exercise 4.99.2 (14): a metric space need not be Lindelöf. -/
theorem not_every_metricSpace_lindelof :
    ¬ ∀ (X : Type u) [MetricSpace X], LindelofSpace X := by
  -- A Lindelöf metric space is second-countable, contradicting part (13).
  intro h
  apply not_every_metricSpace_secondCountable
  intro X _
  letI : LindelofSpace X := h X
  infer_instance

/-- Helper for Exercise 4.99.2 (15): a metric space need not have a countable dense subset. -/
theorem not_every_metricSpace_separable :
    ¬ ∀ (X : Type u) [MetricSpace X], TopologicalSpace.SeparableSpace X := by
  -- A separable metric space is second-countable, again contradicting part (13).
  intro h
  apply not_every_metricSpace_secondCountable
  intro X _
  letI : TopologicalSpace.SeparableSpace X := h X
  infer_instance

/- Exercise 4.99.2 (16): Every metric space is locally metrizable. -/
#check fun (X : Type u) [MetricSpace X] ↦
  (inferInstance : LocallyMetrizableSpace X)

/- Exercise 4.99.2 (17): Every metric space is metrizable. -/
#check fun (X : Type u) [MetricSpace X] ↦
  (inferInstance : TopologicalSpace.MetrizableSpace X)

/-- Exercise 4.99.2: the combined classification of the listed metric-space properties. -/
theorem metricSpace_propertyClassification :
    (¬ ∀ (X : Type u) [MetricSpace X], ConnectedSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], PathConnectedSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], LocallyConnectedSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], LocallyPathConnectedSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], CompactSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], LimitPointCompactSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], LocallyCompactSpace X ∧ T2Space X) ∧
      (∀ (X : Type u) [MetricSpace X], T2Space X) ∧
      (∀ (X : Type u) [MetricSpace X], T3Space X) ∧
      (∀ (X : Type u) [MetricSpace X], T35Space X) ∧
      (∀ (X : Type u) [MetricSpace X], T4Space X) ∧
      (∀ (X : Type u) [MetricSpace X], FirstCountableTopology X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], SecondCountableTopology X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], LindelofSpace X) ∧
      (¬ ∀ (X : Type u) [MetricSpace X], TopologicalSpace.SeparableSpace X) ∧
      (∀ (X : Type u) [MetricSpace X], LocallyMetrizableSpace X) ∧
      ∀ (X : Type u) [MetricSpace X], TopologicalSpace.MetrizableSpace X := by
  -- Assemble the counterexamples and canonical metric-space instances in source order.
  exact ⟨not_every_metricSpace_connected, not_every_metricSpace_pathConnected,
    not_every_metricSpace_locallyConnected, not_every_metricSpace_locallyPathConnected,
    not_every_metricSpace_compact, not_every_metricSpace_limitPointCompact,
    not_every_metricSpace_locallyCompactHausdorff, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, not_every_metricSpace_secondCountable,
    not_every_metricSpace_lindelof, not_every_metricSpace_separable,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
