module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Example_23_4
public import Topology_Munkres_2000.Book.Exercise_28_3
public import Topology_Munkres_2000.Book.Exercise_30_17
public import Topology_Munkres_2000.Book.Exercise_31_4
public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Separation.CompletelyRegular

public section

universe u v

/-- Helper for Exercise 4.99.6: the discrete copy of a small topological space maps
surjectively onto the space itself, with independently chosen source and target universes. -/
private def discreteCover (Z : Type) [TopologicalSpace Z] :
    ULift.{u} (WithDiscreteTopology Z) → ULift.{v} Z :=
  ULift.map WithTopology.ofTopology

/-- Helper for Exercise 4.99.6: the discrete cover is continuous. -/
private lemma discreteCover_continuous (Z : Type) [TopologicalSpace Z] :
    Continuous (discreteCover Z : ULift.{u} (WithDiscreteTopology Z) → ULift.{v} Z) := by
  -- Every map from the discrete source is continuous.
  exact continuous_of_discreteTopology

/-- Helper for Exercise 4.99.6: the discrete cover is surjective. -/
private lemma discreteCover_surjective (Z : Type) [TopologicalSpace Z] :
    Function.Surjective (discreteCover Z :
      ULift.{u} (WithDiscreteTopology Z) → ULift.{v} Z) := by
  -- Lift a target point after viewing it in the discrete copy.
  intro z
  refine ⟨ULift.up (WithTopology.toTopology ⊥ z.down), ?_⟩
  cases z
  rfl

/-- Helper for Exercise 4.99.6: every locally metrizable space is first-countable. -/
private lemma locallyMetrizableSpace_to_firstCountableTopology
    (X : Type u) [TopologicalSpace X] [LocallyMetrizableSpace X] :
    FirstCountableTopology X := by
  -- A metrizable neighborhood supplies a countably generated neighborhood filter.
  constructor
  intro x
  obtain ⟨s, hs, hmetric⟩ := LocallyMetrizableSpace.exists_metrizable_nhds x
  letI : TopologicalSpace.MetrizableSpace s := hmetric
  have hx : x ∈ s := mem_of_mem_nhds hs
  rw [← map_nhds_subtype_coe_eq_nhds hx hs]
  infer_instance

/-- Helper for Exercise 4.99.6: the rational numbers are not locally connected. -/
private lemma rational_not_locallyConnected : ¬ LocallyConnectedSpace ℚ := by
  -- Local connectedness would make the singleton connected component of zero open.
  intro hlocal
  letI : LocallyConnectedSpace ℚ := hlocal
  apply not_isOpen_singleton (0 : ℚ)
  rw [← connectedComponent_eq_singleton (0 : ℚ)]
  exact isOpen_connectedComponent

/- Exercise 4.99.6 refers, in order, to the following list printed at the start of the
supplementary exercises: connected, path connected, locally connected, locally path
connected, compact, limit point compact, locally compact Hausdorff, Hausdorff,
regular, completely regular, normal, first-countable, second-countable, Lindelöf,
having a countable dense subset, locally metrizable, and metrizable. -/

/- Exercise 4.99.6 (1): Connectedness is preserved by continuous images. -/
#check Function.Surjective.connectedSpace

/- Exercise 4.99.6 (2): Path connectedness is preserved by continuous images. -/
#check Function.Surjective.pathConnectedSpace

/-- Exercise 4.99.6 (3): Local connectedness is not always preserved by continuous images. -/
theorem continuousImage_not_always_locallyConnected :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyConnectedSpace X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), LocallyConnectedSpace Y := by
  -- A discrete copy of `ℚ` is locally connected and maps onto the usual rationals.
  intro hpreserved
  letI : LocallyConnectedSpace (ULift.{u} (WithDiscreteTopology ℚ)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover ℚ) (discreteCover_continuous ℚ)
    (discreteCover_surjective ℚ)
  letI : LocallyConnectedSpace (ULift.{v} ℚ) := htarget
  exact rational_not_locallyConnected Homeomorph.ulift.symm.locallyConnectedSpace

/-- Exercise 4.99.6 (4): Local path connectedness is not always preserved by continuous images. -/
theorem continuousImage_not_always_locallyPathConnected :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyPathConnectedSpace X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), LocallyPathConnectedSpace Y := by
  -- The same discrete cover would make the usual rationals locally path connected.
  intro hpreserved
  letI : LocallyPathConnectedSpace (ULift.{u} (WithDiscreteTopology ℚ)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover ℚ) (discreteCover_continuous ℚ)
    (discreteCover_surjective ℚ)
  letI : LocallyPathConnectedSpace (ULift.{v} ℚ) := htarget
  letI : LocallyPathConnectedSpace ℚ :=
    Homeomorph.ulift.symm.isOpenEmbedding.locallyPathConnectedSpace
  exact rational_not_locallyConnected inferInstance

/- Exercise 4.99.6 (5): Compactness is preserved by continuous images. -/
#check Function.Surjective.compactSpace

/-- Exercise 4.99.6 (6): Limit point compactness is not always preserved by continuous images. -/
theorem continuousImage_not_always_limitPointCompact :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LimitPointCompactSpace X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), LimitPointCompactSpace Y := by
  -- Surjective preservation would imply preservation for every range subtype.
  intro hpreserved
  apply limitPointCompactSpace_range_not_preserved
  intro X Y _ _ _ f hf
  exact hpreserved X (Set.range f) (Set.rangeFactorization f) hf.rangeFactorization
    Set.rangeFactorization_surjective

/-- Exercise 4.99.6 (7): Being locally compact Hausdorff is not always preserved by
continuous images. -/
theorem continuousImage_not_always_locallyCompactT2 :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyCompactSpace X] [T2Space X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), LocallyCompactSpace Y ∧ T2Space Y := by
  -- A discrete cover of the indiscrete two-point space contradicts Hausdorffness.
  intro hpreserved
  let Z := WithTopology Bool (⊤ : TopologicalSpace Bool)
  letI : LocallyCompactSpace (ULift.{u} (WithDiscreteTopology Z)) := inferInstance
  letI : T2Space (ULift.{u} (WithDiscreteTopology Z)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover Z) (discreteCover_continuous Z)
    (discreteCover_surjective Z)
  letI : T2Space (ULift.{v} Z) := htarget.2
  exact notT2Space_indiscrete_bool Homeomorph.ulift.t2Space

/-- Exercise 4.99.6 (8): The Hausdorff property is not always preserved by continuous images. -/
theorem continuousImage_not_always_t2 :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] (f : X → Y) (_ : Continuous f) (_ : Function.Surjective f),
      T2Space Y := by
  -- The indiscrete two-point target is a continuous quotient of its discrete copy.
  intro hpreserved
  let Z := WithTopology Bool (⊤ : TopologicalSpace Bool)
  letI : T2Space (ULift.{u} (WithDiscreteTopology Z)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover Z) (discreteCover_continuous Z)
    (discreteCover_surjective Z)
  letI : T2Space (ULift.{v} Z) := htarget
  exact notT2Space_indiscrete_bool Homeomorph.ulift.t2Space

/-- Exercise 4.99.6 (9): Regularity is not always preserved by continuous images. -/
theorem continuousImage_not_always_t3 :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [T3Space X] (f : X → Y) (_ : Continuous f) (_ : Function.Surjective f),
      T3Space Y := by
  -- Regular Hausdorffness would in particular make the indiscrete target Hausdorff.
  intro hpreserved
  let Z := WithTopology Bool (⊤ : TopologicalSpace Bool)
  letI : T3Space (ULift.{u} (WithDiscreteTopology Z)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover Z) (discreteCover_continuous Z)
    (discreteCover_surjective Z)
  letI : T3Space (ULift.{v} Z) := htarget
  letI : T2Space (ULift.{v} Z) := inferInstance
  exact notT2Space_indiscrete_bool Homeomorph.ulift.t2Space

/-- Exercise 4.99.6 (10): Complete regularity is not always preserved by continuous images. -/
theorem continuousImage_not_always_t35 :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [T35Space X] (f : X → Y) (_ : Continuous f) (_ : Function.Surjective f),
      T35Space Y := by
  -- Complete regularity also includes Hausdorffness, which fails on this target.
  intro hpreserved
  let Z := WithTopology Bool (⊤ : TopologicalSpace Bool)
  letI : T35Space (ULift.{u} (WithDiscreteTopology Z)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover Z) (discreteCover_continuous Z)
    (discreteCover_surjective Z)
  letI : T35Space (ULift.{v} Z) := htarget
  letI : T2Space (ULift.{v} Z) := inferInstance
  exact notT2Space_indiscrete_bool Homeomorph.ulift.t2Space

/-- Exercise 4.99.6 (11): Normality is not always preserved by continuous images. -/
theorem continuousImage_not_always_t4 :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [T4Space X] (f : X → Y) (_ : Continuous f) (_ : Function.Surjective f),
      T4Space Y := by
  -- Normal Hausdorffness likewise forces the false Hausdorff conclusion.
  intro hpreserved
  let Z := WithTopology Bool (⊤ : TopologicalSpace Bool)
  letI : T4Space (ULift.{u} (WithDiscreteTopology Z)) := inferInstance
  have htarget := hpreserved _ _ (discreteCover Z) (discreteCover_continuous Z)
    (discreteCover_surjective Z)
  letI : T4Space (ULift.{v} Z) := htarget
  letI : T2Space (ULift.{v} Z) := inferInstance
  exact notT2Space_indiscrete_bool Homeomorph.ulift.t2Space

/-- Exercise 4.99.6 (12): First countability is not always preserved by continuous images. -/
theorem continuousImage_not_always_firstCountable :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [FirstCountableTopology X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), FirstCountableTopology Y := by
  -- The countable eventually-zero box is covered by a first-countable discrete space.
  intro hpreserved
  have htarget := hpreserved _ _ (discreteCover RationalEventuallyZeroBox)
    (discreteCover_continuous RationalEventuallyZeroBox)
    (discreteCover_surjective RationalEventuallyZeroBox)
  letI : FirstCountableTopology (ULift.{v} RationalEventuallyZeroBox) := htarget
  exact rationalEventuallyZeroBox_not_firstCountable
    Homeomorph.ulift.symm.isEmbedding.firstCountableTopology

/-- Exercise 4.99.6 (13): Second countability is not always preserved by continuous images. -/
theorem continuousImage_not_always_secondCountable :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [SecondCountableTopology X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), SecondCountableTopology Y := by
  -- Countability makes the discrete cover second-countable, but its target is not.
  intro hpreserved
  letI : Countable (WithDiscreteTopology RationalEventuallyZeroBox) :=
    (WithTopology.equiv RationalEventuallyZeroBox ⊥).countable_iff.mpr inferInstance
  have htarget := hpreserved _ _ (discreteCover RationalEventuallyZeroBox)
    (discreteCover_continuous RationalEventuallyZeroBox)
    (discreteCover_surjective RationalEventuallyZeroBox)
  letI : SecondCountableTopology (ULift.{v} RationalEventuallyZeroBox) := htarget
  exact rationalEventuallyZeroBox_not_secondCountable Homeomorph.ulift.symm.secondCountableTopology

/- Exercise 4.99.6 (14): The Lindelöf property is preserved by continuous images. -/
#check LindelofSpace.of_continuous_surjective

/- Exercise 4.99.6 (15): Having a countable dense subset is preserved by continuous images. -/
#check fun (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace.SeparableSpace X] (f : X → Y) (hf : Continuous f)
    (hsurj : Function.Surjective f) ↦ hsurj.denseRange.separableSpace hf

/-- Exercise 4.99.6 (16): Local metrizability is not always preserved by continuous images. -/
theorem continuousImage_not_always_locallyMetrizable :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LocallyMetrizableSpace X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), LocallyMetrizableSpace Y := by
  -- Local metrizability of the target would force its known-false first countability.
  intro hpreserved
  have htarget := hpreserved _ _ (discreteCover RationalEventuallyZeroBox)
    (discreteCover_continuous RationalEventuallyZeroBox)
    (discreteCover_surjective RationalEventuallyZeroBox)
  letI : LocallyMetrizableSpace (ULift.{v} RationalEventuallyZeroBox) := htarget
  have hfirst := locallyMetrizableSpace_to_firstCountableTopology
    (ULift.{v} RationalEventuallyZeroBox)
  letI : FirstCountableTopology (ULift.{v} RationalEventuallyZeroBox) := hfirst
  exact rationalEventuallyZeroBox_not_firstCountable
    Homeomorph.ulift.symm.isEmbedding.firstCountableTopology

/-- Exercise 4.99.6 (17): Metrizability is not always preserved by continuous images. -/
theorem continuousImage_not_always_metrizable :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [TopologicalSpace.MetrizableSpace X] (f : X → Y) (_ : Continuous f)
      (_ : Function.Surjective f), TopologicalSpace.MetrizableSpace Y := by
  -- Metrizability of the target would contradict its failure of first countability.
  intro hpreserved
  have htarget := hpreserved _ _ (discreteCover RationalEventuallyZeroBox)
    (discreteCover_continuous RationalEventuallyZeroBox)
    (discreteCover_surjective RationalEventuallyZeroBox)
  letI : TopologicalSpace.MetrizableSpace (ULift.{v} RationalEventuallyZeroBox) := htarget
  letI : TopologicalSpace.MetrizableSpace RationalEventuallyZeroBox :=
    Homeomorph.ulift.symm.isEmbedding.metrizableSpace
  exact rationalEventuallyZeroBox_not_firstCountable inferInstance

end
