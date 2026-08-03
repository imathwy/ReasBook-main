module

public import Topology_Munkres_2000.Book.Exercise_4_99_4.Subspace
public import Topology_Munkres_2000.Book.Example_29_1
public import Topology_Munkres_2000.Book.Exercise_8_99_6
public import Topology_Munkres_2000.Book.Exercise_28_3
public import Topology_Munkres_2000.Book.Exercise_30_9
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.Instances.RatLemmas
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Separation.Regular

public section

universe u

open Set Topology

/-- Helper for Exercise 4.99.4: a subtype pulled back along `ULift.down` is homeomorphic
to the original subtype. -/
noncomputable def liftedSubtypeHomeomorph {X : Type*} [TopologicalSpace X] (s : Set X) :
    {x : ULift.{u} X // x.down ∈ s} ≃ₜ s :=
  Homeomorph.ulift.subtype fun _ ↦ Iff.rfl

/-- Helper for Exercise 4.99.4: an infinite discrete space is not compact. -/
lemma infiniteDiscrete_not_compact (X : Type*) [TopologicalSpace X] [DiscreteTopology X]
    [Infinite X] : ¬ CompactSpace X := by
  -- Compactness would make the discrete carrier finite.
  intro h
  letI : CompactSpace X := h
  letI : Finite X := finite_of_compact_of_discrete
  exact Infinite.false (α := X) inferInstance

/-- Helper for Exercise 4.99.4: an infinite discrete space is not limit point compact. -/
lemma infiniteDiscrete_not_limitPointCompact (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [Infinite X] : ¬ LimitPointCompactSpace X := by
  -- The whole carrier is infinite, but no point is an accumulation point in a discrete space.
  intro h
  obtain ⟨x, hx⟩ := h.exists_accPt (Set.univ : Set X) Set.infinite_univ
  rw [accPt_iff_nhds] at hx
  obtain ⟨y, hy, hne⟩ := hx {x} (discreteTopology_iff_singleton_mem_nhds.mp inferInstance x)
  exact hne (by simpa using hy.1)

/-- Helper for Exercise 4.99.4: an uncountable discrete space is not Lindelöf. -/
lemma uncountableDiscrete_not_lindelof (X : Type*) [TopologicalSpace X] [DiscreteTopology X]
    (hX : ¬ Countable X) : ¬ LindelofSpace X := by
  -- A discrete Lindelöf space has countable carrier.
  intro h
  letI : LindelofSpace X := h
  exact hX countable_of_Lindelof_of_discrete

/-- Helper for Exercise 4.99.4: the standard two-point subspace of `ℝ` is disconnected. -/
lemma realPair_not_connected : ¬ ConnectedSpace ({0, 1} : Set ℝ) := by
  -- The finite Hausdorff subtype is discrete, so connectedness would identify its two points.
  intro h
  letI : ConnectedSpace ({0, 1} : Set ℝ) := h
  letI : DiscreteTopology ({0, 1} : Set ℝ) := inferInstance
  have hEq : (⟨0, by simp⟩ : ({0, 1} : Set ℝ)) = ⟨1, by simp⟩ :=
    isPreconnected_univ.subsingleton (Set.mem_univ _) (Set.mem_univ _)
  have hVal := congrArg Subtype.val hEq
  norm_num at hVal

/-- Helper for Exercise 4.99.4: the punctured real line is disconnected. -/
lemma puncturedReal_not_connected : ¬ ConnectedSpace ({0}ᶜ : Set ℝ) := by
  -- Order connectedness would force the omitted midpoint `0` between `-1` and `1` to belong.
  intro h
  letI : ConnectedSpace ({0}ᶜ : Set ℝ) := h
  have hpre : IsPreconnected (({0}ᶜ : Set ℝ)) := by
    have hrange : IsPreconnected (Set.range (Subtype.val : ({0}ᶜ : Set ℝ) → ℝ)) :=
      isPreconnected_range continuous_subtype_val
    rw [@Subtype.range_val ℝ ({0}ᶜ)] at hrange
    exact hrange
  rw [isPreconnected_iff_ordConnected, Set.ordConnected_iff] at hpre
  have hinterval : (0 : ℝ) ∈ Set.Icc (-1) 1 := by
    constructor
    · norm_num
    · norm_num
  have hzero := hpre (-1) (by norm_num) 1 (by norm_num) (by norm_num) hinterval
  exact hzero (by simp)

/-- Helper for Exercise 4.99.4: Cantor space is not locally connected. -/
lemma cantorSet_not_locallyConnected : ¬ LocallyConnectedSpace cantorSet := by
  -- Transport to Boolean sequences, where total disconnectedness makes components singletons.
  intro h
  letI : LocallyConnectedSpace cantorSet := h
  letI : LocallyConnectedSpace (ℕ → Bool) :=
    cantorSetHomeomorphNatToBool.symm.locallyConnectedSpace
  have hOpen : ∀ x : ℕ → Bool, IsOpen ({x} : Set (ℕ → Bool)) := by
    intro x
    rw [← connectedComponent_eq_singleton x]
    exact isOpen_connectedComponent
  letI : DiscreteTopology (ℕ → Bool) := discreteTopology_iff_isOpen_singleton.mpr hOpen
  letI : Finite (ℕ → Bool) := finite_of_compact_of_discrete
  exact Infinite.false (α := ℕ → Bool) inferInstance

/-- Helper for Exercise 4.99.4: separability is preserved in both directions by a homeomorphism. -/
lemma Homeomorph.separableSpace_iff {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TopologicalSpace.SeparableSpace X ↔ TopologicalSpace.SeparableSpace Y := by
  -- Each direction is a continuous surjective image.
  constructor
  · intro h
    letI : TopologicalSpace.SeparableSpace X := h
    exact e.isQuotientMap.separableSpace
  · intro h
    letI : TopologicalSpace.SeparableSpace Y := h
    exact e.symm.isQuotientMap.separableSpace

/- Exercise 4.99.4 refers, in order, to the following list printed at the start of the
supplementary exercises: connected, path connected, locally connected, locally path
connected, compact, limit point compact, locally compact Hausdorff, Hausdorff,
regular, completely regular, normal, first-countable, second-countable, Lindelöf,
having a countable dense subset, locally metrizable, and metrizable. -/

/-- Exercise 4.99.4: connectedness is not preserved by closed subspaces. -/
theorem exists_closed_subspace_not_connected :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (s : Set X),
      IsClosed s ∧ ¬ ConnectedSpace s := by
  -- Lift the real line and use its closed two-point subspace.
  let s : Set (ULift.{u} ℝ) := {x | x.down ∈ ({0, 1} : Set ℝ)}
  refine ⟨ULift.{u} ℝ, inferInstance,
    Homeomorph.ulift.connectedSpace_iff.mpr inferInstance, s, ?_, ?_⟩
  · rw [ULift.isClosed_iff]
    have hset : ULift.up ⁻¹' s = ({0} ∪ {1} : Set ℝ) := by
      ext x
      simp only [s, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hset]
    exact isClosed_singleton.union isClosed_singleton
  · intro h
    exact realPair_not_connected <|
      (liftedSubtypeHomeomorph ({0, 1} : Set ℝ)).connectedSpace_iff.mp h

/-- Helper for Exercise 4.99.4: connectedness is not preserved by open subspaces. -/
theorem exists_open_subspace_not_connected :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (s : Set X),
      IsOpen s ∧ ¬ ConnectedSpace s := by
  -- Lift the real line and remove one point.
  let s : Set (ULift.{u} ℝ) := {x | x.down ∈ ({0}ᶜ : Set ℝ)}
  refine ⟨ULift.{u} ℝ, inferInstance,
    Homeomorph.ulift.connectedSpace_iff.mpr inferInstance, s, ?_, ?_⟩
  · rw [ULift.isOpen_iff]
    have hset : ULift.up ⁻¹' s = ({0}ᶜ : Set ℝ) := by
      ext x
      simp only [s, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_singleton.isOpen_compl
  · intro h
    exact puncturedReal_not_connected
      ((liftedSubtypeHomeomorph ({0}ᶜ : Set ℝ)).connectedSpace_iff.mp h)

/-- Helper for Exercise 4.99.4: path connectedness is not preserved by closed subspaces. -/
theorem exists_closed_subspace_not_pathConnected :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : PathConnectedSpace X) (s : Set X),
      IsClosed s ∧ ¬ PathConnectedSpace s := by
  -- The same closed two-point subspace cannot be path connected because path connected
  -- spaces are connected.
  let s : Set (ULift.{u} ℝ) := {x | x.down ∈ ({0, 1} : Set ℝ)}
  refine ⟨ULift.{u} ℝ, inferInstance,
    Homeomorph.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous,
    s, ?_, ?_⟩
  · rw [ULift.isClosed_iff]
    have hset : ULift.up ⁻¹' s = ({0} ∪ {1} : Set ℝ) := by
      ext x
      simp only [s, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hset]
    exact isClosed_singleton.union isClosed_singleton
  · intro h
    letI : PathConnectedSpace s := h
    have hsConnected : ConnectedSpace s := PathConnectedSpace.connectedSpace
    letI : ConnectedSpace {x : ULift.{u} ℝ // x.down ∈ ({0, 1} : Set ℝ)} := hsConnected
    exact realPair_not_connected
      ((liftedSubtypeHomeomorph ({0, 1} : Set ℝ)).connectedSpace_iff.mp inferInstance)

/-- Helper for Exercise 4.99.4: path connectedness is not preserved by open subspaces. -/
theorem exists_open_subspace_not_pathConnected :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : PathConnectedSpace X) (s : Set X),
      IsOpen s ∧ ¬ PathConnectedSpace s := by
  -- The punctured real line is disconnected and therefore cannot be path connected.
  let s : Set (ULift.{u} ℝ) := {x | x.down ∈ ({0}ᶜ : Set ℝ)}
  refine ⟨ULift.{u} ℝ, inferInstance,
    Homeomorph.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous,
    s, ?_, ?_⟩
  · rw [ULift.isOpen_iff]
    have hset : ULift.up ⁻¹' s = ({0}ᶜ : Set ℝ) := by
      ext x
      simp only [s, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_singleton.isOpen_compl
  · intro h
    letI : PathConnectedSpace s := h
    have hsConnected : ConnectedSpace s := PathConnectedSpace.connectedSpace
    letI : ConnectedSpace {x : ULift.{u} ℝ // x.down ∈ ({0}ᶜ : Set ℝ)} := hsConnected
    exact puncturedReal_not_connected
      ((liftedSubtypeHomeomorph ({0}ᶜ : Set ℝ)).connectedSpace_iff.mp inferInstance)

/- Exercise 4.99.4 (5): Local connectedness is preserved by open subspaces. -/
#check IsOpen.locallyConnectedSpace

/-- Helper for Exercise 4.99.4: local connectedness is not preserved by closed subspaces. -/
theorem exists_closed_subspace_not_locallyConnected :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : LocallyConnectedSpace X) (s : Set X),
      IsClosed s ∧ ¬ LocallyConnectedSpace s := by
  -- Lift the closed Cantor set into the locally connected real line.
  let s : Set (ULift.{u} ℝ) := {x | x.down ∈ cantorSet}
  refine ⟨ULift.{u} ℝ, inferInstance, Homeomorph.ulift.locallyConnectedSpace, s, ?_, ?_⟩
  · exact ULift.isClosed_iff.mpr (by simpa [s] using isClosed_cantorSet)
  · intro h
    letI : LocallyConnectedSpace {x : ULift.{u} ℝ // x.down ∈ cantorSet} := h
    exact cantorSet_not_locallyConnected
      (liftedSubtypeHomeomorph cantorSet).symm.locallyConnectedSpace

/- Exercise 4.99.4 (7): Local path connectedness is preserved by open subspaces. -/
#check IsOpen.locallyPathConnectedSpace

/-- Helper for Exercise 4.99.4: local path connectedness is not preserved by closed subspaces. -/
theorem exists_closed_subspace_not_locallyPathConnected :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : LocallyPathConnectedSpace X) (s : Set X),
      IsClosed s ∧ ¬ LocallyPathConnectedSpace s := by
  -- Local path connectedness of the lifted Cantor set would imply local connectedness.
  let s : Set (ULift.{u} ℝ) := {x | x.down ∈ cantorSet}
  refine ⟨ULift.{u} ℝ, inferInstance,
    Homeomorph.ulift.symm.isQuotientMap.locallyPathConnectedSpace, s, ?_, ?_⟩
  · exact ULift.isClosed_iff.mpr (by simpa [s] using isClosed_cantorSet)
  · intro h
    letI : LocallyPathConnectedSpace {x : ULift.{u} ℝ // x.down ∈ cantorSet} := h
    have hsConnected : LocallyConnectedSpace
        {x : ULift.{u} ℝ // x.down ∈ cantorSet} := inferInstance
    letI : LocallyConnectedSpace {x : ULift.{u} ℝ // x.down ∈ cantorSet} := hsConnected
    exact cantorSet_not_locallyConnected
      (liftedSubtypeHomeomorph cantorSet).symm.locallyConnectedSpace

/- Exercise 4.99.4 (9): Compactness is preserved by closed subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] (s : Set X)
    (hs : IsClosed s) ↦ isCompact_iff_compactSpace.mp hs.isCompact

/-- Helper for Exercise 4.99.4: compactness is not preserved by open subspaces. -/
theorem exists_open_subspace_not_compact :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (s : Set X),
      IsOpen s ∧ ¬ CompactSpace s := by
  -- The canonical open copy of an infinite discrete space in its one-point
  -- compactification is noncompact.
  let s : Set (OnePoint (WithDiscreteTopology (ULift.{u} ℝ))) :=
    Set.range ((↑) : WithDiscreteTopology (ULift.{u} ℝ) →
      OnePoint (WithDiscreteTopology (ULift.{u} ℝ)))
  refine ⟨OnePoint (WithDiscreteTopology (ULift.{u} ℝ)), inferInstance, inferInstance,
    s, OnePoint.isOpen_range_coe, ?_⟩
  intro h
  letI : CompactSpace s := h
  letI : Infinite (WithDiscreteTopology (ULift.{u} ℝ)) :=
    Infinite.of_injective (fun x : ℝ ↦
      (WithTopology.toTopology ⊥ (ULift.up x) : WithDiscreteTopology (ULift.{u} ℝ))) <| by
        intro x y hxy
        exact ULift.up_injective (congrArg WithTopology.ofTopology hxy)
  letI : CompactSpace (WithDiscreteTopology (ULift.{u} ℝ)) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.symm.compactSpace
  exact infiniteDiscrete_not_compact (WithDiscreteTopology (ULift.{u} ℝ)) inferInstance

/- Exercise 4.99.4 (11): Limit point compactness is preserved by closed subspaces. -/
#check IsClosed.limitPointCompactSpace

/-- Helper for Exercise 4.99.4: limit point compactness is not preserved by open subspaces. -/
theorem exists_open_subspace_not_limitPointCompact :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : LimitPointCompactSpace X) (s : Set X),
      IsOpen s ∧ ¬ LimitPointCompactSpace s := by
  -- The same open discrete range has no accumulation point, while the ambient compact space does.
  let s : Set (OnePoint (WithDiscreteTopology (ULift.{u} ℝ))) :=
    Set.range ((↑) : WithDiscreteTopology (ULift.{u} ℝ) →
      OnePoint (WithDiscreteTopology (ULift.{u} ℝ)))
  refine ⟨OnePoint (WithDiscreteTopology (ULift.{u} ℝ)), inferInstance, inferInstance,
    s, OnePoint.isOpen_range_coe, ?_⟩
  intro h
  letI : LimitPointCompactSpace s := h
  letI : Infinite (WithDiscreteTopology (ULift.{u} ℝ)) :=
    Infinite.of_injective (fun x : ℝ ↦
      (WithTopology.toTopology ⊥ (ULift.up x) : WithDiscreteTopology (ULift.{u} ℝ))) <| by
        intro x y hxy
        exact ULift.up_injective (congrArg WithTopology.ofTopology hxy)
  letI : LimitPointCompactSpace (WithDiscreteTopology (ULift.{u} ℝ)) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.symm.limitPointCompactSpace
  exact infiniteDiscrete_not_limitPointCompact
    (WithDiscreteTopology (ULift.{u} ℝ)) inferInstance

/- Exercise 4.99.4 (13): Local compactness is preserved by closed subspaces. -/
#check IsClosed.locallyCompactSpace

/- Exercise 4.99.4 (14): Local compactness is preserved by open subspaces. -/
#check IsOpen.locallyCompactSpace

/- Exercise 4.99.4 (15): Hausdorffness is preserved by arbitrary subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [T2Space X] (s : Set X) ↦
  (inferInstance : T2Space s)

/-- Helper for Exercise 4.99.4: local compactness is not preserved by arbitrary subspaces,
even when both the ambient space and subspace are Hausdorff. -/
theorem exists_t2_subspace_not_locallyCompact :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : LocallyCompactSpace X) (_ : T2Space X)
      (s : Set X), T2Space s ∧ ¬ LocallyCompactSpace s := by
  -- Embed the rationals into the lifted real line and transport their failure of local compactness.
  let f : ℚ → ULift.{u} ℝ := fun q ↦ ULift.up (q : ℝ)
  have hf : IsEmbedding f := Homeomorph.ulift.symm.isEmbedding.comp Rat.isEmbedding_coe_real
  let s : Set (ULift.{u} ℝ) := Set.range f
  refine ⟨ULift.{u} ℝ, inferInstance,
    Homeomorph.ulift.locallyCompactSpace_iff.mpr inferInstance, inferInstance,
    s, inferInstance, ?_⟩
  intro h
  letI : LocallyCompactSpace s := h
  have hq : LocallyCompactSpace ℚ := hf.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance
  letI : LocallyCompactSpace ℚ := hq
  exact Rat.notWeaklyLocallyCompact inferInstance

/- Exercise 4.99.4 (17): Regularity is preserved by arbitrary subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [T3Space X] (s : Set X) ↦
  (inferInstance : T3Space s)

/- Exercise 4.99.4 (18): Complete regularity is preserved by arbitrary subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [T35Space X] (s : Set X) ↦
  (inferInstance : T35Space s)

/- Exercise 4.99.4 (19): Normality is preserved by closed subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [T4Space X] (s : Set X)
    (hs : IsClosed s) ↦ hs.isClosedEmbedding_subtypeVal.t4Space

/-- Helper for Exercise 4.99.4: normality is not preserved by open subspaces. -/
theorem exists_open_subspace_not_t4 :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T4Space X) (s : Set X),
      IsOpen s ∧ ¬ T4Space s := by
  -- Use the open copy of the locally compact nonnormal Prüfer manifold in its
  -- compact Hausdorff one-point compactification, lifted to the quantified universe.
  let P := ULift.{u} PruferManifold
  let s : Set (OnePoint P) := Set.range ((↑) : P → OnePoint P)
  letI : LocallyCompactSpace PruferManifold :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) PruferManifold
  letI : LocallyCompactSpace P := Homeomorph.ulift.locallyCompactSpace_iff.mpr inferInstance
  letI : T2Space P := Homeomorph.ulift.symm.t2Space
  refine ⟨OnePoint P, inferInstance, inferInstance, s, OnePoint.isOpen_range_coe, ?_⟩
  intro h
  letI : T4Space s := h
  have hLifted : T4Space P :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.symm.t4Space
  letI : T4Space P := hLifted
  have hPrufer : T4Space PruferManifold :=
    Homeomorph.ulift.t4Space
  exact PruferManifold.not_normal hPrufer.toNormalSpace

/- Exercise 4.99.4 (21): First-countability is preserved by arbitrary subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [FirstCountableTopology X] (s : Set X) ↦
  (inferInstance : FirstCountableTopology s)

/- Exercise 4.99.4 (22): Second-countability is preserved by arbitrary subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] (s : Set X) ↦
  (inferInstance : SecondCountableTopology s)

/- Exercise 4.99.4 (23): Lindelöfness is preserved by closed subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [LindelofSpace X] (s : Set X)
    (hs : IsClosed s) ↦ isLindelof_iff_lindelofSpace.mp hs.isLindelof

/-- Helper for Exercise 4.99.4: Lindelöfness is not preserved by open subspaces. -/
theorem exists_open_subspace_not_lindelof :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : LindelofSpace X) (s : Set X),
      IsOpen s ∧ ¬ LindelofSpace s := by
  -- Use the open copy of an uncountable discrete lifted real line.
  let s : Set (OnePoint (WithDiscreteTopology (ULift.{u} ℝ))) :=
    Set.range ((↑) : WithDiscreteTopology (ULift.{u} ℝ) →
      OnePoint (WithDiscreteTopology (ULift.{u} ℝ)))
  refine ⟨OnePoint (WithDiscreteTopology (ULift.{u} ℝ)), inferInstance, inferInstance,
    s, OnePoint.isOpen_range_coe, ?_⟩
  intro h
  letI : LindelofSpace s := h
  have hsource : IsLindelof (Set.univ : Set (WithDiscreteTopology (ULift.{u} ℝ))) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isLindelof_iff]
    simpa only [Set.image_univ, Set.range_comp, Function.comp_def] using
      (isLindelof_iff_lindelofSpace.mpr inferInstance : IsLindelof s)
  have hD : LindelofSpace (WithDiscreteTopology (ULift.{u} ℝ)) :=
    letI : LindelofSpace (Set.univ : Set (WithDiscreteTopology (ULift.{u} ℝ))) :=
      isLindelof_iff_lindelofSpace.mp hsource
    LindelofSpace.of_continuous_surjective continuous_subtype_val fun x ↦
      ⟨⟨x, Set.mem_univ x⟩, rfl⟩
  have huncountable : ¬ Countable (WithDiscreteTopology (ULift.{u} ℝ)) := by
    intro hcountable
    letI : Countable (WithDiscreteTopology (ULift.{u} ℝ)) := hcountable
    have hinjective : Function.Injective (fun x : ℝ ↦
        (WithTopology.toTopology ⊥ (ULift.up x) : WithDiscreteTopology (ULift.{u} ℝ))) := by
      intro x y hxy
      exact ULift.up_injective (congrArg WithTopology.ofTopology hxy)
    have hreal : Countable ℝ := hinjective.countable
    exact Cardinal.not_countable_real Set.countable_univ
  exact uncountableDiscrete_not_lindelof
    (WithDiscreteTopology (ULift.{u} ℝ)) huncountable hD

/- Exercise 4.99.4 (25): Having a countable dense subset is preserved by open subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    (s : Set X) (hs : IsOpen s) ↦ hs.isOpenEmbedding_subtypeVal.separableSpace

/-- Helper for Exercise 4.99.4: having a countable dense subset is not preserved by closed
subspaces. -/
theorem exists_closed_subspace_not_separable :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : TopologicalSpace.SeparableSpace X)
      (s : Set X), IsClosed s ∧ ¬ TopologicalSpace.SeparableSpace s := by
  -- Lift the Sorgenfrey plane and its closed nonseparable antidiagonal.
  let s : Set (ULift.{u} (SorgenfreyLine × SorgenfreyLine)) :=
    {x | x.down ∈ SorgenfreyPlane.antiDiagonal}
  refine ⟨ULift.{u} (SorgenfreyLine × SorgenfreyLine), inferInstance,
    Homeomorph.ulift.symm.isQuotientMap.separableSpace, s, ?_, ?_⟩
  · rw [ULift.isClosed_iff]
    have hset : ULift.up ⁻¹' s = SorgenfreyPlane.antiDiagonal := by
      ext x
      simp only [s, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hset]
    exact SorgenfreyPlane.isClosed_antiDiagonal
  · intro h
    exact SorgenfreyPlane.antiDiagonal_not_separable <|
      (liftedSubtypeHomeomorph SorgenfreyPlane.antiDiagonal).separableSpace_iff.mp h

/- Exercise 4.99.4 (27): Local metrizability is preserved by arbitrary subspaces. -/
#check Subtype.locallyMetrizableSpace

/- Exercise 4.99.4 (28): Metrizability is preserved by arbitrary subspaces. -/
#check fun (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (s : Set X) ↦ (inferInstance : TopologicalSpace.MetrizableSpace s)
