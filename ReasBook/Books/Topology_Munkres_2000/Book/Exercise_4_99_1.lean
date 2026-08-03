module

import Topology_Munkres_2000.Book.Example_32_2.Separation
import Topology_Munkres_2000.Book.Example_18_3
import Topology_Munkres_2000.Book.Example_23_6
import Topology_Munkres_2000.Book.Example_29_2
import Topology_Munkres_2000.Book.Exercise_25_1.Connectedness
import Topology_Munkres_2000.Book.Exercise_25_2
import Topology_Munkres_2000.Book.Exercise_28_2
import Topology_Munkres_2000.Book.Exercise_28_1
import Topology_Munkres_2000.Book.Exercise_30_1
import Topology_Munkres_2000.Book.Exercise_32_9
import Topology_Munkres_2000.Book.Exercise_34_8
import Topology_Munkres_2000.Book.Theorem_20_2
import Topology_Munkres_2000.Book.Theorem_28_2
public import Topology_Munkres_2000.Book.Example_31_1
public import Topology_Munkres_2000.Book.Example_31_2.Instances
public import Topology_Munkres_2000.Book.Example_30_2
public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Topology_Munkres_2000.Book.Example_28_2.Instances
public import Topology_Munkres_2000.Book.Definition_20_9.UniformMetric
public import Topology_Munkres_2000.Book.Example_30_5.Compactness
public import Topology_Munkres_2000.Book.Exercise_30_16.Instances
public import Topology_Munkres_2000.Book.Exercise_30_7
public import Topology_Munkres_2000.Book.Exercise_23_7
public import Topology_Munkres_2000.Book.Exercise_23_8
public import Topology_Munkres_2000.Book.Exercise_22_6.RealKLine
public import Topology_Munkres_2000.Book.Exercise_25_3
public import Topology_Munkres_2000.Book.Exercise_27_3
public import Topology_Munkres_2000.Book.Exercise_34_1.RealLine
public import Topology_Munkres_2000.Book.Exercise_33_9
public import Topology_Munkres_2000.Book.Exercise_4_99_1.LocallyMetrizable
public import Topology_Munkres_2000.Book.Example_41_3.Instances
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UnitInterval

public section

/- Source recovery for Exercise 4.99.1: the original Munkres second-edition scan,
book page 228, prints the antecedent list in this order: connected, path connected,
locally connected, locally path connected, compact, limit point compact, locally
compact Hausdorff, Hausdorff, regular, completely regular, normal, first-countable,
second-countable, Lindelöf, having a countable dense subset, locally metrizable, and
metrizable. The entries below classify the eleven spaces against precisely that list. -/

universe u

/-- Helper for Exercise 4.99.1: every locally metrizable space is first-countable. -/
private lemma locallyMetrizableSpaceToFirstCountableTopology
    (X : Type u) [TopologicalSpace X] [LocallyMetrizableSpace X] :
    FirstCountableTopology X := by
  -- A metrizable neighborhood supplies a countably generated neighborhood filter at each point.
  constructor
  intro x
  obtain ⟨s, hs, hmetric⟩ := LocallyMetrizableSpace.exists_metrizable_nhds x
  -- Local instance justification (metrizable-neighborhood bridge): use the metric structure
  -- supplied specifically on the chosen neighborhood subtype.
  letI : TopologicalSpace.MetrizableSpace s := hmetric
  have hx : x ∈ s := mem_of_mem_nhds hs
  rw [← map_nhds_subtype_coe_eq_nhds hx hs]
  infer_instance

/-- Helper for Exercise 4.99.1: a nonconnected space cannot be path connected. -/
private lemma notPathConnectedOfNotConnected
    (X : Type u) [TopologicalSpace X] (h : ¬ ConnectedSpace X) :
    ¬ PathConnectedSpace X := by
  -- Path connectedness would supply the forbidden connected-space instance.
  intro hpath
  -- Local instance justification (hypothetical class): use the assumed structure to invoke
  -- its canonical implication.
  letI : PathConnectedSpace X := hpath
  exact h PathConnectedSpace.connectedSpace

/-- Helper for Exercise 4.99.1: failure of local connectedness rules out local path
connectedness. -/
private lemma notLocallyPathConnectedOfNotLocallyConnected
    (X : Type u) [TopologicalSpace X] (h : ¬ LocallyConnectedSpace X) :
    ¬ LocallyPathConnectedSpace X := by
  -- The canonical local path connectedness instance would imply local connectedness.
  intro hpath
  -- Local instance justification (hypothetical class): expose the assumed local path structure
  -- to typeclass inference.
  letI : LocallyPathConnectedSpace X := hpath
  exact h inferInstance

/-- Helper for Exercise 4.99.1: failure of first countability rules out local metrizability. -/
private lemma notLocallyMetrizableOfNotFirstCountable
    (X : Type u) [TopologicalSpace X] (h : ¬ FirstCountableTopology X) :
    ¬ LocallyMetrizableSpace X := by
  -- Apply the generic first-countability consequence of local metrizability.
  intro hlocal
  -- Local instance justification (hypothetical class): make the assumed local metric structure
  -- available to the helper.
  letI : LocallyMetrizableSpace X := hlocal
  exact h (locallyMetrizableSpaceToFirstCountableTopology X)

/-- Helper for Exercise 4.99.1: failure of first countability rules out metrizability. -/
private lemma notMetrizableOfNotFirstCountable
    (X : Type u) [TopologicalSpace X] (h : ¬ FirstCountableTopology X) :
    ¬ TopologicalSpace.MetrizableSpace X := by
  -- A compatible metric always gives a countable neighborhood basis.
  intro hmetric
  -- Local instance justification (hypothetical class): make the assumed compatible metric
  -- available to inference.
  letI : TopologicalSpace.MetrizableSpace X := hmetric
  exact h inferInstance

/-- Helper for Exercise 4.99.1: failure of second countability rules out metrizability. -/
private lemma notMetrizableOfNotSecondCountable
    (X : Type u) [TopologicalSpace X] [LindelofSpace X]
    (h : ¬ SecondCountableTopology X) :
    ¬ TopologicalSpace.MetrizableSpace X := by
  -- A metrizable Lindelöf space is second-countable; the applications below already supply
  -- Lindelöfness.
  intro hmetric
  -- Local instance justification (hypothetical class): make the assumed compatible metric
  -- available to inference.
  letI : TopologicalSpace.MetrizableSpace X := hmetric
  exact h inferInstance

/-- Helper for Exercise 4.99.1: every nonempty power of `ℝ` is noncompact. -/
private lemma realPowerNotCompact (J : Type u) [Nonempty J] :
    ¬ CompactSpace (J → ℝ) := by
  -- A coordinate projection is a continuous surjection onto the noncompact real line.
  intro hcompact
  -- Local instance justification (hypothetical class): expose the assumed compact product.
  letI : CompactSpace (J → ℝ) := hcompact
  let j : J := Classical.choice inferInstance
  have hsurjective : Function.Surjective (fun x : J → ℝ ↦ x j) := by
    intro y
    exact ⟨fun _ ↦ y, rfl⟩
  exact (not_compactSpace_iff.mpr inferInstance)
    (hsurjective.compactSpace (continuous_apply j))

/-- Helper for Exercise 4.99.1: in a metrizable noncompact space, limit-point compactness fails. -/
private lemma notLimitPointCompactOfMetrizableNotCompact
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (h : ¬ CompactSpace X) : ¬ LimitPointCompactSpace X := by
  -- The metrizable compactness equivalence converts the alleged limit-point compactness.
  intro hlimit
  exact h ((compactSpace_iff_limitPointCompactSpace X).mpr hlimit)

/-- Helper for Exercise 4.99.1: an infinite product of real lines is not limit-point compact. -/
private lemma realPowerNotLimitPointCompact (J : Type u) [Infinite J] :
    ¬ LimitPointCompactSpace (J → ℝ) := by
  -- Restriction along a countable coordinate embedding is a continuous surjection onto `ℕ → ℝ`.
  intro hlimit
  -- Local instance justification (countable-compactness bridge): convert the assumed limit-point
  -- compactness through the T₁ equivalence used by the image theorem below.
  letI : CountablyCompactSpace (J → ℝ) :=
    (limitPointCompactSpace_iff_countablyCompactSpace (J → ℝ)).mp hlimit
  let e : ℕ ↪ J := Infinite.natEmbedding J
  let restrict : (J → ℝ) → (ℕ → ℝ) := fun x n ↦ x (e n)
  have hcontinuous : Continuous restrict := by
    -- Product continuity is checked one restricted coordinate at a time.
    exact continuous_pi fun n ↦ continuous_apply (e n)
  have hsurjective : Function.Surjective restrict := by
    -- Extend an arbitrary countable sequence by zero off the embedded coordinates.
    intro y
    classical
    refine ⟨Function.extend e y 0, ?_⟩
    funext n
    exact e.injective.extend_apply y 0 n
  have hcountablyCompact : IsCountablyCompact (Set.univ : Set (ℕ → ℝ)) := by
    rw [← Set.image_univ_of_surjective hsurjective]
    exact CountablyCompactSpace.isCountablyCompact_univ.image hcontinuous
  have htarget : LimitPointCompactSpace (ℕ → ℝ) :=
    (limitPointCompactSpace_iff_countablyCompactSpace (ℕ → ℝ)).mpr
      (isCountablyCompact_univ_iff.mp hcountablyCompact)
  exact (notLimitPointCompactOfMetrizableNotCompact (ℕ → ℝ)
    (realPowerNotCompact ℕ)) htarget

/-- Helper for Exercise 4.99.1: no point of an infinite real power has a compact neighborhood. -/
private lemma realPowerNotWeaklyLocallyCompact (J : Type u) [Infinite J] :
    ¬ WeaklyLocallyCompactSpace (J → ℝ) := by
  -- A compact neighborhood restricts each coordinate to a proper compact subset of `ℝ`.
  intro hweak
  rw [weaklyLocallyCompactSpace_iff] at hweak
  have hpoint := hweak (0 : J → ℝ)
  rw [isWeaklyLocallyCompactAt_iff] at hpoint
  obtain ⟨K, hKcompact, hKnhds⟩ := hpoint
  classical
  have hproper (j : J) : (fun z : J → ℝ ↦ z j) '' K ≠ Set.univ :=
    (hKcompact.image (continuous_apply j)).ne_univ
  have hescape : ∀ j : J, ∃ r : ℝ, r ∉ (fun z : J → ℝ ↦ z j) '' K := by
    intro j
    exact (Set.ne_univ_iff_exists_notMem _).mp (hproper j)
  choose y hy using hescape
  -- A product neighborhood changes only finitely many coordinates, leaving one escape value free.
  obtain ⟨I, hI⟩ := exists_finset_piecewise_mem_of_mem_nhds hKnhds y
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
  apply hy j
  refine ⟨I.piecewise (0 : J → ℝ) y, hI, ?_⟩
  exact I.piecewise_eq_of_notMem (0 : J → ℝ) y hj

/-- Helper for Exercise 4.99.1: a successor-ordered order topology is totally separated. -/
private lemma totallySeparatedSpaceOfSuccOrder
    (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [SuccOrder X] : TotallySeparatedSpace X := by
  -- A clopen initial segment separates any two distinct points.
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · have hxNotMax : ¬ IsMax x := by
      intro hx
      exact (not_le_of_gt hxy) (hx hxy.le)
    have hxClopen : IsClopen (Set.Iic x) := by
      constructor
      · exact isClosed_Iic
      · rw [← Order.Iio_succ_of_not_isMax hxNotMax]
        exact isOpen_Iio
    have hyNotMem : y ∉ Set.Iic x := by
      simpa using hxy
    exact ⟨Set.Iic x, hxClopen, le_rfl, hyNotMem⟩
  · have hyNotMax : ¬ IsMax y := by
      intro hy
      exact (not_le_of_gt hyx) (hy hyx.le)
    have hyClopen : IsClopen (Set.Iic y) := by
      constructor
      · exact isClosed_Iic
      · rw [← Order.Iio_succ_of_not_isMax hyNotMax]
        exact isOpen_Iio
    have hxMem : x ∈ (Set.Iic y)ᶜ := by
      simpa using hyx
    have hyNotMem : y ∉ (Set.Iic y)ᶜ := by
      simp
    exact ⟨(Set.Iic y)ᶜ, hyClopen.compl, hxMem, hyNotMem⟩

/-- Helper for Exercise 4.99.1: the ordinal `ω` regarded as a point of `OpenOmegaOne`. -/
private noncomputable def openOmegaOneOmega : OpenOmegaOne :=
  ⟨Ordinal.omega0, Ordinal.omega0_lt_omega_one⟩

/-- Helper for Exercise 4.99.1: the point `ω` is a successor limit in `OpenOmegaOne`. -/
private lemma openOmegaOneOmega_isSuccLimit :
    Order.IsSuccLimit openOmegaOneOmega := by
  -- The ambient ordinal `ω` is nonminimal and has no immediate predecessor.
  constructor
  · rw [not_isMin_iff]
    have hzeroLt : CountableOrdinal.zero < openOmegaOneOmega := by
      change (0 : Ordinal) < Ordinal.omega0
      exact Ordinal.omega0_pos
    exact ⟨CountableOrdinal.zero, hzeroLt⟩
  · intro b hb
    apply Ordinal.isSuccLimit_omega0.isSuccPrelimit b.1
    refine ⟨hb.lt, ?_⟩
    intro c hbc hcω
    let c' : OpenOmegaOne := ⟨c, hcω.trans openOmegaOneOmega.property⟩
    exact hb.2 (show b < c' from hbc) (show c' < openOmegaOneOmega from hcω)

/-- Helper for Exercise 4.99.1: the open first-uncountable ordinal has no greatest point. -/
private instance openOmegaOneNoMaxOrder : NoMaxOrder OpenOmegaOne where
  exists_gt := OpenOmegaOne.exists_gt

/-- Helper for Exercise 4.99.1: the point `ω` is not isolated in `OpenOmegaOne`. -/
private lemma openOmegaOneOmega_singleton_not_isOpen :
    ¬ IsOpen ({openOmegaOneOmega} : Set OpenOmegaOne) := by
  -- In a successor order, precisely the non-limit points have open singletons.
  intro hopen
  exact (SuccOrder.isOpen_singleton_iff.mp hopen) openOmegaOneOmega_isSuccLimit

/-- Helper for Exercise 4.99.1: the image of `ω` is not isolated in `ClosedOmegaOne`. -/
private lemma closedOmegaOneOmega_singleton_not_isOpen :
    ¬ IsOpen ({OpenOmegaOne.toClosed openOmegaOneOmega} : Set ClosedOmegaOne) := by
  -- An open singleton upstairs would pull back to the forbidden singleton downstairs.
  intro hopen
  have hpreimage :
      OpenOmegaOne.toClosed ⁻¹' ({OpenOmegaOne.toClosed openOmegaOneOmega} : Set ClosedOmegaOne) =
        ({openOmegaOneOmega} : Set OpenOmegaOne) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact OpenOmegaOne.isEmbedding_toClosed.injective.eq_iff
  apply openOmegaOneOmega_singleton_not_isOpen
  rw [← hpreimage]
  exact OpenOmegaOne.isEmbedding_toClosed.continuous.isOpen_preimage _ hopen

/-- Helper for Exercise 4.99.1: a nontrivial totally disconnected space is not connected. -/
private lemma notConnectedOfTotallyDisconnected
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X]
    {x y : X} (hxy : x ≠ y) : ¬ ConnectedSpace X := by
  -- A continuous identity map from a connected space to a totally disconnected one is constant.
  intro hconnected
  -- Local instance justification (hypothetical class): expose the assumed connected structure.
  letI : ConnectedSpace X := hconnected
  exact hxy (TotallyDisconnectedSpace.eq_of_continuous (fun z : X ↦ z) continuous_id x y)

/-- Helper for Exercise 4.99.1: a nonisolated point in a totally disconnected space
rules out local connectedness. -/
private lemma notLocallyConnectedOfTotallyDisconnected
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (x : X) (hx : ¬ IsOpen ({x} : Set X)) : ¬ LocallyConnectedSpace X := by
  -- Local connectedness would make the singleton connected component of `x` open.
  intro hlocal
  -- Local instance justification (hypothetical class): expose the assumed local structure.
  letI : LocallyConnectedSpace X := hlocal
  apply hx
  rw [← connectedComponent_eq_singleton x]
  exact isOpen_connectedComponent

/-- Helper for Exercise 4.99.1: `OpenOmegaOne` is totally disconnected. -/
private instance openOmegaOneTotallyDisconnectedSpace :
    TotallyDisconnectedSpace OpenOmegaOne :=
  (totallySeparatedSpaceOfSuccOrder OpenOmegaOne).totallyDisconnectedSpace

/-- Helper for Exercise 4.99.1: the closed ordinal interval has its adjoined endpoint as top. -/
private noncomputable instance closedOmegaOneOrderTop : OrderTop ClosedOmegaOne where
  top := ClosedOmegaOne.omega
  le_top a := a.property

/-- Helper for Exercise 4.99.1: the closed ordinal interval carries its induced order topology. -/
private instance closedOmegaOneOrderTopology : OrderTopology ClosedOmegaOne := by
  -- This is the standard order topology on the initial interval ending at `ω₁`.
  exact (inferInstance : OrderTopology (Set.Iic (Ordinal.omega 1)))

/-- Helper for Exercise 4.99.1: the closed ordinal interval inherits ordinal successors. -/
private noncomputable instance closedOmegaOneSuccOrder : SuccOrder ClosedOmegaOne := by
  -- Expose the interval spelling required by the canonical subtype successor instance.
  change SuccOrder (Set.Iic (Ordinal.omega 1))
  infer_instance

/-- Helper for Exercise 4.99.1: `ClosedOmegaOne` is totally disconnected. -/
private instance closedOmegaOneTotallyDisconnectedSpace :
    TotallyDisconnectedSpace ClosedOmegaOne :=
  (totallySeparatedSpaceOfSuccOrder ClosedOmegaOne).totallyDisconnectedSpace

/-- Helper for Exercise 4.99.1: every point of `OpenOmegaOne` has a compact neighborhood. -/
private instance openOmegaOneWeaklyLocallyCompactSpace :
    WeaklyLocallyCompactSpace OpenOmegaOne where
  exists_compact_mem_nhds a := by
    -- Enlarge the point once and use the resulting compact initial interval.
    obtain ⟨b, hab⟩ := OpenOmegaOne.exists_gt a
    exact ⟨Set.Iic b, OpenOmegaOne.isCompact_Iic b, Iic_mem_nhds hab⟩

namespace OpenOmegaOne

/-- Exercise 4.99.1 (1): The open first-uncountable ordinal is not connected. -/
theorem notConnected : ¬ (ConnectedSpace (OpenOmegaOne)) := by
  -- The least ordinal and the countable limit `ω` are distinct in a totally disconnected space.
  refine notConnectedOfTotallyDisconnected OpenOmegaOne
    (x := CountableOrdinal.zero) (y := openOmegaOneOmega) ?_
  intro h
  have hOrdinal := congrArg (fun x : OpenOmegaOne ↦ (x : Ordinal)) h
  exact Ordinal.omega0_ne_zero hOrdinal.symm

/-- Exercise 4.99.1 (2): The open first-uncountable ordinal is not path connected. -/
theorem notPathConnected : ¬ (PathConnectedSpace (OpenOmegaOne)) := by
  -- Path connectedness would imply the already excluded connectedness.
  exact notPathConnectedOfNotConnected OpenOmegaOne notConnected

/-- Exercise 4.99.1 (3): The open first-uncountable ordinal is not locally connected. -/
theorem notLocallyConnected : ¬ (LocallyConnectedSpace (OpenOmegaOne)) := by
  -- The nonisolated countable limit point obstructs local connectedness.
  exact notLocallyConnectedOfTotallyDisconnected OpenOmegaOne openOmegaOneOmega
    openOmegaOneOmega_singleton_not_isOpen

/-- Exercise 4.99.1 (4): The open first-uncountable ordinal is not locally path connected. -/
theorem notLocallyPathConnected :
    ¬ (LocallyPathConnectedSpace (OpenOmegaOne)) := by
  -- Local path connectedness would imply the already excluded local connectedness.
  exact notLocallyPathConnectedOfNotLocallyConnected OpenOmegaOne notLocallyConnected

/-- Exercise 4.99.1 (5): The open first-uncountable ordinal is not compact. -/
theorem notCompact : ¬ CompactSpace OpenOmegaOne :=
  not_compactSpace_iff.mpr inferInstance

/- Exercise 4.99.1 (6): The open first-uncountable ordinal is limit point compact. -/
#check (inferInstance : LimitPointCompactSpace OpenOmegaOne)

/-- Exercise 4.99.1 (7): The open first-uncountable ordinal is locally compact Hausdorff. -/
instance instLocallyCompactSpace : LocallyCompactSpace OpenOmegaOne := by
  -- Hausdorff weak local compactness upgrades to local compactness.
  infer_instance

#check instLocallyCompactSpace
#check (inferInstance : T2Space OpenOmegaOne)

/- Exercise 4.99.1 (8): The open first-uncountable ordinal is Hausdorff. -/
#check (inferInstance : T2Space OpenOmegaOne)

/- Exercise 4.99.1 (9): The open first-uncountable ordinal is regular. -/
#check (inferInstance : T3Space OpenOmegaOne)

/- Exercise 4.99.1 (10): The open first-uncountable ordinal is completely regular. -/
#check (inferInstance : T35Space OpenOmegaOne)

/- Exercise 4.99.1 (11): The open first-uncountable ordinal is normal. -/
#check (inferInstance : T4Space OpenOmegaOne)

/- Exercise 4.99.1 (12): The open first-uncountable ordinal is first-countable. -/
#check OpenOmegaOne.instFirstCountableTopology
/- Exercise 4.99.1 (13): The open first-uncountable ordinal is not second-countable. -/
#check OpenOmegaOne.notSecondCountable

/- Exercise 4.99.1 (14): The open first-uncountable ordinal is not Lindelöf. -/
#check OpenOmegaOne.notLindelof

/- Exercise 4.99.1 (15): The open first-uncountable ordinal does not have a countable dense
subset. -/
#check OpenOmegaOne.notSeparable

/- Exercise 4.99.1 (16): The open first-uncountable ordinal is locally metrizable. -/
#check OpenOmegaOne.instLocallyMetrizableSpace

/-- Exercise 4.99.1 (17): The open first-uncountable ordinal is not metrizable. -/
theorem notMetrizable : ¬ (TopologicalSpace.MetrizableSpace (OpenOmegaOne)) := by
  -- In a metrizable space, limit-point compactness would force compactness.
  intro hmetric
  -- Local instance justification (hypothetical class): expose the assumed compatible metric.
  letI : TopologicalSpace.MetrizableSpace OpenOmegaOne := hmetric
  exact notCompact ((compactSpace_iff_limitPointCompactSpace OpenOmegaOne).mpr inferInstance)

end OpenOmegaOne

namespace ClosedOmegaOne

/-- Exercise 4.99.1 (18): The closed first-uncountable ordinal is not connected. -/
theorem notConnected : ¬ (ConnectedSpace (ClosedOmegaOne)) := by
  -- The embedded least ordinal and embedded `ω` remain distinct.
  refine notConnectedOfTotallyDisconnected ClosedOmegaOne
    (x := OpenOmegaOne.toClosed CountableOrdinal.zero)
    (y := OpenOmegaOne.toClosed openOmegaOneOmega) ?_
  have hne : CountableOrdinal.zero ≠ openOmegaOneOmega := by
    intro h
    have hOrdinal := congrArg (fun x : OpenOmegaOne ↦ (x : Ordinal)) h
    exact Ordinal.omega0_ne_zero hOrdinal.symm
  exact OpenOmegaOne.isEmbedding_toClosed.injective.ne hne

/-- Exercise 4.99.1 (19): The closed first-uncountable ordinal is not path connected. -/
theorem notPathConnected : ¬ (PathConnectedSpace (ClosedOmegaOne)) := by
  -- Path connectedness would imply the already excluded connectedness.
  exact notPathConnectedOfNotConnected ClosedOmegaOne notConnected

/-- Exercise 4.99.1 (20): The closed first-uncountable ordinal is not locally connected. -/
theorem notLocallyConnected : ¬ (LocallyConnectedSpace (ClosedOmegaOne)) := by
  -- The embedded countable limit point is still nonisolated.
  exact notLocallyConnectedOfTotallyDisconnected ClosedOmegaOne
    (OpenOmegaOne.toClosed openOmegaOneOmega) closedOmegaOneOmega_singleton_not_isOpen

/-- Exercise 4.99.1 (21): The closed first-uncountable ordinal is not locally path connected. -/
theorem notLocallyPathConnected :
    ¬ (LocallyPathConnectedSpace (ClosedOmegaOne)) := by
  -- Local path connectedness would imply the already excluded local connectedness.
  exact notLocallyPathConnectedOfNotLocallyConnected ClosedOmegaOne notLocallyConnected

/- Exercise 4.99.1 (22): The closed first-uncountable ordinal is compact. -/
#check ClosedOmegaOne.instCompactSpace

/- Exercise 4.99.1 (23): The closed first-uncountable ordinal is limit point compact. -/
#check (inferInstance : LimitPointCompactSpace ClosedOmegaOne)

/- Exercise 4.99.1 (24): The closed first-uncountable ordinal is locally compact Hausdorff. -/
#check (inferInstance : LocallyCompactSpace ClosedOmegaOne)
#check (inferInstance : T2Space ClosedOmegaOne)

/- Exercise 4.99.1 (25): The closed first-uncountable ordinal is Hausdorff. -/
#check (inferInstance : T2Space ClosedOmegaOne)

/- Exercise 4.99.1 (26): The closed first-uncountable ordinal is regular. -/
#check (inferInstance : T3Space ClosedOmegaOne)

/- Exercise 4.99.1 (27): The closed first-uncountable ordinal is completely regular. -/
#check (inferInstance : T35Space ClosedOmegaOne)

/- Exercise 4.99.1 (28): The closed first-uncountable ordinal is normal. -/
#check (inferInstance : T4Space ClosedOmegaOne)

/- Exercise 4.99.1 (29): The closed first-uncountable ordinal is not first-countable. -/
#check ClosedOmegaOne.notFirstCountable

/- Exercise 4.99.1 (30): The closed first-uncountable ordinal is not second-countable. -/
#check ClosedOmegaOne.notSecondCountable

/- Exercise 4.99.1 (31): The closed first-uncountable ordinal is Lindelöf. -/
#check (inferInstance : LindelofSpace ClosedOmegaOne)

/- Exercise 4.99.1 (32): The closed first-uncountable ordinal does not have a countable dense
subset. -/
#check ClosedOmegaOne.notSeparable

/-- Exercise 4.99.1 (33): The closed first-uncountable ordinal is not locally metrizable. -/
theorem notLocallyMetrizable : ¬ (LocallyMetrizableSpace (ClosedOmegaOne)) := by
  -- Local metrizability would contradict failure of first countability at the endpoint.
  exact notLocallyMetrizableOfNotFirstCountable ClosedOmegaOne ClosedOmegaOne.notFirstCountable

/-- Exercise 4.99.1 (34): The closed first-uncountable ordinal is not metrizable. -/
theorem notMetrizable :
    ¬ (TopologicalSpace.MetrizableSpace (ClosedOmegaOne)) := by
  -- Every metrizable space is first-countable.
  exact notMetrizableOfNotFirstCountable ClosedOmegaOne ClosedOmegaOne.notFirstCountable

end ClosedOmegaOne

namespace OmegaOneProduct

/-- Helper for Exercise 4.99.1: a strip with bounded first ordinal coordinate is compact. -/
private lemma isCompact_boundedStrip (b : OpenOmegaOne) :
    IsCompact {p : OpenOmegaOne × ClosedOmegaOne | p.1 ≤ b} := by
  -- The strip is the product of a compact initial interval with the compact closed ordinal.
  have hproduct : IsCompact (Set.Iic b ×ˢ (Set.univ : Set ClosedOmegaOne)) :=
    (OpenOmegaOne.isCompact_Iic b).prod isCompact_univ
  have hset : {p : OpenOmegaOne × ClosedOmegaOne | p.1 ≤ b} =
      Set.Iic b ×ˢ (Set.univ : Set ClosedOmegaOne) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true]
  rw [hset]
  exact hproduct

/-- Helper for Exercise 4.99.1: the product point over `ω` is not isolated. -/
private lemma omegaProductPoint_singleton_not_isOpen :
    ¬ IsOpen ({(openOmegaOneOmega, ClosedOmegaOne.omega)} :
      Set (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Pull an alleged singleton neighborhood back along the fixed-coordinate embedding.
  intro hopen
  apply openOmegaOneOmega_singleton_not_isOpen
  have hpreimage := (continuous_id.prodMk
    (continuous_const : Continuous (fun _ : OpenOmegaOne ↦ ClosedOmegaOne.omega))).isOpen_preimage
      _ hopen
  have hset : (fun x : OpenOmegaOne ↦ (id x, ClosedOmegaOne.omega)) ⁻¹'
      ({(openOmegaOneOmega, ClosedOmegaOne.omega)} :
        Set (OpenOmegaOne × ClosedOmegaOne)) = {openOmegaOneOmega} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, and_true, id_eq]
  rwa [hset] at hpreimage

/-- Exercise 4.99.1 (35): The product of the open and closed first-uncountable ordinals is not
connected. -/
theorem notConnected :
    ¬ (ConnectedSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Total disconnectedness and two points with different first coordinates give disconnection.
  refine notConnectedOfTotallyDisconnected (OpenOmegaOne × ClosedOmegaOne)
    (x := (CountableOrdinal.zero, ClosedOmegaOne.omega))
    (y := (openOmegaOneOmega, ClosedOmegaOne.omega)) ?_
  intro h
  have hfirst := congrArg Prod.fst h
  have hOrdinal := congrArg (fun x : OpenOmegaOne ↦ (x : Ordinal)) hfirst
  exact Ordinal.omega0_ne_zero hOrdinal.symm

/-- Exercise 4.99.1 (36): The product of the open and closed first-uncountable ordinals is not
path connected. -/
theorem notPathConnected :
    ¬ (PathConnectedSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Path connectedness would imply the already excluded connectedness.
  exact notPathConnectedOfNotConnected (OpenOmegaOne × ClosedOmegaOne) notConnected

/-- Exercise 4.99.1 (37): The product of the open and closed first-uncountable ordinals is not
locally connected. -/
theorem notLocallyConnected :
    ¬ (LocallyConnectedSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- The product is totally disconnected and has a nonisolated point.
  exact notLocallyConnectedOfTotallyDisconnected
    (OpenOmegaOne × ClosedOmegaOne) (openOmegaOneOmega, ClosedOmegaOne.omega)
      omegaProductPoint_singleton_not_isOpen

/-- Exercise 4.99.1 (38): The product of the open and closed first-uncountable ordinals is not
locally path connected. -/
theorem notLocallyPathConnected :
    ¬ (LocallyPathConnectedSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Local path connectedness would imply local connectedness.
  exact notLocallyPathConnectedOfNotLocallyConnected
    (OpenOmegaOne × ClosedOmegaOne) notLocallyConnected

/-- Exercise 4.99.1 (39): The product of the open and closed first-uncountable ordinals is not
compact. -/
theorem notCompact : ¬ (CompactSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Compactness would descend along the surjective first projection.
  intro hcompact
  -- Local instance justification (hypothetical class): expose the assumed product compactness.
  letI : CompactSpace (OpenOmegaOne × ClosedOmegaOne) := hcompact
  exact OpenOmegaOne.notCompact (Prod.fst_surjective.compactSpace
    (continuous_fst : Continuous
      (Prod.fst : OpenOmegaOne × ClosedOmegaOne → OpenOmegaOne)))

/-- Exercise 4.99.1 (40): The product of the open and closed first-uncountable ordinals is limit
point compact. -/
instance instLimitPointCompactSpace :
    LimitPointCompactSpace (OpenOmegaOne × ClosedOmegaOne) := by
  -- Bound a countably infinite subset in one compact ordinal strip.
  rw [limitPointCompactSpace_iff]
  intro A hA
  obtain ⟨B, hBA, hBcountable, hBinfinite⟩ := hA.exists_subset_countable_infinite
  have hFirstCountable : (Prod.fst '' B).Countable := hBcountable.image Prod.fst
  obtain ⟨b, hb⟩ := OpenOmegaOne.bddAbove_of_countable _ hFirstCountable
  have hBstrip : B ⊆ {p : OpenOmegaOne × ClosedOmegaOne | p.1 ≤ b} := by
    intro p hp
    exact hb ⟨p, hp, rfl⟩
  obtain ⟨p, _, hp⟩ :=
    (isCompact_boundedStrip b).isCountablyCompact.exists_accPt_of_infinite
      hBstrip hBinfinite
  exact ⟨p, hp.mono (Filter.principal_mono.mpr hBA)⟩

/-- Exercise 4.99.1 (41): The product of the open and closed first-uncountable ordinals is
locally compact Hausdorff. -/
theorem locallyCompactT2 :
    (LocallyCompactSpace (OpenOmegaOne × ClosedOmegaOne)) ∧
      T2Space (OpenOmegaOne × ClosedOmegaOne) := by
  -- Both factors are locally compact Hausdorff, so their product is as well.
  exact ⟨inferInstance, inferInstance⟩

/-- The product of the open and closed first-uncountable ordinals is locally compact. -/
instance instLocallyCompactSpace :
    LocallyCompactSpace (OpenOmegaOne × ClosedOmegaOne) := by
  -- Products of locally compact Hausdorff spaces are locally compact.
  infer_instance

/-- Exercise 4.99.1 (42): The product of the open and closed first-uncountable ordinals is
Hausdorff. -/
instance instT2Space : T2Space (OpenOmegaOne × ClosedOmegaOne) := by
  -- Hausdorffness is inherited componentwise by products.
  infer_instance

/-- Exercise 4.99.1 (43): The product of the open and closed first-uncountable ordinals is
regular. -/
instance instT3Space : T3Space (OpenOmegaOne × ClosedOmegaOne) := by
  -- The canonical product separation instance applies to the two regular factors.
  infer_instance

/-- Exercise 4.99.1 (44): The product of the open and closed first-uncountable ordinals is
completely regular. -/
instance instT35Space : T35Space (OpenOmegaOne × ClosedOmegaOne) := by
  -- The canonical product separation instance applies to the completely regular factors.
  infer_instance

/- Exercise 4.99.1 (45): The product of the open and closed first-uncountable ordinals is not
normal. -/
#check OpenOmegaOne.prodClosedOmegaOne_notT4

/-- Exercise 4.99.1 (46): The product of the open and closed first-uncountable ordinals is not
first-countable. -/
theorem notFirstCountable :
    ¬ (FirstCountableTopology (OpenOmegaOne × ClosedOmegaOne)) := by
  -- A fixed first-coordinate copy would make `ClosedOmegaOne` first-countable.
  intro hfirst
  -- Local instance justification (hypothetical class): expose the assumed product local bases.
  letI : FirstCountableTopology (OpenOmegaOne × ClosedOmegaOne) := hfirst
  exact ClosedOmegaOne.notFirstCountable
    (isEmbedding_prodMkRight CountableOrdinal.zero).firstCountableTopology

/-- Exercise 4.99.1 (47): The product of the open and closed first-uncountable ordinals is not
second-countable. -/
theorem notSecondCountable :
    ¬ (SecondCountableTopology (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Second countability would in particular give first countability.
  intro hsecond
  -- Local instance justification (hypothetical class): expose the assumed countable basis.
  letI : SecondCountableTopology (OpenOmegaOne × ClosedOmegaOne) := hsecond
  exact notFirstCountable inferInstance

/-- Exercise 4.99.1 (48): The product of the open and closed first-uncountable ordinals is not
Lindelöf. -/
theorem notLindelof : ¬ (LindelofSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Lindelöfness would descend along the surjective first projection.
  intro hlindelof
  -- Local instance justification (hypothetical class): expose the assumed product property.
  letI : LindelofSpace (OpenOmegaOne × ClosedOmegaOne) := hlindelof
  exact OpenOmegaOne.notLindelof
    (LindelofSpace.of_continuous_surjective
      (continuous_fst : Continuous
        (Prod.fst : OpenOmegaOne × ClosedOmegaOne → OpenOmegaOne))
      Prod.fst_surjective)

/-- Exercise 4.99.1 (49): The product of the open and closed first-uncountable ordinals is not
has a countable dense subset. -/
theorem notSeparable :
    ¬ (TopologicalSpace.SeparableSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- A continuous surjective projection would make the open ordinal separable.
  intro hseparable
  -- Local instance justification (hypothetical class): expose the assumed dense countable set.
  letI : TopologicalSpace.SeparableSpace (OpenOmegaOne × ClosedOmegaOne) := hseparable
  exact OpenOmegaOne.notSeparable
    (Prod.fst_surjective.denseRange.separableSpace
      (continuous_fst : Continuous
        (Prod.fst : OpenOmegaOne × ClosedOmegaOne → OpenOmegaOne)))

/-- Exercise 4.99.1 (50): The product of the open and closed first-uncountable ordinals is not
locally metrizable. -/
theorem notLocallyMetrizable :
    ¬ (LocallyMetrizableSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Local metrizability would force first countability.
  exact notLocallyMetrizableOfNotFirstCountable
    (OpenOmegaOne × ClosedOmegaOne) notFirstCountable

/-- Exercise 4.99.1 (51): The product of the open and closed first-uncountable ordinals is not
metrizable. -/
theorem notMetrizable :
    ¬ (TopologicalSpace.MetrizableSpace (OpenOmegaOne × ClosedOmegaOne)) := by
  -- Metrizability would force first countability.
  exact notMetrizableOfNotFirstCountable (OpenOmegaOne × ClosedOmegaOne) notFirstCountable

end OmegaOneProduct

namespace OrderedSquare

/-- Exercise 4.99.1 (52): The ordered square is connected. -/
instance instConnectedSpace : ConnectedSpace (OrderedSquare) := by
  -- The ordered square is a linear continuum, hence connected in its order topology.
  infer_instance

/-- Exercise 4.99.1 (53): The ordered square is not path connected. -/
theorem notPathConnected : ¬ (PathConnectedSpace (OrderedSquare)) := by
  -- A path-connected structure would contradict the known failure of path preconnectedness.
  intro hpath
  -- Local instance justification (hypothetical class): expose the assumed path-connected structure.
  letI : PathConnectedSpace OrderedSquare := hpath
  exact OrderedSquare.notPathPreconnected inferInstance

/- Exercise 4.99.1 (54): The ordered square is locally connected. -/
#check OrderedSquare.instLocallyConnectedSpace

/- Exercise 4.99.1 (55): The ordered square is not locally path connected. -/
#check OrderedSquare.notLocallyPathConnected

/- Exercise 4.99.1 (56): The ordered square is compact. -/
#check (inferInstance : CompactSpace OrderedSquare)

/- Exercise 4.99.1 (57): The ordered square is limit point compact. -/
#check (inferInstance : LimitPointCompactSpace OrderedSquare)

/- Exercise 4.99.1 (58): The ordered square is locally compact Hausdorff. -/
#check (inferInstance : LocallyCompactSpace OrderedSquare)
#check (inferInstance : T2Space OrderedSquare)

/- Exercise 4.99.1 (59): The ordered square is Hausdorff. -/
#check (inferInstance : T2Space OrderedSquare)

/- Exercise 4.99.1 (60): The ordered square is regular. -/
#check (inferInstance : T3Space OrderedSquare)

/- Exercise 4.99.1 (61): The ordered square is completely regular. -/
#check (inferInstance : T35Space OrderedSquare)

/- Exercise 4.99.1 (62): The ordered square is normal. -/
#check (inferInstance : T4Space OrderedSquare)

/- Exercise 4.99.1 (63): The ordered square is first-countable. -/
#check OrderedSquare.instFirstCountableTopology

/-- Helper for Exercise 4.99.1: the ordered square has an uncountable disjoint family of
nonempty open vertical intervals, so it is not separable. -/
private theorem orderedSquareNotSeparable :
    ¬ TopologicalSpace.SeparableSpace OrderedSquare := by
  -- Use the open interiors of the vertical fibers, indexed by the unit interval.
  let slice (x : unitInterval) : Set OrderedSquare :=
    {q | q.1 = x ∧ q.2 ∈ Set.Ioo (⊥ : unitInterval) ⊤}
  have hOpen (x : unitInterval) : IsOpen (slice x) := by
    rw [show slice x = @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap x ⊥) (verticalMap x ⊤) from verticalFiberInterior_eq_Ioo x]
    exact isOpen_Ioo
  have hNonempty (x : unitInterval) : (slice x).Nonempty := by
    refine ⟨toLex (x, unitIntervalMidpoint), rfl,
      unitIntervalMidpoint_pos, unitIntervalMidpoint_lt_top⟩
  have hDisjoint : Pairwise (Function.onFun Disjoint slice) := by
    intro x y hxy
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro q hqx hqy
    exact hxy (hqx.1.symm.trans hqy.1)
  intro hseparable
  -- Local instance justification (hypothetical class): invoke the disjoint-open-family theorem.
  letI : TopologicalSpace.SeparableSpace OrderedSquare := hseparable
  have hCountable : Countable unitInterval :=
    hDisjoint.countable_of_isOpen_disjoint hOpen hNonempty
  have hInterval : (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp hCountable
  exact (not_le_of_gt zero_lt_one) (Cardinal.Real.Icc_countable_iff.mp hInterval)

/-- Exercise 4.99.1 (64): The ordered square is not second-countable. -/
theorem notSecondCountable : ¬ (SecondCountableTopology (OrderedSquare)) := by
  -- A second-countable ordered square would be separable, contradicting the vertical family.
  intro hsecond
  -- Local instance justification (hypothetical class): expose the assumed countable basis.
  letI : SecondCountableTopology OrderedSquare := hsecond
  exact orderedSquareNotSeparable inferInstance

/- Exercise 4.99.1 (65): The ordered square is Lindelöf. -/
#check (inferInstance : LindelofSpace OrderedSquare)

/-- Exercise 4.99.1 (66): The ordered square does not have a countable dense subset. -/
theorem notSeparable : ¬ (TopologicalSpace.SeparableSpace (OrderedSquare)) := by
  -- The uncountable family of disjoint open vertical intervals is the obstruction.
  exact orderedSquareNotSeparable

/-- Exercise 4.99.1 (67): The ordered square is not locally metrizable. -/
theorem notLocallyMetrizable : ¬ LocallyMetrizableSpace OrderedSquare := by
  -- Compact local metrizability would produce a global metric, already ruled out below.
  intro hlocal
  -- Local instance justification (hypothetical class): globalize the assumed local metrics.
  letI : LocallyMetrizableSpace OrderedSquare := hlocal
  exact notSecondCountable
    (inferInstanceAs (SecondCountableTopology OrderedSquare))

/-- Exercise 4.99.1 (68): The ordered square is not metrizable. -/
theorem notMetrizable :
    ¬ TopologicalSpace.MetrizableSpace OrderedSquare := by
  -- Compactness makes a metrizable ordered square second-countable.
  exact notMetrizableOfNotSecondCountable OrderedSquare notSecondCountable

end OrderedSquare

namespace SorgenfreyLine

/-- Helper for Exercise 4.99.1: closed order intervals are closed in the Sorgenfrey line. -/
private lemma isClosed_Icc_lowerLimit (a b : SorgenfreyLine) :
    IsClosed (Set.Icc a b) := by
  -- Pull the usual-real closed interval back along the continuous carrier identity.
  have hpreimage : SorgenfreyLine.toReal ⁻¹'
      Set.Icc (SorgenfreyLine.toReal a) (SorgenfreyLine.toReal b) = Set.Icc a b := by
    ext x
    rfl
  rw [← hpreimage]
  exact isClosed_Icc.preimage SorgenfreyLine.continuous_toReal

/-- Helper for Exercise 4.99.1: every compact subset of the Sorgenfrey line is countable. -/
private theorem countable_of_isCompact {K : Set SorgenfreyLine} (hK : IsCompact K) :
    K.Countable := by
  classical
  -- On a compact subset, the carrier identity into the usual real line is an embedding.
  have hCompactSubtype : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Local instance justification (compact-subtype bridge): use the proved compactness of `K`.
  letI : CompactSpace K := hCompactSubtype
  let f : K → ℝ := fun x ↦ SorgenfreyLine.toReal x
  have hfContinuous : Continuous f :=
    SorgenfreyLine.continuous_toReal.comp continuous_subtype_val
  have hfInjective : Function.Injective f :=
    SorgenfreyLine.toReal.injective.comp Subtype.val_injective
  have hfEmbedding : Topology.IsClosedEmbedding f :=
    hfContinuous.isClosedEmbedding hfInjective
  -- Each point has a usual-real left interval containing no other point of `K`.
  have hLeftGap (x : K) :
      ∃ l : ℝ, l < f x ∧ ∀ y : K, l < f y → f y < f x → False := by
    let rightNhd : Set K :=
      {y | f x ≤ f y ∧ f y < f x + 1}
    have hAmbientOpen : IsOpen (SorgenfreyLine.toReal ⁻¹'
        Set.Ico (f x) (f x + 1)) := by
      apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨f x, f x + 1, lt_add_one (f x), rfl⟩
    have hRightOpen : IsOpen rightNhd := by
      change IsOpen (Subtype.val ⁻¹' (SorgenfreyLine.toReal ⁻¹'
        Set.Ico (f x) (f x + 1)))
      exact hAmbientOpen.preimage continuous_subtype_val
    have hRightNhd : rightNhd ∈ nhds x :=
      hRightOpen.mem_nhds ⟨le_rfl, lt_add_one (f x)⟩
    rw [hfEmbedding.isEmbedding.nhds_eq_comap] at hRightNhd
    obtain ⟨V, hV, hVRight⟩ := Filter.mem_comap.mp hRightNhd
    obtain ⟨l, u, hxu, hIooV⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
    refine ⟨l, hxu.1, ?_⟩
    intro y hly hyx
    have hyV : f y ∈ V := hIooV ⟨hly, hyx.trans hxu.2⟩
    exact (not_le_of_gt hyx) (hVRight hyV).1
  choose left hleft hgap using hLeftGap
  have hRational (x : K) :
      ∃ q : ℚ, left x < (q : ℝ) ∧ (q : ℝ) < f x :=
    exists_rat_btwn (hleft x)
  choose rational hleftRational hRationalPoint using hRational
  -- Equal chosen rationals would put one of two ordered points in the other's left gap.
  have hRationalInjective : Function.Injective rational := by
    intro x y hxy
    apply Subtype.ext
    apply SorgenfreyLine.toReal.injective
    apply le_antisymm
    · by_contra hnot
      have hyx : f y < f x := lt_of_not_ge hnot
      apply hgap x y
      · calc
          left x < (rational x : ℝ) := hleftRational x
          _ = (rational y : ℝ) := congrArg ((↑) : ℚ → ℝ) hxy
          _ < f y := hRationalPoint y
      · exact hyx
    · by_contra hnot
      have hxyPoint : f x < f y := lt_of_not_ge hnot
      apply hgap y x
      · calc
          left y < (rational y : ℝ) := hleftRational y
          _ = (rational x : ℝ) := congrArg ((↑) : ℚ → ℝ) hxy.symm
          _ < f x := hRationalPoint x
      · exact hxyPoint
  have hSubtypeCountable : Countable K := hRationalInjective.countable
  exact Set.countable_coe_iff.mp hSubtypeCountable

/-- Helper for Exercise 4.99.1: the Sorgenfrey line is not limit-point compact. -/
private theorem sorgenfreyNotLimitPointCompact :
    ¬ LimitPointCompactSpace SorgenfreyLine := by
  -- A closed unit interval would inherit countable compactness, contrary to Exercise 28.2.
  intro hlimit
  -- Local instance justification (hypothetical class): convert the assumed property to
  -- countable compactness.
  letI : LimitPointCompactSpace SorgenfreyLine := hlimit
  -- Local instance justification (countable-compactness bridge): expose the equivalent structure
  -- required to pass the property to the closed interval.
  letI : CountablyCompactSpace SorgenfreyLine :=
    (limitPointCompactSpace_iff_countablyCompactSpace SorgenfreyLine).mp hlimit
  have hIntervalCountablyCompact :
      IsCountablyCompact (Set.Icc (0 : SorgenfreyLine) 1) :=
    (isClosed_Icc_lowerLimit 0 1).isCountablyCompact
  have hSubtypeCountablyCompact :
      CountablyCompactSpace (Set.Icc (0 : SorgenfreyLine) 1) :=
    isCountablyCompact_iff_countablyCompactSpace.mp hIntervalCountablyCompact
  -- Local instance justification (closed subspace bridge): install the proved subtype property.
  letI : CountablyCompactSpace (Set.Icc (0 : SorgenfreyLine) 1) :=
    hSubtypeCountablyCompact
  exact sorgenfreyIcc_not_limitPointCompact
    ((limitPointCompactSpace_iff_countablyCompactSpace
      (Set.Icc (0 : SorgenfreyLine) 1)).mpr inferInstance)

/- Exercise 4.99.1 (69): The Sorgenfrey line is not connected. -/
#check SorgenfreyLine.notConnected

/-- Exercise 4.99.1 (70): The sorgenfrey line is not path connected. -/
theorem notPathConnected : ¬ (PathConnectedSpace (SorgenfreyLine)) := by
  -- Path connectedness would imply connectedness.
  exact notPathConnectedOfNotConnected SorgenfreyLine SorgenfreyLine.notConnected

/-- Exercise 4.99.1 (71): The sorgenfrey line is not locally connected. -/
theorem notLocallyConnected : ¬ (LocallyConnectedSpace (SorgenfreyLine)) := by
  -- The totally disconnected line has no isolated points; test the singleton at zero.
  apply notLocallyConnectedOfTotallyDisconnected SorgenfreyLine 0
  intro hopen
  obtain ⟨U, ⟨a, b, hab, rfl⟩, hzero, hU⟩ :=
    SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.exists_subset_of_mem_open
      (Set.mem_singleton (0 : SorgenfreyLine)) hopen
  let c : SorgenfreyLine := SorgenfreyLine.toReal.symm (b / 2)
  have hbpos : 0 < b := hzero.2
  have hcInterval : c ∈ Set.Ico a b := by
    constructor
    · apply hzero.1.trans
      change (0 : ℝ) ≤ b / 2
      exact (half_pos hbpos).le
    · change b / 2 < b
      exact half_lt_self hbpos
  have hcZero := hU hcInterval
  have hczero : c = 0 := Set.mem_singleton_iff.mp hcZero
  have hcoord := congrArg SorgenfreyLine.toReal hczero
  change b / 2 = 0 at hcoord
  linarith

/-- Exercise 4.99.1 (72): The sorgenfrey line is not locally path connected. -/
theorem notLocallyPathConnected :
    ¬ (LocallyPathConnectedSpace (SorgenfreyLine)) := by
  -- Local path connectedness would imply the already excluded local connectedness.
  exact notLocallyPathConnectedOfNotLocallyConnected SorgenfreyLine notLocallyConnected

/-- Exercise 4.99.1 (73): The sorgenfrey line is not compact. -/
theorem notCompact : ¬ (CompactSpace (SorgenfreyLine)) := by
  -- Compactness implies limit-point compactness, contradicting the interval obstruction.
  intro hcompact
  -- Local instance justification (hypothetical class): expose the assumed compactness.
  letI : CompactSpace SorgenfreyLine := hcompact
  exact sorgenfreyNotLimitPointCompact inferInstance

/-- Exercise 4.99.1 (74): The sorgenfrey line is not limit point compact. -/
theorem notLimitPointCompact : ¬ (LimitPointCompactSpace (SorgenfreyLine)) := by
  -- The closed unit interval supplies the obstruction.
  exact sorgenfreyNotLimitPointCompact

/-- Exercise 4.99.1 (75): The sorgenfrey line is not locally compact Hausdorff. -/
theorem notLocallyCompactT2 :
    ¬ ((LocallyCompactSpace (SorgenfreyLine)) ∧ (T2Space (SorgenfreyLine))) := by
  -- A compact neighborhood contains an uncountable basic interval, contradicting the helper.
  rintro ⟨hlocal, _⟩
  -- Local instance justification (hypothetical class): obtain a compact neighborhood at zero.
  letI : LocallyCompactSpace SorgenfreyLine := hlocal
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds (0 : SorgenfreyLine)
  obtain ⟨U, ⟨⟨a, b, hab, rfl⟩, hzero⟩, hUK⟩ :=
    SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.nhds_hasBasis.mem_iff.mp hKnhds
  have hBasicCountable : (Set.Ico a b : Set SorgenfreyLine).Countable :=
    (countable_of_isCompact hKcompact).mono hUK
  have hImage : SorgenfreyLine.toReal '' (Set.Ico a b : Set SorgenfreyLine) =
      (Set.Ico a b : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨SorgenfreyLine.toReal.symm x, hx,
        SorgenfreyLine.toReal.apply_symm_apply x⟩
  have hRealCountable : (Set.Ico a b : Set ℝ).Countable := by
    rw [← hImage]
    exact hBasicCountable.image SorgenfreyLine.toReal
  exact (not_le_of_gt hab) (Cardinal.Real.Ico_countable_iff.mp hRealCountable)

/- Exercise 4.99.1 (76): The Sorgenfrey line is Hausdorff. -/
#check (inferInstance : T2Space SorgenfreyLine)

/- Exercise 4.99.1 (77): The Sorgenfrey line is regular. -/
#check (inferInstance : T3Space SorgenfreyLine)

/- Exercise 4.99.1 (78): The Sorgenfrey line is completely regular. -/
#check (inferInstance : T35Space SorgenfreyLine)

/- Exercise 4.99.1 (79): The Sorgenfrey line is normal. -/
#check SorgenfreyLine.instT4Space

/- Exercise 4.99.1 (80): The Sorgenfrey line is first-countable. -/
#check SorgenfreyLine.instFirstCountableTopology

/- Exercise 4.99.1 (81): The Sorgenfrey line is not second-countable. -/
#check SorgenfreyLine.notSecondCountable

/- Exercise 4.99.1 (82): The Sorgenfrey line is Lindelöf. -/
#check SorgenfreyLine.instLindelofSpace

/- Exercise 4.99.1 (83): The Sorgenfrey line has a countable dense subset. -/
#check SorgenfreyLine.instSeparableSpace

/-- Exercise 4.99.1 (84): The sorgenfrey line is not locally metrizable. -/
theorem notLocallyMetrizable : ¬ (LocallyMetrizableSpace (SorgenfreyLine)) := by
  -- Regular Lindelöf local metrizability globalizes to a metric and hence second countability.
  intro hlocal
  -- Local instance justification (hypothetical class): globalize the assumed local metrics.
  letI : LocallyMetrizableSpace SorgenfreyLine := hlocal
  -- Local instance justification (globalization bridge): the preceding local metric structure,
  -- together with the canonical regular Lindelöf instances, supplies this global metric.
  letI : TopologicalSpace.MetrizableSpace SorgenfreyLine :=
    LocallyMetrizableSpace.metrizableSpace_of_t3_lindelof
  exact SorgenfreyLine.notSecondCountable inferInstance

/-- Exercise 4.99.1 (85): The Sorgenfrey line is not metrizable. -/
theorem notMetrizable :
    ¬ TopologicalSpace.MetrizableSpace SorgenfreyLine := by
  -- A Lindelöf metrizable Sorgenfrey line would be second-countable.
  exact notMetrizableOfNotSecondCountable SorgenfreyLine SorgenfreyLine.notSecondCountable

end SorgenfreyLine

namespace SquareMetricPlane

/- Exercise 4.99.1 (86): The square-metric plane is connected. -/
#check (inferInstance : ConnectedSpace (Fin 2 → ℝ))

/- Exercise 4.99.1 (87): The square-metric plane is path connected. -/
#check (inferInstance : PathConnectedSpace (Fin 2 → ℝ))

/- Exercise 4.99.1 (88): The square-metric plane is locally connected. -/
#check (inferInstance : LocallyConnectedSpace (Fin 2 → ℝ))

/- Exercise 4.99.1 (89): The square-metric plane is locally path connected. -/
#check (inferInstance : LocallyPathConnectedSpace (Fin 2 → ℝ))

/-- Exercise 4.99.1 (90): The square-metric plane is not compact. -/
theorem notCompact : ¬ (CompactSpace (Fin 2 → ℝ)) := by
  -- Projection onto either coordinate maps continuously onto the noncompact real line.
  exact realPowerNotCompact (Fin 2)

/-- Exercise 4.99.1 (91): The square-metric plane is not limit point compact. -/
theorem notLimitPointCompact :
    ¬ (LimitPointCompactSpace (Fin 2 → ℝ)) := by
  -- For this metrizable finite power, limit-point compactness is equivalent to compactness.
  exact notLimitPointCompactOfMetrizableNotCompact (Fin 2 → ℝ) notCompact

/-- Exercise 4.99.1 (92): The square-metric plane is locally compact Hausdorff. -/
theorem locallyCompactT2 :
    (LocallyCompactSpace (Fin 2 → ℝ)) ∧ (T2Space (Fin 2 → ℝ)) := by
  -- Finite products inherit local compactness and Hausdorffness from `ℝ`.
  exact ⟨inferInstance, inferInstance⟩

/-- The square-metric plane is locally compact. -/
instance instLocallyCompactSpace : LocallyCompactSpace (Fin 2 → ℝ) := by
  -- Extract the local compactness component of the preceding classification cell.
  exact locallyCompactT2.1

/- Exercise 4.99.1 (93): The square-metric plane is Hausdorff. -/
#check (inferInstance : T2Space (Fin 2 → ℝ))

/- Exercise 4.99.1 (94): The square-metric plane is regular. -/
#check (inferInstance : T3Space (Fin 2 → ℝ))

/- Exercise 4.99.1 (95): The square-metric plane is completely regular. -/
#check (inferInstance : T35Space (Fin 2 → ℝ))

/- Exercise 4.99.1 (96): The square-metric plane is normal. -/
#check (inferInstance : T4Space (Fin 2 → ℝ))

/- Exercise 4.99.1 (97): The square-metric plane is first-countable. -/
#check (inferInstance : FirstCountableTopology (Fin 2 → ℝ))

/- Exercise 4.99.1 (98): The square-metric plane is second-countable. -/
#check (inferInstance : SecondCountableTopology (Fin 2 → ℝ))

/- Exercise 4.99.1 (99): The square-metric plane is Lindelöf. -/
#check (inferInstance : LindelofSpace (Fin 2 → ℝ))

/- Exercise 4.99.1 (100): The square-metric plane has a countable dense subset. -/
#check (inferInstance : TopologicalSpace.SeparableSpace (Fin 2 → ℝ))

/- Exercise 4.99.1 (101): The square-metric plane is locally metrizable. -/
#check (inferInstance : LocallyMetrizableSpace (Fin 2 → ℝ))

/- Exercise 4.99.1 (102): The square-metric plane is metrizable. -/
#check (inferInstance : TopologicalSpace.MetrizableSpace (Fin 2 → ℝ))

end SquareMetricPlane

namespace RealSequence

/- Exercise 4.99.1 (103): Real sequence space in the product topology is connected. -/
#check (inferInstance : ConnectedSpace (ℕ → ℝ))

/- Exercise 4.99.1 (104): Real sequence space in the product topology is path connected. -/
#check (inferInstance : PathConnectedSpace (ℕ → ℝ))

/- Exercise 4.99.1 (105): Real sequence space in the product topology is locally connected. -/
#check (inferInstance : LocallyConnectedSpace (ℕ → ℝ))

/- Exercise 4.99.1 (106): Real sequence space in the product topology is locally path connected. -/
#check (inferInstance : LocallyPathConnectedSpace (ℕ → ℝ))

/-- Exercise 4.99.1 (107): Real sequence space in the product topology is not compact. -/
theorem notCompact : ¬ (CompactSpace (ℕ → ℝ)) := by
  -- A coordinate projection maps continuously onto the noncompact real line.
  exact realPowerNotCompact ℕ

/-- Exercise 4.99.1 (108): Real sequence space in the product topology is not limit point
compact. -/
theorem notLimitPointCompact : ¬ (LimitPointCompactSpace (ℕ → ℝ)) := by
  -- For the metrizable countable product, limit-point compactness is equivalent to compactness.
  exact notLimitPointCompactOfMetrizableNotCompact (ℕ → ℝ) notCompact

/-- Exercise 4.99.1 (109): Real sequence space in the product topology is not locally compact
Hausdorff. -/
theorem notLocallyCompactT2 :
    ¬ ((LocallyCompactSpace (ℕ → ℝ)) ∧ (T2Space (ℕ → ℝ))) := by
  -- Local compactness would imply weak local compactness, contradicting the product obstruction.
  rintro ⟨hlocal, _⟩
  -- Local instance justification (hypothetical class): expose the assumed local compactness.
  letI : LocallyCompactSpace (ℕ → ℝ) := hlocal
  exact realSequences_not_weaklyLocallyCompact inferInstance

/- Exercise 4.99.1 (110): Real sequence space in the product topology is Hausdorff. -/
#check (inferInstance : T2Space (ℕ → ℝ))

/- Exercise 4.99.1 (111): Real sequence space in the product topology is regular. -/
#check (inferInstance : T3Space (ℕ → ℝ))

/- Exercise 4.99.1 (112): Real sequence space in the product topology is completely regular. -/
#check (inferInstance : T35Space (ℕ → ℝ))

/- Exercise 4.99.1 (113): Real sequence space in the product topology is normal. -/
#check (inferInstance : T4Space (ℕ → ℝ))

/- Exercise 4.99.1 (114): Real sequence space in the product topology is first-countable. -/
#check (inferInstance : FirstCountableTopology (ℕ → ℝ))

/- Exercise 4.99.1 (115): Real sequence space in the product topology is second-countable. -/
#check (inferInstance : SecondCountableTopology (ℕ → ℝ))

/- Exercise 4.99.1 (116): Real sequence space in the product topology is Lindelöf. -/
#check (inferInstance : LindelofSpace (ℕ → ℝ))

/- Exercise 4.99.1 (117): Real sequence space in the product topology is has a countable dense
subset. -/
#check (inferInstance : TopologicalSpace.SeparableSpace (ℕ → ℝ))

/- Exercise 4.99.1 (118): Real sequence space in the product topology is locally metrizable. -/
#check (inferInstance : LocallyMetrizableSpace (ℕ → ℝ))

/- Exercise 4.99.1 (119): Real sequence space in the product topology is metrizable. -/
#check (inferInstance : TopologicalSpace.MetrizableSpace (ℕ → ℝ))

end RealSequence

namespace UniformRealSequence

/-- Exercise 4.99.1 (136): Real sequence space with the uniform topology is metrizable. -/
instance instMetrizableSpace :
    TopologicalSpace.MetrizableSpace UniformRealSequence := by
  -- Unwrap the named topology and pull back its defining uniform metric.
  -- Local instance justification (named-topology bridge): replace the default product topology
  -- on raw sequences by the topology defining `UniformRealSequence`.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  -- Local instance justification (named-metric bridge): install the metric that generates the
  -- preceding named topology while constructing the compatible metric witness.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  let unwrap : UniformRealSequence ≃ₜ (ℕ → ℝ) :=
    { WithTopology.equiv (ℕ → ℝ) (UniformMetric.topology ℕ) with
      continuous_toFun := WithTopology.continuous_ofTopology (UniformMetric.topology ℕ)
      continuous_invFun := WithTopology.continuous_toTopology (UniformMetric.topology ℕ) }
  exact unwrap.isEmbedding.metrizableSpace

/- Exercise 4.99.1 (120): Real sequence space with the uniform topology is not connected. -/
#check UniformRealSequence.notConnected

/-- Exercise 4.99.1 (121): Real sequence space with the uniform topology is not path connected. -/
theorem notPathConnected :
    ¬ PathConnectedSpace UniformRealSequence := by
  -- Path connectedness would imply the known-false connectedness property.
  exact notPathConnectedOfNotConnected UniformRealSequence UniformRealSequence.notConnected

/-- Helper for Exercise 4.99.1: a coordinatewise affine segment with uniformly bounded
coefficients is continuous in the uniform topology. -/
private lemma continuousUniformAffineSegmentOfCoordinateBound
    (y z : UniformRealSequence) {C : ℝ}
    (hC : ∀ n, |z.ofTopology n - y.ofTopology n| ≤ C) :
    Continuous (fun t ↦ UniformRealSequence.ofSequence
      (fun n ↦ y.ofTopology n + t * (z.ofTopology n - y.ofTopology n))) := by
  -- Bound the raw uniform distance by one Lipschitz constant, then wrap the codomain once.
  -- Local instance justification (named-topology bridge): the affine segment is estimated in the
  -- raw topology that defines the uniform wrapper.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  -- Local instance justification (named-metric bridge): Lipschitz continuity uses the explicit
  -- uniform metric generating that topology.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hcoeff : ∀ n, |z.ofTopology n - y.ofTopology n| ≤ K := by
    intro n
    exact (hC n).trans (le_max_left _ _)
  let rawSegment : ℝ → ℕ → ℝ :=
    fun t n ↦ y.ofTopology n + t * (z.ofTopology n - y.ofTopology n)
  have hLipschitz : LipschitzWith K rawSegment := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [UniformMetric.dist_eq]
    refine ciSup_le fun n ↦ ?_
    calc
      min (dist (rawSegment s n) (rawSegment t n)) 1 ≤
          dist (rawSegment s n) (rawSegment t n) := min_le_left _ _
      _ = |z.ofTopology n - y.ofTopology n| * dist s t := by
        rw [Real.dist_eq, Real.dist_eq, ← abs_mul]
        dsimp only [rawSegment]
        congr 1
        ring
      _ ≤ K * dist s t :=
        mul_le_mul_of_nonneg_right (hcoeff n) dist_nonneg
      _ = (K : ℝ) * dist s t := rfl
  have hraw : Continuous rawSegment := hLipschitz.continuous
  have hsegment :
      (fun t ↦ UniformRealSequence.ofSequence
        (fun n ↦ y.ofTopology n + t * (z.ofTopology n - y.ofTopology n))) =
        WithTopology.toTopology (UniformMetric.topology ℕ) ∘ rawSegment := by
    funext t
    exact UniformRealSequence.ofSequence_eq_toTopology _
  rw [hsegment]
  exact (WithTopology.continuous_toTopology (UniformMetric.topology ℕ)).comp hraw

/-- Helper for Exercise 4.99.1: every uniform ball of positive radius at most one is path
connected. -/
private lemma isPathConnectedUniformBall (x : UniformRealSequence) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsPathConnected {y : UniformRealSequence |
      (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < ε} := by
  -- Join two points by their coordinatewise affine segment and control it by the larger radius.
  rw [isPathConnected_iff]
  have hxBall : x ∈ {y : UniformRealSequence |
      (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < ε} := by
    simpa using hε
  refine ⟨⟨x, hxBall⟩, ?_⟩
  intro y hy z hz
  have hy1 : (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < 1 :=
    hy.trans_le hε1
  have hz1 : (UniformMetric.metricSpace ℕ).dist z.ofTopology x.ofTopology < 1 :=
    hz.trans_le hε1
  have hyCoord (n : ℕ) : dist (y.ofTopology n) (x.ofTopology n) ≤
      (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology :=
    UniformRealSequence.coordinateDistance_le_uniformDistance hy1 n
  have hzCoord (n : ℕ) : dist (z.ofTopology n) (x.ofTopology n) ≤
      (UniformMetric.metricSpace ℕ).dist z.ofTopology x.ofTopology :=
    UniformRealSequence.coordinateDistance_le_uniformDistance hz1 n
  have hyzBound : ∀ n, |z.ofTopology n - y.ofTopology n| ≤
      (UniformMetric.metricSpace ℕ).dist z.ofTopology x.ofTopology +
        (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology := by
    intro n
    rw [← Real.dist_eq]
    have hyCoord' : dist (x.ofTopology n) (y.ofTopology n) ≤
        (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology := by
      simpa only [dist_comm] using hyCoord n
    exact (dist_triangle _ (x.ofTopology n) _).trans
      (add_le_add (hzCoord n) hyCoord')
  let f : ℝ → UniformRealSequence := fun t ↦ UniformRealSequence.ofSequence
    (fun n ↦ y.ofTopology n + t * (z.ofTopology n - y.ofTopology n))
  have hf : Continuous f :=
    continuousUniformAffineSegmentOfCoordinateBound y z hyzBound
  refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
  · ext n
    dsimp only [f]
    simp only [UniformRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology, zero_mul, add_zero]
  · ext n
    dsimp only [f]
    simp only [UniformRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology, one_mul, add_sub_cancel]
  · rintro _ ⟨t, ht, rfl⟩
    let r : ℝ := max
      ((UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology)
      ((UniformMetric.metricSpace ℕ).dist z.ofTopology x.ofTopology)
    have hrε : r < ε := max_lt hy hz
    have hcoord : ∀ n, dist ((f t).ofTopology n) (x.ofTopology n) ≤ r := by
      intro n
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      calc
        dist ((f t).ofTopology n) (x.ofTopology n) =
            |(1 - t) * (y.ofTopology n - x.ofTopology n) +
              t * (z.ofTopology n - x.ofTopology n)| := by
          rw [Real.dist_eq]
          dsimp only [f]
          rw [UniformRealSequence.ofSequence_eq_toTopology,
            WithTopology.ofTopology_toTopology]
          congr 1
          ring
        _ ≤ |(1 - t) * (y.ofTopology n - x.ofTopology n)| +
            |t * (z.ofTopology n - x.ofTopology n)| := abs_add_le _ _
        _ = (1 - t) * dist (y.ofTopology n) (x.ofTopology n) +
            t * dist (z.ofTopology n) (x.ofTopology n) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0,
            Real.dist_eq, Real.dist_eq]
        _ ≤ (1 - t) *
              (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology +
            t * (UniformMetric.metricSpace ℕ).dist z.ofTopology x.ofTopology :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hyCoord n) (sub_nonneg.mpr ht1))
            (mul_le_mul_of_nonneg_left (hzCoord n) ht0)
        _ ≤ r := by
          dsimp only [r]
          have hyr : (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology ≤ r :=
            le_max_left _ _
          have hzr : (UniformMetric.metricSpace ℕ).dist z.ofTopology x.ofTopology ≤ r :=
            le_max_right _ _
          nlinarith
    calc
      (UniformMetric.metricSpace ℕ).dist (f t).ofTopology x.ofTopology =
          ⨆ n, min (dist ((f t).ofTopology n) (x.ofTopology n)) 1 :=
        UniformMetric.dist_eq _ _
      _ ≤ r := ciSup_le fun n ↦ (min_le_left _ _).trans (hcoord n)
      _ < ε := hrε

/-- Helper for Exercise 4.99.1: every neighborhood in the named uniform topology contains an
explicit positive-radius uniform ball. -/
private lemma existsUniformBallSubsetOfNhd (x : UniformRealSequence)
    {U : Set UniformRealSequence} (hU : U ∈ nhds x) :
    ∃ ε : ℝ, 0 < ε ∧
      {y : UniformRealSequence |
        (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < ε} ⊆ U := by
  -- Pull the neighborhood to the raw metric space and use its metric-ball basis.
  -- Local instance justification (named-topology bridge): unwrap the neighborhood into the
  -- topology used in the definition of `UniformRealSequence`.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  -- Local instance justification (named-metric bridge): use the generating metric's ball basis.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hUraw :
      WithTopology.toTopology (UniformMetric.topology ℕ) ⁻¹' U ∈ nhds x.ofTopology :=
    (WithTopology.continuous_toTopology (UniformMetric.topology ℕ)).tendsto x.ofTopology hU
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hUraw
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hyRaw : y.ofTopology ∈ Metric.ball x.ofTopology ε := hy
  have hyU := hball hyRaw
  simpa only [Set.mem_preimage, WithTopology.toTopology_ofTopology] using hyU

/-- Helper for Exercise 4.99.1: the named uniform sequence space is locally path connected. -/
private lemma uniformRealSequenceLocallyPathConnectedSpace :
    LocallyPathConnectedSpace UniformRealSequence := by
  -- Shrink each neighborhood to a small path-connected metric ball.
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨ε, hε, hballU⟩ := existsUniformBallSubsetOfNhd x hU
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hhalfOne : (1 / 2 : ℝ) ≤ 1 := by
    norm_num
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans hhalfOne
  let B : Set UniformRealSequence :=
    {y | (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < δ}
  have hBopen : IsOpen B := by
    rw [WithTopology.isOpen_iff]
    exact UniformRealSequence.uniformBall_isOpen x.ofTopology δ
  have hxB : x ∈ B := by
    dsimp only [B]
    simpa using hδ
  have hBU : B ⊆ U := by
    intro y hy
    apply hballU
    change (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < δ at hy
    have hδε : δ ≤ ε := by
      dsimp only [δ]
      exact min_le_left _ _
    exact hy.trans_le hδε
  refine ⟨B, ?_, isPathConnectedUniformBall x hδ hδ1, hBU⟩
  exact hBopen.mem_nhds hxB

/-- Exercise 4.99.1 (122): Real sequence space with the uniform topology is locally connected. -/
instance instLocallyConnectedSpace :
    LocallyConnectedSpace UniformRealSequence := by
  -- Local instance justification (declaration-order bridge): the canonical path-connected
  -- structure is established by the helper immediately before its public instance below.
  letI : LocallyPathConnectedSpace UniformRealSequence :=
    uniformRealSequenceLocallyPathConnectedSpace
  infer_instance

/-- Exercise 4.99.1 (123): Real sequence space with the uniform topology is locally path
connected. -/
instance instLocallyPathConnectedSpace :
    LocallyPathConnectedSpace UniformRealSequence := by
  -- Reuse the small-ball basis constructed above.
  exact uniformRealSequenceLocallyPathConnectedSpace

/-- Helper for Exercise 4.99.1: every positive-radius uniform ball about zero contains an
infinite closed discrete family of coordinate spikes. -/
private lemma existsInfiniteClosedDiscreteSubsetUniformBall {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set UniformRealSequence,
      A ⊆ {y : UniformRealSequence |
        (UniformMetric.metricSpace ℕ).dist y.ofTopology
          (UniformRealSequence.ofSequence 0).ofTopology < ε} ∧
        A.Infinite ∧ IsClosed A ∧ IsDiscrete A := by
  -- Choose a common spike height small enough to remain inside the prescribed ball.
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hhalfOne : (1 / 2 : ℝ) ≤ 1 := by
    norm_num
  have hhalfEps : ε / 2 < ε := by
    linarith
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans hhalfOne
  have hδε : δ < ε := (min_le_left _ _).trans_lt hhalfEps
  -- Local instance justification (named-topology bridge): construct the spike embedding in the
  -- raw topology defining the uniform wrapper.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  -- Local instance justification (named-metric bridge): uniform separation is measured by the
  -- explicit generating metric.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  let spike : ℕ → ℕ → ℝ := fun n k ↦ if k = n then δ else 0
  have hbounded (p q : ℕ → ℝ) :
      BddAbove (Set.range fun k ↦ min (dist (p k) (q k)) 1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact min_le_right _ _
  have hspikeZero (n : ℕ) :
      (UniformMetric.metricSpace ℕ).dist (spike n) 0 = δ := by
    rw [UniformMetric.dist_eq]
    apply le_antisymm
    · refine ciSup_le fun k ↦ ?_
      by_cases hk : k = n
      · simp only [spike, hk, ↓reduceIte, Pi.zero_apply, Real.dist_eq, sub_zero,
          abs_of_pos hδ, min_eq_left hδ1]
        exact le_rfl
      · simp only [spike, hk, ↓reduceIte, Pi.zero_apply, dist_self,
          min_eq_left zero_le_one]
        exact hδ.le
    · calc
        δ = min (dist (spike n n) (0 : ℝ)) 1 := by
          simp only [spike, ↓reduceIte, Real.dist_eq, sub_zero,
            abs_of_pos hδ, min_eq_left hδ1]
        _ ≤ ⨆ k, min (dist (spike n k) (0 : ℝ)) 1 :=
          le_ciSup (hbounded (spike n) 0) n
  have hpairwise : Pairwise fun n m : ℕ ↦
      δ ≤ (UniformMetric.metricSpace ℕ).dist (spike n) (spike m) := by
    intro n m hnm
    rw [UniformMetric.dist_eq]
    calc
      δ = min (dist (spike n n) (spike m n)) 1 := by
        simp only [spike, hnm, ↓reduceIte, Real.dist_eq, sub_zero,
          abs_of_pos hδ, min_eq_left hδ1]
      _ ≤ ⨆ k, min (dist (spike n k) (spike m k)) 1 :=
        le_ciSup (hbounded (spike n) (spike m)) n
  have hrawClosedEmbedding : Topology.IsClosedEmbedding spike :=
    Metric.isClosedEmbedding_of_pairwise_le_dist hδ hpairwise
  let wrap : (ℕ → ℝ) ≃ₜ UniformRealSequence :=
    { (WithTopology.equiv (ℕ → ℝ) (UniformMetric.topology ℕ)).symm with
      continuous_toFun := WithTopology.continuous_toTopology (UniformMetric.topology ℕ)
      continuous_invFun := WithTopology.continuous_ofTopology (UniformMetric.topology ℕ) }
  let wrappedSpike : ℕ → UniformRealSequence := fun n ↦ wrap (spike n)
  have hwrappedClosedEmbedding : Topology.IsClosedEmbedding wrappedSpike :=
    wrap.isClosedEmbedding.comp hrawClosedEmbedding
  let A : Set UniformRealSequence := Set.range wrappedSpike
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · -- Every wrapped spike has uniform distance exactly `δ` from zero.
    rintro _ ⟨n, rfl⟩
    have hwrappedApply : (wrappedSpike n).ofTopology = spike n := rfl
    change (UniformMetric.metricSpace ℕ).dist (wrappedSpike n).ofTopology
      (UniformRealSequence.ofSequence 0).ofTopology < ε
    rw [hwrappedApply, UniformRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology]
    exact (hspikeZero n).trans_lt hδε
  · -- The closed embedding is injective, so its range is infinite.
    exact Set.infinite_range_of_injective hwrappedClosedEmbedding.injective
  · exact hwrappedClosedEmbedding.isClosed_range
  · exact hwrappedClosedEmbedding.isInducing.isDiscrete_range

/-- Exercise 4.99.1 (124): Real sequence space with the uniform topology is not compact. -/
theorem notCompact :
    ¬ CompactSpace UniformRealSequence := by
  -- Compact metrizable spaces are second-countable, contradicting the uniform obstruction.
  intro hcompact
  -- Local instance justification (hypothetical class): expose compactness to metric countability.
  letI : CompactSpace UniformRealSequence := hcompact
  exact UniformRealSequence.notSecondCountable inferInstance

/-- Exercise 4.99.1 (125): Real sequence space with the uniform topology is not limit point
compact. -/
theorem notLimitPointCompact :
    ¬ LimitPointCompactSpace UniformRealSequence := by
  -- Metrizability identifies limit-point compactness with compactness.
  exact notLimitPointCompactOfMetrizableNotCompact UniformRealSequence notCompact

/-- Exercise 4.99.1 (126): Real sequence space with the uniform topology is not locally compact
Hausdorff. -/
theorem notLocallyCompactT2 :
    ¬ (LocallyCompactSpace UniformRealSequence ∧ T2Space UniformRealSequence) := by
  -- A compact neighborhood of zero would contain an infinite closed discrete spike family.
  rintro ⟨hlocal, _⟩
  -- Local instance justification (hypothetical class): obtain the alleged compact neighborhood.
  letI : LocallyCompactSpace UniformRealSequence := hlocal
  obtain ⟨K, hKcompact, hKnhds⟩ :=
    exists_compact_mem_nhds (UniformRealSequence.ofSequence 0)
  obtain ⟨ε, hε, hballK⟩ :=
    existsUniformBallSubsetOfNhd (UniformRealSequence.ofSequence 0) hKnhds
  obtain ⟨A, hAball, hAinfinite, hAclosed, hAdiscrete⟩ :=
    existsInfiniteClosedDiscreteSubsetUniformBall hε
  have hAK : A ⊆ K := hAball.trans hballK
  have hAcompact : IsCompact A :=
    IsCompact.of_isClosed_subset hKcompact hAclosed hAK
  exact hAinfinite (hAcompact.finite hAdiscrete)

/-- Exercise 4.99.1 (127): Real sequence space with the uniform topology is Hausdorff. -/
instance instT2Space : T2Space UniformRealSequence := by
  -- A compatible metric supplies Hausdorff separation.
  infer_instance

/-- Exercise 4.99.1 (128): Real sequence space with the uniform topology is regular. -/
instance instT3Space : T3Space UniformRealSequence := by
  -- A compatible metric supplies regular Hausdorff separation.
  infer_instance

/-- Exercise 4.99.1 (129): Real sequence space with the uniform topology is completely regular. -/
instance instT35Space : T35Space UniformRealSequence := by
  -- A compatible metric supplies complete regularity.
  infer_instance

/-- Exercise 4.99.1 (130): Real sequence space with the uniform topology is normal. -/
instance instT4Space : T4Space UniformRealSequence := by
  -- Metric spaces are normal Hausdorff spaces.
  infer_instance

/- Exercise 4.99.1 (131): Real sequence space with the uniform topology is first-countable. -/
#check _root_.UniformRealSequence.instFirstCountableTopology

/- Exercise 4.99.1 (132): Real sequence space with the uniform topology is not second-countable. -/
#check _root_.UniformRealSequence.notSecondCountable

/-- Exercise 4.99.1 (133): Real sequence space with the uniform topology is not Lindelöf. -/
theorem notLindelof :
    ¬ LindelofSpace UniformRealSequence := by
  -- A Lindelöf metrizable space would be second-countable.
  intro hlindelof
  -- Local instance justification (hypothetical class): expose the assumed Lindelöf structure.
  letI : LindelofSpace UniformRealSequence := hlindelof
  exact UniformRealSequence.notSecondCountable inferInstance

/-- Exercise 4.99.1 (134): Real sequence space with the uniform topology is not has a countable
dense subset. -/
theorem notSeparable :
    ¬ TopologicalSpace.SeparableSpace UniformRealSequence := by
  -- A separable pseudometrizable space has a countable basis for its compatible uniformity.
  intro hseparable
  -- Local instance justification (hypothetical class): expose the assumed separability.
  letI : TopologicalSpace.SeparableSpace UniformRealSequence := hseparable
  -- Local instance justification (pseudometric-uniformity bridge): separability controls the
  -- compatible uniformity canonically reconstructed from the proved metrizable topology.
  letI : UniformSpace UniformRealSequence :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity UniformRealSequence
  have hUniformity : (uniformity UniformRealSequence).IsCountablyGenerated :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated
      UniformRealSequence
  exact UniformRealSequence.notSecondCountable
    (@UniformSpace.secondCountable_of_separable UniformRealSequence inferInstance
      hUniformity inferInstance)

/-- Exercise 4.99.1 (135): Real sequence space with the uniform topology is locally metrizable. -/
instance instLocallyMetrizableSpace :
    LocallyMetrizableSpace UniformRealSequence := by
  -- Every metrizable space is locally metrizable.
  infer_instance

end UniformRealSequence

namespace BoxRealSequence

/-- Helper for Exercise 4.99.1: the binary cube inside the real box product. -/
private def zeroOneCube : Set BoxRealSequence :=
  {x | ∀ n, x.ofTopology n = 0 ∨ x.ofTopology n = 1}

/-- Helper for Exercise 4.99.1: the binary cube is closed in the box topology. -/
private lemma zeroOneCube_isClosed : IsClosed zeroOneCube := by
  -- It is already closed in the product topology, and the box topology is finer.
  rw [WithTopology.isClosed_iff]
  let A : Set (ℕ → ℝ) := Set.pi Set.univ (fun _ ↦ ({0, 1} : Set ℝ))
  have hProduct : @IsClosed (ℕ → ℝ) Pi.topologicalSpace A := by
    exact isClosed_set_pi fun _ _ ↦ isClosed_singleton.union isClosed_singleton
  have hProductOpen : @IsOpen (ℕ → ℝ) Pi.topologicalSpace Aᶜ :=
    hProduct.isOpen_compl
  have hBoxOpen : @IsOpen (ℕ → ℝ)
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) Aᶜ :=
    Pi.box_le_product _ hProductOpen
  have hBox : @IsClosed (ℕ → ℝ)
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) A := by
    -- Local instance justification (box-topology bridge): interpret complement-closedness using
    -- the explicit box topology appearing in the stated type.
    letI : TopologicalSpace (ℕ → ℝ) :=
      Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
    exact isOpen_compl_iff.mp hBoxOpen
  convert hBox using 1
  ext x
  simp only [zeroOneCube, A, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, true_implies, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Helper for Exercise 4.99.1: the binary cube is discrete in the box topology. -/
private lemma zeroOneCube_isDiscrete : IsDiscrete zeroOneCube := by
  -- A full coordinate box excludes the opposite binary value at every coordinate.
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  let C : ℕ → Set ℝ := fun n ↦
    if x.ofTopology n = 0 then ({1} : Set ℝ)ᶜ else ({0} : Set ℝ)ᶜ
  let U : Set BoxRealSequence :=
    {y | y.ofTopology ∈ Set.pi Set.univ C}
  refine ⟨U, ?_, ?_⟩
  · rw [WithTopology.isOpen_iff]
    change @IsOpen (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      (Set.pi Set.univ C)
    apply Pi.isOpen_box
    intro n
    dsimp only [C]
    split_ifs <;> exact isClosed_singleton.isOpen_compl
  · ext y
    constructor
    · rintro ⟨hyU, hyCube⟩
      have hraw : y.ofTopology = x.ofTopology := by
        funext n
        have hyUn := hyU n (Set.mem_univ n)
        dsimp only [C] at hyUn
        rcases hx n with hxn | hxn
        · rw [if_pos hxn] at hyUn
          rcases hyCube n with hyn | hyn
          · exact hyn.trans hxn.symm
          · exact (hyUn hyn).elim
        · have hxn0 : x.ofTopology n ≠ 0 := by
            linarith
          rw [if_neg hxn0] at hyUn
          rcases hyCube n with hyn | hyn
          · exact (hyUn hyn).elim
          · exact hyn.trans hxn.symm
      have hyx : y = x := WithTopology.ofTopology_injective _ hraw
      simp [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      refine ⟨?_, hx⟩
      intro n _
      dsimp only [C]
      rcases hx n with hxn | hxn
      · rw [if_pos hxn]
        simp [hxn]
      · have hxn0 : x.ofTopology n ≠ 0 := by
          linarith
        rw [if_neg hxn0]
        simp [hxn]

/-- Helper for Exercise 4.99.1: a uniform zero-one sequence remains zero-one-valued after
rewrapping it with the box topology. -/
private lemma uniformZeroOneSequenceMemBoxCube
    (x : UniformRealSequence.zeroOneSequences) :
    BoxRealSequence.ofSequence x.1.ofTopology ∈ zeroOneCube := by
  -- The topology wrapper changes while every coordinate value stays fixed.
  intro n
  have hx : ∀ m, x.1.ofTopology m = 0 ∨ x.1.ofTopology m = 1 :=
    (UniformRealSequence.mem_zeroOneSequences x.1).mp x.property
  simpa only [BoxRealSequence.ofSequence_eq_toTopology,
    WithTopology.ofTopology_toTopology] using hx n

/-- Helper for Exercise 4.99.1: rewrap a uniform zero-one sequence as a point of the box
binary cube. -/
private def uniformZeroOneSequenceToBoxCube
    (x : UniformRealSequence.zeroOneSequences) : zeroOneCube :=
  ⟨BoxRealSequence.ofSequence x.1.ofTopology, uniformZeroOneSequenceMemBoxCube x⟩

/-- Helper for Exercise 4.99.1: the binary cube is uncountable. -/
private lemma zeroOneCube_notCountable : ¬ zeroOneCube.Countable := by
  -- Rewrap the already-known uncountable uniform binary cube without changing coordinates.
  intro hcountable
  have hrewrap : Function.Injective uniformZeroOneSequenceToBoxCube := by
    intro x y hxy
    apply Subtype.ext
    apply WithTopology.ofTopology_injective _
    have hval := congrArg (fun z : zeroOneCube ↦ z.1.ofTopology) hxy
    simpa only [uniformZeroOneSequenceToBoxCube,
      BoxRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology] using hval
  -- Local instance justification (countability transport): install the assumed countability only
  -- to pull it back along the explicit injection `rewrap`.
  letI : Countable zeroOneCube := hcountable.to_subtype
  have hUniformCountable : Countable UniformRealSequence.zeroOneSequences :=
    hrewrap.countable
  exact UniformRealSequence.zeroOneSequences_uncountable
    (Set.countable_coe_iff.mp hUniformCountable)

/-- Helper for Exercise 4.99.1: infinite binary sequences form an uncountable type. -/
private lemma binarySequences_uncountable : Uncountable (ℕ → Bool) := by
  -- A proposed enumeration misses the pointwise Boolean complement of its diagonal.
  rw [uncountable_iff_forall_not_surjective]
  intro f hf
  let diagonal : ℕ → Bool := fun n ↦ !(f n n)
  obtain ⟨n, hn⟩ := hf diagonal
  have h := congrFun hn n
  simp [diagonal] at h

/-- Helper for Exercise 4.99.1: binary sequences index pairwise disjoint nonempty open boxes. -/
private lemma binaryOpenBoxes :
    ∃ O : (ℕ → Bool) → Set BoxRealSequence,
      (∀ c, IsOpen (O c) ∧ (O c).Nonempty) ∧
        Pairwise (Function.onFun Disjoint O) := by
  -- Separate the values `0` and `1` by the fixed cut at `1 / 2` in every coordinate.
  let I : Bool → Set ℝ := fun b ↦ if b then Set.Ioi (1 / 2 : ℝ) else Set.Iio (1 / 2 : ℝ)
  let O : (ℕ → Bool) → Set BoxRealSequence := fun c ↦
    {x | x.ofTopology ∈ Set.pi Set.univ (fun n ↦ I (c n))}
  refine ⟨O, ?_, ?_⟩
  · intro c
    constructor
    · rw [WithTopology.isOpen_iff]
      change @IsOpen (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
        (Set.pi Set.univ (fun n ↦ I (c n)))
      apply Pi.isOpen_box
      intro n
      dsimp only [I]
      split_ifs
      · exact isOpen_Ioi
      · exact isOpen_Iio
    · let point : ℕ → ℝ := fun n ↦ if c n then 1 else 0
      refine ⟨BoxRealSequence.ofSequence point, ?_⟩
      intro n _
      dsimp only [O, point, I]
      rw [BoxRealSequence.ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology]
      split_ifs <;> norm_num
  · intro c d hcd
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro x hxc hxd
    have hcoord : ∃ n, c n ≠ d n := by
      by_contra h
      push Not at h
      exact hcd (funext h)
    obtain ⟨n, hn⟩ := hcoord
    have hcn := hxc n (Set.mem_univ n)
    have hdn := hxd n (Set.mem_univ n)
    cases hcnValue : c n with
    | false =>
        cases hdnValue : d n with
        | false => exact (hn (hcnValue.trans hdnValue.symm)).elim
        | true =>
            simp only [I, hcnValue, hdnValue, Bool.false_eq_true, Set.mem_Iio,
              Set.mem_Ioi, ↓reduceIte] at hcn hdn
            linarith
    | true =>
        cases hdnValue : d n with
        | false =>
            simp only [I, hcnValue, hdnValue, Bool.false_eq_true, Set.mem_Iio,
              Set.mem_Ioi, ↓reduceIte] at hcn hdn
            linarith
        | true => exact (hn (hcnValue.trans hdnValue.symm)).elim

/-- Helper for Exercise 4.99.1: every coordinate box about zero contains an uncountable closed
discrete affine copy of the binary cube. -/
private lemma existsClosedDiscreteUncountableSubsetOfBox
    (W : ℕ → Set ℝ) (hWopen : ∀ n, IsOpen (W n)) (hWzero : ∀ n, 0 ∈ W n) :
    ∃ A : Set BoxRealSequence,
      A ⊆ WithTopology.ofTopology ⁻¹' Set.pi Set.univ W ∧
        IsClosed A ∧ IsDiscrete A ∧ ¬ A.Countable := by
  -- Choose a nonzero scale in each coordinate neighborhood.
  have hWnhds : ∀ n, W n ∈ nhds (0 : ℝ) := fun n ↦
    (hWopen n).mem_nhds (hWzero n)
  choose ε hε hεW using fun n ↦ Metric.mem_nhds_iff.mp (hWnhds n)
  let a : ℕ → ℝ := fun n ↦ ε n / 2
  have ha : ∀ n, a n ≠ 0 := by
    intro n
    dsimp only [a]
    linarith [hε n]
  have haW : ∀ n, a n ∈ W n := by
    intro n
    apply hεW n
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp only [a]
    rw [sub_zero, abs_of_pos]
    · linarith [hε n]
    · linarith [hε n]
  let f : BoxRealSequence → BoxRealSequence :=
    Pi.boxMap fun n t ↦ a n * t + (0 : ℝ)
  have hf : IsHomeomorph f := by
    dsimp only [f]
    simpa only [Pi.zero_apply] using
      (isHomeomorph_realSequenceAffineMap_box_of_ne_zero a 0 ha)
  let A : Set BoxRealSequence := f '' zeroOneCube
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · -- The affine copy uses only the selected values `0` and `a n`.
    rintro _ ⟨x, hx, rfl⟩
    intro n _
    rcases hx n with hxn | hxn
    · simpa only [f, Pi.boxMap_apply, Pi.map_apply, hxn, mul_zero, add_zero] using hWzero n
    · simpa only [f, Pi.boxMap_apply, Pi.map_apply, hxn, mul_one, add_zero] using haW n
  · -- A homeomorphism carries the closed cube to a closed set.
    exact hf.isClosedMap zeroOneCube zeroOneCube_isClosed
  · -- Its inducing property also carries discreteness to the image.
    exact zeroOneCube_isDiscrete.image hf.isInducing
  · -- Injectivity transports any alleged countability back to the original cube.
    intro hAcountable
    apply zeroOneCube_notCountable
    apply Set.countable_of_injective_of_countable_image hf.injective.injOn
    simpa only [A] using hAcountable

/-- Exercise 4.99.1 (137): Real sequence space with the box topology is not connected. -/
theorem notConnected :
    ¬ ConnectedSpace BoxRealSequence := by
  -- The bounded-sequence clopen separation gives the required disconnection.
  exact BoxRealSequence.not_connected

/-- Exercise 4.99.1 (138): Real sequence space with the box topology is not path connected. -/
theorem notPathConnected :
    ¬ PathConnectedSpace BoxRealSequence := by
  -- Path connectedness would imply connectedness.
  exact notPathConnectedOfNotConnected BoxRealSequence notConnected

/-- Exercise 4.99.1 (139): Real sequence space with the box topology is not locally connected. -/
theorem notLocallyConnected :
    ¬ LocallyConnectedSpace BoxRealSequence := by
  -- Any connected neighborhood of zero contains a sequence differing from zero everywhere.
  intro hlocal
  -- Local instance justification (hypothetical class): use the assumed connected-neighborhood
  -- basis.
  letI : LocallyConnectedSpace BoxRealSequence := hlocal
  obtain ⟨V, hVnhds, hVpreconnected, _⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp inferInstance
      (BoxRealSequence.ofSequence 0) Set.univ Filter.univ_mem
  obtain ⟨W, hWopen, hWzero, hWV⟩ :=
    BoxRealSequence.exists_box_subset_nhds_zero hVnhds
  have hWnhds : ∀ n, W n ∈ nhds (0 : ℝ) := fun n ↦
    (hWopen n).mem_nhds (hWzero n)
  choose ε hε hεW using fun n ↦ Metric.mem_nhds_iff.mp (hWnhds n)
  let yRaw : ℕ → ℝ := fun n ↦ ε n / 2
  let y : BoxRealSequence := BoxRealSequence.ofSequence yRaw
  have hyBox : y ∈ WithTopology.ofTopology ⁻¹' Set.pi Set.univ W := by
    intro n _
    apply hεW n
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp only [y, yRaw]
    rw [BoxRealSequence.ofSequence_eq_toTopology, WithTopology.ofTopology_toTopology,
      sub_zero, abs_of_pos]
    · linarith [hε n]
    · linarith [hε n]
  have hyV : y ∈ V := hWV hyBox
  have hzeroV : BoxRealSequence.ofSequence 0 ∈ V := mem_of_mem_nhds hVnhds
  have hyComponent : y ∈ connectedComponent (BoxRealSequence.ofSequence 0) :=
    hVpreconnected.subset_connectedComponent hzeroV hyV
  have heventual :=
    (boxRealSequences_sameConnectedComponent_iff (BoxRealSequence.ofSequence 0) y).mp
      hyComponent
  rw [Filter.eventually_atTop] at heventual
  obtain ⟨N, hN⟩ := heventual
  have hzero := hN N le_rfl
  dsimp only [y, yRaw] at hzero
  rw [BoxRealSequence.ofSequence_eq_toTopology, BoxRealSequence.ofSequence_eq_toTopology,
    WithTopology.ofTopology_toTopology, WithTopology.ofTopology_toTopology] at hzero
  simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, neg_eq_zero] at hzero
  linarith [hε N]

/-- Exercise 4.99.1 (140): Real sequence space with the box topology is not locally path
connected. -/
theorem notLocallyPathConnected :
    ¬ LocallyPathConnectedSpace BoxRealSequence := by
  -- Local path connectedness would imply the already excluded local connectedness.
  exact notLocallyPathConnectedOfNotLocallyConnected BoxRealSequence notLocallyConnected

/-- Exercise 4.99.1 (141): Real sequence space with the box topology is not compact. -/
theorem notCompact :
    ¬ CompactSpace BoxRealSequence := by
  -- In a compact ambient space the closed discrete binary cube would be finite.
  intro hcompact
  -- Local instance justification (hypothetical class): expose the assumed compactness.
  letI : CompactSpace BoxRealSequence := hcompact
  have hfinite : zeroOneCube.Finite :=
    zeroOneCube_isClosed.isCompact.finite zeroOneCube_isDiscrete
  exact zeroOneCube_notCountable hfinite.countable

/-- Exercise 4.99.1 (142): Real sequence space with the box topology is not limit point compact. -/
theorem notLimitPointCompact :
    ¬ LimitPointCompactSpace BoxRealSequence := by
  -- The infinite closed discrete binary cube cannot have the required accumulation point.
  intro hlimit
  have hinfinite : zeroOneCube.Infinite := by
    intro hfinite
    exact zeroOneCube_notCountable hfinite.countable
  obtain ⟨x, hx⟩ := hlimit.exists_accPt zeroOneCube hinfinite
  exact UnitIntervalUniformPower.not_accPt_principal_of_isClosed_isDiscrete
    zeroOneCube_isClosed zeroOneCube_isDiscrete x hx

/-- Exercise 4.99.1 (143): Real sequence space with the box topology is not locally compact
Hausdorff. -/
theorem notLocallyCompactT2 :
    ¬ (LocallyCompactSpace BoxRealSequence ∧ T2Space BoxRealSequence) := by
  -- A compact neighborhood of zero would contain a compact affine binary cube.
  rintro ⟨hlocal, _⟩
  -- Local instance justification (hypothetical class): obtain the alleged compact neighborhood.
  letI : LocallyCompactSpace BoxRealSequence := hlocal
  obtain ⟨K, hKcompact, hKnhds⟩ :=
    exists_compact_mem_nhds (BoxRealSequence.ofSequence 0)
  obtain ⟨W, hWopen, hWzero, hWK⟩ :=
    BoxRealSequence.exists_box_subset_nhds_zero hKnhds
  obtain ⟨A, hAbox, hAclosed, hAdiscrete, hAuncountable⟩ :=
    existsClosedDiscreteUncountableSubsetOfBox W hWopen hWzero
  have hAK : A ⊆ K := hAbox.trans hWK
  have hAcompact : IsCompact A :=
    IsCompact.of_isClosed_subset hKcompact hAclosed hAK
  exact hAuncountable (hAcompact.finite hAdiscrete).countable

/- Exercise 4.99.1 (144): Real sequence space with the box topology is Hausdorff. -/
#check (inferInstance : T2Space BoxRealSequence)

/- Exercise 4.99.1 (145): Real sequence space with the box topology is regular. -/
#check (inferInstance : T3Space BoxRealSequence)

/- Exercise 4.99.1 (146): Real sequence space with the box topology is completely regular. -/
#check (inferInstance : T35Space BoxRealSequence)

/- Exercise 4.99.1 (147): Whether real sequence space with the box topology is normal is left
unresolved by the results assumed in the text. -/
#check T4Space BoxRealSequence

/-- Exercise 4.99.1 (148): Real sequence space with the box topology is not first-countable. -/
theorem notFirstCountable :
    ¬ FirstCountableTopology BoxRealSequence := by
  -- Use the diagonal-box obstruction to a countable neighborhood basis.
  exact boxRealSequences_not_firstCountable

/-- Exercise 4.99.1 (149): Real sequence space with the box topology is not second-countable. -/
theorem notSecondCountable :
    ¬ SecondCountableTopology BoxRealSequence := by
  -- Second countability would imply first countability.
  intro hsecond
  -- Local instance justification (hypothetical class): expose the assumed countable basis.
  letI : SecondCountableTopology BoxRealSequence := hsecond
  exact notFirstCountable inferInstance

/-- Exercise 4.99.1 (150): Real sequence space with the box topology is not Lindelöf. -/
theorem notLindelof :
    ¬ LindelofSpace BoxRealSequence := by
  -- A closed discrete subspace of a Lindelöf space is countable.
  intro hlindelof
  -- Local instance justification (hypothetical class): expose the assumed Lindelöf structure.
  letI : LindelofSpace BoxRealSequence := hlindelof
  exact zeroOneCube_notCountable
    (zeroOneCube_isClosed.isLindelof.countable_of_isDiscrete zeroOneCube_isDiscrete)

/-- Exercise 4.99.1 (151): Real sequence space with the box topology is not has a countable
dense subset. -/
theorem notSeparable :
    ¬ TopologicalSpace.SeparableSpace BoxRealSequence := by
  -- A countable dense set cannot meet an uncountable pairwise-disjoint family of open boxes.
  intro hseparable
  -- Local instance justification (hypothetical class): expose the assumed dense countable set.
  letI : TopologicalSpace.SeparableSpace BoxRealSequence := hseparable
  obtain ⟨O, hO, hdisjoint⟩ := binaryOpenBoxes
  have hcountable : Countable (ℕ → Bool) :=
    hdisjoint.countable_of_isOpen_disjoint (fun c ↦ (hO c).1) (fun c ↦ (hO c).2)
  exact binarySequences_uncountable.not_countable hcountable

/-- Exercise 4.99.1 (152): Real sequence space with the box topology is not locally metrizable. -/
theorem notLocallyMetrizable :
    ¬ LocallyMetrizableSpace BoxRealSequence := by
  -- Local metrizability would imply first countability.
  exact notLocallyMetrizableOfNotFirstCountable BoxRealSequence notFirstCountable

/-- Exercise 4.99.1 (153): Real sequence space with the box topology is not metrizable. -/
theorem notMetrizable :
    ¬ TopologicalSpace.MetrizableSpace BoxRealSequence := by
  -- Metrizability would imply first countability.
  exact notMetrizableOfNotFirstCountable BoxRealSequence notFirstCountable

end BoxRealSequence

namespace UnitIntervalRealPower

/- Exercise 4.99.1 (154): The product of real lines indexed by the unit interval is connected. -/
#check (inferInstance : ConnectedSpace (unitInterval → ℝ))

/- Exercise 4.99.1 (155): The product of real lines indexed by the unit interval is path
connected. -/
#check (inferInstance : PathConnectedSpace (unitInterval → ℝ))

/- Exercise 4.99.1 (156): The product of real lines indexed by the unit interval is locally
connected. -/
#check (inferInstance : LocallyConnectedSpace (unitInterval → ℝ))

/- Exercise 4.99.1 (157): The product of real lines indexed by the unit interval is locally
path connected. -/
#check (inferInstance : LocallyPathConnectedSpace (unitInterval → ℝ))

/-- Exercise 4.99.1 (158): The product of real lines indexed by the unit interval is not compact. -/
theorem notCompact : ¬ (CompactSpace (unitInterval → ℝ)) := by
  -- A coordinate projection maps continuously onto the noncompact real line.
  exact realPowerNotCompact unitInterval

/-- Exercise 4.99.1 (159): The product of real lines indexed by the unit interval is not limit
point compact. -/
theorem notLimitPointCompact :
    ¬ (LimitPointCompactSpace (unitInterval → ℝ)) := by
  -- Restrict to countably many coordinates and descend countable compactness.
  -- Local instance justification (index infinitude): the nondegenerate real interval is infinite.
  letI : Infinite unitInterval := Set.Icc.infinite zero_lt_one
  exact realPowerNotLimitPointCompact unitInterval

/-- Exercise 4.99.1 (160): The product of real lines indexed by the unit interval is not locally
compact Hausdorff. -/
theorem notLocallyCompactT2 :
    ¬ ((LocallyCompactSpace (unitInterval → ℝ)) ∧ (T2Space (unitInterval → ℝ))) := by
  -- Local compactness implies weak local compactness, excluded for every infinite real power.
  rintro ⟨hlocal, _⟩
  -- Local instance justification (hypothetical class): expose the assumed local compactness.
  letI : LocallyCompactSpace (unitInterval → ℝ) := hlocal
  -- Local instance justification (index infinitude): the nondegenerate real interval is infinite.
  letI : Infinite unitInterval := Set.Icc.infinite zero_lt_one
  exact realPowerNotWeaklyLocallyCompact unitInterval inferInstance

/- Exercise 4.99.1 (161): The product of real lines indexed by the unit interval is Hausdorff. -/
#check (inferInstance : T2Space (unitInterval → ℝ))

/- Exercise 4.99.1 (162): The product of real lines indexed by the unit interval is regular. -/
#check (inferInstance : T3Space (unitInterval → ℝ))

/- Exercise 4.99.1 (163): The product of real lines indexed by the unit interval is completely
regular. -/
#check (inferInstance : T35Space (unitInterval → ℝ))

/-- Exercise 4.99.1 (164): The product of real lines indexed by the unit interval is not normal. -/
theorem notT4Space : ¬ (T4Space (unitInterval → ℝ)) := by
  -- The uncountable real power fails normal Hausdorff separation.
  have hunitUncountable : Uncountable unitInterval := by
    rw [uncountable_iff_not_countable]
    intro hcountable
    have hinterval : (Set.Icc (0 : ℝ) 1).Countable :=
      Set.countable_coe_iff.mp hcountable
    exact (not_le_of_gt zero_lt_one) (Cardinal.Real.Icc_countable_iff.mp hinterval)
  -- Local instance justification (index cardinality): the interval-countability theorem proves
  -- the exact uncountability instance required by `realPower_notT4`.
  letI : Uncountable unitInterval := hunitUncountable
  exact realPower_notT4

/-- Exercise 4.99.1 (165): The product of real lines indexed by the unit interval is not
first-countable. -/
theorem notFirstCountable :
    ¬ (FirstCountableTopology (unitInterval → ℝ)) := by
  -- A first-countable real product would have only countably many coordinates.
  intro hfirst
  -- Local instance justification (hypothetical class): expose the assumed countable local bases.
  letI : FirstCountableTopology (unitInterval → ℝ) := hfirst
  have hcountable : Countable unitInterval :=
    Pi.countable_of_firstCountable_real_pi unitInterval
  have hinterval : (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp hcountable
  exact (not_le_of_gt zero_lt_one) (Cardinal.Real.Icc_countable_iff.mp hinterval)

/-- Exercise 4.99.1 (166): The product of real lines indexed by the unit interval is not
second-countable. -/
theorem notSecondCountable :
    ¬ (SecondCountableTopology (unitInterval → ℝ)) := by
  -- Second countability would imply first countability.
  intro hsecond
  -- Local instance justification (hypothetical class): expose the assumed countable basis.
  letI : SecondCountableTopology (unitInterval → ℝ) := hsecond
  exact notFirstCountable inferInstance

/-- Exercise 4.99.1 (167): The product of real lines indexed by the unit interval is not
Lindelöf. -/
theorem notLindelof : ¬ (LindelofSpace (unitInterval → ℝ)) := by
  -- A regular Lindelöf space is normal, contradicting the real-power obstruction.
  intro hlindelof
  -- Local instance justification (hypothetical class): expose the assumed Lindelöf structure.
  letI : LindelofSpace (unitInterval → ℝ) := hlindelof
  exact notT4Space inferInstance

/- Exercise 4.99.1 (168): The product of real lines indexed by the unit interval has a
countable dense subset. -/
#check (inferInstance : TopologicalSpace.SeparableSpace (unitInterval → ℝ))

/-- Exercise 4.99.1 (169): The product of real lines indexed by the unit interval is not locally
metrizable. -/
theorem notLocallyMetrizable :
    ¬ (LocallyMetrizableSpace (unitInterval → ℝ)) := by
  -- Local metrizability would imply first countability.
  exact notLocallyMetrizableOfNotFirstCountable (unitInterval → ℝ) notFirstCountable

/-- Exercise 4.99.1 (170): The product of real lines indexed by the unit interval is not
metrizable. -/
theorem notMetrizable :
    ¬ (TopologicalSpace.MetrizableSpace (unitInterval → ℝ)) := by
  -- Metrizability would imply first countability.
  exact notMetrizableOfNotFirstCountable (unitInterval → ℝ) notFirstCountable

end UnitIntervalRealPower

/-- Helper for Exercise 4.99.1: a `K`-line subspace meeting the reciprocal set in at most one
point is metrizable. -/
private lemma metrizableRealKSubspaceOfSubsingletonIntersection
    (s : Set RealKLine)
    (hs : (s ∩ RealTopology.positiveReciprocals).Subsingleton) :
    @TopologicalSpace.MetrizableSpace s
      (TopologicalSpace.induced (fun x : s ↦ (x.1 : RealKLine))
        RealKLine.instTopologicalSpace) := by
  -- On such a subspace every deleted-interval generator is already standard-open.
  let forget : s → ℝ := fun x ↦ x.1
  have hreciprocal : (forget ⁻¹' RealTopology.positiveReciprocals).Subsingleton := by
    intro x hx y hy
    dsimp only [forget, Set.mem_preimage] at hx hy
    apply Subtype.ext
    exact hs ⟨x.property, hx⟩ ⟨y.property, hy⟩
  have hforgetInjective : Function.Injective forget := by
    intro x y hxy
    apply Subtype.ext
    exact hxy
  have hreciprocalClosed : @IsClosed s
      (TopologicalSpace.induced forget (inferInstance : TopologicalSpace ℝ))
      (forget ⁻¹' RealTopology.positiveReciprocals) := by
    rw [isClosed_induced_iff]
    rcases hreciprocal.eq_empty_or_singleton with hempty | ⟨x, hx⟩
    · have himage : forget ⁻¹' ∅ = forget ⁻¹' RealTopology.positiveReciprocals := by
        rw [Set.preimage_empty, hempty]
      exact ⟨∅, isClosed_empty, himage⟩
    · refine ⟨{forget x}, isClosed_singleton, ?_⟩
      rw [hx]
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hforgetInjective.eq_iff
  have hembedding : @Topology.IsEmbedding s ℝ
      (TopologicalSpace.induced (fun x : s ↦ (x.1 : RealKLine))
        RealKLine.instTopologicalSpace)
      (inferInstance : TopologicalSpace ℝ) forget := by
    refine ⟨⟨?_⟩, ?_⟩
    · change TopologicalSpace.induced forget RealTopology.k =
        TopologicalSpace.induced forget (inferInstance : TopologicalSpace ℝ)
      apply le_antisymm
      · exact induced_mono RealTopology.k_lt_standard.le
      · rw [RealTopology.k_eq_generateFrom]
        rw [induced_generateFrom_eq]
        apply le_generateFrom
        rintro _ ⟨U, hU, rfl⟩
        obtain ⟨a, b, _, rfl | rfl⟩ := (RealTopology.mem_kBasis_iff U).mp hU
        · exact isOpen_induced isOpen_Ioo
        · rw [Set.preimage_sdiff]
          -- Local instance justification (explicit induced topology): the method-style open-set
          -- operation must use the same standard induced topology as the comparison goal.
          letI : TopologicalSpace s :=
            TopologicalSpace.induced forget (inferInstance : TopologicalSpace ℝ)
          exact (isOpen_induced isOpen_Ioo).sdiff hreciprocalClosed
    · intro x y hxy
      dsimp only [forget] at hxy
      exact Subtype.ext hxy
  -- The standard real line is metrizable, so the established embedding pulls a metric back.
  exact hembedding.metrizableSpace

namespace RealKLine

/- Exercise 4.99.1 (171): The real line with the k-topology is connected. -/
#check RealKLine.instConnectedSpace

/- Exercise 4.99.1 (172): The real line with the k-topology is not path connected. -/
#check RealKLine.notPathConnected

/-- Exercise 4.99.1 (173): The real line with the k-topology is not locally connected. -/
theorem notLocallyConnected :
    ¬ LocallyConnectedSpace RealKLine := by
  -- A connected neighborhood of zero inside a deleted interval would cross a deleted reciprocal.
  intro hlocal
  -- Local instance justification (hypothetical class): use the assumed connected-neighborhood
  -- basis.
  letI : LocallyConnectedSpace RealKLine := hlocal
  let U : Set RealKLine := Set.Ioo (-1) 1 \ RealTopology.positiveReciprocals
  have hUopen : IsOpen U := by
    change @IsOpen ℝ RealTopology.k U
    apply RealKLine.isOpen_k_of_mem_kBasis
    rw [RealTopology.mem_kBasis_iff]
    have hminusOneLtOne : (-1 : ℝ) < 1 := by
      norm_num
    exact ⟨(-1 : ℝ), (1 : ℝ), hminusOneLtOne, Or.inr rfl⟩
  have hzeroU : (0 : RealKLine) ∈ U := by
    have hzeroInterval : (0 : RealKLine) ∈ Set.Ioo (-1) 1 := by
      norm_num
    refine ⟨hzeroInterval, ?_⟩
    exact RealTopology.zeroNotMemPositiveReciprocals
  obtain ⟨V, hVnhds, hVpreconnected, hVU⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp inferInstance 0 U
      (hUopen.mem_nhds hzeroU)
  obtain ⟨W, hWV, hWopen, hzeroW⟩ := mem_nhds_iff.mp hVnhds
  change @IsOpen ℝ RealTopology.k W at hWopen
  rw [RealTopology.k_eq_generateFrom] at hWopen
  obtain ⟨a, b, ha, hb, hab⟩ :=
    RealKLine.exists_puncturedInterval_subset_of_generateOpen hWopen hzeroW
  -- Choose points of `V` on both sides of zero, avoiding the reciprocal set on the right.
  let q : RealKLine := (a / 2 : ℝ)
  have htwoPos : (0 : ℝ) < 2 := by
    norm_num
  have hqneg : (q : ℝ) < 0 := by
    dsimp only [q]
    exact div_neg_of_neg_of_pos ha htwoPos
  have hqW : q ∈ W := by
    apply hab
    have haq : a < q := by
      dsimp only [q]
      rw [lt_div_iff₀ htwoPos]
      linarith
    have hqb : q < b := hqneg.trans hb
    refine ⟨⟨haq, hqb⟩, ?_⟩
    intro hqReciprocal
    exact (not_lt_of_ge (RealTopology.positiveReciprocals_pos hqReciprocal).le)
      hqneg
  obtain ⟨p, hpIrrational, hp, hpb⟩ := exists_irrational_btwn hb
  have hpNotReciprocal : p ∉ RealTopology.positiveReciprocals := by
    intro hpReciprocal
    obtain ⟨n, hn, hpn⟩ := (RealTopology.mem_positiveReciprocals p).mp hpReciprocal
    have hcast : (((n : ℚ)⁻¹ : ℚ) : ℝ) = (n : ℝ)⁻¹ :=
      Rat.cast_inv_nat n
    have hpRat : p = (((n : ℚ)⁻¹ : ℚ) : ℝ) := hpn.trans hcast.symm
    exact hpIrrational.ne_rat ((n : ℚ)⁻¹) hpRat
  have hpW : (p : RealKLine) ∈ W :=
    hab ⟨⟨ha.trans hp, hpb⟩, hpNotReciprocal⟩
  have hqV : q ∈ V := hWV hqW
  have hpV : (p : RealKLine) ∈ V := hWV hpW
  obtain ⟨r, hrReciprocal, hrp⟩ := RealTopology.exists_positiveReciprocal_lt hp
  let forget : RealKLine → ℝ := fun z ↦ z
  have hforget : Continuous forget := RealKLine.continuousToReal
  have himagePreconnected : IsPreconnected (forget '' V) :=
    hVpreconnected.image forget hforget.continuousOn
  have hqImage : (q : ℝ) ∈ forget '' V := ⟨q, hqV, rfl⟩
  have hpImage : p ∈ forget '' V := ⟨p, hpV, rfl⟩
  have hqr : (q : ℝ) ≤ r :=
    hqneg.le.trans (RealTopology.positiveReciprocals_pos hrReciprocal).le
  have hrInterval : r ∈ Set.Icc (q : ℝ) p := ⟨hqr, hrp.le⟩
  have hrImage := himagePreconnected.Icc_subset hqImage hpImage hrInterval
  obtain ⟨z, hzV, hzr⟩ := hrImage
  have hzU := hVU hzV
  apply hzU.2
  change (z : ℝ) ∈ RealTopology.positiveReciprocals
  have hzr' : (z : ℝ) = r := hzr
  rwa [hzr']

/-- Exercise 4.99.1 (174): The real line with the k-topology is not locally path connected. -/
theorem notLocallyPathConnected :
    ¬ LocallyPathConnectedSpace RealKLine := by
  -- Local path connectedness would imply the excluded local connectedness.
  exact notLocallyPathConnectedOfNotLocallyConnected RealKLine notLocallyConnected

/-- Exercise 4.99.1 (175): The real line with the k-topology is not compact. -/
theorem notCompact : ¬ CompactSpace RealKLine := by
  -- A compact Hausdorff `K`-line would be regular, contrary to its separation obstruction.
  intro hcompact
  -- Local instance justification (hypothetical class): expose the assumed compactness.
  letI : CompactSpace RealKLine := hcompact
  -- Local instance justification (named-topology bridge): use the proved Hausdorff structure for
  -- the `K`-topology while deriving regularity from compactness.
  letI : T2Space RealKLine := RealTopology.kT2Space
  have hT3 : T3Space RealKLine := inferInstance
  exact RealTopology.kNotT3Space hT3

/-- Exercise 4.99.1 (176): The real line with the k-topology is not limit point compact. -/
theorem notLimitPointCompact :
    ¬ LimitPointCompactSpace RealKLine := by
  -- The closed infinite discrete reciprocal set would have to possess an accumulation point.
  intro hlimit
  obtain ⟨x, hx⟩ := hlimit.exists_accPt
    RealTopology.positiveReciprocals positiveReciprocals_infinite
  exact @UnitIntervalUniformPower.not_accPt_principal_of_isClosed_isDiscrete
    RealKLine RealKLine.instTopologicalSpace RealTopology.positiveReciprocals
    positiveReciprocals_isClosed positiveReciprocals_isDiscrete x hx

/-- Exercise 4.99.1 (177): The real line with the k-topology is not locally compact Hausdorff. -/
theorem notLocallyCompactT2 :
    ¬ (LocallyCompactSpace RealKLine ∧ T2Space RealKLine) := by
  -- Locally compact Hausdorff spaces are regular, contradicting the `K`-line obstruction.
  rintro ⟨hlocal, hT2⟩
  -- Local instance justification (hypothetical class): expose both assumed structures.
  letI : LocallyCompactSpace RealKLine := hlocal
  -- Local instance justification (hypothetical class): expose the assumed Hausdorff structure to
  -- the locally-compact regularity instance.
  letI : T2Space RealKLine := hT2
  have hT3 : T3Space RealKLine := inferInstance
  exact RealTopology.kNotT3Space hT3

/- Exercise 4.99.1 (178): The real line with the k-topology is Hausdorff. -/
#check RealTopology.kT2Space

/- Exercise 4.99.1 (179): The real line with the k-topology is not regular. -/
#check RealTopology.kNotT3Space

/-- Exercise 4.99.1 (180): The real line with the k-topology is not completely regular. -/
theorem notT35Space : ¬ T35Space RealKLine := by
  -- Complete regular Hausdorff separation implies regular Hausdorff separation.
  intro hT35
  -- Local instance justification (hypothetical class): expose the assumed complete regularity.
  letI : T35Space RealKLine := hT35
  have hT3 : T3Space RealKLine := inferInstance
  exact RealTopology.kNotT3Space hT3

/-- Exercise 4.99.1 (181): The real line with the k-topology is not normal. -/
theorem notT4Space : ¬ T4Space RealKLine := by
  -- Normal Hausdorff separation implies regular Hausdorff separation.
  intro hT4
  -- Local instance justification (hypothetical class): expose the assumed normality.
  letI : T4Space RealKLine := hT4
  have hT3 : T3Space RealKLine := inferInstance
  exact RealTopology.kNotT3Space hT3

/-- Exercise 4.99.1 (182): The real line with the k-topology is first-countable. -/
instance instFirstCountableTopology : FirstCountableTopology RealKLine := by
  -- The existing second-countability instance supplies countable local bases.
  infer_instance

/- Exercise 4.99.1 (183): The real line with the k-topology is second-countable. -/
#check RealKLine.instSecondCountableTopology

/-- Exercise 4.99.1 (184): The real line with the k-topology is Lindelöf. -/
instance instLindelofSpace : LindelofSpace RealKLine := by
  -- Second-countable spaces are Lindelöf.
  infer_instance

/-- Exercise 4.99.1 (185): The real line with the k-topology has a countable dense subset. -/
instance instSeparableSpace : TopologicalSpace.SeparableSpace RealKLine := by
  -- Second-countable spaces have a countable dense subset.
  infer_instance

/-- Exercise 4.99.1 (186): The real line with the k-topology is locally metrizable. -/
instance instLocallyMetrizableSpace : LocallyMetrizableSpace RealKLine := by
  -- Away from the reciprocal set use its open complement; at a reciprocal use an isolating
  -- interval.
  rw [locallyMetrizableSpace_iff]
  intro x
  by_cases hx : x ∈ RealTopology.positiveReciprocals
  · obtain ⟨n, hn, hxn⟩ := (RealTopology.mem_positiveReciprocals x).mp hx
    obtain ⟨u, huOpen, hxu, huIntersection⟩ :=
      RealKLine.exists_isOpen_reciprocal_isolating n hn
    have huKOpen : @IsOpen RealKLine RealKLine.instTopologicalSpace u :=
      RealKLine.isOpen_of_standard huOpen
    refine ⟨u, huKOpen.mem_nhds ?_, ?_⟩
    · rwa [hxn]
    · apply metrizableRealKSubspaceOfSubsingletonIntersection
      intro y hy z hz
      change (y : ℝ) ∈ u ∩ RealTopology.positiveReciprocals at hy
      change (z : ℝ) ∈ u ∩ RealTopology.positiveReciprocals at hz
      rw [huIntersection] at hy hz
      exact hy.trans hz.symm
  · let s : Set RealKLine := RealTopology.positiveReciprocalsᶜ
    have hsOpen : @IsOpen RealKLine RealKLine.instTopologicalSpace s :=
      positiveReciprocals_isClosed.isOpen_compl
    refine ⟨s, hsOpen.mem_nhds hx, ?_⟩
    apply metrizableRealKSubspaceOfSubsingletonIntersection
    intro y hy z hz
    change (y : ℝ) ∈ RealTopology.positiveReciprocalsᶜ ∩
      RealTopology.positiveReciprocals at hy
    exact (hy.1 hy.2).elim

/-- Exercise 4.99.1 (187): The real line with the k-topology is not metrizable. -/
theorem notMetrizable :
    ¬ TopologicalSpace.MetrizableSpace RealKLine := by
  -- Metrizable spaces are regular Hausdorff, contradicting the `K`-topology obstruction.
  intro hmetric
  -- Local instance justification (hypothetical class): expose the assumed compatible metric.
  letI : TopologicalSpace.MetrizableSpace RealKLine := hmetric
  have hT3 : T3Space RealKLine := inferInstance
  exact RealTopology.kNotT3Space hT3

end RealKLine
