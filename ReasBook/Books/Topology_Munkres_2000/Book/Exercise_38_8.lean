module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Instances.PNat
public import Mathlib.Topology.UnitInterval

public section

/-- Helper for Exercise 38.8: the product space of unit-interval self-maps is separable. -/
private instance unitIntervalSelfMapsSeparable :
    TopologicalSpace.SeparableSpace (unitInterval → unitInterval) := by
  -- Continuous self-maps meet every nonempty basic cylinder because finitely
  -- prescribed values extend from the corresponding closed finite subset.
  have hDense :
      DenseRange (fun f : C(unitInterval, unitInterval) ↦
        (f : unitInterval → unitInterval)) := by
    refine dense_iff_inter_open.2 fun U hU hUne ↦ ?_
    obtain ⟨g, hgU⟩ := hUne
    obtain ⟨I, V, hV, hVU⟩ := isOpen_pi_iff.mp hU g hgU
    let s : Set unitInterval := I
    have hsClosed : IsClosed s := I.finite_toSet.isClosed
    let f : C(s, unitInterval) :=
      ⟨fun x ↦ g x, continuous_of_discreteTopology⟩
    obtain ⟨F, hF⟩ := f.exists_restrict_eq hsClosed
    have hFI : ∀ i : I, F i = g i := by
      intro i
      exact congrArg (fun q : C(s, unitInterval) ↦ q ⟨i, i.2⟩) hF
    refine ⟨F, hVU fun i hi ↦ ?_, ⟨F, rfl⟩⟩
    rw [hFI ⟨i, hi⟩]
    exact (hV i hi).2
  -- A dense continuous image of the separable continuous-map space is separable.
  exact hDense.separableSpace (continuous_pi fun i ↦ continuous_eval_const i)

/-- Helper for Exercise 38.8: every nonempty separable space has a continuous
dense-range parametrization by the positive natural numbers. -/
private lemma existsContinuousDenseRangeFromPNat {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] [Nonempty X] :
    ∃ f : ℕ+ → X, Continuous f ∧ DenseRange f := by
  let f : ℕ+ → X := TopologicalSpace.denseSeq X ∘ Equiv.pnatEquivNat
  -- Both countable indexing spaces are discrete, while surjectivity of the
  -- equivalence preserves the range of the chosen dense sequence.
  have hfContinuous : Continuous f := continuous_of_discreteTopology
  have hfDense : DenseRange f :=
    (TopologicalSpace.denseRange_denseSeq X).comp
      Equiv.pnatEquivNat.surjective.denseRange continuous_of_discreteTopology
  exact ⟨f, hfContinuous, hfDense⟩

/-- Helper for Exercise 38.8: a Stone–Čech extension of a continuous dense-range
map into a compact Hausdorff space is surjective. -/
private lemma stoneCechExtendSurjectiveOfDenseRange {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    {g : X → Y} (hg : Continuous g) (hDense : DenseRange g) :
    Function.Surjective (stoneCechExtend hg) := by
  -- The extension equation puts the original dense range inside the range of
  -- the extended map.
  have hRange : Set.range g ⊆ Set.range (stoneCechExtend hg) := by
    rintro y ⟨x, rfl⟩
    exact ⟨stoneCechUnit x, stoneCechExtend_stoneCechUnit hg x⟩
  have hExtensionDense : DenseRange (stoneCechExtend hg) := hDense.mono hRange
  -- Its range is also closed, since its domain is compact and its codomain is
  -- Hausdorff; therefore that closed dense range is the whole codomain.
  have hRangeClosed : IsClosed (Set.range (stoneCechExtend hg)) :=
    (continuous_stoneCechExtend hg).isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← hRangeClosed.closure_eq]
  exact hExtensionDense.closure_range

/-- Exercise 38.8: The Stone–Čech compactification of the positive integers has
cardinality at least that of the self-map space `unitInterval → unitInterval`. -/
theorem unitIntervalSelfMaps_cardinality_le_stoneCechPNat :
    Cardinal.mk (unitInterval → unitInterval) ≤ Cardinal.mk (StoneCech ℕ+) := by
  -- Enumerate a dense subset of the self-map space by the positive integers.
  obtain ⟨f, hfContinuous, hfDense⟩ :=
    existsContinuousDenseRangeFromPNat (X := unitInterval → unitInterval)
  -- Extending that enumeration produces the required surjection, hence the
  -- desired comparison of cardinalities.
  exact Cardinal.mk_le_of_surjective
    (stoneCechExtendSurjectiveOfDenseRange hfContinuous hfDense)
