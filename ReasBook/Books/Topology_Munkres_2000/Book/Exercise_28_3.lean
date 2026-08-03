module

public import Topology_Munkres_2000.Book.Example_28_1.IndiscretePair
public import Topology_Munkres_2000.Book.Example_28_2.Instances
public import Topology_Munkres_2000.Book.Exercise_4_99_4.Subspace
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Order.WithTop
public import Mathlib.Topology.Order.MonotoneContinuity

public section

universe u v

/-- Helper for Exercise 28.3: limit point compactness is preserved by homeomorphisms. -/
theorem Homeomorph.limitPointCompactSpace {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    [LimitPointCompactSpace X] : LimitPointCompactSpace Y := by
  -- Pull an infinite set back to the source space.
  rw [limitPointCompactSpace_iff]
  intro s hs
  have hpreimage : (e ⁻¹' s).Infinite :=
    hs.preimage (Set.subset_range_of_surjective e.surjective s)
  obtain ⟨x, hx⟩ :=
    (limitPointCompactSpace_iff X).mp (inferInstance : LimitPointCompactSpace X)
      (e ⁻¹' s) hpreimage
  -- Map the resulting accumulation point forward through the homeomorphism.
  refine ⟨e x, ?_⟩
  have hmapped := AccPt.map hx e.continuous.continuousAt e.injective
  simpa only [Filter.map_principal, e.image_preimage] using hmapped

/-- Helper for Exercise 28.3: a universe lift of the positive integers is not limit point
compact. -/
theorem uliftPNat_not_limitPointCompactSpace :
    ¬ LimitPointCompactSpace (ULift.{u} ℕ+) := by
  intro h
  -- In this countable `T₁` space, limit point compactness yields compactness.
  letI : CountablyCompactSpace (ULift.{u} ℕ+) :=
    (limitPointCompactSpace_iff_countablyCompactSpace _).mp h
  letI : CompactSpace (ULift.{u} ℕ+) := LindelofSpace.compactSpace
  letI : CompactSpace ℕ+ := Homeomorph.ulift.compactSpace
  -- This contradicts the standard noncompactness instance on positive integers.
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℕ+))
    (inferInstance : CompactSpace ℕ+)

/-- Helper for Exercise 28.3: the greatest point of `WithTop α` accumulates the canonical
copy of a nonempty linear order without a greatest element. -/
theorem withTop_top_accPt_range_coe {α : Type u} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [Nonempty α] [NoMaxOrder α] :
    AccPt (⊤ : WithTop α) (Filter.principal (Set.range ((↑) : α → WithTop α))) := by
  -- Every basic neighborhood of the added top point contains a larger ordinary point.
  rw [accPt_iff_frequently, nhds_top_basis.frequently_iff]
  intro a ha
  obtain ⟨b, rfl⟩ := WithTop.ne_top_iff_exists.mp ha.ne
  obtain ⟨c, hbc⟩ := exists_gt b
  exact ⟨c, WithTop.coe_lt_coe.mpr hbc, WithTop.coe_ne_top, ⟨c, rfl⟩⟩

/-- Helper for Exercise 28.3 (a): a continuous image of a limit point compact space need not
be limit point compact, even when the image is represented by the range subtype. -/
theorem limitPointCompactSpace_range_not_preserved :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LimitPointCompactSpace X] (f : X → Y) (_hf : Continuous f),
      LimitPointCompactSpace (Set.range f) := by
  intro hpreserved
  -- Lift the projection counterexample into the universes required by the statement.
  letI : LimitPointCompactSpace (ULift.{u} PNatIndiscretePair) :=
    Homeomorph.ulift.symm.limitPointCompactSpace
  let f : ULift.{u} PNatIndiscretePair → ULift.{v} ℕ+ := ULift.map Prod.fst
  have hf : Continuous f := continuous_uliftMap Prod.fst continuous_fst
  have hrange : LimitPointCompactSpace (Set.range f) :=
    hpreserved _ _ f hf
  -- Surjectivity identifies the range subtype with the non-limit-point-compact codomain.
  have hsurjective : Function.Surjective f := by
    intro y
    refine ⟨ULift.up (y.down, WithTopology.toTopology ⊤ false), ?_⟩
    cases y
    rfl
  let e : Set.range f ≃ₜ ULift.{v} ℕ+ :=
    (Homeomorph.setCongr hsurjective.range_eq).trans (Homeomorph.Set.univ _)
  letI : LimitPointCompactSpace (Set.range f) := hrange
  exact uliftPNat_not_limitPointCompactSpace e.limitPointCompactSpace

/- Helper for Exercise 28.3 (b): A closed subspace of a limit point compact space is
limit point compact. -/
#check IsClosed.limitPointCompactSpace

/-- Helper for Exercise 28.3 (c): a limit point compact subspace of a Hausdorff space need not
be closed. -/
theorem limitPointCompact_subspace_not_closed :
    ¬ ∀ (Z : Type u) [TopologicalSpace Z] [T2Space Z] (s : Set Z)
      (_hs : LimitPointCompactSpace s), IsClosed s := by
  intro hclosed
  -- Use a small type representing the countable ordinals, then add one greatest point.
  let A : Type u := (Ordinal.omega 1 : Ordinal.{u}).ToType
  letI : TopologicalSpace A := Preorder.topology A
  letI : OrderTopology A := ⟨rfl⟩
  letI : Nonempty A := Ordinal.nonempty_toType_iff.mpr (ne_of_gt (Ordinal.omega_pos 1))
  letI : NoMaxOrder A :=
    Ordinal.isSuccPrelimit_type_lt_iff.mp <| by
      simpa only [A, Ordinal.type_toType] using (Cardinal.isSuccLimit_omega 1).isSuccPrelimit
  letI : LimitPointCompactSpace A :=
    (Ordinal.ToType.mk (o := (Ordinal.omega 1 : Ordinal.{u}))).toHomeomorph.limitPointCompactSpace
  let s : Set (WithTop A) := Set.range ((↑) : A → WithTop A)
  letI : LimitPointCompactSpace s :=
    WithTop.isEmbedding_coe.toHomeomorph.limitPointCompactSpace
  have hs_closed : IsClosed s := hclosed (WithTop A) s inferInstance
  -- Closedness would force the omitted accumulation point to belong to the range.
  have htop : (⊤ : WithTop A) ∈ s :=
    (isClosed_iff_accPt.mp hs_closed) ⊤ withTop_top_accPt_range_coe
  obtain ⟨x, hx⟩ := htop
  exact WithTop.coe_ne_top hx

/-- Exercise 28.3: continuous images need not preserve limit point compactness, closed
subspaces do preserve it, and limit point compact subspaces of Hausdorff spaces need not be
closed. -/
theorem «limitPointCompactSpace_range_not_preserved; limitPointCompact_subspace_not_closed» :
    (¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [LimitPointCompactSpace X] (f : X → Y) (_hf : Continuous f),
      LimitPointCompactSpace (Set.range f)) ∧
    (¬ ∀ (Z : Type u) [TopologicalSpace Z] [T2Space Z] (s : Set Z)
      (_hs : LimitPointCompactSpace s), IsClosed s) := by
  -- Combine the counterexamples answering parts (a) and (c).
  constructor
  · exact limitPointCompactSpace_range_not_preserved
  · exact limitPointCompact_subspace_not_closed
