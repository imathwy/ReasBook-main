module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace

public section

universe u

namespace OpenOmegaOne

/-- Helper for Theorem 10.3: every strict lower interval in `OpenOmegaOne` is countable. -/
lemma countable_Iio (a : OpenOmegaOne.{u}) : (Set.Iio a).Countable := by
  -- Convert the defining bound on `a` into countability of its ordinal realization.
  have hcard : a.1.card ≤ Cardinal.aleph0 :=
    (CountableOrdinal.mem_iff_card_le_aleph0 a.1).mp a.2
  have htype : Countable a.1.ToType := by
    apply Cardinal.mk_le_aleph0_iff.mp
    rwa [Cardinal.mk_toType]
  -- Transport countability across the canonical order isomorphism with the lower interval.
  exact (CountableOrdinal.orderIsoIio a).toEquiv.countable_iff.mp htype

/-- Helper for Theorem 10.3: the union of lower intervals indexed by a countable set is
countable. -/
lemma countable_biUnion_Iio (A : Set OpenOmegaOne.{u}) (hA : A.Countable) :
    (⋃ a ∈ A, Set.Iio a).Countable := by
  -- Apply countable-union closure to the countable family of lower intervals.
  exact hA.biUnion fun a _ ↦ countable_Iio a

/-- Helper for Theorem 10.3: a point outside all lower intervals of `A` is an upper bound
of `A`. -/
lemma mem_upperBounds_of_not_mem_biUnion_Iio (A : Set OpenOmegaOne.{u})
    (x : OpenOmegaOne.{u}) (hx : x ∉ ⋃ a ∈ A, Set.Iio a) : x ∈ upperBounds A := by
  -- If some member of `A` exceeded `x`, then `x` would lie in its lower interval.
  intro a ha
  by_contra hax
  apply hx
  refine Set.mem_iUnion.mpr ⟨a, ?_⟩
  refine Set.mem_iUnion.mpr ⟨ha, ?_⟩
  exact lt_of_not_ge hax

/-- Theorem 10.3: If `A` is a countable subset of `S_Ω`, then `A` has an upper
bound in `S_Ω`. -/
theorem bddAbove_of_countable (A : Set OpenOmegaOne.{u}) (hA : A.Countable) :
    BddAbove A := by
  -- The union of all sections below members of `A` is still countable.
  have hsections : (⋃ a ∈ A, Set.Iio a).Countable := countable_biUnion_Iio A hA
  -- Uncountability of `OpenOmegaOne` provides a point outside that union.
  have hsections_ne : (⋃ a ∈ A, Set.Iio a) ≠ Set.univ := by
    intro h_univ
    have h_univ_countable : (Set.univ : Set OpenOmegaOne.{u}).Countable := by
      rwa [← h_univ]
    exact Set.not_countable_univ h_univ_countable
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hsections_ne
  -- Such a point is an upper bound because it lies below no member of `A`.
  exact ⟨x, mem_upperBounds_of_not_mem_biUnion_Iio A x hx⟩

end OpenOmegaOne
