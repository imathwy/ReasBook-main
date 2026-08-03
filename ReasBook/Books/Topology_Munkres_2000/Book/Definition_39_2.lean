module

public import Topology_Munkres_2000.Book.Definition_6_0_1.LocallyFinite

public section

universe u v

/- Definition 39.2: An indexed family `f : ι → Set X` is locally finite if every
point of `X` has a neighborhood meeting `f i` for only finitely many indices `i`. -/
#check LocallyFinite

/-- Helper for Definition 39.2: every nonempty value of a locally finite indexed family
occurs at only finitely many indices. -/
lemma finiteFiberOfLocallyFinite {ι : Type u} {X : Type v} [TopologicalSpace X]
    {f : ι → Set X} (hf : LocallyFinite f) {s : Set X} (hs : s.Nonempty) :
    {i | f i = s}.Finite := by
  -- A point of `s` turns every occurrence of `s` into an index containing that point.
  rcases hs with ⟨x, hx⟩
  refine (hf.point_finite x).subset ?_
  intro i hi
  have hiEq : f i = s := hi
  have hxi : x ∈ f i := hiEq.symm ▸ hx
  exact hxi

/-- Helper for Definition 39.2: local finiteness of the distinct values, together with
finite fibers over nonempty values, implies local finiteness of the indexed family. -/
lemma locallyFiniteOfRangeLocallyFiniteAndFiniteFibers {ι : Type u} {X : Type v}
    [TopologicalSpace X] {f : ι → Set X} (hRange : (Set.range f).LocallyFinite)
    (hFiber : ∀ s : Set X, s.Nonempty → {i | f i = s}.Finite) : LocallyFinite f := by
  -- Choose a neighborhood meeting only finitely many distinct values of the family.
  intro x
  rcases Set.locallyFinite_iff.mp hRange x with ⟨U, hU, hValues⟩
  let meetingValues : Set (Set X) := {s | s ∈ Set.range f ∧ (s ∩ U).Nonempty}
  have hMeetingValues : meetingValues.Finite := by
    simpa only [meetingValues] using hValues
  -- Each value meeting `U` is nonempty, so its equality fiber is finite.
  have hMeetingIndices : (f ⁻¹' meetingValues).Finite := by
    refine hMeetingValues.preimage' ?_
    intro s hs
    have hsNonempty : s.Nonempty := hs.2.mono Set.inter_subset_left
    have hsFiber : {i | f i = s}.Finite := hFiber s hsNonempty
    have hFiberEq : f ⁻¹' {s} = {i | f i = s} := by
      ext i
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rwa [hFiberEq]
  -- The preimage is exactly the set of indices whose values meet the neighborhood.
  have hPreimage : f ⁻¹' meetingValues = {i | (f i ∩ U).Nonempty} := by
    ext i
    constructor
    · intro hi
      exact hi.2
    · intro hi
      exact ⟨Set.mem_range_self i, hi⟩
  refine ⟨U, hU, ?_⟩
  rwa [← hPreimage]

/-- An indexed family is locally finite exactly when its family of distinct values is
locally finite and every nonempty value occurs at only finitely many indices. -/
theorem locallyFinite_iff_onRange_finiteFibers {ι : Type u} {X : Type v}
    [TopologicalSpace X] (f : ι → Set X) :
    LocallyFinite f ↔
      (Set.range f).LocallyFinite ∧ ∀ s : Set X, s.Nonempty → {i | f i = s}.Finite := by
  -- Separate the collection of distinct values from the multiplicity of each value.
  constructor
  · intro hf
    refine ⟨hf.on_range, ?_⟩
    intro s hs
    exact finiteFiberOfLocallyFinite hf hs
  · rintro ⟨hRange, hFiber⟩
    exact locallyFiniteOfRangeLocallyFiniteAndFiniteFibers hRange hFiber
