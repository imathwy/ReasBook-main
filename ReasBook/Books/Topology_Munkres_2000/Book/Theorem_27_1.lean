module

public import Mathlib.Topology.Order.Compact
public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty

public section

universe u

/-- Helper for Theorem 27.1: the least upper bound property supplies a greatest
lower bound for every nonempty set that is bounded below. -/
private lemma exists_isGLB_of_leastUpperBoundProperty {X : Type u} [LinearOrder X]
    (h : LeastUpperBoundProperty X) (s : Set X) (hs : s.Nonempty) (hb : BddBelow s) :
    ∃ a, IsGLB s a := by
  -- Apply the upper-bound property to the set of lower bounds.
  obtain ⟨a, ha⟩ := h.exists_isLUB (lowerBounds s) hb hs.bddAbove_lowerBounds
  -- The canonical lower-bounds equivalence turns this LUB into the required GLB.
  exact ⟨a, isLUB_lowerBounds.mp ha⟩

/-- Helper for Theorem 27.1: choose a supremum for a nonempty bounded-above set,
and use a fixed fallback point otherwise. -/
private noncomputable def chosenSupOfLeastUpperBoundProperty {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) : X :=
  -- Valid sets use the supplied least upper bound; all other sets share the fallback.
  @dite X (s.Nonempty ∧ BddAbove s) (Classical.propDecidable _)
    (fun hs ↦ Classical.choose (h.exists_isLUB s hs.1 hs.2))
    (fun _ ↦ Classical.choice inferInstance)

/-- Helper for Theorem 27.1: choose an infimum for a nonempty bounded-below set,
and use a fixed fallback point otherwise. -/
private noncomputable def chosenInfOfLeastUpperBoundProperty {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) : X :=
  -- Valid sets use the derived greatest lower bound; all other sets share the fallback.
  @dite X (s.Nonempty ∧ BddBelow s) (Classical.propDecidable _)
    (fun hs ↦
      Classical.choose (exists_isGLB_of_leastUpperBoundProperty h s hs.1 hs.2))
    (fun _ ↦ Classical.choice inferInstance)

/-- Helper for Theorem 27.1: the chosen supremum is a least upper bound whenever
the set is nonempty and bounded above. -/
private lemma chosenSupOfLeastUpperBoundProperty_isLUB {X : Type u} [LinearOrder X]
    [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) (hs : s.Nonempty)
    (hb : BddAbove s) : IsLUB s (chosenSupOfLeastUpperBoundProperty h s) := by
  -- On a valid set the choice function reduces to the witness supplied by `h`.
  rw [chosenSupOfLeastUpperBoundProperty, dif_pos ⟨hs, hb⟩]
  exact Classical.choose_spec (h.exists_isLUB s hs hb)

/-- Helper for Theorem 27.1: the chosen infimum is a greatest lower bound whenever
the set is nonempty and bounded below. -/
private lemma chosenInfOfLeastUpperBoundProperty_isGLB {X : Type u} [LinearOrder X]
    [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) (hs : s.Nonempty)
    (hb : BddBelow s) : IsGLB s (chosenInfOfLeastUpperBoundProperty h s) := by
  -- On a valid set the choice function reduces to the derived GLB witness.
  rw [chosenInfOfLeastUpperBoundProperty, dif_pos ⟨hs, hb⟩]
  exact Classical.choose_spec (exists_isGLB_of_leastUpperBoundProperty h s hs hb)

/-- Helper for Theorem 27.1: every set that is not bounded above receives the
same chosen supremum as the empty set. -/
private lemma chosenSupOfLeastUpperBoundProperty_of_not_bddAbove {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X)
    (hs : ¬ BddAbove s) :
    chosenSupOfLeastUpperBoundProperty h s =
      chosenSupOfLeastUpperBoundProperty h (∅ : Set X) := by
  -- Both the given set and the empty set select the common fallback branch.
  have hsinvalid : ¬ (s.Nonempty ∧ BddAbove s) := fun hvalid ↦ hs hvalid.2
  have hempty : ¬ ((∅ : Set X).Nonempty ∧ BddAbove (∅ : Set X)) :=
    fun hvalid ↦ Set.not_nonempty_empty hvalid.1
  simp only [chosenSupOfLeastUpperBoundProperty, dif_neg hsinvalid, dif_neg hempty]

/-- Helper for Theorem 27.1: every set that is not bounded below receives the
same chosen infimum as the empty set. -/
private lemma chosenInfOfLeastUpperBoundProperty_of_not_bddBelow {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X)
    (hs : ¬ BddBelow s) :
    chosenInfOfLeastUpperBoundProperty h s =
      chosenInfOfLeastUpperBoundProperty h (∅ : Set X) := by
  -- Both the given set and the empty set select the common fallback branch.
  have hsinvalid : ¬ (s.Nonempty ∧ BddBelow s) := fun hvalid ↦ hs hvalid.2
  have hempty : ¬ ((∅ : Set X).Nonempty ∧ BddBelow (∅ : Set X)) :=
    fun hvalid ↦ Set.not_nonempty_empty hvalid.1
  simp only [chosenInfOfLeastUpperBoundProperty, dif_neg hsinvalid, dif_neg hempty]

/-- Helper for Theorem 27.1: a nonempty linear order with the least upper bound
property carries a conditionally complete linear order structure. -/
@[implicit_reducible] private noncomputable def
    conditionallyCompleteLinearOrderOfLeastUpperBoundProperty
    {X : Type u} [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) :
    ConditionallyCompleteLinearOrder X where
  -- Retain the original order and lattice operations, adding only chosen set bounds.
  __ := ‹LinearOrder X›
  __ := LinearOrder.toLattice
  sSup := chosenSupOfLeastUpperBoundProperty h
  sInf := chosenInfOfLeastUpperBoundProperty h
  isLUB_csSup := chosenSupOfLeastUpperBoundProperty_isLUB h
  isGLB_csInf := chosenInfOfLeastUpperBoundProperty_isGLB h
  csSup_of_not_bddAbove := chosenSupOfLeastUpperBoundProperty_of_not_bddAbove h
  csInf_of_not_bddBelow := chosenInfOfLeastUpperBoundProperty_of_not_bddBelow h

/-- Theorem 27.1: If a linear order has the least upper bound property, then in
its order topology every closed interval is compact. -/
instance instCompactIccSpaceOfLeastUpperBoundProperty (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [LeastUpperBoundProperty X] :
    CompactIccSpace X := by
  -- Empty orders have no interval endpoints, so compactness is immediate.
  cases isEmpty_or_nonempty X with
  | inl hempty =>
      refine CompactIccSpace.mk' ?_
      intro a
      exact isEmptyElim a
  | inr hnonempty =>
      -- On a nonempty order, expose the completeness property through mathlib's
      -- canonical conditional-completeness interface and reuse interval compactness.
      let originalOrder : LinearOrder X := inferInstance
      letI : Nonempty X := hnonempty
      letI : ConditionallyCompleteLinearOrder X :=
        conditionallyCompleteLinearOrderOfLeastUpperBoundProperty inferInstance
      letI : LinearOrder X := originalOrder
      infer_instance

/-- Every closed interval in a linear order with the least upper bound property is compact. -/
theorem isCompact_Icc_of_leastUpperBoundProperty (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [LeastUpperBoundProperty X]
    (a b : X) : IsCompact (Set.Icc a b) :=
  isCompact_Icc
