module

public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum
public import Mathlib.Topology.Order.IntermediateValue

public section

universe u

namespace LinearContinuum

/-- Helper for Theorem 24.1: the least upper bound property supplies a greatest
lower bound for every nonempty set that is bounded below. -/
private lemma existsIsGLBOfLeastUpperBoundProperty {X : Type u} [LinearOrder X]
    (h : LeastUpperBoundProperty X) (s : Set X) (hs : s.Nonempty) (hb : BddBelow s) :
    ∃ a, IsGLB s a := by
  -- Apply the upper-bound property to the ordered set of lower bounds.
  obtain ⟨a, ha⟩ := h.exists_isLUB (lowerBounds s) hb hs.bddAbove_lowerBounds
  -- The standard lower-bounds equivalence turns that supremum into the desired infimum.
  exact ⟨a, isLUB_lowerBounds.mp ha⟩

/-- Helper for Theorem 24.1: choose a supremum for a nonempty bounded-above set,
and use a fixed fallback point otherwise. -/
private noncomputable def chosenSupOfLeastUpperBoundProperty {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) : X :=
  -- Valid sets use the supplied least upper bound; all other sets share the fallback.
  @dite X (s.Nonempty ∧ BddAbove s) (Classical.propDecidable _)
    (fun hs ↦ Classical.choose (h.exists_isLUB s hs.1 hs.2))
    (fun _ ↦ Classical.choice inferInstance)

/-- Helper for Theorem 24.1: choose an infimum for a nonempty bounded-below set,
and use a fixed fallback point otherwise. -/
private noncomputable def chosenInfOfLeastUpperBoundProperty {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) : X :=
  -- Valid sets use the derived greatest lower bound; all other sets share the fallback.
  @dite X (s.Nonempty ∧ BddBelow s) (Classical.propDecidable _)
    (fun hs ↦
      Classical.choose (existsIsGLBOfLeastUpperBoundProperty h s hs.1 hs.2))
    (fun _ ↦ Classical.choice inferInstance)

/-- Helper for Theorem 24.1: the chosen supremum is a least upper bound whenever
the set is nonempty and bounded above. -/
private lemma chosenSupOfLeastUpperBoundProperty_isLUB {X : Type u} [LinearOrder X]
    [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) (hs : s.Nonempty)
    (hb : BddAbove s) : IsLUB s (chosenSupOfLeastUpperBoundProperty h s) := by
  -- Reduce the choice to the valid branch and use its specification.
  rw [chosenSupOfLeastUpperBoundProperty, dif_pos ⟨hs, hb⟩]
  exact Classical.choose_spec (h.exists_isLUB s hs hb)

/-- Helper for Theorem 24.1: the chosen infimum is a greatest lower bound whenever
the set is nonempty and bounded below. -/
private lemma chosenInfOfLeastUpperBoundProperty_isGLB {X : Type u} [LinearOrder X]
    [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X) (hs : s.Nonempty)
    (hb : BddBelow s) : IsGLB s (chosenInfOfLeastUpperBoundProperty h s) := by
  -- Reduce the choice to the valid branch and use the derived infimum specification.
  rw [chosenInfOfLeastUpperBoundProperty, dif_pos ⟨hs, hb⟩]
  exact Classical.choose_spec (existsIsGLBOfLeastUpperBoundProperty h s hs hb)

/-- Helper for Theorem 24.1: every set that is not bounded above receives the
same chosen supremum as the empty set. -/
private lemma chosenSupOfLeastUpperBoundProperty_of_not_bddAbove {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X)
    (hs : ¬ BddAbove s) :
    chosenSupOfLeastUpperBoundProperty h s =
      chosenSupOfLeastUpperBoundProperty h (∅ : Set X) := by
  -- Both sets select the common fallback branch.
  have hsinvalid : ¬ (s.Nonempty ∧ BddAbove s) := fun hvalid ↦ hs hvalid.2
  have hempty : ¬ ((∅ : Set X).Nonempty ∧ BddAbove (∅ : Set X)) :=
    fun hvalid ↦ Set.not_nonempty_empty hvalid.1
  simp only [chosenSupOfLeastUpperBoundProperty, dif_neg hsinvalid, dif_neg hempty]

/-- Helper for Theorem 24.1: every set that is not bounded below receives the
same chosen infimum as the empty set. -/
private lemma chosenInfOfLeastUpperBoundProperty_of_not_bddBelow {X : Type u}
    [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) (s : Set X)
    (hs : ¬ BddBelow s) :
    chosenInfOfLeastUpperBoundProperty h s =
      chosenInfOfLeastUpperBoundProperty h (∅ : Set X) := by
  -- Both sets select the common fallback branch.
  have hsinvalid : ¬ (s.Nonempty ∧ BddBelow s) := fun hvalid ↦ hs hvalid.2
  have hempty : ¬ ((∅ : Set X).Nonempty ∧ BddBelow (∅ : Set X)) :=
    fun hvalid ↦ Set.not_nonempty_empty hvalid.1
  simp only [chosenInfOfLeastUpperBoundProperty, dif_neg hsinvalid, dif_neg hempty]

/-- Helper for Theorem 24.1: a nonempty linear order with the least upper bound
property carries a compatible conditionally complete linear order structure. -/
@[implicit_reducible] private noncomputable def
    conditionallyCompleteLinearOrderOfLeastUpperBoundProperty
    {X : Type u} [LinearOrder X] [Nonempty X] (h : LeastUpperBoundProperty X) :
    ConditionallyCompleteLinearOrder X where
  -- Preserve the original order and add only the chosen set bounds and their specifications.
  __ := ‹LinearOrder X›
  __ := LinearOrder.toLattice
  sSup := chosenSupOfLeastUpperBoundProperty h
  sInf := chosenInfOfLeastUpperBoundProperty h
  isLUB_csSup := chosenSupOfLeastUpperBoundProperty_isLUB h
  isGLB_csInf := chosenInfOfLeastUpperBoundProperty_isGLB h
  csSup_of_not_bddAbove := chosenSupOfLeastUpperBoundProperty_of_not_bddAbove h
  csInf_of_not_bddBelow := chosenInfOfLeastUpperBoundProperty_of_not_bddBelow h

/-- Connected-space instance supplied by Theorem 24.1 for a nontrivial linear continuum. -/
instance instConnectedSpace (L : Type u) [LinearOrder L] [Nontrivial L]
    [TopologicalSpace L] [OrderTopology L] [LinearContinuum L] : ConnectedSpace L := by
  -- Expose the continuum's supremum invariant through mathlib's completeness interface.
  let originalOrder : LinearOrder L := inferInstance
  letI : ConditionallyCompleteLinearOrder L :=
    conditionallyCompleteLinearOrderOfLeastUpperBoundProperty
      LinearContinuum.leastUpperBoundProperty
  letI : LinearOrder L := originalOrder
  -- The whole carrier is order-convex, hence preconnected in the order topology.
  rw [connectedSpace_iff_univ]
  refine ⟨Set.univ_nonempty, ?_⟩
  exact Set.ordConnected_univ.isPreconnected

/-- Theorem 24.1: Every nonempty order-convex subset of a linear continuum is connected;
this includes the whole space, intervals, and rays. -/
theorem isConnected_of_ordConnected {L : Type u} [LinearOrder L]
    [TopologicalSpace L] [OrderTopology L] [LinearContinuum L] {s : Set L}
    (hs : s.OrdConnected) (hne : s.Nonempty) : IsConnected s := by
  -- A point of the subset supplies the carrier needed by the completeness bridge.
  let originalOrder : LinearOrder L := inferInstance
  letI : Nonempty L := ⟨hne.some⟩
  letI : ConditionallyCompleteLinearOrder L :=
    conditionallyCompleteLinearOrderOfLeastUpperBoundProperty
      LinearContinuum.leastUpperBoundProperty
  letI : LinearOrder L := originalOrder
  -- Order-convexity gives preconnectedness, and the given witness gives nonemptiness.
  exact ⟨hne, hs.isPreconnected⟩

end LinearContinuum
