module

public import Topology_Munkres_2000.Book.Theorem_27_1

public section

universe u

/-- Helper for Exercise 27.1: truncating a set below at one of its points
preserves its upper bounds. -/
private lemma upperBounds_inter_Ici_of_mem {α : Type u} [LinearOrder α]
    {s : Set α} {a : α} (ha : a ∈ s) :
    upperBounds (s ∩ Set.Ici a) = upperBounds s := by
  -- An upper bound of the original set plainly bounds its truncation.
  apply Set.Subset.antisymm
  · intro b hb x hx
    -- Compare `x` with the truncation point and use whichever point lies above.
    rcases le_total x a with hxa | hax
    · exact hxa.trans (hb ⟨ha, le_rfl⟩)
    · exact hb ⟨hx, hax⟩
  · intro b hb x hx
    exact hb hx.1

/-- Helper for Exercise 27.1: the closure of a bounded lower truncation is compact. -/
private lemma isCompact_closure_inter_Ici_of_upperBound
    {α : Type u} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [CompactIccSpace α] {s : Set α} {a b : α} (hb : b ∈ upperBounds s) :
    IsCompact (closure (s ∩ Set.Ici a)) := by
  -- First place the truncation inside the compact interval `[a, b]`.
  have hsubset : s ∩ Set.Ici a ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨hx.2, hb hx.1⟩
  -- Closedness of the interval extends this containment to the closure.
  have hclosure : closure (s ∩ Set.Ici a) ⊆ Set.Icc a b :=
    closure_minimal hsubset isClosed_Icc
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hclosure

/-- Exercise 27.1: If every closed interval in an ordered space is compact,
then the space has the least upper bound property. -/
theorem leastUpperBoundProperty_of_compactIccSpace (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [CompactIccSpace X] :
    LeastUpperBoundProperty X := by
  -- Reduce an arbitrary nonempty bounded set to a compact cofinal truncation.
  apply LeastUpperBoundProperty.of_exists_isLUB
  intro s hs hbounded
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hbounded
  have hcompact : IsCompact (closure (s ∩ Set.Ici a)) :=
    isCompact_closure_inter_Ici_of_upperBound hb
  have hnonempty : (closure (s ∩ Set.Ici a)).Nonempty := by
    exact ⟨a, subset_closure ⟨ha, le_rfl⟩⟩
  obtain ⟨c, -, hc⟩ := hcompact.exists_isLUB hnonempty
  -- Closure and truncation preserve upper bounds, so the same point is an LUB of `s`.
  have hupperBounds : upperBounds (closure (s ∩ Set.Ici a)) = upperBounds s := by
    rw [upperBounds_closure, upperBounds_inter_Ici_of_mem ha]
  exact ⟨c, (isLUB_congr hupperBounds).mp hc⟩

/-- In an order topology, compactness of every closed interval is equivalent to
the least upper bound property. -/
theorem compactIccSpace_iff_leastUpperBoundProperty (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] :
    CompactIccSpace X ↔ LeastUpperBoundProperty X := by
  -- The forward implication is the compact-closure argument above.
  constructor
  · intro hcompact
    letI : CompactIccSpace X := hcompact
    exact leastUpperBoundProperty_of_compactIccSpace X
  · intro hlub
    -- The reverse implication is Theorem 27.1, exposed as the canonical instance.
    letI : LeastUpperBoundProperty X := hlub
    infer_instance
