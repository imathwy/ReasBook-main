module

public import Topology_Munkres_2000.Book.Exercise_4_99_5.UltrafilterCardinality
public import Topology_Munkres_2000.Book.Exercise_4_99_5.NovakClosedSet
public import Mathlib.Topology.DerivedSet

public section

open Set

/-- Helper for Exercise 4.99.5: a countably infinite subset of `Ultrafilter ℕ` has a
full-cardinality derived set. -/
lemma ultrafilterNat_derivedSet_cardinalMk (S : Set (Ultrafilter ℕ))
    (hSCountable : S.Countable) (hSInfinite : S.Infinite) :
    Cardinal.mk (derivedSet S) = Cardinal.mk (Ultrafilter ℕ) := by
  -- The closure is an infinite closed set, hence already has full ambient cardinality.
  have hClosureInfinite : (closure S).Infinite :=
    hSInfinite.mono subset_closure
  have hClosureCard :
      Cardinal.mk (closure S) = Cardinal.mk (Ultrafilter ℕ) :=
    ultrafilterNat_closedSet_cardinalMk (closure S) isClosed_closure hClosureInfinite
  have hAmbientUncountable : Cardinal.aleph0 < Cardinal.mk (Ultrafilter ℕ) := by
    rw [cardinalMk_ultrafilterNat]
    exact Cardinal.aleph0_le_continuum.trans_lt (Cardinal.cantor _)
  -- A finite derived set would make the closure countable, contradicting its full cardinality.
  have hDerivedInfinite : (derivedSet S).Infinite := by
    intro hDerivedFinite
    have hClosureCountable : (closure S).Countable := by
      rw [closure_eq_self_union_derivedSet]
      exact hSCountable.union hDerivedFinite.countable
    exact (not_le_of_gt hAmbientUncountable)
      (hClosureCard ▸ hClosureCountable.le_aleph0)
  exact ultrafilterNat_closedSet_cardinalMk (derivedSet S)
    (isClosed_derivedSet S) hDerivedInfinite
