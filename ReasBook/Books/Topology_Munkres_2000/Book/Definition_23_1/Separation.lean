module

public import Mathlib.Topology.Connected.Basic

public section

universe u

namespace Set

/-- Two subsets form a separation when they are disjoint nonempty open sets covering the space. -/
structure IsSeparation {X : Type u} [TopologicalSpace X] (U V : Set X) : Prop where
  isOpen_left : IsOpen U
  isOpen_right : IsOpen V
  disjoint : Disjoint U V
  left_nonempty : U.Nonempty
  right_nonempty : V.Nonempty
  union_eq_univ : U ∪ V = Set.univ

/-- A separation remains a separation after exchanging its two subsets. -/
theorem IsSeparation.symm {X : Type u} [TopologicalSpace X] {U V : Set X}
    (h : U.IsSeparation V) : V.IsSeparation U :=
  ⟨h.isOpen_right, h.isOpen_left, h.disjoint.symm, h.right_nonempty,
    h.left_nonempty, (union_comm V U).trans h.union_eq_univ⟩

end Set

/-- A space is preconnected exactly when it admits no separation. -/
theorem preconnectedSpace_iff_no_separation (X : Type u) [TopologicalSpace X] :
    PreconnectedSpace X ↔ ¬ ∃ U V : Set X, U.IsSeparation V := by
  rw [preconnectedSpace_iff_univ]
  constructor
  · intro h ⟨U, V, hUV⟩
    have hinter := h U V hUV.isOpen_left hUV.isOpen_right
      (by rw [hUV.union_eq_univ]) (by simpa using hUV.left_nonempty)
      (by simpa using hUV.right_nonempty)
    rcases hinter with ⟨x, -, hxU, hxV⟩
    exact Set.disjoint_left.mp hUV.disjoint hxU hxV
  · intro h U V hU hV hcover hUnonempty hVnonempty
    by_contra hinter
    apply h
    refine ⟨U, V, hU, hV, ?_, ?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr fun x hxU hxV ↦ hinter ⟨x, Set.mem_univ x, hxU, hxV⟩
    · simpa using hUnonempty
    · simpa using hVnonempty
    · exact Set.eq_univ_of_univ_subset hcover
