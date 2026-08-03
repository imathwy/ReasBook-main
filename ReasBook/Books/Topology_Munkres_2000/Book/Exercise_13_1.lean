module

import Mathlib.Topology.Closure

universe u

/- Exercise 13.1: A subset is open if each of its points lies in an open subset
contained in it. -/
#check fun {X : Type u} [TopologicalSpace X] {A : Set X}
    (h : ∀ x ∈ A, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ A) ↦
  isOpen_iff_forall_mem_open.mpr fun x hx ↦ by
    obtain ⟨U, hU, hxU, hUA⟩ := h x hx
    exact ⟨U, hUA, hU, hxU⟩
