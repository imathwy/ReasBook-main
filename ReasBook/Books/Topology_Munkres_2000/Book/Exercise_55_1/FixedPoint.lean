module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction

public section

universe u

namespace Set

variable {X : Type u} [TopologicalSpace X]

/-- Fixed-point existence for continuous self-maps descends from a space to its retracts. -/
theorem IsRetract.exists_fixedPoint {A : Set X} (hA : IsRetract A)
    (hX : ∀ g : C(X, X), ∃ x, Function.IsFixedPt g x) (f : C(A, A)) :
    ∃ x, Function.IsFixedPt f x := by
  rw [isRetract_iff] at hA
  rcases hA with ⟨r, hr⟩
  let g : C(X, X) :=
    ⟨fun x ↦ f (r x), continuous_subtype_val.comp (f.continuous.comp r.continuous)⟩
  obtain ⟨x, hx⟩ := hX g
  refine ⟨r x, ?_⟩
  exact (hr (f (r x))).symm.trans (by simpa [g] using congr_arg r hx)

end Set
