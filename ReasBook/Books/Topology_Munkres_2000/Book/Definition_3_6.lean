module

public import Topology_Munkres_2000.Book.Definition_3_5

universe u

public section

variable {α : Type u} {A : Set α}

open Setoid

/- Definition 3.6: A partition determines the canonical equivalence relation
whose related elements lie in the same block. -/
#check mkClasses

/-- Two elements are related by `Setoid.mkClasses` exactly when they lie in a
common block. -/
theorem Setoid.mkClasses_rel_iff (D : Set (Set A))
    (hD : ∀ x, ∃! d ∈ D, x ∈ d) (x y : A) :
    mkClasses D hD x y ↔ ∃ d ∈ D, x ∈ d ∧ y ∈ d := by
  constructor
  · intro h
    obtain ⟨d, ⟨hd, hx⟩, _⟩ := hD x
    exact ⟨d, hd, hx, h d hd hx⟩
  · rintro ⟨d, hd, hx, hy⟩ s hs hxs
    rw [(hD x).unique ⟨hs, hxs⟩ ⟨hd, hx⟩]
    exact hy

/- The equivalence classes of the constructed relation are the original blocks. -/
#check classes_mkClasses

end
