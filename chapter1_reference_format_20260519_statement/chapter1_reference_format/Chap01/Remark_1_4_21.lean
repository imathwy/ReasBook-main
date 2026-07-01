import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Submodule
open Module

universe u v

section

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  {s t : Set V}

/- Remark 1.4.21: for an arbitrary `K`-vector space, any linearly independent subset of a
spanning set extends to a basis contained in that spanning set; this noncomputable extension uses
the axiom of choice and is formalized by `Basis.extendLe`. -/
recall Basis.extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
  Basis (hs.extend hst) K V

/- The basis produced by `Basis.extendLe` contains the original linearly independent set. -/
recall Basis.subset_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
  s ⊆ range (Basis.extendLe hs hst ht)

/- The basis produced by `Basis.extendLe` is contained in the ambient spanning set. -/
recall Basis.extendLe_subset (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
  range (Basis.extendLe hs hst ht) ⊆ t

end
