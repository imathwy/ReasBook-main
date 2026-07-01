import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (L : Type u) [Field L]

/- Definition 1.2.4: if `L` is a field, a subfield of `L` is the canonical bundled owner
`Subfield L`. The field structure on the subfield and the resulting extension structure on `L` are
derived from this owner, rather than stored as separate primitive data. -/
#check (Subfield L)

section

variable {L : Type u} [Field L] (S : Subfield L)

/- A subfield carries its field structure by restriction from the ambient field. -/
#check (inferInstance : Field S)

/- The ambient field `L` is canonically a field extension of the subfield `S`. -/
#check (inferInstance : Algebra S L)

end
