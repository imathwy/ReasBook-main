import chapter1_reference_format.Chap01.Definition_1_1_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u}

/- Definition 1.7.8: for an equivalence relation `r` on `S`, an equivalence class is a subset
`C ∈ r.classes`, equivalently a subset of the form `{ y | r y x }` for some `x : S`; any element
of such a class is called a representative of that class. -/
recall Setoid.classes (r : Setoid S) : Set (Set S)
