import StacksProject_2024.Chap12.Definition_12_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

section

variable (P : ObjectProperty C) [P.IsSerreClass]

/- Lemma 12.10.2 is a `bridge/view` item: a LinearRepresentations_Serre_1977 subcategory is, via the chapter owner
abstraction from Definition 12.10.1, a weak LinearRepresentations_Serre_1977 subcategory. The primitive source-facing data
remain `P.IsSerreClass`; strict fullness and exactness are derived later from
`P.IsWeakSerreClass`. -/
recall instIsWeakSerreClassOfIsSerreClass (P : ObjectProperty C) [P.IsSerreClass] :
    P.IsWeakSerreClass

end

end CategoryTheory.ObjectProperty
