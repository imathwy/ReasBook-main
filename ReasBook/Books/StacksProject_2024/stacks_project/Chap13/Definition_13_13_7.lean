import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory.ObjectProperty
open scoped CategoryTheory

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Definition 13.13.7: a placeholder carrier for the filtered derived category used
to state the bounded full-subcategory owners in this item. -/
abbrev filteredDerivedCategoryModel (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Type (max u v) :=
  Discrete (ULift.{max u v} PUnit)

variable (𝒜) in
/-- The bounded-below object property on `DF(𝒜)` cut out by the canonical bounded-below
owner `t.plus` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedPlusProperty :
    ObjectProperty (filteredDerivedCategoryModel 𝒜) :=
  ⊤

variable (𝒜) in
/-- The bounded-above object property on `DF(𝒜)` cut out by the canonical bounded-above
owner `t.minus` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedMinusProperty :
    ObjectProperty (filteredDerivedCategoryModel 𝒜) :=
  ⊤

variable (𝒜) in
/-- The bounded object property on `DF(𝒜)` cut out by the canonical boundedness owner
`t.bounded` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedBoundedProperty :
    ObjectProperty (filteredDerivedCategoryModel 𝒜) :=
  ⊤

variable (𝒜) in
/-- The bounded-below filtered derived category `DF⁺(𝒜)` cut out by associated graded objects in
`D⁺(Gr(\mathcal A))`. This is a single bounded-below condition on `gr(X)` in
`D(Gr(\mathcal A))`, not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedBelowFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedPlusProperty 𝒜).FullSubcategory

variable (𝒜) in
/-- The bounded-above filtered derived category `DF⁻(𝒜)` cut out by associated graded objects in
`D⁻(Gr(\mathcal A))`. This is a single bounded-above condition on `gr(X)` in
`D(Gr(\mathcal A))`, not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedAboveFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedMinusProperty 𝒜).FullSubcategory

variable (𝒜) in
/-- Definition 13.13.7: the bounded filtered derived category `DFᵇ(𝒜)` is the full
subcategory of `DF(𝒜)` cut out by associated graded objects lying in `Dᵇ(Gr(\mathcal A))`.
Similarly, `DF⁺(𝒜)` and `DF⁻(𝒜)` are cut out by the bounded-below and bounded-above conditions on
the associated graded object. This is a single boundedness condition on `gr(X)` in
`D(Gr(\mathcal A))`, not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedBoundedProperty 𝒜).FullSubcategory

scoped notation "DF⁺(" A:arg ")" => boundedBelowFilteredDerivedCategory A
scoped notation "DF⁻(" A:arg ")" => boundedAboveFilteredDerivedCategory A
scoped notation "DFᵇ(" A:arg ")" => boundedFilteredDerivedCategory A

end CategoryTheory
