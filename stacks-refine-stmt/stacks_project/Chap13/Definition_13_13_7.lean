import Mathlib
import stacks_project.Chap13.Lemma_13_13_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)] [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/- Domain-style sampling for Definition `13.13.7`.
- primary domain: bounded full subcategories of the filtered derived category cut out by the
  cohomological boundedness of the single associated graded object in `D(Gr(\mathcal A))`;
- sampled owner declarations:
  `filteredDerivedCategory`,
  `gr`,
  `t.plus`,
  `t.bounded`;
- best owner abstraction: the source-facing owners are the bounded full subcategories of the
  chapter owner `filteredDerivedCategory 𝒜`, cut out by pulling back the canonical boundedness
  owners on `D(Gr(\mathcal A))` along the associated-graded functor
  `gr : DF(𝒜) ⥤ D(Gr(𝒜))` from Lemma `13.13.6`;
- primitive data: the canonical boundedness owners `t.plus`, `t.minus`, and `t.bounded` on
  `D(GradedObject ℤ 𝒜)`, together with the canonical bridge
  `gr`;
- derived API: the pulled-back boundedness predicates on `DF(𝒜)`, kept as the reusable
  bridge/view owners for downstream restriction functors, and the bounded full subcategories
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the bounded-below, bounded-above, and bounded filtered derived categories
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)`;
- `core/canonical`: the chapter owner `filteredDerivedCategory 𝒜`, the boundedness owners
  `t.plus`, `t.minus`, and `t.bounded` on `D(GradedObject ℤ 𝒜)`;
- `bridge/view`: the associated-graded bridge `gr : DF(𝒜) ⥤ D(Gr(𝒜))`;
  the further comparison `filteredDerivedGradedFunctor : DF(𝒜) ⥤ Gr(D(𝒜))` is only a derived
  graded-piece view, not the owner used to define boundedness here.

This item therefore keeps the actual chapter owner `DF(𝒜)` at the public surface and uses the
associated-graded functor to `D(Gr(\mathcal A))` as bridge data, rather than replacing the source
definition by the weaker degreewise condition in `Gr(D(\mathcal A))`. -/

local notation "DGr" => DerivedCategory (GradedObject ℤ 𝒜)

variable (𝒜) in
/- Companion recall: the filtered derived category `DF(𝒜)` is the canonical owner from
Definition `13.13.5`. -/
#check (DF(𝒜))

variable (𝒜) in
/-- The bounded-below object property on `DF(𝒜)` cut out by the canonical bounded-below
owner `t.plus` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedPlusProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.plus : ObjectProperty DGr).inverseImage
    (filteredDerivedAssociatedGradedFunctor : DF(𝒜) ⥤ DGr)

variable (𝒜) in
/-- The bounded-above object property on `DF(𝒜)` cut out by the canonical bounded-above
owner `t.minus` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedMinusProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.minus : ObjectProperty DGr).inverseImage
    (filteredDerivedAssociatedGradedFunctor : DF(𝒜) ⥤ DGr)

variable (𝒜) in
/-- The bounded object property on `DF(𝒜)` cut out by the canonical boundedness owner
`t.bounded` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedBoundedProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.bounded : ObjectProperty DGr).inverseImage
    (filteredDerivedAssociatedGradedFunctor : DF(𝒜) ⥤ DGr)

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
/-- The bounded filtered derived category `DFᵇ(𝒜)` cut out by associated graded objects in
`Dᵇ(Gr(\mathcal A))`. This is a single bounded condition on `gr(X)` in `D(Gr(\mathcal A))`,
not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedBoundedProperty 𝒜).FullSubcategory

scoped notation "DF⁺(" A:arg ")" => boundedBelowFilteredDerivedCategory A
scoped notation "DF⁻(" A:arg ")" => boundedAboveFilteredDerivedCategory A
scoped notation "DFᵇ(" A:arg ")" => boundedFilteredDerivedCategory A

/- Definition `13.13.7`: the chapter owners `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)` are the bounded
full subcategories of `DF(𝒜)` cut out by the canonical associated-graded functor
`gr : DF(𝒜) ⥤ D(Gr(\mathcal A))` from Lemma `13.13.6`. -/
#check (filteredDerivedPlusProperty 𝒜)
#check (filteredDerivedMinusProperty 𝒜)
#check (filteredDerivedBoundedProperty 𝒜)
#check (DF⁺(𝒜))
#check (DF⁻(𝒜))
#check (DFᵇ(𝒜))

end CategoryTheory
