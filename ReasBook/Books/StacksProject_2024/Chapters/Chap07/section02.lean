import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_2_1 (from Chap07) -/
universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 7.2.1:
- primary domain: set-valued presheaves on a category
- sampled canonical declarations:
  `CategoryTheory.Functor`,
  the ambient functor category `Cᵒᵖ ⥤ Type w`,
  the chapter owner `Presheaf C` from Definition 4.3.3,
  the site-level sheaf owner `Sheaf J (Type w)`, whose primitive underlying object is again a
  set-valued presheaf
- best owner abstraction in this chapter/project: `Presheaf C`
- primitive data: only the underlying contravariant functor
- derived API: natural transformations and the inherited category structure from the functor
  category
-/
/-
Source/core/bridge triage for Definition 7.2.1:
- source-facing notion: a set-valued presheaf on `C`
- core/canonical owner in this chapter/project: `Presheaf C`, introduced in Definition 4.3.3
- derived API: the category structure and natural-transformation morphisms are inherited from the
  functor category `Cᵒᵖ ⥤ Type w`
-/
/-
Definition 7.2.1: a presheaf of sets on `C` is the chapter owner `Presheaf C` from
Definition 4.3.3, i.e. a contravariant functor
`Cᵒᵖ ⥤ Type w`.
-/
recall Presheaf

end CategoryTheory

/-! ### Definition_7_2_2 (from Chap07) -/
universe uC vC uA vA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C]
variable (A : Type uA) [Category.{vA} A]

/- Domain-style sampling for Definition 7.2.2:
- primary domain: presheaves as contravariant functors in `CategoryTheory`
- sampled owner declarations:
  the Chapter 4 owner recall `(Cᵒᵖ ⥤ A)` from Definition 4.3.2,
  `NatTrans` and `F ⟶ G` from Definition 4.2.15,
  the specialized chapter owner `Presheaf C` from Definition 4.3.3
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`
- primitive data: only the standard functor data on `Cᵒᵖ`
- derived API: natural transformations and the inherited category structure; `Presheaf C` is only
  the `Type`-valued specialization
-/
/- Source/core/bridge triage for Definition 7.2.2:
- source-facing notion: an `A`-valued presheaf on `C`
- core/canonical owner: the Chapter 4 owner `Cᵒᵖ ⥤ A`
- bridge/view: `Presheaf C` when `A = Type _`
-/
/- Definition 7.2.2 is exactly Definition 4.3.2 in presheaf language: an `A`-valued presheaf on
`C` is an object of the functor category `Cᵒᵖ ⥤ A`. -/
#check (Cᵒᵖ ⥤ A)

/- Companion recall: the primitive data are the usual functor data out of `Cᵒᵖ`. -/
recall Functor

end

end CategoryTheory

/-! ### Remark_7_2_3 (from Chap07) -/
universe u

namespace CategoryTheory

section

variable (C : Type u) [SmallCategory C]
variable (A : Type (u + 1)) [LargeCategory A]

/-
Domain-style sampling for Remark 7.2.3:
- primary domain: presheaf categories as functor categories with inherited size structure
- sampled declarations in this domain:
  `Functor.category`,
  `LargeCategory`,
  the source-facing owner `Cᵒᵖ ⥤ A` from Definition 7.2.2,
  and the set-valued specialization `Presheaf`
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`
- primitive data: none beyond the owner `Cᵒᵖ ⥤ A` already recalled in Definition 7.2.2
- derived API: the inherited category structure `Functor.category` and the induced
  `LargeCategory (Cᵒᵖ ⥤ A)` instance
-/
/-
Source/core/bridge triage for Remark 7.2.3:
- source-facing content: the category of `A`-valued presheaves on `C`
- core/canonical owner: the functor category `Cᵒᵖ ⥤ A`
- derived API recalled here: its canonical category structure `Functor.category` and the induced
  large-category interface
-/
/- Remark 7.2.3: if `A` is one of the ambient large categories from Remark 4.2.2, then the
category of `A`-valued presheaves on a small category `C` is again the canonical functor category.
The new content here is therefore the inherited category structure and size interface on
`Cᵒᵖ ⥤ A`, not a second restatement of its underlying type. -/
recall Functor.category

/- Companion size recall: the presheaf functor category again satisfies the canonical
large-category interface. -/
#check (inferInstance : LargeCategory (Cᵒᵖ ⥤ A))

end

end CategoryTheory
