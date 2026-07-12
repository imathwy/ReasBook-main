import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

scoped notation "PAb(" C ")" => Cᵒᵖ ⥤ AddCommGrpCat

end CategoryTheory

open scoped CategoryTheory

universe u v u₁ v₁

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable (U : C)

/- Domain-style sampling for Lemma 18.2.1:
- primary domain: (co)limits in the abelian-presheaf category `PAb(C)`;
- inspected owner declarations:
  `Cᵒᵖ ⥤ AddCommGrpCat`,
  `functorCategoryHasLimitsOfShape`,
  `functorCategoryHasColimitsOfShape`,
  `evaluation_preservesLimitsOfShape`,
  `evaluation_preservesColimitsOfShape`;
- best owner abstraction: the canonical functor category `Cᵒᵖ ⥤ AddCommGrpCat` together with its
  generic (co)limit instances and the canonical evaluation-functor preservation instances; the
  source-facing project notation `PAb(C)` is a bridge to that owner, not a second owner.

Primitive-vs-derived split:
- primitive data: `J`-shaped limits and colimits in `AddCommGrpCat`;
- derived API: the induced `HasLimitsOfShape` / `HasColimitsOfShape` instances on
  `Cᵒᵖ ⥤ AddCommGrpCat`, together with the source-facing notation specialization `PAb(C)` and the
  corresponding pointwise preservation statements for evaluation.

Source/core/bridge triage:
- `source-facing`: the Stacks category `PAb(C)` of abelian presheaves on `C` admits `J`-shaped
  limits and colimits, and sections over `U` preserve them;
- `core/canonical`: the functor category `Cᵒᵖ ⥤ AddCommGrpCat` together with the generic
  functor-category owner instances and evaluation-preservation instances in
  `CategoryTheory.Limits`;
- `bridge/view`: the source-facing notation `PAb(C)` for `Cᵒᵖ ⥤ AddCommGrpCat`. -/

/- The canonical owner is the functor category `Cᵒᵖ ⥤ AddCommGrpCat`. -/
#check (Cᵒᵖ ⥤ AddCommGrpCat)

/- The source-facing Stacks notation for the same owner is `PAb(C)`. -/
#check (PAb(C))

/- Lemma 18.2.1: abelian presheaves on `C`, written `PAb(C)`, admit `J`-shaped limits. This is
the canonical functor-category limit instance specialized to `PAb(C)`. -/
recall functorCategoryHasLimitsOfShape

#check
  (inferInstance : HasLimitsOfShape J (PAb(C)))

/- Abelian presheaves on `C` also admit `J`-shaped colimits by the same canonical functor-category
construction. -/
recall functorCategoryHasColimitsOfShape

#check
  (inferInstance : HasColimitsOfShape J (PAb(C)))

/- Taking sections over `U` is evaluation at `op U`, and evaluation preserves `J`-shaped limits in
any functor category. -/
recall evaluation_preservesLimitsOfShape

#check
  (inferInstance :
    PreservesLimitsOfShape J ((evaluation Cᵒᵖ AddCommGrpCat).obj (op U)))

/- Taking sections over `U` also preserves `J`-shaped colimits, again by the canonical
functor-category evaluation instance. -/
recall evaluation_preservesColimitsOfShape

#check
  (inferInstance :
    PreservesColimitsOfShape J ((evaluation Cᵒᵖ AddCommGrpCat).obj (op U)))
