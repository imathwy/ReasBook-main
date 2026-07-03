import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_2_1 (from Chap18) -/
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
  `TopCat.Presheaf`,
  `functorCategoryHasLimitsOfShape`,
  `functorCategoryHasColimitsOfShape`,
  `evaluation_preservesLimitsOfShape`;
- best owner abstraction: the canonical functor-category (co)limit instances together with the
  canonical evaluation-functor preservation instances, with the source-facing project notation
  `PAb(C)` for the underlying owner `Cᵒᵖ ⥤ AddCommGrpCat`.

Primitive-vs-derived split:
- primitive data: `J`-shaped limits and colimits in `AddCommGrpCat`;
- derived API: the induced `HasLimitsOfShape` / `HasColimitsOfShape` instances on
  `PAb(C)` and the corresponding pointwise preservation statements for evaluation.

Source/core/bridge triage:
- `source-facing`: the Stacks category `PAb(C)` of abelian presheaves on `C` admits `J`-shaped
  limits and colimits, and sections over `U` preserve them;
- `core/canonical`: the generic functor-category owner instances and evaluation-preservation
  instances in `CategoryTheory.Limits`;
- `bridge/view`: the source-facing notation `PAb(C)` and its specialization of those owners to
  `Cᵒᵖ ⥤ AddCommGrpCat`. -/

/- The source-facing Stacks notation for the category of abelian presheaves on `C` is `PAb(C)`,
implemented by the canonical functor category `Cᵒᵖ ⥤ AddCommGrpCat`. -/
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
