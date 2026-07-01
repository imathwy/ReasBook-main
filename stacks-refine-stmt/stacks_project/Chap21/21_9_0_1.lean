import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Tactic.Recall

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {ι : Type w} (U : ι → C)

/-
Domain-style sampling for 21.9.0.1:
- primary domain: Čech complexes of presheaves valued in a preadditive category;
- sampled relevant declarations:
  `CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor`,
  `CategoryTheory.cechComplexFunctor`,
  `CategoryTheory.cechComplex`,
  `CategoryTheory.cechComplexOnAbelianSheaves`;
- best owner abstraction: the core/canonical owner is the general mathlib functor
  `CategoryTheory.cechComplexFunctor`, with the present item just its specialization to
  `AddCommGrpCat`;
- primitive data: a category `C` with finite products, an index type `ι`, and a family
  `U : ι → C`;
- derived API: the specialization from a general preadditive target category to abelian groups,
  and the downstream slice-site/sheaf variants built from this owner.

Source/core/bridge triage:
- `source-facing`: the abelian-presheaf Čech complex functor attached to `U`;
- `core/canonical`: `CategoryTheory.cechComplexFunctor`;
- `bridge/view`: the specialization `A := AddCommGrpCat`, with no extra mathematics and hence no
  separate owner.
-/

/- 21.9.0.1: the canonical owner of the Čech complex construction is
`CategoryTheory.cechComplexFunctor`. -/
recall cechComplexFunctor

/- For a family `U : ι → C`, the source-facing abelian-group version is exactly the specialization
of that owner to `AddCommGrpCat`. -/
#check (cechComplexFunctor U : (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ CochainComplex AddCommGrpCat ℕ)
