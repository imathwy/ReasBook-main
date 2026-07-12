import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Limits
open Opposite

variable {C : Type u} [Category.{v} C]

section

variable {U : C} [HasFiniteProducts (Over U)]

/-- The index type of the degree-`n` iterated Čech intersections of a covering `cover` of `U`. -/
abbrev cechCoverIntersectionIndex (cover : FormalCoproduct (Over U)) (n : ℕ) :=
  (cover.cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying object of `C` of the `i`-th degree-`n` Čech intersection of a covering
`cover` of `U`; this is the iterated fibre product of the corresponding members of the covering
over `U`. -/
abbrev cechCoverIntersectionObject (cover : FormalCoproduct (Over U)) (n : ℕ)
    (i : cechCoverIntersectionIndex cover n) : C :=
  ((cover.cech.obj (op (SimplexCategory.mk n))).obj i).left

end

/- Domain-style sampling for Definition 21.8.1:
- primary domain: Čech complexes and Čech cohomology of abelian presheaves on the slice category
  `Over U`, obtained by restricting a presheaf on `C` along the localization functor
  `Over.forget U : Over U ⥤ C`;
- sampled canonical declarations:
  `CategoryTheory.cechComplexFunctor`,
  `CategoryTheory.restrictPresheafToOver`,
  `HomologicalComplex.homologyFunctor`,
  the canonical precomposition owner from `Remark_7_25_10`;
- best owner abstraction: the core/canonical owner is `CategoryTheory.cechComplexFunctor`, while
  restriction to the slice category is the thin reusable bridge `restrictPresheafToOver U`.

Source/core/bridge triage:
- `source-facing`: the Čech complex and its degree-`i` cohomology for a family
  `family : ι → Over U`;
- `core/canonical`: `CategoryTheory.cechComplexFunctor`;
- `bridge/view`: `CategoryTheory.restrictPresheafToOver`.

Primitive data versus derived API:
- primitive data: `U`, the family `family : ι → Over U`, and the abelian presheaf `F`;
- derived API: the restricted presheaf on `Over U`, the resulting Čech complex, and its homology.

The refinement therefore keeps the source-facing names `cechComplex` and `cechCohomology`, and
exposes the thin reusable bridge `restrictPresheafToOver U` for restriction to `Over U`.
-/

section

variable (U : C)

/-- Restriction of an abelian presheaf on `C` to the slice category `Over U`, given by
precomposition with `(Over.forget U).op`. -/
abbrev restrictPresheafToOver :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{v}).obj (Over.forget U).op

@[simp] theorem restrictPresheafToOver_obj
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (restrictPresheafToOver U).obj F = (Over.forget U).op ⋙ F :=
  rfl

@[simp] theorem restrictPresheafToOver_obj_obj
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (V : Over U) :
    ((restrictPresheafToOver U).obj F).obj (op V) = F.obj (op V.left) :=
  rfl

@[simp] theorem restrictPresheafToOver_obj_map
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) {V W : Over U} (f : V ⟶ W) :
    ((restrictPresheafToOver U).obj F).map f.op = F.map f.left.op :=
  rfl

@[simp] theorem restrictPresheafToOver_map
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) :
    (restrictPresheafToOver U).map α = (Over.forget U).op.whiskerLeft α :=
  rfl

@[simp] theorem restrictPresheafToOver_map_app
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) (V : Over U) :
    ((restrictPresheafToOver U).map α).app (op V) = α.app (op V.left) :=
  rfl

end

section

variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w}
variable [HasProducts AddCommGrpCat.{v}]

/-- Definition 21.8.1: for a family `family : ι → Over U` and an abelian presheaf `F` on `C`,
the associated Čech complex is the Čech complex of the restricted presheaf on the slice category
`Over U`; its cohomology groups are written `cechCohomology U family F i`. -/
@[stacks 03AM]
abbrev cechComplex (family : ι → Over U) (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  (cechComplexFunctor family).obj ((restrictPresheafToOver U).obj F)

/-- The degree-`i` Čech cohomology group of the abelian presheaf `F` with respect to the family
`family : ι → Over U`. -/
abbrev cechCohomology
    (family : ι → Over U) (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (i : ℕ) :
    AddCommGrpCat.{v} :=
  (cechComplex U family F).homology i

/-- The source-facing Čech cohomology owner is the degree-`i` homology object of the associated
Čech complex. -/
@[simp] theorem cechComplex_homology
    (family : ι → Over U) (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (i : ℕ) :
    (cechComplex U family F).homology i = cechCohomology U family F i :=
  rfl

end

end CategoryTheory
