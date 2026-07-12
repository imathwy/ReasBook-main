import StacksProject_2024.Chap21.Definition_21_8_1

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : C)

variable [HasFiniteProducts (Over U)]
variable [HasProducts AddCommGrpCat.{v}]
variable {ι : Type w} (family : ι → Over U)

/-
Domain-style sampling for 21.9.0.1:
- primary domain: Čech complexes of abelian presheaves on `C` attached to a family of morphisms
  `family : ι → Over U` with fixed target `U`;
- sampled relevant declarations:
  `CategoryTheory.cechComplexFunctor`,
  `CategoryTheory.restrictPresheafToOver`,
  `cechComplex U family`,
  `cechCohomology U family`;
- best owner abstraction: the `core/canonical` owner remains `CategoryTheory.cechComplexFunctor`
  on `Over U`, while the correct `source-facing` owner here is the restriction-plus-Čech functor
  on abelian presheaves on `C`;
- primitive data: the object `U`, the family `family : ι → Over U`, and an abelian presheaf on
  `C`;
- derived API: objectwise evaluation gives `cechComplex U family`, and homology gives
  `cechCohomology U family`.

Source/core/bridge triage:
- `source-facing`: the functor sending an abelian presheaf `F` on `C` to its Čech complex
  attached to `family`;
- `core/canonical`: `CategoryTheory.cechComplexFunctor`;
- `bridge/view`: `CategoryTheory.restrictPresheafToOver`.
-/

/-- 21.9.0.1: the functor sending an abelian presheaf `F` on `C` to the Čech complex
`cechComplex U family F`, obtained by first applying `restrictPresheafToOver U` and then the
canonical Čech-complex functor on `Over U`. -/
@[stacks 03AP]
abbrev cechComplexOnPresheaves :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex AddCommGrpCat.{v} ℕ :=
  restrictPresheafToOver U ⋙ cechComplexFunctor family

/-- Evaluating the functor of `21.9.0.1` at a presheaf recovers the Čech complex of
`Definition 21.8.1`. -/
@[simp] theorem cechComplexOnPresheaves_obj
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (cechComplexOnPresheaves U family).obj F = cechComplex U family F :=
  rfl

/-- In degree `p`, the complex of `21.9.0.1` is the product of the values of `F` on the
degree-`p` iterated Čech intersections of `family`. -/
@[simp] theorem cechComplexOnPresheaves_obj_X
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (p : ℕ) :
    ((cechComplexOnPresheaves U family).obj F).X p =
      ∏ᶜ fun i : cechCoverIntersectionIndex (FormalCoproduct.mk _ family) p ↦
        F.obj (Opposite.op (cechCoverIntersectionObject (FormalCoproduct.mk _ family) p i)) :=
  rfl

/-- The morphism part of the Čech-complex functor on presheaves is obtained by first restricting
the natural transformation to `Over U` and then applying the canonical Čech-complex functor. -/
@[simp] theorem cechComplexOnPresheaves_map
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) :
    (cechComplexOnPresheaves U family).map α =
      (cechComplexFunctor family).map ((restrictPresheafToOver U).map α) :=
  rfl

/-- The degree-`i` homology of the functor of `21.9.0.1` is the Čech cohomology object of
`Definition 21.8.1`. -/
@[simp] theorem cechComplexOnPresheaves_obj_homology
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (i : ℕ) :
    ((cechComplexOnPresheaves U family).obj F).homology i = cechCohomology U family F i :=
  rfl

end CategoryTheory
