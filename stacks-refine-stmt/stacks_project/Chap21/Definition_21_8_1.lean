import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

/- Domain-style sampling for Definition 21.8.1:
- primary domain: Čech complexes and Čech cohomology of abelian presheaves on the slice category
  `Over U`, obtained by restricting a presheaf on `C` along the localization functor
  `Over.forget U : Over U ⥤ C`;
- sampled canonical declarations:
  `CategoryTheory.cechComplexFunctor`,
  `(Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat).obj (Over.forget U).op`,
  `HomologicalComplex.homologyFunctor`,
  `#check (whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type (max u v))).obj (Over.forget U).op`
  from `Remark_7_25_10`;
- best owner abstraction: the core/canonical owner is `CategoryTheory.cechComplexFunctor`, while
  restriction to the slice category is the existing precomposition owner along `(Over.forget U).op`
  rather than a new public wrapper.

Source/core/bridge triage:
- `source-facing`: the Čech complex and its degree-`i` cohomology for a family
  `family : ι → Over U`;
- `core/canonical`: `CategoryTheory.cechComplexFunctor`;
- `bridge/view`: precomposition with `(Over.forget U).op`.

Primitive data versus derived API:
- primitive data: `U`, the family `family : ι → Over U`, and the abelian presheaf `F`;
- derived API: the restricted presheaf on `Over U`, the resulting Čech complex, and its homology.

The refinement therefore keeps the source-facing names `cechComplex` and `cechCohomology`, but
deletes the redundant public restriction-functor wrapper and reuses the canonical owners directly.
-/

/-- Definition 21.8.1: for a family `family : ι → Over U` and an abelian presheaf `F` on `C`,
the associated Čech complex is the Čech complex of the restricted presheaf on the slice category
`Over U`; its cohomology groups are written `cechCohomology U family F i`. -/
abbrev cechComplex {C : Type u} [Category.{v} C] {ι : Type w} (U : C)
    [HasFiniteProducts (Over U)] (family : ι → Over U) (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    CochainComplex AddCommGrpCat ℕ :=
  (cechComplexFunctor family).obj ((Over.forget U).op ⋙ F)

-- Proof sketch: unfold `cechComplex`; it is defined by applying `cechComplexFunctor` to the
-- restricted presheaf on the slice category `Over U`.
/-- The Čech complex attached to `family` and `F` is the image of the restricted presheaf on
`Over U` under `cechComplexFunctor family`. -/
theorem cechComplex_def {C : Type u} [Category.{v} C] {ι : Type w} (U : C)
    [HasFiniteProducts (Over U)] (family : ι → Over U) (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    cechComplex U family F =
      (cechComplexFunctor family).obj ((Over.forget U).op ⋙ F) :=
  rfl

/-- The degree-`i` Čech cohomology group of the abelian presheaf `F` with respect to the family
`family : ι → Over U`. -/
abbrev cechCohomology {C : Type u} [Category.{v} C] {ι : Type w} (U : C)
    [HasFiniteProducts (Over U)] (family : ι → Over U) (F : Cᵒᵖ ⥤ AddCommGrpCat) (i : ℕ) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
    (cechComplex U family F)

end CategoryTheory
