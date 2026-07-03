import Mathlib
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_8_1 (from Chap21) -/
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

/-! ### Lemma_21_8_2 (from Chap21) -/
/- Domain-style sampling for Lemma 21.8.2:
- primary domain: Grothendieck-topology sheaf conditions for abelian presheaves expressed through
  canonical multiequalizer comparison maps.
- inspected canonical declarations:
  `CategoryTheory.Presheaf.IsSheaf`,
  `GrothendieckTopology.Cover.toMultiequalizer`,
  `CategoryTheory.Presheaf.isSheaf_iff_multifork`,
  `CategoryTheory.Presheaf.isSheaf_iff_multiequalizer`;
- owner abstraction: `CategoryTheory.Presheaf.isSheaf_iff_multiequalizer`.
- primitive data: a cover `S : J.Cover X` and a presheaf `F : Cᵒᵖ ⥤ AddCommGrpCat`; the canonical
  map to the multiequalizer is derived from `S` as `S.toMultiequalizer F`.
- derived API: the equivalence between the sheaf predicate and the statement that each
  `S.toMultiequalizer F` is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the Stacks criterion that for every covering sieve the canonical map
  `F(X) → \check{H}^0(\mathcal U, F)` is an isomorphism.
- `core/canonical`: `CategoryTheory.Presheaf.isSheaf_iff_multiequalizer`.
- `bridge/view`: `GrothendieckTopology.Cover.toMultiequalizer`, which packages the source-facing
  comparison map into the canonical multiequalizer morphism.

This item is already a direct recall of the canonical owner theorem, so the refinement stays
recall-shaped rather than rebuilding a parallel local multiequalizer API. -/

/- Lemma 21.8.2: an abelian presheaf `F` on a site is a sheaf if and only if for every covering
sieve `S` of an object `X`, the canonical map from `F(X)` to the corresponding multiequalizer—
which is the library-facing form of the natural map `F(U) → \check{H}^0(\mathcal U, F)`—is an
isomorphism. -/
recall CategoryTheory.Presheaf.isSheaf_iff_multiequalizer
