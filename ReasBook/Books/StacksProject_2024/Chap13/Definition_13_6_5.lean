import Mathlib
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v₁ v₂ u₁ u₂

/-
Domain-style sampling for Definition 13.6.5:
- primary domain: strictly full triangulated subcategories cut out as kernels of exact or
  homological functors;
- sampled owner declarations:
  `Functor.kernel`,
  `Functor.homologicalKernel`,
  `ObjectProperty.IsTriangulated`,
  `Pretriangulated P.FullSubcategory`;
- best owner abstraction: the kernel object property attached to the functor itself, namely
  `Functor.kernel` in the exact-functor case and `Functor.homologicalKernel` in the homological
  case;
- primitive data:
  for `Functor.kernel`, only the functor `F : D ⥤ D'`;
  for `Functor.homologicalKernel`, only the functor `H : D ⥤ A` together with the shift on the
  source category;
- derived API: closure under isomorphisms, stability under retracts, triangulated structure on the
  object property, and the induced pretriangulated/triangulated structures on the full
  subcategory.

Source/core/bridge triage:
- `source-facing`: the kernel subcategory attached to an exact functor, and the vanishing
  subcategory attached to a homological functor;
- `core/canonical`: `Functor.kernel` and `Functor.homologicalKernel`;
- `bridge/view`: the corresponding full subcategories
  `F.kernel.FullSubcategory` and `H.homologicalKernel.FullSubcategory`, together with their
  induced triangulated structures.

No local wrapper is needed here: Definition 13.6.5 is a pure recall of the canonical owner
declarations already used by Lemmas 13.6.2 and 13.6.3.
-/

section

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D']
variable (F : D ⥤ D')

/- Definition 13.6.5: for an exact functor `F : D ⥤ D'`, the kernel subcategory is the canonical
object property `F.kernel`, and its source-facing realization is the full subcategory
`F.kernel.FullSubcategory`; the exactness hypotheses only enter the derived triangulated closure
results of Lemma 13.6.2. -/
recall Functor.kernel
#check F.kernel.FullSubcategory

end

section

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A]
variable (H : D ⥤ A)

/- Companion recall: for a homological functor `H : D ⥤ A`, the kernel subcategory is the
canonical object property `H.homologicalKernel`, and its source-facing realization is the full
subcategory `H.homologicalKernel.FullSubcategory`; the homological and abelian hypotheses only
enter the derived closure results recalled in Lemma 13.6.3. -/
recall Functor.homologicalKernel
#check H.homologicalKernel.FullSubcategory

end
