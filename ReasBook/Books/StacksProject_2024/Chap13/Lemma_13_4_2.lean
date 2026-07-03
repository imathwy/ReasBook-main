import StacksProject_2024.Chap13.Definition_13_3_5
import Mathlib.CategoryTheory.Triangulated.Yoneda

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits Opposite
open scoped Pretriangulated.Opposite

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.2:
- primary domain: represented Hom functors on a pretriangulated category and their
  homological/cohomological exactness;
- sampled declarations:
  `Functor.IsHomological`,
  `preadditiveCoyoneda.obj`,
  `preadditiveYoneda.obj`,
  `Functor.rightOp`;
- best owner abstraction: `Functor.IsHomological`;
- primitive data: only the represented functor itself;
- derived API: the homologicality instances of `preadditiveCoyoneda.obj (op W)` and
  `(preadditiveYoneda.obj W).rightOp`;
- source/core/bridge triage:
  `source-facing`: the contravariant cohomological statement for `preadditiveYoneda.obj W`;
  `core/canonical`: the mathlib `Functor.IsHomological` instances on the represented Hom functors;
  `bridge/view`: the chapter-level generic instance on `Functor.rightOp`, applied to
    `preadditiveYoneda.obj W`.

Both parts of the lemma are therefore direct recall items: the covariant case from mathlib's
represented-Hom owner instance, and the contravariant case from the chapter's generic
`Functor.rightOp` bridge to the same owner. -/

variable (W : D)

/- Lemma 13.4.2 (1): for any object `W` of a pretriangulated category, the covariant Hom functor
`Hom_D(W,-)`, represented by `preadditiveCoyoneda.obj (op W)`, is homological. This is exactly the
canonical instance in `CategoryTheory.Triangulated.Yoneda`. -/
#synth (preadditiveCoyoneda.obj (op W)).IsHomological

/- Lemma 13.4.2 (2): for any object `W` of a pretriangulated category, the contravariant Hom
functor `Hom_D(-,W)`, represented by `preadditiveYoneda.obj W`, is cohomological; equivalently,
its opposite-valued functor is homological. This is likewise already inferable from the canonical
owner infrastructure. -/
#synth (preadditiveYoneda.obj W).rightOp.IsHomological

end CategoryTheory
