import stacks_proof.stacks_project.Chap13.Definition_13_3_5
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 13.4.2: the represented covariant Hom functor `Hom_D(W,-)` is homological. -/
lemma represented_coyoneda_is_homological :
    (preadditiveCoyoneda.obj (op W)).IsHomological := by
  -- The source TR3 argument is already packaged upstream as the owner instance for represented
  -- covariant Hom functors, so the proof here is a direct recall.
  infer_instance

/-- Helper for Lemma 13.4.2: the represented contravariant Hom functor is cohomological, written
as homologicality of its opposite-valued covariant view. -/
lemma represented_yoneda_rightOp_is_homological :
    (preadditiveYoneda.obj W).rightOp.IsHomological := by
  -- The chapter bridge `Functor.rightOp.IsHomological` turns the canonical yoneda owner into the
  -- source-facing cohomological statement, so this is again a direct recall.
  infer_instance

/-- Lemma 13.4.2: for any object `W`, the represented covariant Hom functor is homological and the
represented contravariant Hom functor is cohomological. -/
@[stacks 0149]
theorem lemma_13_4_2 :
    (preadditiveCoyoneda.obj (op W)).IsHomological ∧
      (preadditiveYoneda.obj W).rightOp.IsHomological := by
  constructor
  · -- The first half is exactly the owner-level represented coyoneda instance.
    simpa using represented_coyoneda_is_homological (D := D) W
  · -- The second half is the opposite-valued owner view of the represented yoneda functor.
    simpa using represented_yoneda_rightOp_is_homological (D := D) W

end CategoryTheory
