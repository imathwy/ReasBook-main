import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Sites.Hypercover.One

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {X : C}

/- Lemma 25.5.1: for a `1`-hypercover `K` of `X` and a sheaf `ℱ` of abelian groups on `J`, the
canonical degree-zero comparison diagram `K.multifork ℱ` is limiting. This is exactly the
source-facing `AddCommGrpCat` specialization of mathlib's canonical owner
`GrothendieckTopology.OneHypercover.isLimitMultifork`, so the faithful refinement is a thin
specialization theorem rather than a heavier local wrapper. -/
theorem oneHypercover_multifork_isLimit
    (K : J.OneHypercover X) (ℱ : Sheaf J AddCommGrpCat.{max u v}) :
    IsLimit (K.multifork ℱ) :=
  K.isLimitMultifork ℱ

end CategoryTheory
