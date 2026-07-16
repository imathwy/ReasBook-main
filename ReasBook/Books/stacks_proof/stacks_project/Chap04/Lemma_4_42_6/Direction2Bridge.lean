import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_42_6.SliceRepresentable
import stacks_proof.stacks_project.Chap04.Lemma_4_42_6.Core

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)

variable {C : Type (max u v)} [Category.{v} C]

/-- Specialized absolutization bridge for the diagonal target.  This avoids re-instantiating the
generic rewrite at the final direction `(2) -> (1)` call site. -/
opaque diagonal_slice_isRepresentable_of_twoFibreProduct
    [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct H
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)).IsRepresentable →
      (FibredInGroupoidsMor.sliceTwoFibreProduct
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) H).IsRepresentable := by
  intro h
  apply (isRepresentable_iff_absolutize_isRepresentable _).mpr
  exact absolutize_sliceTwoFibreProduct_isRepresentable_of_twoFibreProduct
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) H h

end CategoryTheory
