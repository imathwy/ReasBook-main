import Mathlib.AlgebraicGeometry.Sites.Representability
import StacksProject_2024.Chap26.Definition_26_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Opposite

universe v w

namespace CategoryTheory

-- Semantic recall: `lean_leansearch` surfaced the canonical owner theorem
-- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`. The source-facing hypotheses
-- in Definition 26.15.3 are a sheaf condition on `F`, a family of subfunctors `H i`,
-- representability of each `H i`, representability by open immersions, and the local cover
-- predicate `Subfunctor.covers H`, so this item is best stated as the direct bridge from those
-- source predicates to the canonical representability conclusion `F.IsRepresentable`.

/-- Lemma 26.15.4: a contravariant set-valued functor on schemes is representable if it is a
Zariski sheaf and admits a covering family of representable subfunctors whose inclusions are
representable by open immersions. -/
@[stacks 01JJ]
theorem isRepresentable_of_zariskiSheaf_of_openImmersionSubfunctorCover
    (F : Schemeᵒᵖ ⥤ Type v) (hFsheaf : Presheaf.IsSheaf Scheme.zariskiTopology F)
    {I : Type w} (H : I → Subfunctor F)
    (hHrep : ∀ i, (H i).toFunctor.IsRepresentable)
    (hHopen : ∀ i, (H i).isRepresentableByOpenImmersions)
    (hHcover : Subfunctor.covers H) :
    F.IsRepresentable := sorry

end CategoryTheory
