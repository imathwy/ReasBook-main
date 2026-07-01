import stacks_project.Chap12.Lemma_12_19_12

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject.Hom

open FilteredObject

variable {A B : FilteredObject C}

-- Proof sketch: the equivalence `(1) ↔ (2)` is `strict_iff_coimageImageComparison_isIso`, the
-- kernel/coimage and image/cokernel short exact sequences from Lemma `12.19.12` identify `(3)`
-- with `(4)`, `(5)`, and `(6)`, and finiteness of the filtrations lets one recover `(2)` from
-- `(3)` by descending induction on the filtration degree.
/-- Lemma 12.19.13: for a morphism `f : A ⟶ B` of finite filtered objects in an abelian category,
the following are equivalent: `f` is strict; the filtered coimage-image comparison
`coim(f) ⟶ im(f)` is an isomorphism; the induced morphism
`gr(coim(f)) ⟶ gr(im(f))` is an isomorphism; the sequence
`gr(\ker(f)) ⟶ gr(A) ⟶ gr(B)` is exact in every degree; the sequence
`gr(A) ⟶ gr(B) ⟶ gr(\operatorname{coker}(f))` is exact in every degree; and the sequence
`0 ⟶ gr(\ker(f)) ⟶ gr(A) ⟶ gr(B) ⟶ gr(\operatorname{coker}(f)) ⟶ 0` is exact in every
degree. -/
theorem strict_tfae_coimageImageComparison_isIso_and_graded_exactness
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B) :
    List.TFAE
      [ Strict f
      , IsIso (coimageImageComparison f)
      , IsIso (associatedGradedMap (coimageImageComparison f))
      , ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact
      , ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact
      , ∀ p : ℤ,
          (ComposableArrows.mk₅
            (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
            (gradedPieceMap (kernelι f) p)
            (gradedPieceMap f p)
            (gradedPieceMap (toCokernel f) p)
            (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact
      ] := sorry

end FilteredObject.Hom

end CategoryTheory
