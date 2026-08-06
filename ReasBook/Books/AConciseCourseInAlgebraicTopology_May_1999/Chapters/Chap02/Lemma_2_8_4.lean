import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open BasedSpace
open scoped FundamentalGroupoid

noncomputable section

/-- Helper for Lemma 2.8.4: the projection maps induce the canonical product isomorphism on
fundamental groups. -/
-- Proof sketch: apply the inverse functor of the canonical groupoid isomorphism
-- `FundamentalGroupoidFunctor.prodIso X.right Y.right` at the product basepoint.
-- By construction this inverse functor is induced by the two projections
-- `X.right × Y.right ⟶ X.right` and `X.right × Y.right ⟶ Y.right`.
noncomputable def fundamentalGroupMulEquivProd (X Y : BasedSpace) :
    FundamentalGroup (TopCat.of (X.right × Y.right))
        (underTopBasepoint X, underTopBasepoint Y) ≃*
      (FundamentalGroup X.right (underTopBasepoint X) ×
        FundamentalGroup Y.right (underTopBasepoint Y)) :=
  let E : πₓ (TopCat.of (X.right × Y.right)) ≌ Grpd.of (πₓ X.right × πₓ Y.right) :=
    CategoryTheory.Equivalence.mk
      (FundamentalGroupoidFunctor.prodIso X.right Y.right).inv
      (FundamentalGroupoidFunctor.prodIso X.right Y.right).hom
      (eqToIso (FundamentalGroupoidFunctor.prodIso X.right Y.right).inv_hom_id.symm)
      (eqToIso (FundamentalGroupoidFunctor.prodIso X.right Y.right).hom_inv_id)
  E.fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk (underTopBasepoint X, underTopBasepoint Y))

/-- Helper for Lemma 2.8.4: the underlying homomorphism of `fundamentalGroupMulEquivProd` is the
map induced by the two projections from `X × Y`. -/
@[simp] theorem fundamentalGroupMulEquivProd_toMonoidHom (X Y : BasedSpace) :
    (fundamentalGroupMulEquivProd X Y).toMonoidHom =
      MonoidHom.prod
        (FundamentalGroup.map ContinuousMap.fst (underTopBasepoint X, underTopBasepoint Y))
        (FundamentalGroup.map ContinuousMap.snd (underTopBasepoint X, underTopBasepoint Y)) :=
  rfl

/-- Lemma 2.8.4: for based spaces `X` and `Y`, the projection-induced homomorphism
`π₁(X × Y) → π₁(X) × π₁(Y)` is an isomorphism. -/
instance fundamental_group_product_isIso (X Y : BasedSpace) :
    IsIso
      (GrpCat.ofHom
        (MonoidHom.prod
          (FundamentalGroup.map
            ContinuousMap.fst
            (underTopBasepoint X, underTopBasepoint Y))
          (FundamentalGroup.map
            ContinuousMap.snd
            (underTopBasepoint X, underTopBasepoint Y)))) := by
  -- The target map is exactly the hom underlying this canonical product isomorphism.
  rw [← fundamentalGroupMulEquivProd_toMonoidHom X Y]
  let e := fundamentalGroupMulEquivProd X Y
  let i :
      GrpCat.of
          (FundamentalGroup (TopCat.of (X.right × Y.right))
            (underTopBasepoint X, underTopBasepoint Y)) ≅
        GrpCat.of
          (FundamentalGroup X.right (underTopBasepoint X) ×
            FundamentalGroup Y.right (underTopBasepoint Y)) :=
    e.toGrpIso
  change IsIso i.hom
  simpa [i] using (i.isIso_hom : IsIso i.hom)
