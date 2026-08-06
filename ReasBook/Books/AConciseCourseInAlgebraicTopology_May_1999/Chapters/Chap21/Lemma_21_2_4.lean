import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Definition_21_2_2

open AlgebraicTopology
open ROrientedManifold
open scoped Manifold

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable {M' : Type} [TopologicalSpace M'] [ChartedSpace H M'] [CompactSpace M']
variable [Fact (Module.finrank ℝ E = n)]

namespace ROrientedManifold

/-- An orientation `oSum` on `M ⊕ M'` is induced from orientations `o` and `o'` on the two
summands when its canonical fundamental class is the sum of the two canonical fundamental classes
pushed forward along the canonical coproduct inclusions in `TopCat`. -/
def IsDisjointUnionOrientation
    (o : ROrientedManifold ℤ I n M)
    (o' : ROrientedManifold ℤ I n M')
    (oSum : ROrientedManifold ℤ I n (M ⊕ M')) : Prop :=
  let F : CategoryTheory.Functor TopCat (ModuleCat ℤ) :=
    (singularHomologyFunctor (ModuleCat ℤ) n).obj (constantCoefficientModule ℤ)
  let inl : TopCat.of M ⟶ TopCat.of (M ⊕ M') := TopCat.ofHom ⟨Sum.inl, by fun_prop⟩
  let inr : TopCat.of M' ⟶ TopCat.of (M ⊕ M') := TopCat.ofHom ⟨Sum.inr, by fun_prop⟩
  canonicalRFundamentalClass oSum =
    F.map inl (canonicalRFundamentalClass o) + F.map inr (canonicalRFundamentalClass o')

end ROrientedManifold

/-- Lemma 21.2.4. If `oSum` is the orientation on `M ⊕ M'` induced from the given orientations of
the two summands, then the index is additive under disjoint union.

The current Chapter 20 orientation API does not yet export an atlas-level constructor
`ROrientedManifold.disjointUnion`, so the induced orientation is recorded here by the
source-faithful predicate `ROrientedManifold.IsDisjointUnionOrientation`: the canonical
fundamental class of `oSum` is the sum of the canonical fundamental classes of the two summands
pushed forward along the coproduct inclusions. The statement remains directly in terms of
Definition 21.2.2's owner `manifoldIndex`.
-/
theorem manifoldIndex_disjointUnion
    (o : ROrientedManifold ℤ I n M)
    (o' : ROrientedManifold ℤ I n M')
    (oSum : ROrientedManifold ℤ I n (M ⊕ M'))
    (hoSum : ROrientedManifold.IsDisjointUnionOrientation o o' oSum) :
    manifoldIndex oSum = manifoldIndex o + manifoldIndex o' := by
  sorry

end
