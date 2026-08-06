import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_7

noncomputable section

open CategoryTheory Limits
open Topology

namespace CWPairHomologyTheory

/-- A relative cellular model for `(E q).obj P` chooses an absolute CW complex `X`, a subcomplex
`A ⊆ X`, an identification of the pair `(X, A)` with `P`, Chapter 13 relative cellular
differential data on `(X, A)`, and the resulting comparison isomorphism from `E_q(P)` to the
corresponding relative cellular homology group with coefficients in `π`. -/
structure RelativeCellularHomologyModel
    {π : Type} [AddCommGroup π] (E : CWPairHomologyTheory π) (q : ℤ) (P : CWPair) where
  X : TopCat
  [cw : CWComplex (Set.univ : Set X)]
  A : Topology.CWComplex.Subcomplex (Set.univ : Set X)
  pairIso : (⟨X, (A : Set X)⟩ : SpacePair) ≅ IsCWPair.toSpacePair P
  data : CellularDifferentialFamily X
  [descends : RelativeCellularDifferentialDescends X A data]
  homologyIso : (E q).obj P ≅ relativeCellularHomologyWithCoefficients X A data π (Int.toNat q)

attribute [instance] RelativeCellularHomologyModel.cw
attribute [instance] RelativeCellularHomologyModel.descends

/-- A choice of relative cellular models for a bundled CW-pair homology theory in every
nonnegative degree and every CW pair. -/
abbrev RelativeCellularModels
    {π : Type} [AddCommGroup π] (E : CWPairHomologyTheory π) : Type _ :=
  ∀ q : ℤ, 0 ≤ q → ∀ P : CWPair, E.RelativeCellularHomologyModel q P

/-- A bundled CW-pair homology theory vanishes in negative degrees when each negative graded piece
is zero on every CW pair. -/
def VanishesInNegativeDegrees
    {π : Type} [AddCommGroup π] (E : CWPairHomologyTheory π) : Prop :=
  ∀ q : ℤ, q < 0 → ∀ P : CWPair, IsZero ((E q).obj P)

/-- The connecting morphism of a bundled CW-pair homology theory. -/
abbrev boundary
    {π : Type} [AddCommGroup π] (E : CWPairHomologyTheory π) (q : ℤ) :=
  E.2.boundary q

/-- A degreewise natural isomorphism from the restriction of `H` to the bundled CW-pair homology
theory `E`. -/
abbrev ComparisonIso
    {π : Type} [AddCommGroup π] (E : CWPairHomologyTheory π) (H : PairHomologyTheory π) :
    Type _ :=
  ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q

/-- A comparison isomorphism from `H` to the bundled CW-pair homology theory `E` is compatible
with the boundary maps when it satisfies the Chapter 13 comparison condition for the bundled
homology-theory structure carried by `E`. -/
def HasComparison
    {π : Type} [AddCommGroup π] (E : CWPairHomologyTheory π) (H : PairHomologyTheory π)
    (e : E.ComparisonIso H) : Prop :=
  HasCWPairTheoryComparison H E.2 e

/-- The bundled comparison condition for `e` says exactly that the boundary square commutes for
every degree `q` and CW pair `P`. -/
theorem hasComparison_boundary_comm
    {π : Type} [AddCommGroup π] {E : CWPairHomologyTheory π} {H : PairHomologyTheory π}
    {e : E.ComparisonIso H} (he : E.HasComparison H e) (q : ℤ) (P : CWPair) :
    ((e q).hom.app P) ≫ (CWPairHomologyTheory.boundary E q).app P =
      ((H.boundary q).app (IsCWPair.toSpacePair P)) ≫
        ((e (q - 1)).hom.app (IsCWPair.subspacePair P)) :=
  hasCWPairTheoryComparison_boundary_comm he q P

end CWPairHomologyTheory
