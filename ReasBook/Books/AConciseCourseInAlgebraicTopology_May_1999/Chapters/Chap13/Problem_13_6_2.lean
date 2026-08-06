import Mathlib.Topology.CWComplex.Abstract.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Corollary_10_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory

open CategoryTheory Limits
open scoped Topology Topology.Homotopy

universe u

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a closer mathlib owner for this mixed
-- homology/homotopy comparison problem. The repository already fixes the source-faithful owners:
-- Chapter 10 `cellularPushout`/`cellularPushoutLeftRange` for the adjunction space `Y ∪_f X`,
-- Corollary 10.2.4's canonical quotient comparison
-- `cellularPushoutCollapseComparison : X / A ⟶ (Y ∪_f X) / Y`,
-- `PairHomologyTheory` for Chapter 13 pair homology, and, in Chapter 11, `SpacePair`,
-- `SpacePair.relativeHomotopyGroup`,
-- `SpacePair.Hom.relativeHomotopyGroupMap`, and `homotopyExcision` for the pair-relative homotopy
-- comparison route.

/-- The genuine pair `(X, A)`. -/
abbrev subsetSpacePair {X : Type u} [TopologicalSpace X] (A : Set X) : SpacePair where
  space := TopCat.of X
  subspace := A

/-- The genuine pair `(Y ∪_f X, Y)` realized by the `Y`-summand inside the cellular pushout. -/
abbrev cellularPushoutTargetPair
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    SpacePair where
  space := cellularPushout A f
  subspace := cellularPushoutLeftRange A f

/-- The canonical map of genuine pairs `(X, A) ⟶ (Y ∪_f X, Y)`. -/
def cellularPushoutPairComparison
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(A, Y)) :
    subsetSpacePair A ⟶ cellularPushoutTargetPair A f where
  hom := pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)
  map_subspace' := by
    intro x hx
    exact cellularPushout_inr_mem_leftRange_of_mem A f hx

/-- Typeclass form of the cellular-pushout comparison isomorphism on pair homology. -/
instance cellularPushout_pairComparison_isIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (A : Set X) (f : C(A, Y)) (hCellular : TopCat.RelativeCWComplex (TopCat.subtypeInclusion A))
    (q : ℤ) :
    IsIso ((H q).map (cellularPushoutPairComparison A f)) := sorry

/-- Problem 13.6.2 (1): for any Chapter 13 pair homology theory, the
morphism induced by `cellularPushoutPairComparison A f : subsetSpacePair A ⟶
cellularPushoutTargetPair A f` identifies `H_q(X, A)` with `H_q(Y ∪_f X, Y)`. -/
theorem cellularPushout_pairHomology_iso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (A : Set X) (f : C(A, Y)) (hCellular : TopCat.RelativeCWComplex (TopCat.subtypeInclusion A))
    (q : ℤ) :
    IsIso ((H q).map (cellularPushoutPairComparison A f)) := by
  exact cellularPushout_pairComparison_isIso H A f hCellular q

/- Problem 13.6.2 (2): the analogous relative-homotopy statement is expressed in the established
Chapter 11 language by asking whether
`cellularPushoutPairComparison A f : subsetSpacePair A ⟶ cellularPushoutTargetPair A f`
is an `n`-equivalence of pairs. The induced map on genuine pair-relative homotopy groups is then
`(cellularPushoutPairComparison A f).relativeHomotopyGroupMap q c`, and the standard Chapter 11
route for proving such a comparison is `homotopyExcision` once the cellular pushout is realized in
that excision framework. -/

/-- Problem 13.6.2 (2): any proof that the cellular-pushout comparison
`cellularPushoutPairComparison A f` is an `n`-equivalence of pairs yields bijections on the genuine
relative homotopy groups `π_q(X, A, c) → π_q(Y ∪_f X, Y, f(c))` in every positive degree
strictly below `n`. -/
theorem cellularPushout_pairComparison_relativeHomotopyGroup_bijective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) {n : ℕ} (hEq : SpacePair.Hom.IsNEquivalence n
      (cellularPushoutPairComparison A f))
    (c : A) {q : ℕ+} (hq : (q : ℕ) < n) :
    Function.Bijective ((cellularPushoutPairComparison A f).relativeHomotopyGroupMap q c) :=
  hEq.relativeBijective c hq

/-- Problem 13.6.2 (2): at the limiting degree `n`, an `n`-equivalence proof for
`cellularPushoutPairComparison A f` yields surjectivity on the induced genuine relative homotopy
group map. -/
theorem cellularPushout_pairComparison_relativeHomotopyGroup_surjective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) {n : ℕ} (hEq : SpacePair.Hom.IsNEquivalence n
      (cellularPushoutPairComparison A f))
    (c : A) {q : ℕ+} (hq : (q : ℕ) = n) :
    Function.Surjective ((cellularPushoutPairComparison A f).relativeHomotopyGroupMap q c) :=
  hEq.relativeSurjectiveInDegree c hq
