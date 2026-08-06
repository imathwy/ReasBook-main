import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair

open CategoryTheory

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch` surfaced only abstract homology-sequence exactness lemmas,
-- not the chapter's reduced-homology owner. Local precedent from `Construction_14_1_3` therefore
-- controls the reduced-homology API and the induced maps used below.

/-- The subspace `A ⊆ X.right`, based at the chosen point `underTopBasepoint X`. -/
def basedSubspace (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit ((⟨underTopBasepoint X, hA⟩ : A))))

/-- The underlying inclusion `A ↪ X.right` of the based subspace attached to `A`. -/
abbrev basedSubspaceSubtypeInclusion (X : BasedSpace) (A : Set X.right) :
    TopCat.of A ⟶ X.right :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `A ↪ X.right` respects the chosen basepoints, so it defines a based map
`basedSubspace X A hA ⟶ X`. -/
theorem basedSubspaceInclusion_w
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    (basedSubspace X A hA).hom ≫
        basedSubspaceSubtypeInclusion X A =
      X.hom := sorry

/-- The inclusion of the based subspace `A` into `X`. -/
def basedSubspaceInclusion
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    basedSubspace X A hA ⟶ X :=
  Under.homMk
    (basedSubspaceSubtypeInclusion X A)
    (basedSubspaceInclusion_w X A hA)

/-- The singleton basepoint subset lies in any subspace `A ⊆ X.right` containing
`underTopBasepoint X`. -/
theorem basepointSingleton_subset
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    ({underTopBasepoint X} : Set X.right) ⊆ A := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  simpa [hx] using hA

/-- The map `Ẽ_q(A) ⟶ Ẽ_q(X)` induced by the based inclusion `A ↪ X`. -/
abbrev reducedSubspaceInclusionMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    basedReducedHomology H q (basedSubspace X A hA) →+ basedReducedHomology H q X :=
  basedHomologyReducedMap H q (basedSubspaceInclusion X A hA)

/-- The map `Ẽ_q(X) ⟶ E_q(X, A)` induced by the pair morphism
`(X, {underTopBasepoint X}) ⟶ (X, A)`. -/
abbrev reducedToRelativeMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    basedReducedHomology H q X →+ pairHomologyGroup H q X.right A :=
  ((H.homology q).map
    (subsetPairInclusion (basepointSingleton_subset X A hA))).hom.toAddMonoidHom

/-- The map `Ẽ_(q - 1)(A) ⟶ Ẽ_(q - 1)(X)` induced by the based inclusion `A ↪ X`. -/
abbrev reducedBoundarySuccessorMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    basedReducedHomology H (q - 1) (basedSubspace X A hA) →+
      basedReducedHomology H (q - 1) X :=
  basedHomologyReducedMap H (q - 1) (basedSubspaceInclusion X A hA)

/-- A family of reduced boundary maps `E_q(X, A) ⟶ Ẽ_(q - 1)(A)`. -/
abbrev reducedBoundaryFamily
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :=
  ∀ q : ℤ, pairHomologyGroup H q X.right A →+ basedReducedHomology H (q - 1) (basedSubspace X A hA)

/-- The canonical reduced boundary map `E_q(X, A) ⟶ Ẽ_(q - 1)(A)` is the Chapter 13 boundary
for the pair `(X, A)`, followed by the canonical passage from absolute to reduced homology on the
based subspace `A`. -/
noncomputable def reducedBoundaryMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    pairHomologyGroup H q X.right A →+
      basedReducedHomology H (q - 1) (basedSubspace X A hA) :=
  (((H.boundary q).app (subsetPair X.right A)) ≫
      (H.homology (q - 1)).map
        (SpacePair.absoluteToRelative (basedReducedPair (basedSubspace X A hA)))).hom.toAddMonoidHom

/-- The canonical family of reduced boundary maps in Sequence 14.1.4. -/
noncomputable def reducedLongExactBoundaryFamily
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) :
    reducedBoundaryFamily H X A hA :=
  fun q ↦ reducedBoundaryMap H q X A hA

/-- The exactness assertions for the three consecutive maps in the reduced long exact sequence
at degree `q`. -/
structure ReducedHomologyLongExactDegree
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A)
    (δ : reducedBoundaryFamily H X A hA) (q : ℤ) : Prop where
  exact₁ :
    Function.Exact
      (reducedSubspaceInclusionMap H q X A hA)
      (reducedToRelativeMap H q X A hA)
  exact₂ :
    Function.Exact
      (reducedToRelativeMap H q X A hA)
      (δ q)
  exact₃ :
    Function.Exact
      (δ q)
      (reducedBoundarySuccessorMap H q X A hA)

/-- Sequence 14.1.4. For a based space `X` and a subspace `A ⊆ X.right` containing the chosen
basepoint, there is a reduced long exact sequence
`... ⟶ Ẽ_q(A) ⟶ Ẽ_q(X) ⟶ E_q(X, A) ⟶ Ẽ_(q - 1)(A) ⟶ ...`. Here this is formalized using the
canonical boundary family `reducedLongExactBoundaryFamily H X A hA`, with each adjacent triple
exact. -/
theorem reducedHomologyLongExactSequence
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (X : BasedSpace) (A : Set X.right) (hA : underTopBasepoint X ∈ A) (q : ℤ) :
    ReducedHomologyLongExactDegree H X A hA
      (reducedLongExactBoundaryFamily H X A hA) q := sorry
