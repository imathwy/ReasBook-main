import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

open CategoryTheory Limits
open HomotopicalAlgebra
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` surfaced only general cohomology and weak-equivalence
-- infrastructure, while local precedent from Chapter 13 supplies the canonical owner `SpacePair`.
-- Because the later Chapter 19 pair-cohomology owner omits the source-facing dimension axiom,
-- this file keeps a source-faithful owner for pair cohomology theories.

/-- A contravariant cohomology theory on pairs of spaces with coefficients in `π`, formalized on
the Chapter 13 category `SpacePair` with its intended weak-equivalence structure. The graded
functors, connecting morphisms, and the dimension, exactness, excision, additivity, and
weak-equivalence axioms are bundled together. -/
structure PairCohomologyTheory (π : Type u)
    [AddCommGroup π] where
  /-- The graded contravariant functor `H^q(X, A; π)` on pairs. -/
  cohomology : ℤ → SpacePair.{u}ᵒᵖ ⥤ AddCommGrpCat.{u}
  /-- The connecting morphisms `H^q(A; π) ⟶ H^(q + 1)(X, A; π)` in the long exact sequence of a
  pair. -/
  boundary (q : ℤ) : subspaceFunctor.op ⋙ cohomology q ⟶ cohomology (q + 1)
  /-- The degree-zero cohomology of the one-point pair is the coefficient group `π`. -/
  dimensionZero :
    Nonempty ((cohomology 0).obj (Opposite.op point) ≅ AddCommGrpCat.of π)
  /-- The higher and lower cohomology of the one-point pair vanishes away from degree `0`. -/
  dimensionHigher (q : ℤ) (hq : q ≠ 0) : IsZero ((cohomology q).obj (Opposite.op point))
  /-- The sequence `H^q(X, A; π) ⟶ H^q(X; π) ⟶ H^q(A; π)` is exact. -/
  exact₁ (q : ℤ) (P : SpacePair.{u}) :
    Function.Exact
      ((cohomology q).map (absoluteToRelative P).op)
      ((cohomology q).map (subspaceInclusion P).op)
  /-- The sequence `H^q(X; π) ⟶ H^q(A; π) ⟶ H^(q + 1)(X, A; π)` is exact. -/
  exact₂ (q : ℤ) (P : SpacePair.{u}) :
    Function.Exact
      ((cohomology q).map (subspaceInclusion P).op)
      ((boundary q).app (Opposite.op P))
  /-- The sequence `H^q(A; π) ⟶ H^(q + 1)(X, A; π) ⟶ H^(q + 1)(X; π)` is exact. -/
  exact₃ (q : ℤ) (P : SpacePair.{u}) :
    Function.Exact
      ((boundary q).app (Opposite.op P))
      ((cohomology (q + 1)).map (absoluteToRelative P).op)
  /-- Excision identifies `H^q(X, A; π)` with `H^q(X \ U, A \ U; π)` when `closure U ⊆ interior
  A`. -/
  excision (q : ℤ) (P : SpacePair.{u}) (U : Set P.space)
      (hU : closure U ⊆ interior P.subspace) :
      IsIso ((cohomology q).map (removeSubsetInclusion P U).op)
  /-- Coproducts of pairs are sent to products in each degree. -/
  additivity (q : ℤ) {ι : Type u} : PreservesLimitsOfShape (Discrete ι) (cohomology q)
  /-- Weakly equivalent pairs induce isomorphisms in each cohomological degree. -/
  weakEquivalenceInvariant (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((cohomology q).map f.op)

/-- A `PairCohomologyTheory` can be used as its underlying graded contravariant functor. -/
instance {π : Type u} [AddCommGroup π] :
    CoeFun (PairCohomologyTheory π)
      (fun _ ↦ ℤ → SpacePair.{u}ᵒᵖ ⥤ AddCommGrpCat.{u}) where
  coe H := H.cohomology

namespace PairCohomologyTheory

variable {π : Type u} [AddCommGroup π]

/-- A `PairCohomologyTheory` exposes the dimension, exactness, excision, additivity, and
weak-equivalence axioms recorded in its fields. -/
theorem spec (H : PairCohomologyTheory π) :
    Nonempty ((H 0).obj (Opposite.op point) ≅ AddCommGrpCat.of π) ∧
      (∀ q : ℤ, q ≠ 0 → IsZero ((H q).obj (Opposite.op point))) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u},
        Function.Exact
          ((H q).map (absoluteToRelative P).op)
          ((H q).map (subspaceInclusion P).op)) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u},
        Function.Exact
          ((H q).map (subspaceInclusion P).op)
          ((H.boundary q).app (Opposite.op P))) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u},
        Function.Exact
          ((H.boundary q).app (Opposite.op P))
          ((H (q + 1)).map (absoluteToRelative P).op)) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u}, ∀ U : Set P.space,
        closure U ⊆ interior P.subspace →
          IsIso ((H q).map (removeSubsetInclusion P U).op)) ∧
      (∀ {ι : Type u}, ∀ q : ℤ, PreservesLimitsOfShape (Discrete ι) (H q)) ∧
      (∀ q : ℤ, ∀ {P Q : SpacePair.{u}} (f : P ⟶ Q),
        [WeakEquivalence f] → IsIso ((H q).map f.op)) := by
  refine ⟨H.dimensionZero, H.dimensionHigher, H.exact₁, H.exact₂, H.exact₃, ?_, ?_, ?_⟩
  · intro q P U hU
    exact H.excision q P U hU
  · intro ι q
    exact H.additivity q
  · intro q P Q f
    exact H.weakEquivalenceInvariant q f

/-- The first exactness window of a pair cohomology theory is the source-facing sequence
`H^q(X, A; π) ⟶ H^q(X; π) ⟶ H^q(A; π)`. -/
theorem exact_absoluteToRelative_subspaceInclusion
    (H : PairCohomologyTheory π) (q : ℤ) (P : SpacePair.{u}) :
    Function.Exact
      ((H q).map (absoluteToRelative P).op)
      ((H q).map (subspaceInclusion P).op) :=
  H.exact₁ q P

/-- The second exactness window of a pair cohomology theory is the source-facing sequence
`H^q(X; π) ⟶ H^q(A; π) ⟶ H^(q + 1)(X, A; π)`. -/
theorem exact_subspaceInclusion_boundary
    (H : PairCohomologyTheory π) (q : ℤ) (P : SpacePair.{u}) :
    Function.Exact
      ((H q).map (subspaceInclusion P).op)
      ((H.boundary q).app (Opposite.op P)) :=
  H.exact₂ q P

/-- The third exactness window of a pair cohomology theory is the source-facing sequence
`H^q(A; π) ⟶ H^(q + 1)(X, A; π) ⟶ H^(q + 1)(X; π)`. -/
theorem exact_boundary_absoluteToRelative
    (H : PairCohomologyTheory π) (q : ℤ) (P : SpacePair.{u}) :
    Function.Exact
      ((H.boundary q).app (Opposite.op P))
      ((H (q + 1)).map (absoluteToRelative P).op) :=
  H.exact₃ q P

/-- The connecting morphism of a pair cohomology theory is natural with respect to maps of
pairs. -/
theorem boundary_naturality
    (H : PairCohomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q) :
    ((H q).map (subspaceFunctor.map f).op) ≫ (H.boundary q).app (Opposite.op P) =
      (H.boundary q).app (Opposite.op Q) ≫ ((H (q + 1)).map f.op) := by
  simpa using (H.boundary q).naturality f.op

/-- A weak equivalence of pairs induces an isomorphism on the cohomology groups of a pair
cohomology theory. -/
instance map_isIso_of_weakEquivalence
    (H : PairCohomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q)
    [WeakEquivalence f] :
    IsIso ((H q).map f.op) :=
  H.weakEquivalenceInvariant q f

end PairCohomologyTheory

/-- Theorem 18.1.1: relative to the Chapter 13 weak-equivalence structure on `SpacePair`, there
exists a contravariant cohomology theory `H^q(X, A; π)` on pairs of spaces satisfying the
dimension, exactness, excision, additivity, and weak-equivalence axioms. -/
theorem exists_pairCohomologyTheory
    (π : Type u) [AddCommGroup π] :
    Nonempty (PairCohomologyTheory π) := sorry
