import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Proposition_6_5_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_5_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open CategoryTheory
open scoped ContinuousMap Topology Topology.Homotopy

noncomputable section

universe u v

section HomotopyGroup

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: mathlib's canonical owner for a homotopy equivalence of
-- spaces is `ContinuousMap.HomotopyEquiv`, while local Chapter 9 precedent already fixes
-- `homotopyGroupMap` as the induced map on homotopy groups.

/-- Corollary 9.5.10 (1): a homotopy equivalence of spaces induces bijections on all based
homotopy groups. In the local Chapter 9 API, this says that if `e : X ≃ₕ Y`, then the induced
map `e_* : π_ q X x → π_ q Y (e x)` is bijective for every degree `q` and every basepoint `x`.
-/
theorem ContinuousMap.HomotopyEquiv.bijective_homotopyGroupMap
    (e : X ≃ₕ Y) (q : ℕ) (x : X) :
    Function.Bijective (e.toFun.eStar q x) := sorry

end HomotopyGroup

section RelativeHomotopyGroup

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set X} {B : Set Y} {n : ℕ+}
variable
  (eA :
    ∀ a : A, relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)
  (eB :
    ∀ b : B, relativeHomotopyGroup n B b ≃ basedDiskBoundaryPairMapHomotopyClass n B b)

-- Semantic recall via `lean_leansearch`: Chapter 9 fixes
-- `relativeHomotopyGroupMapOfPairMap` as the induced map on relative homotopy groups, and
-- Chapter 6 already provides the source-faithful owner `PairMap` with predicate
-- `IsPairHomotopyEquivalence` for the pair-level hypothesis.

/-- The commutative square of subset inclusions determined by a continuous map `f : X → Y` carrying
`A` into `B`. This is the Chapter 9 source-facing bridge from `Set.MapsTo` data to the Chapter 6
owner `PairMap`, using the repository's canonical subtype inclusions. -/
abbrev subsetPairMap {A : Set X} {B : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    PairMap (TopCat.subtypeInclusion A).hom (TopCat.subtypeInclusion B).hom :=
  { left := TopCat.ofHom (pairMapSubspace f hf)
    right := TopCat.ofHom f
    w := by
      ext a
      rfl }

@[simp] theorem subsetPairMap_subspaceMap {A : Set X} {B : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    (subsetPairMap f hf).subspaceMap = pairMapSubspace f hf := rfl

@[simp] theorem subsetPairMap_ambientMap {A : Set X} {B : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    (subsetPairMap f hf).ambientMap = f := rfl

/-- Corollary 9.5.10 (2): a pair homotopy equivalence induces bijections on all relative homotopy
groups. In the local Chapter 9 API, if the canonical square `subsetPairMap f hf` is a pair
homotopy equivalence, then the induced map
`f_* : π_n(X, A, a) → π_n(Y, B, pairMapSubspace f hf a)` is bijective for every `a : A`,
relative to the supplied disk-boundary model comparisons. -/
theorem relativeHomotopyGroupMapOfPairMap_bijective_of_isPairHomotopyEquivalence
    (f : C(X, Y)) (hf : Set.MapsTo f A B)
    (h_pair : IsPairHomotopyEquivalence (subsetPairMap f hf)) (a : A) :
    Function.Bijective (relativeHomotopyGroupMapOfPairMap eA eB f hf a) := sorry

end RelativeHomotopyGroup
