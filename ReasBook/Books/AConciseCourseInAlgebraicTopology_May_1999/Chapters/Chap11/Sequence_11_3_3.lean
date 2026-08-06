import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_3_2

open scoped Topology Topology.Homotopy unitInterval

universe u v w z

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch` and repo search found no existing local owner for the
-- triad long exact sequence. This file therefore keeps the Chapter 9/11 owners for the displayed
-- terms, with the middle arrow fixed canonically by `triadSubspaceInclusionMap` and the outer
-- arrows exposed through named degree-indexed map types.

/-- The pair-relative group `π_(q + 2)(A, C)` in the displayed triad long exact sequence window,
where `C = A ∩ B`. -/
abbrev triadSubspaceRelativeHomotopyGroup (T : Triad X) (x : T.intersection) (q : ℕ) :=
  SpacePair.relativeHomotopyGroup (q + 1).succPNat
    (triadSubspacePair T) (triadSubspaceBasepoint T x)

/-- The pair-relative group `π_(q + 2)(X, B)` in the displayed triad long exact sequence window. -/
abbrev triadAmbientRelativeHomotopyGroup (T : Triad X) (x : T.intersection) (q : ℕ) :=
  SpacePair.relativeHomotopyGroup (q + 1).succPNat
    (triadAmbientPair T) (triadAmbientMappedBasepoint T x)

/-- The map `π_(q + 2)(A, C) ⟶ π_(q + 2)(X, B)` induced by the canonical inclusion
`(A, C) ⟶ (X, B)`, where `C = A ∩ B`. -/
def triadSubspaceInclusionMap (T : Triad X) (x : T.intersection) (q : ℕ) :
    triadSubspaceRelativeHomotopyGroup T x q →
      triadAmbientRelativeHomotopyGroup T x q :=
  (triadSubspaceInclusion T).relativeHomotopyGroupMap (q + 1).succPNat
    (triadSubspaceBasepoint T x)

/-- The displayed source degree `q + 2` always satisfies the `q ≥ 2` hypothesis needed for
`triadHomotopyGroup`. -/
abbrev triadDisplayedHomotopyGroupDegree (q : ℕ) : 2 ≤ q + 2 :=
  Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le q))

/-- The displayed term `π_(q + 2)(X; A, B)` carries the distinguished basepoint represented by
the constant relative path in the path-space pair from Definition 11.3.2, used as `1` in the
exactness predicate `Function.MulExact`. -/
instance triadDisplayedHomotopyGroupOne
    (T : Triad X) (x : T.intersection) (q : ℕ) :
    One (triadHomotopyGroup T x (q + 2) (triadDisplayedHomotopyGroupDegree q)) where
  one := Quotient.mk'' GenLoop.const

/-- The type of boundary maps `π_(q + 3)(X; A, B) ⟶ π_(q + 2)(A, C)` in the displayed exact
fragment. -/
abbrev TriadBoundaryMap (T : Triad X) (x : T.intersection) (q : ℕ) :=
  triadHomotopyGroup T x (q + 3) (triadHigherGroupDegree q) →
    triadSubspaceRelativeHomotopyGroup T x q

/-- The type of connecting maps `π_(q + 2)(X, B) ⟶ π_(q + 2)(X; A, B)` in the displayed exact
fragment. -/
abbrev TriadConnectingMap (T : Triad X) (x : T.intersection) (q : ℕ) :=
  triadAmbientRelativeHomotopyGroup T x q →
    triadHomotopyGroup T x (q + 2) (triadDisplayedHomotopyGroupDegree q)

/-- Exactness for the displayed four-term fragment of the triad homotopy long exact sequence in
the group-valued range. -/
structure TriadHomotopyExactFragment
    (T : Triad X) (x : T.intersection) (q : ℕ)
    (boundary : TriadBoundaryMap T x q)
    (connecting : TriadConnectingMap T x q) : Prop where
  /-- Exactness at `π_(q + 2)(A, C)`. -/
  exact_boundary_subspaceInclusionMap :
    Function.MulExact boundary (triadSubspaceInclusionMap T x q)
  /-- Exactness at `π_(q + 2)(X, B)`. -/
  exact_subspaceInclusionMap_connecting :
    Function.MulExact (triadSubspaceInclusionMap T x q) connecting

/-- A long exact sequence for the triad `(X; A, B)` in the group-valued range, with the middle
map fixed canonically by `triadSubspaceInclusionMap`. -/
structure TriadHomotopyLongExactSequence (T : Triad X) (x : T.intersection) where
  /-- The boundary maps `π_(q + 3)(X; A, B) ⟶ π_(q + 2)(A, C)` indexed by `q`. -/
  boundary : ∀ q : ℕ, TriadBoundaryMap T x q
  /-- The connecting maps `π_(q + 2)(X, B) ⟶ π_(q + 2)(X; A, B)` indexed by `q`. -/
  connecting : ∀ q : ℕ, TriadConnectingMap T x q
  /-- Exactness of the `q`th displayed fragment, with middle map `triadSubspaceInclusionMap`. -/
  exact : ∀ q : ℕ, TriadHomotopyExactFragment T x q (boundary q) (connecting q)

/-- A source-facing specification of the displayed four-term fragments in the triad homotopy
long exact sequence, indexed by `q`. -/
def triadHomotopyLongExactSequenceSpec
    (T : Triad X) (x : T.intersection)
    (boundary : ∀ q : ℕ, TriadBoundaryMap T x q)
    (connecting : ∀ q : ℕ, TriadConnectingMap T x q) : Prop :=
  ∀ q : ℕ, TriadHomotopyExactFragment T x q (boundary q) (connecting q)

namespace TriadHomotopyLongExactSequenceSpec

variable {T : Triad X} {x : T.intersection}
variable {boundary : ∀ q : ℕ, TriadBoundaryMap T x q}
variable {connecting : ∀ q : ℕ, TriadConnectingMap T x q}

/-- The `q`th displayed fragment packaged by
`triadHomotopyLongExactSequenceSpec T x boundary connecting`. -/
theorem exactFragment
    (h : triadHomotopyLongExactSequenceSpec T x boundary connecting) (q : ℕ) :
    TriadHomotopyExactFragment T x q (boundary q) (connecting q) :=
  h q

/-- Exactness at `π_(q + 2)(A, C)` in the `q`th displayed fragment encoded by
`triadHomotopyLongExactSequenceSpec T x boundary connecting`. -/
theorem exact_boundary_subspaceInclusionMap
    (h : triadHomotopyLongExactSequenceSpec T x boundary connecting) (q : ℕ) :
    Function.MulExact (boundary q) (triadSubspaceInclusionMap T x q) :=
  (h q).exact_boundary_subspaceInclusionMap

/-- Exactness at `π_(q + 2)(X, B)` in the `q`th displayed fragment encoded by
`triadHomotopyLongExactSequenceSpec T x boundary connecting`. -/
theorem exact_subspaceInclusionMap_connecting
    (h : triadHomotopyLongExactSequenceSpec T x boundary connecting) (q : ℕ) :
    Function.MulExact (triadSubspaceInclusionMap T x q) (connecting q) :=
  (h q).exact_subspaceInclusionMap_connecting

end TriadHomotopyLongExactSequenceSpec

namespace TriadHomotopyLongExactSequence

variable {T : Triad X} {x : T.intersection}

/-- Exactness at `π_(q + 2)(A, C)` in the `q`th displayed fragment. -/
theorem exact_boundary_subspaceInclusionMap
    (les : TriadHomotopyLongExactSequence T x) (q : ℕ) :
    Function.MulExact (les.boundary q) (triadSubspaceInclusionMap T x q) :=
  (les.exact q).exact_boundary_subspaceInclusionMap

/-- Exactness at `π_(q + 2)(X, B)` in the `q`th displayed fragment. -/
theorem exact_subspaceInclusionMap_connecting
    (les : TriadHomotopyLongExactSequence T x) (q : ℕ) :
    Function.MulExact (triadSubspaceInclusionMap T x q) (les.connecting q) :=
  (les.exact q).exact_subspaceInclusionMap_connecting

/-- The `q`th displayed fragment of a triad long exact sequence. -/
theorem exactFragment (les : TriadHomotopyLongExactSequence T x) (q : ℕ) :
    TriadHomotopyExactFragment T x q (les.boundary q) (les.connecting q) :=
  les.exact q

/-- Forgetting the internal packaging of `TriadHomotopyLongExactSequence T x` recovers the
source-facing exact fragment specification. -/
theorem spec
    (les : TriadHomotopyLongExactSequence T x) :
    triadHomotopyLongExactSequenceSpec T x les.boundary les.connecting :=
  les.exact

end TriadHomotopyLongExactSequence

/- Sequence 11.3.3. In the group-valued range, there exists a long exact sequence of triad
homotopy groups whose `q`th displayed fragment is
`π_(q + 3)(X; A, B) ⟶ π_(q + 2)(A, C) ⟶ π_(q + 2)(X, B) ⟶ π_(q + 2)(X; A, B)`, with
`C = A ∩ B`, with the middle map fixed canonically by `triadSubspaceInclusionMap T x q`, and
with the textbook `π_(q + 1) ⟶ π_q` segment reindexed to the group-valued window
`π_(q + 3) ⟶ π_(q + 2)` formalized in this file. The internal structure
`TriadHomotopyLongExactSequence T x` packages one such choice, while this theorem exposes the
source-facing families of maps through `triadHomotopyLongExactSequenceSpec T x boundary
connecting`. -/
theorem triadHomotopyLongExactSequenceInGroupValuedRange
    (T : Triad X) (x : T.intersection) :
    ∃ boundary : ∀ q : ℕ, TriadBoundaryMap T x q,
      ∃ connecting : ∀ q : ℕ, TriadConnectingMap T x q,
        triadHomotopyLongExactSequenceSpec T x boundary connecting := by
  sorry
