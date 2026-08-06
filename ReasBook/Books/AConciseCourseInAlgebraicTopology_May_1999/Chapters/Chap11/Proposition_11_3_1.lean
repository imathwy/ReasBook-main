import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.PointedExact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Proposition_14_5_1

open scoped Topology.Homotopy unitInterval

universe u

variable {X : TopCat.{u}}

-- Semantic recall via `lean_leansearch`: no current mathlib owner surfaced for the triple long
-- exact sequence in relative homotopy. This file therefore reuses the chapter-level pair owners
-- `tripleSubpair` and `subspacePair`, and keeps the source-facing relative-homotopy exactness
-- data as the main public content.

/-- A chosen basepoint `b ∈ B` also determines the basepoint of the pair `(A, B)`. -/
abbrev tripleSubpairBasepoint {A B : Set X} (hBA : B ⊆ A) (b : B) :
    (tripleSubpair A B).subspace :=
  ⟨⟨b.1, hBA b.2⟩, b.2⟩

/-- A chosen basepoint `b ∈ B ⊆ A` also determines the basepoint of the ambient pair `(X, A)`. -/
abbrev tripleAmbientBasepoint {A B : Set X} (hBA : B ⊆ A) (b : B) :
    (subspacePair A).subspace :=
  ⟨b.1, hBA b.2⟩

/-- The map `π_n(A, B) ⟶ π_n(X, B)` induced by the Chapter 14 triple-left map
`(A, B) ⟶ (X, B)`. -/
def tripleLeftRelativeHomotopyGroupMap {A B : Set X} (hBA : B ⊆ A) (b : B) (n : ℕ+) :
    SpacePair.relativeHomotopyGroup n (tripleSubpair A B)
        (tripleSubpairBasepoint hBA b) →
      SpacePair.relativeHomotopyGroup n (subspacePair B) b :=
  (tripleLeftPairHom A B).relativeHomotopyGroupMap n (tripleSubpairBasepoint hBA b)

/-- The map `π_n(X, B) ⟶ π_n(X, A)` induced by the Chapter 14 triple-right map
`(X, B) ⟶ (X, A)`. -/
def tripleRightRelativeHomotopyGroupMap {A B : Set X} (hBA : B ⊆ A) (b : B) (n : ℕ+) :
    SpacePair.relativeHomotopyGroup n (subspacePair B) b →
      SpacePair.relativeHomotopyGroup n (subspacePair A) (tripleAmbientBasepoint hBA b) :=
  (tripleRightPairHom hBA).relativeHomotopyGroupMap n b

/-- The source degree `q + 3` used for the group-valued exact fragment of the triple sequence. -/
abbrev tripleBoundarySourceDegree (q : ℕ) : ℕ+ :=
  (q + 2).succPNat

/-- The target degree `q + 2` used for the group-valued exact fragment of the triple sequence. -/
abbrev tripleBoundaryTargetDegree (q : ℕ) : ℕ+ :=
  (q + 1).succPNat

/-- A family of connecting morphisms `π_(q + 3)(X, A) ⟶ π_(q + 2)(A, B)` for a triple
`B ⊆ A ⊆ X` based at `b ∈ B`, using the basepoints induced by the canonical maps of pairs. -/
abbrev tripleRelativeBoundaryFamily (A B : Set X) (hBA : B ⊆ A) (b : B) :=
  ∀ q : ℕ,
    SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (subspacePair A)
        (tripleAmbientBasepoint hBA b) →
      SpacePair.relativeHomotopyGroup (tripleBoundaryTargetDegree q) (tripleSubpair A B)
        (tripleSubpairBasepoint hBA b)

/-- Relative homotopy groups in degree `n + 2` inherit an identity element from the group
structure on the shifted homotopy group of the modeled path space. -/
noncomputable instance spacePairRelativeHomotopyGroupOne (P : SpacePair) (c : P.subspace) (n : ℕ) :
    One (SpacePair.relativeHomotopyGroup ((n + 1).succPNat) P c) :=
  @Eq.ndrec
    (Type _)
    (HomotopyGroup.Pi (n + 1) (inclusionHomotopyFiber P.subspace c)
      (SpacePair.relativeHomotopyBasepoint P c))
    (fun T ↦ One T)
    (inferInstance :
      One
        (HomotopyGroup.Pi (n + 1) (inclusionHomotopyFiber P.subspace c)
          (SpacePair.relativeHomotopyBasepoint P c)))
    (SpacePair.relativeHomotopyGroup ((n + 1).succPNat) P c)
    rfl

/-- The higher-degree source term `π_(q + 3)(P)` is group-valued, hence has a distinguished
identity element. -/
noncomputable instance spacePairRelativeHomotopyGroupOneBoundarySource
    (P : SpacePair) (c : P.subspace) (q : ℕ) :
    One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) P c) := by
  simpa [tripleBoundarySourceDegree, Nat.add_assoc] using
    (spacePairRelativeHomotopyGroupOne P c (q + 1))

/-- The higher-degree target term `π_(q + 2)(P)` is group-valued, hence has a distinguished
identity element. -/
noncomputable instance spacePairRelativeHomotopyGroupOneBoundaryTarget
    (P : SpacePair) (c : P.subspace) (q : ℕ) :
    One (SpacePair.relativeHomotopyGroup (tripleBoundaryTargetDegree q) P c) := by
  simpa [tripleBoundaryTargetDegree] using
    (spacePairRelativeHomotopyGroupOne P c q)

/-- The exactness assertions for one adjacent triple of terms in the long exact sequence of a
triple `B ⊆ A ⊆ X`, indexed so that `δ q` goes from degree `q + 3` to degree `q + 2`. -/
structure TripleRelativeExactFragment
    (A B : Set X) (hBA : B ⊆ A) (b : B)
    (δ : tripleRelativeBoundaryFamily A B hBA b) (q : ℕ) : Prop where
  /-- Exactness at `π_(q + 3)(X, B)`. -/
  exact_left_right :
    by
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (tripleSubpair A B)
            (tripleSubpairBasepoint hBA b)) :=
        spacePairRelativeHomotopyGroupOneBoundarySource
          (tripleSubpair A B) (tripleSubpairBasepoint hBA b) q
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (subspacePair B) b) :=
        spacePairRelativeHomotopyGroupOneBoundarySource (subspacePair B) b q
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (subspacePair A)
            (tripleAmbientBasepoint hBA b)) :=
        spacePairRelativeHomotopyGroupOneBoundarySource
          (subspacePair A) (tripleAmbientBasepoint hBA b) q
      exact Function.MulExact
        (tripleLeftRelativeHomotopyGroupMap hBA b (tripleBoundarySourceDegree q))
        (tripleRightRelativeHomotopyGroupMap hBA b (tripleBoundarySourceDegree q))
  /-- Exactness at `π_(q + 3)(X, A)`. -/
  exact_right_boundary :
    by
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (subspacePair B) b) :=
        spacePairRelativeHomotopyGroupOneBoundarySource (subspacePair B) b q
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (subspacePair A)
            (tripleAmbientBasepoint hBA b)) :=
        spacePairRelativeHomotopyGroupOneBoundarySource
          (subspacePair A) (tripleAmbientBasepoint hBA b) q
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundaryTargetDegree q) (tripleSubpair A B)
            (tripleSubpairBasepoint hBA b)) :=
        spacePairRelativeHomotopyGroupOneBoundaryTarget
          (tripleSubpair A B) (tripleSubpairBasepoint hBA b) q
      exact Function.MulExact
        (tripleRightRelativeHomotopyGroupMap hBA b (tripleBoundarySourceDegree q))
        (δ q)
  /-- Exactness at `π_(q + 2)(A, B)`. -/
  exact_boundary_left :
    by
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundarySourceDegree q) (subspacePair A)
            (tripleAmbientBasepoint hBA b)) :=
        spacePairRelativeHomotopyGroupOneBoundarySource
          (subspacePair A) (tripleAmbientBasepoint hBA b) q
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundaryTargetDegree q) (tripleSubpair A B)
            (tripleSubpairBasepoint hBA b)) :=
        spacePairRelativeHomotopyGroupOneBoundaryTarget
          (tripleSubpair A B) (tripleSubpairBasepoint hBA b) q
      letI :
          One (SpacePair.relativeHomotopyGroup (tripleBoundaryTargetDegree q) (subspacePair B) b) :=
        spacePairRelativeHomotopyGroupOneBoundaryTarget (subspacePair B) b q
      exact Function.MulExact
        (δ q)
        (tripleLeftRelativeHomotopyGroupMap hBA b (tripleBoundaryTargetDegree q))

/-- A boundary map for the low-degree fragment
`π_2(X, A) ⟶ π_1(A, B)` of the long exact sequence of the triple `B ⊆ A ⊆ X`. -/
abbrev tripleRelativeLowDegreeBoundaryMap (A B : Set X) (hBA : B ⊆ A) (b : B) :=
  SpacePair.relativeHomotopyGroup (2 : ℕ+) (subspacePair A)
      (tripleAmbientBasepoint hBA b) →
    SpacePair.relativeHomotopyGroup (1 : ℕ+) (tripleSubpair A B)
      (tripleSubpairBasepoint hBA b)

/-- The distinguished point of `π_1(P)` represented by the constant relative path at a chosen
basepoint of a pair `P`. -/
abbrev relativeHomotopyPiOneBasepoint (P : SpacePair) (c : P.subspace) :
    SpacePair.relativeHomotopyGroup (1 : ℕ+) P c :=
  Quotient.mk'' GenLoop.const

/-- The identity element of the group-valued term `π_2(P)` at a chosen basepoint of a pair `P`. -/
noncomputable abbrev relativeHomotopyPiTwoIdentity (P : SpacePair) (c : P.subspace) :
    SpacePair.relativeHomotopyGroup (2 : ℕ+) P c :=
  @One.one _ (spacePairRelativeHomotopyGroupOne
    P c 0)

/-- The pointed tail exactness assertions for the low-degree part
`π_2(A, B) ⟶ π_2(X, B) ⟶ π_2(X, A) ⟶ π_1(A, B) ⟶ π_1(X, B) ⟶ π_1(X, A)` of the
long exact sequence of the triple `B ⊆ A ⊆ X`. -/
def tripleRelativeHomotopyTailExact
    (A B : Set X) (hBA : B ⊆ A) (b : B)
    (δ₂ : tripleRelativeLowDegreeBoundaryMap A B hBA b) : Prop :=
  pointedExact
      (tripleLeftRelativeHomotopyGroupMap hBA b (2 : ℕ+))
      (tripleRightRelativeHomotopyGroupMap hBA b (2 : ℕ+))
      (relativeHomotopyPiTwoIdentity (subspacePair A) (tripleAmbientBasepoint hBA b)) ∧
    pointedExact
      (tripleRightRelativeHomotopyGroupMap hBA b (2 : ℕ+))
      δ₂
      (relativeHomotopyPiOneBasepoint
        (tripleSubpair A B) (tripleSubpairBasepoint hBA b)) ∧
    pointedExact
      δ₂
      (tripleLeftRelativeHomotopyGroupMap hBA b (1 : ℕ+))
      (relativeHomotopyPiOneBasepoint (subspacePair B) b) ∧
    pointedExact
      (tripleLeftRelativeHomotopyGroupMap hBA b (1 : ℕ+))
      (tripleRightRelativeHomotopyGroupMap hBA b (1 : ℕ+))
      (relativeHomotopyPiOneBasepoint
        (subspacePair A) (tripleAmbientBasepoint hBA b))

/-- A source-facing specification of the long exact sequence of the triple `B ⊆ A ⊆ X`, recorded
as the pointed tail
`π_2(A, B) ⟶ π_2(X, B) ⟶ π_2(X, A) ⟶ π_1(A, B) ⟶ π_1(X, B) ⟶ π_1(X, A)`
together with the higher-degree exact fragments
`π_(q + 3)(A, B) ⟶ π_(q + 3)(X, B) ⟶ π_(q + 3)(X, A) ⟶ π_(q + 2)(A, B)`. -/
def tripleRelativeHomotopyLongExactSequenceSpec
    (A B : Set X) (hBA : B ⊆ A) (b : B)
    (δ₂ : tripleRelativeLowDegreeBoundaryMap A B hBA b)
    (δ : tripleRelativeBoundaryFamily A B hBA b) : Prop :=
  tripleRelativeHomotopyTailExact A B hBA b δ₂ ∧
    ∀ q : ℕ, TripleRelativeExactFragment A B hBA b δ q

/-- Proposition 11.3.1. For a triple `B ⊆ A ⊆ X`, there is a long exact sequence
`⋯ ⟶ π_q(A, B) ⟶ π_q(X, B) ⟶ π_q(X, A) ⟶ π_(q - 1)(A, B) ⟶ ⋯`.
In this file the source statement is recorded by the pointed tail
`π_2(A, B) ⟶ π_2(X, B) ⟶ π_2(X, A) ⟶ π_1(A, B) ⟶ π_1(X, B) ⟶ π_1(X, A)`
and by the higher group-valued fragments
`π_(q + 3)(A, B) ⟶ π_(q + 3)(X, B) ⟶ π_(q + 3)(X, A) ⟶ π_(q + 2)(A, B)` for every `q : ℕ`. -/
theorem tripleRelativeHomotopyLongExactSequence
    (A B : Set X) (hBA : B ⊆ A) (b : B) :
    ∃ δ₂ : tripleRelativeLowDegreeBoundaryMap A B hBA b,
      ∃ δ : tripleRelativeBoundaryFamily A B hBA b,
        tripleRelativeHomotopyLongExactSequenceSpec A B hBA b δ₂ δ := sorry

/-- For a triple `B ⊆ A ⊆ X`, writing the displayed
degree as `q + 3` so that all terms are group-valued relative homotopy groups, the long exact
sequence has exact fragments
`π_(q + 3)(A, B) ⟶ π_(q + 3)(X, B) ⟶ π_(q + 3)(X, A) ⟶ π_(q + 2)(A, B)`
for every `q : ℕ`. This is the `q ≥ 2` range of the source proposition. -/
theorem tripleRelativeHomotopyLongExactSequenceGroupValuedRange
    (A B : Set X) (hBA : B ⊆ A) (b : B) :
    ∃ δ : tripleRelativeBoundaryFamily A B hBA b,
      ∀ q : ℕ, TripleRelativeExactFragment A B hBA b δ q := sorry
