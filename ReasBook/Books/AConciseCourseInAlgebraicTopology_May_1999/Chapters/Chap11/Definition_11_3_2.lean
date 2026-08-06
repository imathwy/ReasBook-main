import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: no current mathlib owner for triad-relative homotopy
-- groups was found in this environment, but local Chapter 11 precedent provides the canonical
-- pair-relative owner `SpacePair.relativeHomotopyGroup`. Accordingly, Definition 11.3.2 is
-- formalized by the path-space pair together with the shifted pair-relative homotopy group it
-- models.

/-- The chosen basepoint of `B`, obtained from a chosen point of `A ∩ B`. -/
abbrev triadAmbientBasepoint (T : Triad X) (x : T.intersection) : T.subspaceB :=
  ⟨x.1, x.2.2⟩

/-- The intersection `C = A ∩ B`, regarded as a subspace of `A`. -/
abbrev triadSubspaceIntersection (T : Triad X) : Set T.subspaceA :=
  { a | a.1 ∈ T.subspaceB }

/-- The chosen basepoint of `C = A ∩ B`, regarded as a point of the `A`-subspace. -/
abbrev triadSubspaceBasepoint (T : Triad X) (x : T.intersection) :
    triadSubspaceIntersection T :=
  ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/-- The pair `(A, C)` with `C = A ∩ B`, attached to a triad `(X; A, B)`. -/
def triadSubspacePair (T : Triad X) : SpacePair where
  space := TopCat.of T.subspaceA
  subspace := triadSubspaceIntersection T

/-- The pair `(X, B)` attached to a triad `(X; A, B)`. -/
def triadAmbientPair (T : Triad X) : SpacePair where
  space := TopCat.of X
  subspace := T.subspaceB

/-- The inclusion `(A, C) ⟶ (X, B)` induced by the subtype embedding `A ↪ X`, with
`C = A ∩ B`. -/
def triadSubspaceInclusion (T : Triad X) :
    triadSubspacePair T ⟶ triadAmbientPair T where
  hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  map_subspace' := fun {_} hx ↦ hx

/-- The chosen basepoint of `(X, B)` obtained by mapping the chosen point of `(A, C)` along the
canonical inclusion `(A, C) ⟶ (X, B)`. -/
abbrev triadAmbientMappedBasepoint (T : Triad X) (x : T.intersection) :
    (triadAmbientPair T).subspace :=
  (triadSubspaceInclusion T).mapSubspace (triadSubspaceBasepoint T x)

/-- The ambient path space `P(X; *, B)` for a triad, modeled as the homotopy fiber of `B ↪ X`
over the chosen basepoint. -/
abbrev triadAmbientPathSpace (T : Triad X) (x : T.intersection) :=
  inclusionHomotopyFiber T.subspaceB (triadAmbientBasepoint T x)

/-- The subspace path space `P(A; *, C)` for a triad, modeled as the homotopy fiber of
`C ↪ A` over the chosen basepoint in `C = A ∩ B`. -/
abbrev triadSubspacePathSpace (T : Triad X) (x : T.intersection) :=
  inclusionHomotopyFiber (triadSubspaceIntersection T) (triadSubspaceBasepoint T x)

/-- The inclusion `P(A; *, C) ⟶ P(X; *, B)` induced by the subtype embedding `A ↪ X`. -/
def triadSubspacePathMap (T : Triad X) (x : T.intersection) :
    triadSubspacePathSpace T x → triadAmbientPathSpace T x
  | z =>
      ⟨(⟨z.1.1.1.1, z.1.1.2⟩,
          (⟨Subtype.val, continuous_subtype_val⟩ : C(T.subspaceA, X)).comp z.1.2),
        ⟨congrArg Subtype.val z.2.1, congrArg Subtype.val z.2.2⟩⟩

/-- The constant path at the chosen point of `C = A ∩ B`, viewed as a point of `P(A; *, C)`. -/
def triadSubspaceConstantPath (T : Triad X) (x : T.intersection) :
    triadSubspacePathSpace T x :=
  ⟨(triadSubspaceBasepoint T x, ContinuousMap.const I ⟨x.1, x.2.1⟩), ⟨rfl, rfl⟩⟩

/-- The path-space pair `(P(X; *, B), P(A; *, C))` whose relative homotopy groups model the
triad homotopy groups. -/
def triadHomotopyPathPair (T : Triad X) (x : T.intersection) : SpacePair where
  space := TopCat.of (triadAmbientPathSpace T x)
  subspace := Set.range (triadSubspacePathMap T x)

/-- The constant path in `P(A; *, C)` gives the distinguished basepoint of the path-space pair. -/
abbrev triadHomotopyPathPairBasepoint (T : Triad X) (x : T.intersection) :
    (triadHomotopyPathPair T x).subspace :=
  ⟨triadSubspacePathMap T x (triadSubspaceConstantPath T x),
    ⟨triadSubspaceConstantPath T x, rfl⟩⟩

/-- Definition 11.3.2. For a triad `(X; A, B)` with basepoint `x ∈ C = A ∩ B` and degree
`q ≥ 2`, the triad homotopy group `π_q(X; A, B)` is the relative homotopy group
`π_(q - 1)(P(X; *, B), P(A; *, C))`, formalized here through
`SpacePair.relativeHomotopyGroup` applied to `triadHomotopyPathPair T x`. -/
abbrev triadHomotopyGroup (T : Triad X) (x : T.intersection) (q : ℕ) (hq : 2 ≤ q) :=
  SpacePair.relativeHomotopyGroup
    ⟨q - 1, Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hq)⟩
    (triadHomotopyPathPair T x)
    (triadHomotopyPathPairBasepoint T x)

/-- Unfolding `triadHomotopyGroup` recovers the shifted pair-relative homotopy group from
Definition 11.3.2. -/
theorem triadHomotopyGroup_def (T : Triad X) (x : T.intersection) (q : ℕ) (hq : 2 ≤ q) :
    triadHomotopyGroup T x q hq =
      SpacePair.relativeHomotopyGroup
        ⟨q - 1, Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hq)⟩
        (triadHomotopyPathPair T x)
        (triadHomotopyPathPairBasepoint T x) :=
  rfl

/-- The displayed higher degrees `q + 3` always satisfy the hypothesis `2 ≤ q + 3` required for
`triadHomotopyGroup`. -/
abbrev triadHigherGroupDegree (q : ℕ) : 2 ≤ q + 3 :=
  Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le (q + 1)))

/-- In degrees `q + 3`, triad homotopy groups inherit the canonical group structure from the
shifted pair-relative homotopy groups of the modeled path-space pair. -/
noncomputable instance triadHigherHomotopyGroupGroup
    (T : Triad X) (x : T.intersection) (q : ℕ) :
    Group (triadHomotopyGroup T x (q + 3) (triadHigherGroupDegree q)) := by
  simpa [triadHomotopyGroup, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (inferInstance :
      Group
        (SpacePair.relativeHomotopyGroup
          (q + 1).succPNat
          (triadHomotopyPathPair T x)
          (triadHomotopyPathPairBasepoint T x)))

/-- A point of `triadHomotopyPathPair T x` lies in the distinguished subspace exactly when it is
represented by a path in `A` ending in `A ∩ B`. -/
theorem mem_triadHomotopyPathPair_iff (T : Triad X) (x : T.intersection)
    (γ : triadAmbientPathSpace T x) :
    γ ∈ ((triadHomotopyPathPair T x).subspace : Set (triadAmbientPathSpace T x)) ↔
      ∃ δ : triadSubspacePathSpace T x, triadSubspacePathMap T x δ = γ :=
  Iff.rfl
