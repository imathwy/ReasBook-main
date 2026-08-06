import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_1

open CategoryTheory
open scoped Topology Topology.Homotopy

universe u w

noncomputable section

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for `π_q`,
-- and Chapter 25 already models stable homotopy groups by sequential `GrpCat` colimits via
-- `Functor.ofSequence` and `GrpCat.FilteredColimits.colimit`. For a single pointed space, the
-- source formula is therefore formalized through the cofinal tail of suspended homotopy groups.

/-- The `n`-fold reduced suspension `Σ^n X` of a pointed compactly generated space. -/
def iteratedSuspensionSpace :
    ℕ → PointedCompactlyGenerated.{u, w} → PointedCompactlyGenerated.{u, w}
  | 0, X => X
  | n + 1, X => Σ (iteratedSuspensionSpace n X)

/-- Lean notation for the textbook iterated reduced suspension `Σ^n X`. -/
scoped[IteratedSuspension] notation "Σ^" n:max X:max => iteratedSuspensionSpace n X

open scoped IteratedSuspension

/-- Zero iterated suspensions recover the original pointed compactly generated space. -/
@[simp] theorem iteratedSuspensionSpace_zero (X : PointedCompactlyGenerated.{u, w}) :
    Σ^0 X = X := rfl

/-- One more iterated suspension is the reduced suspension of the previous stage. -/
@[simp] theorem iteratedSuspensionSpace_succ (n : ℕ) (X : PointedCompactlyGenerated.{u, w}) :
    Σ^(n + 1) X = Σ (Σ^n X) := rfl

/-- The `n`th stage in the cofinal tail computing the stable homotopy group of `X` in degree `q`,
namely `π_ (q + n + 1) (Σ^(n + 1) X)`. This shifted presentation keeps every stage group-valued
while preserving the source colimit `colim_n π_ (q + n) (Σ^n X)`. -/
abbrev stableHomotopyGroupStage
    (X : PointedCompactlyGenerated.{u, w}) (q n : ℕ) : GrpCat :=
  GrpCat.of
    (π_ (q + n + 1)
      (Σ^(n + 1) X).toCompactlyGenerated
      (Σ^(n + 1) X).point)

/-- Unfolding `stableHomotopyGroupStage X q n` gives the `(q + n + 1)`st homotopy group of the
`(n + 1)`st iterated suspension of `X`. -/
@[simp] theorem stableHomotopyGroupStage_def
    (X : PointedCompactlyGenerated.{u, w}) (q n : ℕ) :
    stableHomotopyGroupStage X q n =
      GrpCat.of
        (π_ (q + n + 1)
          (Σ^(n + 1) X).toCompactlyGenerated
          (Σ^(n + 1) X).point) := rfl

/-- The successor map in the stable suspension sequence, induced by the suspension homomorphism on
the `(n + 1)`st iterated suspension stage of `X`. -/
def stableHomotopyGroupStepMap
    (X : PointedCompactlyGenerated.{u, w}) (q n : ℕ) :
    stableHomotopyGroupStage X q n ⟶ stableHomotopyGroupStage X q (n + 1) :=
  let _ : NeZero (q + n + 1) := ⟨Nat.succ_ne_zero (q + n)⟩
  GrpCat.ofHom
    (suspensionHomomorphism (q + n + 1) (Σ^(n + 1) X))

/-- The sequential `GrpCat`-diagram whose filtered colimit computes the stable homotopy group of
`X` in degree `q`. -/
def stableHomotopyGroupDiagram
    (X : PointedCompactlyGenerated.{u, w}) (q : ℕ) : ℕ ⥤ GrpCat :=
  Functor.ofSequence (stableHomotopyGroupStepMap X q)

@[simp] theorem stableHomotopyGroupDiagram_map_succ
    (X : PointedCompactlyGenerated.{u, w}) (q n : ℕ) :
    (stableHomotopyGroupDiagram X q).map (homOfLE (Nat.le_add_right n 1)) =
      stableHomotopyGroupStepMap X q n := by
  exact Functor.ofSequence_map_homOfLE_succ (stableHomotopyGroupStepMap X q) n

/-- Definition 11.2.5. The `q`th stable homotopy group of `X` is formalized as the filtered
colimit of the cofinal tail `n ↦ π_ (q + n + 1) (Σ^(n + 1) X)` of the source sequence
`n ↦ π_ (q + n) (Σ^n X)`, so that every stage lies in `GrpCat`. -/
abbrev stableHomotopyGroup
    (X : PointedCompactlyGenerated.{u, w}) (q : ℕ) : GrpCat :=
  GrpCat.FilteredColimits.colimit (stableHomotopyGroupDiagram X q)

/-- Unfolding `stableHomotopyGroup X q` identifies it with the filtered colimit of its stable
suspension diagram. -/
@[simp] theorem stableHomotopyGroup_def
    (X : PointedCompactlyGenerated.{u, w}) (q : ℕ) :
    stableHomotopyGroup X q =
      GrpCat.FilteredColimits.colimit (stableHomotopyGroupDiagram X q) := rfl
