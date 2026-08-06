import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory

open CategoryTheory
open HomotopicalAlgebra
open SpacePair
open Topology

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: the classical CW API exposes
-- `Topology.RelCWComplex.skeleton`/`skeletonLT`, and Chapter 13 already fixes the relative
-- homology owner as `PairHomologyTheory` with connecting morphisms `(H.boundary q).app P`. This
-- item therefore uses the classical skeleta to build the source pair
-- `(X^n, X^(n-1))` concretely and
-- defines the cellular boundary by the Chapter 13 boundary map followed by the evident map into
-- the previous pair.

/-- The predecessor skeleton used in the skeletal pair `(X^n, X^(n - 1))`; for `n = 0` this is
the empty subspace `∅`, representing `X^(-1)`. -/
def previousCellularSkeleton (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :
    ℕ → Set X
  | 0 => ∅
  | n + 1 => cellularSkeleton X n

/-- In degree `0`, the predecessor skeleton used for the skeletal pair is `∅`. -/
@[simp] theorem previousCellularSkeleton_zero
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :
    previousCellularSkeleton X 0 = ∅ :=
  rfl

/-- In degree `n + 1`, the predecessor skeleton used for the skeletal pair is `X^n`. -/
@[simp] theorem previousCellularSkeleton_succ
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    previousCellularSkeleton X (n + 1) = cellularSkeleton X n :=
  rfl

/-- The predecessor skeleton agrees with the classical `skeletonLT` stages of the chosen CW
structure on `X`. -/
theorem previousCellularSkeleton_eq_skeletonLT
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    previousCellularSkeleton X n = Topology.CWComplex.skeletonLT (Set.univ : Set X) n := by
  cases n with
  | zero =>
      simpa using
        ((Topology.CWComplex.skeletonLT_zero_eq_empty :
          (Topology.CWComplex.skeletonLT (Set.univ : Set X) 0 : Set X) = ∅)).symm
  | succ n =>
      rfl

/-- The concrete pair `(X^n, X^(n - 1))` attached to the chosen CW structure on `X`. -/
abbrev axiomaticCellularChainPair
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) : SpacePair where
  space := TopCat.of (cellularSkeleton X n)
  subspace := Subtype.val ⁻¹' previousCellularSkeleton X n

/-- The canonical map from `X^n`, viewed as the subspace of `X^(n+1)`, to the previous pair
`(X^n, X^(n-1))`. -/
def axiomaticCellularBoundaryTargetMap
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    subspaceAbsolute (axiomaticCellularChainPair X (n + 1)) ⟶ axiomaticCellularChainPair X n :=
  { hom := TopCat.ofHom
      ⟨fun x ↦ ⟨x.1.1, x.2⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x ↦ x.2⟩
    map_subspace' := by
      intro x hx
      cases hx }

/-- Definition 15.2.1 (1): for a CW complex `X`, the cellular chain group `C_n(X)` is the
degree-`n` homology object `H_n(X^n, X^{n-1})`, modeled here by the pair
`axiomaticCellularChainPair X n = (X^n, X^{n-1})`. -/
abbrev axiomaticCellularChainGroup
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (n : ℕ) :
    ModuleCat ℤ :=
  (H.homology (n : ℤ)).obj (axiomaticCellularChainPair X n)

/-- Unfolding `axiomaticCellularChainGroup` identifies it with the degree-`n` homology object of the
explicit pair `(X^n, X^{n-1})`. -/
theorem axiomaticCellularChainGroup_eq
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (n : ℕ) :
    axiomaticCellularChainGroup X H n =
      (H.homology (n : ℤ)).obj (axiomaticCellularChainPair X n) :=
  rfl

/-- The degree identity `((n + 1 : ℤ) - 1) = n` used to align the Chapter 13 exact-sequence API
with the textbook indexing of cellular chains. -/
theorem axiomaticCellularBoundaryDegreeEq (n : ℕ) : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) :=
  Eq.trans (congrArg (fun z : ℤ ↦ z - 1) (Int.natCast_succ n)) (Int.add_sub_cancel (n : ℤ) 1)

/-- Definition 15.2.1 (2): the cellular differential `d : C_(n+1)(X) ⟶ C_n(X)` is the composite
of the Chapter 13 connecting morphism for `(X^(n+1), X^n)` with the canonical map from `X^n`,
viewed as a subspace of `X^(n+1)`, into the pair `(X^n, X^(n-1))`. -/
def axiomaticCellularBoundary
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (n : ℕ) :
    axiomaticCellularChainGroup X H (n + 1) ⟶ axiomaticCellularChainGroup X H n :=
  ((H.boundary ((n + 1 : ℕ) : ℤ)).app (axiomaticCellularChainPair X (n + 1))) ≫
    ((H.homology ((((n + 1 : ℕ) : ℤ) - 1))).map
      (axiomaticCellularBoundaryTargetMap X n)) ≫
      eqToHom
        (congrArg
          (fun q : ℤ ↦ (H.homology q).obj (axiomaticCellularChainPair X n))
          (axiomaticCellularBoundaryDegreeEq n))

/-- The defining formula for `axiomaticCellularBoundary` is the connecting morphism
`H_(n+1)(X^(n+1), X^n) ⟶ H_n(X^n)` followed by the canonical map
`H_n(X^n) ⟶ H_n(X^n, X^(n-1))`. -/
theorem axiomaticCellularBoundary_eq
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (n : ℕ) :
    axiomaticCellularBoundary X H n =
      ((H.boundary ((n + 1 : ℕ) : ℤ)).app (axiomaticCellularChainPair X (n + 1))) ≫
        ((H.homology ((((n + 1 : ℕ) : ℤ) - 1))).map
          (axiomaticCellularBoundaryTargetMap X n)) ≫
          eqToHom
            (congrArg
              (fun q : ℤ ↦ (H.homology q).obj (axiomaticCellularChainPair X n))
              (axiomaticCellularBoundaryDegreeEq n)) :=
  rfl
