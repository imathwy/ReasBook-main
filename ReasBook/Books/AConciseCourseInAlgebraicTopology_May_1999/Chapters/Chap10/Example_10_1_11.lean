import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace

noncomputable section

open scoped TopCat

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall via `lean_leansearch` and local precedent from `Example_10_1_9` and
-- `Example_3_1_7`: the canonical owner for a source CW decomposition is a concrete
-- `Topology.CWComplex (Set.univ : Set X)` together with explicit comparison data, while the
-- standard double cover of `RP^n` is already owned by Chapter 3 as
-- `sphereToRealProjectiveSpace : 𝕊 n → RealProjectiveSpace n`.

/-- Example 10.1.11. A chosen standard CW structure on `RealProjectiveSpace n`, recording the
cell counts, skeletal identifications, and top attaching map. This is the concrete source-facing
owner for the standard CW decomposition of `RP^n`. -/
structure RealProjectiveSpaceStandardCWStructure (n : ℕ) where
  cwComplex : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n))
  finite :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    Topology.CWComplex.Finite (Set.univ : Set (RealProjectiveSpace n))
  cellCard_eq_one (m : ℕ) (hm : m ≤ n) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) = 1
  isEmpty_cell_of_lt (m : ℕ) (hm : n < m) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    IsEmpty (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m)
  skeletonHomeomorph (m : ℕ) (hm : m ≤ n) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    { x : RealProjectiveSpace n //
        x ∈
          (Topology.CWComplex.skeleton
            (Set.univ : Set (RealProjectiveSpace n)) (m : ℕ∞) :
              Set (RealProjectiveSpace n)) } ≃ₜ
      RealProjectiveSpace m
  topCell {k : ℕ} (hk : n = k + 1) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) (k + 1)
  topCellSkeletonHomeomorph {k : ℕ} (hk : n = k + 1) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    { x : RealProjectiveSpace n //
        x ∈
          (Topology.CWComplex.skeleton
            (Set.univ : Set (RealProjectiveSpace n)) (k : ℕ∞) :
              Set (RealProjectiveSpace n)) } ≃ₜ
      RealProjectiveSpace k
  topCellBoundaryHomeomorph {k : ℕ} (hk : n = k + 1) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    TopCat.sphere k ≃ₜ Metric.sphere (0 : Fin (k + 1) → ℝ) 1
  topCellAttachingMap {k : ℕ} (hk : n = k + 1) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    TopCat.sphere k →
      { x : RealProjectiveSpace n //
          x ∈
            (Topology.CWComplex.skeleton
              (Set.univ : Set (RealProjectiveSpace n)) (k : ℕ∞) :
                Set (RealProjectiveSpace n)) }
  topCellAttachingMap_spec {k : ℕ} (hk : n = k + 1) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    ∀ x : TopCat.sphere k,
      (topCellAttachingMap hk x).1 =
        cwComplex.map (k + 1) (topCell hk) (topCellBoundaryHomeomorph hk x).1
  topCellAttachingMap_eq {k : ℕ} (hk : n = k + 1) :
    -- Local instance justification (noncanonical choice): chosen `cwComplex`, not global.
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace n)) := cwComplex
    topCellSkeletonHomeomorph hk ∘ topCellAttachingMap hk = sphereToRealProjectiveSpace k

namespace RealProjectiveSpaceStandardCWStructure

variable {n : ℕ}

/-- The top attaching map of a chosen standard CW structure on `RP^(k + 1)`, viewed through the
canonical identification of the `k`-skeleton with `RP^k`. -/
def topAttachingMap (S : RealProjectiveSpaceStandardCWStructure n) {k : ℕ} (hk : n = k + 1) :
    TopCat.sphere k → RealProjectiveSpace k :=
  S.topCellSkeletonHomeomorph hk ∘ S.topCellAttachingMap hk

/-- Viewed back inside the `k`-skeleton of `RP^(k + 1)`, `topAttachingMap` agrees with the
actual attaching map of the chosen top cell of the underlying CW complex. -/
theorem topAttachingMap_spec (S : RealProjectiveSpaceStandardCWStructure n) {k : ℕ}
    (hk : n = k + 1) (x : TopCat.sphere k) :
    letI := S.cwComplex
    ((S.topCellSkeletonHomeomorph hk).symm (S.topAttachingMap hk x)).1 =
      S.cwComplex.map (k + 1) (S.topCell hk) (S.topCellBoundaryHomeomorph hk x).1 := by
  letI := S.cwComplex
  have hsymm :
      (S.topCellSkeletonHomeomorph hk).symm (S.topAttachingMap hk x) =
        S.topCellAttachingMap hk x := by
    simpa [topAttachingMap] using
      (S.topCellSkeletonHomeomorph hk).symm_apply_apply (S.topCellAttachingMap hk x)
  calc
    ((S.topCellSkeletonHomeomorph hk).symm (S.topAttachingMap hk x)).1 =
        (S.topCellAttachingMap hk x).1 := congrArg Subtype.val hsymm
    _ = S.cwComplex.map (k + 1) (S.topCell hk) (S.topCellBoundaryHomeomorph hk x).1 :=
        S.topCellAttachingMap_spec hk x

/-- For `n = k + 1`, the top attaching map of a chosen standard CW structure on `RP^n` is the
standard double cover `sphereToRealProjectiveSpace k`. -/
theorem topAttachingMap_eq (S : RealProjectiveSpaceStandardCWStructure n) {k : ℕ}
    (hk : n = k + 1) :
    S.topAttachingMap hk = sphereToRealProjectiveSpace k :=
  S.topCellAttachingMap_eq hk

/-- A chosen standard CW structure on `RP^n` exposes the Prop-valued clauses from the source,
while the skeletal identifications remain explicit owner data via `S`. -/
theorem spec (S : RealProjectiveSpaceStandardCWStructure n) :
    letI := S.cwComplex
    (∀ m : ℕ,
      m ≤ n →
        Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m) = 1) ∧
    (∀ m : ℕ,
      n < m →
        IsEmpty (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace n)) m)) ∧
    (∀ {k : ℕ}, ∀ hk : n = k + 1, S.topAttachingMap hk = sphereToRealProjectiveSpace k) := by
  letI := S.cwComplex
  exact ⟨S.cellCard_eq_one, S.isEmpty_cell_of_lt, S.topAttachingMap_eq⟩

end RealProjectiveSpaceStandardCWStructure

/-- Helper for Example 10.1.11: the vector `(1)` lies on the concrete model of `S⁰`. -/
private theorem sphereZeroPos_mem :
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈ TopCat.SphereModel 0 := by
  simp [TopCat.SphereModel]

/-- Helper for Example 10.1.11: the chosen positive point of `S⁰`. -/
private def sphereZeroPos : TopCat.sphere 0 :=
  ULift.up <| ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), sphereZeroPos_mem⟩

/-- Helper for Example 10.1.11: the distinguished point of `RP⁰`. -/
private def realProjectiveSpaceZeroPoint : RealProjectiveSpace 0 :=
  sphereToRealProjectiveSpace 0 sphereZeroPos

/-- Helper for Example 10.1.11: every point of `S⁰` is either `sphereZeroPos` or its antipode. -/
private theorem sphereZero_eq_or_eq_neg (x : TopCat.sphere 0) :
    x = sphereZeroPos ∨ x = -sphereZeroPos := by
  -- Express `x` by its unique coordinate in `ℝ`.
  have hxsingle : x.down.1 = EuclideanSpace.single (0 : Fin 1) (x.down.1 0) := by
    ext i
    fin_cases i
    simp [EuclideanSpace.single]
  have hxmem : dist x.down.1 0 = 1 := by
    simpa [Metric.mem_sphere] using x.down.2
  have hxnorm : ‖x.down.1‖ = 1 := by
    simpa [dist_eq_norm] using hxmem
  have hnormeq : ‖x.down.1‖ = ‖EuclideanSpace.single (0 : Fin 1) (x.down.1 0 : ℝ)‖ :=
    congrArg norm hxsingle
  have hnormsingle : ‖EuclideanSpace.single (0 : Fin 1) (x.down.1 0 : ℝ)‖ = ‖x.down.1 0‖ := by
    simpa using
      (PiLp.norm_single (0 : Fin 1) (x.down.1 0 : ℝ))
  have hxcoordnorm : ‖x.down.1 0‖ = 1 := by
    calc
      ‖x.down.1 0‖ = ‖EuclideanSpace.single (0 : Fin 1) (x.down.1 0 : ℝ)‖ := hnormsingle.symm
      _ = ‖x.down.1‖ := hnormeq.symm
      _ = 1 := hxnorm
  have habs : |x.down.1 0| = 1 := by
    simpa [Real.norm_eq_abs] using hxcoordnorm
  have hsq : (x.down.1 0) ^ 2 = (1 : ℝ) ^ 2 := by
    nlinarith [abs_mul_abs_self (x.down.1 0), habs]
  have hcoord : x.down.1 0 = 1 ∨ x.down.1 0 = -1 :=
    eq_or_eq_neg_of_sq_eq_sq _ _ hsq
  -- The coordinate classification lifts back to `S⁰`.
  cases hcoord with
  | inl h =>
      left
      apply ULift.ext
      apply Subtype.ext
      ext i
      fin_cases i
      simpa [sphereZeroPos, EuclideanSpace.single] using h
  | inr h =>
      right
      apply ULift.ext
      apply Subtype.ext
      ext i
      fin_cases i
      simpa [sphereZeroPos, EuclideanSpace.single] using h

/-- Helper for Example 10.1.11: the quotient model `RP⁰` is a subsingleton. -/
private theorem realProjectiveSpaceZero_subsingleton : Subsingleton (RealProjectiveSpace 0) := by
  refine ⟨fun x y ↦ ?_⟩
  -- Reduce the quotient equality to the two representatives of `S⁰`.
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  rcases sphereZero_eq_or_eq_neg a with ha | ha
  · rcases sphereZero_eq_or_eq_neg b with hb | hb
    · rw [ha, hb]
    · rw [ha, hb]
      exact ((sphereToRealProjectiveSpace_eq_iff 0).2 <| Or.inr rfl).symm
  · rcases sphereZero_eq_or_eq_neg b with hb | hb
    · rw [ha, hb]
      exact (sphereToRealProjectiveSpace_eq_iff 0).2 <| Or.inr rfl
    · rw [ha, hb]

/-- Helper for Example 10.1.11: the one-point cell family has one `0`-cell and no higher cells. -/
private abbrev pointSpaceCell (n : ℕ) :=
  ULift (PLift (n = 0))

/-- Helper for Example 10.1.11: the unique `0`-cell index in the one-point cell family. -/
private theorem pointSpaceCell_zero_eq (c : pointSpaceCell 0) :
    c = ⟨⟨rfl⟩⟩ := by
  -- The degree-`0` cell index type is `PLift True`, so every inhabitant is canonical.
  cases c with
  | up c =>
      cases c
      rfl

/-- Helper for Example 10.1.11: positive-dimensional cells are absent in the one-point cell
family. -/
private theorem pointSpaceCell_false_of_pos {n : ℕ} (hn : 0 < n) (c : pointSpaceCell n) :
    False :=
  (Nat.ne_of_gt hn) c.down.down

/-- Helper for Example 10.1.11: the one-point cell family has a unique `0`-cell. -/
private abbrev pointSpaceZeroCellUnique : Unique (pointSpaceCell 0) where
  default := ⟨⟨rfl⟩⟩
  uniq := pointSpaceCell_zero_eq

/-- Helper for Example 10.1.11: the distinguished `0`-cell index in the one-point CW model. -/
private abbrev pointSpaceZeroCell : pointSpaceCell 0 :=
  pointSpaceZeroCellUnique.default

/-- Helper for Example 10.1.11: the one-point cell family has no positive-dimensional cells. -/
private abbrev pointSpaceCellIsEmptyOfPos {n : ℕ} (hn : 0 < n) : IsEmpty (pointSpaceCell n) where
  false := pointSpaceCell_false_of_pos hn

/-- Helper for Example 10.1.11: the one-point cell family only has a single total cell index. -/
private theorem pointSpaceCells_subsingleton :
    Subsingleton (Σ n, pointSpaceCell n) := by
  -- Any cell index must lie in degree `0`, and the degree-`0` index is itself unique.
  refine ⟨fun a b ↦ ?_⟩
  rcases a with ⟨na, ⟨⟨ha⟩⟩⟩
  rcases b with ⟨nb, ⟨⟨hb⟩⟩⟩
  subst ha
  subst hb
  rfl

/-- Helper for Example 10.1.11: the unique `0`-cell on a one-point space is the constant
characteristic map. -/
private def pointSpaceCellMap (X : Type*) [TopologicalSpace X] [Unique X] (n : ℕ)
    (c : pointSpaceCell n) : PartialEquiv (Fin n → ℝ) X :=
  match n with
  | 0 => PartialEquiv.single 0 (default : X)
  | k + 1 => False.elim (Nat.succ_ne_zero k c.down.down)

/-- Helper for Example 10.1.11: only degree `0` survives in the one-point cell family. -/
private theorem pointSpaceCell_eventuallyIsEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (pointSpaceCell n) := by
  -- Beyond degree `0`, every cell index is impossible.
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  exact pointSpaceCellIsEmptyOfPos (Nat.succ_le_iff.mp hn)

/-- Helper for Example 10.1.11: each degree of the one-point cell family is finite. -/
private theorem pointSpaceCell_finite (n : ℕ) : Finite (pointSpaceCell n) := by
  exact Finite.of_subsingleton

/-- Helper for Example 10.1.11: the one-point characteristic map has the standard open-ball
source. -/
private theorem pointSpaceCell_source_eq (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      (pointSpaceCellMap X n c).source = Metric.ball 0 1 := by
  intro n c
  cases n with
  | zero =>
      -- In dimension `0`, the open unit ball is the singleton empty tuple.
      ext x
      simp [pointSpaceCellMap, Matrix.empty_eq]
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Example 10.1.11: the one-point characteristic map is continuous on the closed unit
ball. -/
private theorem pointSpaceCell_continuousOn (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      ContinuousOn (pointSpaceCellMap X n c) (Metric.closedBall 0 1) := by
  intro n c
  cases n with
  | zero =>
      -- The unique `0`-cell is given by a constant map.
      simpa [pointSpaceCellMap] using
        (continuous_const.continuousOn :
          ContinuousOn (Function.const (Fin 0 → ℝ) (default : X)) (Metric.closedBall 0 1))
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Example 10.1.11: the inverse of the one-point characteristic map is continuous on
its target. -/
private theorem pointSpaceCell_continuousOn_symm (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      ContinuousOn (pointSpaceCellMap X n c).symm (pointSpaceCellMap X n c).target := by
  intro n c
  cases n with
  | zero =>
      -- The inverse is again constant because both source and target are singletons.
      simpa [pointSpaceCellMap] using
        (continuous_const.continuousOn :
          ContinuousOn (Function.const X (0 : Fin 0 → ℝ)) {default})
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Example 10.1.11: the one-point open cells are pairwise disjoint because there is
only one total cell index. -/
private theorem pointSpaceCell_pairwiseDisjoint (X : Type*) [TopologicalSpace X] [Unique X] :
    (Set.univ : Set (Σ n, pointSpaceCell n)).PairwiseDisjoint
      (fun ni ↦ pointSpaceCellMap X ni.1 ni.2 '' Metric.ball 0 1) := by
  -- Distinct sigma-indices cannot occur in the one-point cell family.
  intro a _ b _ hab
  exact (hab (pointSpaceCells_subsingleton.elim a b)).elim

/-- Helper for Example 10.1.11: the boundary condition for the one-point CW model is vacuous
because only a `0`-cell exists. -/
private theorem pointSpaceCell_mapsTo (X : Type*) [TopologicalSpace X] [Unique X] :
    ∀ (n : ℕ) (c : pointSpaceCell n),
      Set.MapsTo
        (pointSpaceCellMap X n c)
        (Metric.sphere 0 1)
        (⋃ (m : ℕ) (_ : m < n) (j : pointSpaceCell m),
          pointSpaceCellMap X m j '' Metric.closedBall 0 1) := by
  intro n c x hx
  cases n with
  | zero =>
      -- The boundary of a `0`-cell is empty.
      simpa [Metric.sphere_eq_empty_of_subsingleton] using hx
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Example 10.1.11: the closed `0`-cell covers any one-point space. -/
private theorem pointSpaceCell_union (X : Type*) [TopologicalSpace X] [Unique X] :
    (⋃ (n : ℕ) (j : pointSpaceCell n),
      pointSpaceCellMap X n j '' Metric.closedBall 0 1) = (Set.univ : Set X) := by
  -- Every point is the unique closed `0`-cell image.
  ext x
  constructor
  · intro _
    simp
  · intro _
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    refine Set.mem_iUnion.2 ⟨(⟨⟨rfl⟩⟩ : pointSpaceCell 0), ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp
    · have hx : x = default := Subsingleton.elim _ _
      simpa [pointSpaceCellMap, hx]

/-- Helper for Example 10.1.11: any one-point space carries the obvious CW complex with one
`0`-cell. -/
private noncomputable abbrev pointSpaceCWComplex (X : Type*) [TopologicalSpace X] [Unique X] :
    Topology.CWComplex (Set.univ : Set X) :=
  Topology.CWComplex.mkFinite
    (Set.univ : Set X)
    pointSpaceCell
    (pointSpaceCellMap X)
    pointSpaceCell_eventuallyIsEmpty
    pointSpaceCell_finite
    (pointSpaceCell_source_eq X)
    (pointSpaceCell_continuousOn X)
    (pointSpaceCell_continuousOn_symm X)
    (pointSpaceCell_pairwiseDisjoint X)
    (pointSpaceCell_mapsTo X)
    (pointSpaceCell_union X)

/-- Helper for Example 10.1.11: the one-point CW complex built by `Topology.CWComplex.mkFinite`
is finite. -/
private theorem pointSpaceCWComplex_finite (X : Type*) [TopologicalSpace X] [Unique X] :
    letI := pointSpaceCWComplex X
    Topology.CWComplex.Finite (Set.univ : Set X) := by
  -- Unfold the explicit `mkFinite` model once and use its finite-cells theorem.
  simpa [pointSpaceCWComplex] using
    (Topology.CWComplex.finite_mkFinite
      (Set.univ : Set X)
      pointSpaceCell
      (pointSpaceCellMap X)
      pointSpaceCell_eventuallyIsEmpty
      pointSpaceCell_finite
      (pointSpaceCell_source_eq X)
      (pointSpaceCell_continuousOn X)
      (pointSpaceCell_continuousOn_symm X)
      (pointSpaceCell_pairwiseDisjoint X)
      (pointSpaceCell_mapsTo X)
      (pointSpaceCell_union X))

/-- Helper for Example 10.1.11: the unique `0`-cell index in the one-point CW complex, viewed in
the `Topology.CWComplex.cell` API. -/
private noncomputable def pointSpaceZeroCellIndex (X : Type*) [TopologicalSpace X] [Unique X] :
    letI := pointSpaceCWComplex X
    Topology.CWComplex.cell (Set.univ : Set X) 0 := by
  letI := pointSpaceCWComplex X
  simpa [pointSpaceCWComplex] using (pointSpaceZeroCell : pointSpaceCell 0)

/-- Helper for Example 10.1.11: in the one-point CW model, the unique point lies in the closed
`0`-cell. -/
private theorem pointSpace_default_mem_closedCell (X : Type*) [TopologicalSpace X] [Unique X] :
    letI := pointSpaceCWComplex X
    (default : X) ∈ Topology.CWComplex.closedCell 0 (pointSpaceZeroCellIndex X) := by
  letI := pointSpaceCWComplex X
  -- The unique point is the image of the center of the closed `0`-ball.
  refine ⟨0, ?_, ?_⟩
  · simp
  · exact Subsingleton.elim _ _

/-- Helper for Example 10.1.11: every skeleton of the one-point CW model contains the unique
point. -/
private theorem pointSpace_default_mem_skeleton (X : Type*) [TopologicalSpace X] [Unique X]
    (q : ℕ∞) :
    letI := pointSpaceCWComplex X
    (default : X) ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) q : Set X) := by
  letI := pointSpaceCWComplex X
  -- First place the point in the closed `0`-cell, then enlarge from the `0`-skeleton.
  have hzero :
      (default : X) ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) (0 : ℕ∞) : Set X) := by
    exact Topology.CWComplex.closedCell_subset_skeleton
      0
      (pointSpaceZeroCellIndex X)
      (pointSpace_default_mem_closedCell X)
  exact Topology.CWComplex.skeleton_mono
    (show (0 : ℕ∞) ≤ q by exact bot_le) hzero

/-- Helper for Example 10.1.11: a nonempty subtype of a one-point space is again a one-point
space. -/
private noncomputable abbrev uniqueSubtypeOfUnique {X : Type*} [Unique X] {s : Set X}
    (hs : (default : X) ∈ s) : Unique s :=
  { default := ⟨default, hs⟩
    uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _) }

/-- Helper for Example 10.1.11: the `q`-skeleton in the explicit one-point CW model. -/
private noncomputable abbrev pointSpaceSkeleton (X : Type*) [TopologicalSpace X] [Unique X]
    (q : ℕ∞) :=
  @Topology.CWComplex.skeleton
    X
    inferInstance
    inferInstance
    (Set.univ : Set X)
    ∅
    (@Topology.CWComplex.instRelCWComplex
      X
      inferInstance
      (Set.univ : Set X)
      (pointSpaceCWComplex X))
    q

/-- Helper for Example 10.1.11: every skeleton of the one-point CW model is homeomorphic to the
ambient one-point space. -/
private noncomputable def pointSpaceSkeletonHomeomorph (X : Type*) [TopologicalSpace X] [Unique X]
    (q : ℕ∞) : pointSpaceSkeleton X q ≃ₜ X := by
  let hskeleton :
      (default : X) ∈ (pointSpaceSkeleton X q : Set X) := by
    simpa [pointSpaceSkeleton] using (pointSpace_default_mem_skeleton X q)
  let hUnique : Unique (pointSpaceSkeleton X q) :=
    uniqueSubtypeOfUnique hskeleton
  refine
    { toEquiv := @Equiv.ofUnique
        (pointSpaceSkeleton X q)
        X
        hUnique
        inferInstance
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }

/-- Helper for Example 10.1.11: `RP⁰` is a one-point space. -/
private noncomputable abbrev realProjectiveSpaceZero_unique :
    Unique (RealProjectiveSpace 0) :=
  letI := realProjectiveSpaceZero_subsingleton
  { default := realProjectiveSpaceZeroPoint
    uniq := fun _ ↦ Subsingleton.elim _ _ }

/-- Helper for Example 10.1.11: the explicit one-point CW complex specialized to `RP⁰`. -/
private noncomputable abbrev realProjectiveSpaceZeroCWComplex :
    Topology.CWComplex (Set.univ : Set (RealProjectiveSpace 0)) :=
  letI : Unique (RealProjectiveSpace 0) := realProjectiveSpaceZero_unique
  pointSpaceCWComplex (RealProjectiveSpace 0)

/-- Helper for Example 10.1.11: the one-point CW model on `RP⁰` has exactly one cell in the only
possible degree. -/
private theorem realProjectiveSpaceStandardCWStructureZero_cellCard_eq_one
    (m : ℕ) (hm : m ≤ 0) :
    letI := realProjectiveSpaceZeroCWComplex
    Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace 0)) m) = 1 := by
  letI := realProjectiveSpaceZeroCWComplex
  match m with
  | 0 =>
      -- The base CW model has a unique `0`-cell.
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨⟨fun a b ↦ by rw [pointSpaceZeroCellUnique.uniq a, pointSpaceZeroCellUnique.uniq b]⟩,
          ⟨pointSpaceZeroCell⟩⟩
  | k + 1 =>
      exact False.elim (Nat.not_succ_le_zero k hm)

/-- Helper for Example 10.1.11: the one-point CW model on `RP⁰` has no positive-dimensional
cells. -/
private noncomputable abbrev realProjectiveSpaceStandardCWStructureZero_isEmpty_cell_of_lt
    (m : ℕ) (hm : 0 < m) :
    letI := realProjectiveSpaceZeroCWComplex
    IsEmpty (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace 0)) m) :=
  pointSpaceCellIsEmptyOfPos hm

/-- Helper for Example 10.1.11: the skeleton clause for `RP⁰` is the one-point homeomorphism. -/
private noncomputable def realProjectiveSpaceStandardCWStructureZero_skeletonHomeomorph
    (m : ℕ) (hm : m ≤ 0) :
    letI := realProjectiveSpaceZeroCWComplex
    { x : RealProjectiveSpace 0 //
        x ∈
          (Topology.CWComplex.skeleton
            (Set.univ : Set (RealProjectiveSpace 0)) (m : ℕ∞) :
              Set (RealProjectiveSpace 0)) } ≃ₜ
      RealProjectiveSpace m :=
  letI : Unique (RealProjectiveSpace 0) := realProjectiveSpaceZero_unique
  match m with
  | 0 => pointSpaceSkeletonHomeomorph (RealProjectiveSpace 0) (0 : ℕ∞)
  | k + 1 => False.elim (Nat.not_succ_le_zero k hm)

/-- Helper for Example 10.1.11: the explicit one-point CW complex on `RP⁰` is finite. -/
private theorem realProjectiveSpaceZeroCWComplex_finite :
    letI := realProjectiveSpaceZeroCWComplex
    Topology.CWComplex.Finite (Set.univ : Set (RealProjectiveSpace 0)) := by
  letI : Unique (RealProjectiveSpace 0) := realProjectiveSpaceZero_unique
  simpa [realProjectiveSpaceZeroCWComplex] using
    pointSpaceCWComplex_finite (RealProjectiveSpace 0)

/-- Helper for Example 10.1.11: the base-case witness should be the one-point CW structure on
`RP⁰`, using the proven fact that `RP⁰` is a singleton quotient of `S⁰`. -/
private noncomputable def realProjectiveSpaceStandardCWStructureZero :
    RealProjectiveSpaceStandardCWStructure 0 :=
  letI : Unique (RealProjectiveSpace 0) := realProjectiveSpaceZero_unique
  { cwComplex := realProjectiveSpaceZeroCWComplex
    finite := realProjectiveSpaceZeroCWComplex_finite
    cellCard_eq_one := realProjectiveSpaceStandardCWStructureZero_cellCard_eq_one
    isEmpty_cell_of_lt := realProjectiveSpaceStandardCWStructureZero_isEmpty_cell_of_lt
    skeletonHomeomorph := realProjectiveSpaceStandardCWStructureZero_skeletonHomeomorph
    topCell := fun hk ↦ False.elim (Nat.succ_ne_zero _ hk.symm)
    topCellSkeletonHomeomorph := fun hk ↦ False.elim (Nat.succ_ne_zero _ hk.symm)
    topCellBoundaryHomeomorph := fun hk ↦ False.elim (Nat.succ_ne_zero _ hk.symm)
    topCellAttachingMap := fun hk ↦ False.elim (Nat.succ_ne_zero _ hk.symm)
    topCellAttachingMap_spec := fun hk ↦ False.elim (Nat.succ_ne_zero _ hk.symm)
    topCellAttachingMap_eq := fun hk ↦ False.elim (Nat.succ_ne_zero _ hk.symm) }

/-- Helper for Example 10.1.11: the equator of `S^(k + 1)` is the last-coordinate zero locus,
which models the boundary sphere of the top cell in `RP^(k + 1)`. -/
private def sphereEquatorLocus (k : ℕ) : Set (TopCat.sphere (k + 1)) :=
  { x | x.down.1 (Fin.last (k + 1)) = 0 }

/-- Helper for Example 10.1.11: the ambient zero-extension map `ℝ^(k + 1) → ℝ^(k + 2)` inserts a
last coordinate equal to `0`. -/
private noncomputable def realProjectiveSpaceSuccLinearMap (k : ℕ) :
    (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 2) → ℝ) :=
  LinearMap.pi fun i : Fin (k + 2) ↦
    if h : i < k + 1 then LinearMap.proj (Fin.castLT i h) else 0

/-- Helper for Example 10.1.11: zero-extension agrees with the original vector on the first
`k + 1` coordinates. -/
@[simp]
private theorem realProjectiveSpaceSuccLinearMap_apply_castSucc (k : ℕ)
    (v : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    realProjectiveSpaceSuccLinearMap k v i.castSucc = v i := by
  -- The initial coordinates are read off by the corresponding coordinate projections.
  have hle : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.is_lt
  simp [realProjectiveSpaceSuccLinearMap, hle]

/-- Helper for Example 10.1.11: zero-extension sends the last coordinate to `0`. -/
@[simp]
private theorem realProjectiveSpaceSuccLinearMap_apply_last (k : ℕ)
    (v : Fin (k + 1) → ℝ) :
    realProjectiveSpaceSuccLinearMap k v (Fin.last (k + 1)) = 0 := by
  -- The last coordinate lands in the zero summand of the extension.
  simp [realProjectiveSpaceSuccLinearMap]

/-- Helper for Example 10.1.11: the ambient zero-extension map is injective. -/
private theorem realProjectiveSpaceSuccLinearMap_injective (k : ℕ) :
    Function.Injective (realProjectiveSpaceSuccLinearMap k) := by
  intro x y hxy
  -- Compare the images on the first `k + 1` coordinates to recover the source vectors.
  ext i
  have hcoord := congrArg (fun f : Fin (k + 2) → ℝ ↦ f i.castSucc) hxy
  simpa using hcoord

/-- Helper for Example 10.1.11: the ambient equatorial hyperplane in `ℝ^(k + 2)` is the
last-coordinate-zero subspace. -/
private noncomputable def realProjectiveSpaceSuccHyperplane (k : ℕ) :
    Submodule ℝ (Fin (k + 2) → ℝ) :=
  LinearMap.ker (LinearMap.proj (Fin.last (k + 1)))

/-- Helper for Example 10.1.11: membership in the equatorial hyperplane means vanishing last
coordinate. -/
@[simp]
private theorem mem_realProjectiveSpaceSuccHyperplane (k : ℕ) (v : Fin (k + 2) → ℝ) :
    v ∈ realProjectiveSpaceSuccHyperplane k ↔ v (Fin.last (k + 1)) = 0 := by
  -- The hyperplane is defined as the kernel of the last-coordinate projection.
  rfl

/-- Helper for Example 10.1.11: zero-extension lands in the equatorial hyperplane. -/
private theorem realProjectiveSpaceSuccLinearMap_mem_hyperplane (k : ℕ)
    (v : Fin (k + 1) → ℝ) :
    realProjectiveSpaceSuccLinearMap k v ∈ realProjectiveSpaceSuccHyperplane k := by
  -- The defining last coordinate of a zero-extended vector is `0`.
  simp [realProjectiveSpaceSuccHyperplane]

/-- Helper for Example 10.1.11: truncation drops the last coordinate of a vector in `ℝ^(k + 2)`.
-/
private noncomputable def realProjectiveSpaceSuccHyperplaneLift (k : ℕ)
    (v : Fin (k + 2) → ℝ) : Fin (k + 1) → ℝ :=
  fun i ↦ v i.castSucc

/-- Helper for Example 10.1.11: if the last coordinate vanishes, truncation followed by
zero-extension recovers the original vector. -/
private theorem realProjectiveSpaceSuccLinearMap_lift_eq (k : ℕ)
    {v : Fin (k + 2) → ℝ} (hv : v ∈ realProjectiveSpaceSuccHyperplane k) :
    realProjectiveSpaceSuccLinearMap k (realProjectiveSpaceSuccHyperplaneLift k v) = v := by
  -- Compare the first `k + 1` coordinates and the last coordinate separately.
  ext i
  cases i using Fin.lastCases with
  | last =>
      simpa [realProjectiveSpaceSuccHyperplane,
        realProjectiveSpaceSuccHyperplaneLift] using hv.symm
  | cast j =>
      simp [realProjectiveSpaceSuccHyperplaneLift]

/-- Helper for Example 10.1.11: the sphere equator condition is exactly the ambient hyperplane
condition on the chosen representative. -/
private theorem mem_sphereEquatorLocus_iff_mem_hyperplane (k : ℕ)
    (x : TopCat.sphere (k + 1)) :
    x ∈ sphereEquatorLocus k ↔
      (((x.down.1 : EuclideanSpace ℝ (Fin (k + 2))) : Fin (k + 2) → ℝ) ∈
        realProjectiveSpaceSuccHyperplane k) := by
  -- Both predicates say that the last coordinate of the representative is `0`.
  simpa [sphereEquatorLocus, mem_realProjectiveSpaceSuccHyperplane]

/-- Helper for Example 10.1.11: an equatorial sphere point is exactly a unit vector coming from
ambient zero-extension. -/
private theorem mem_sphereEquatorLocus_iff_exists_zeroExtend (k : ℕ)
    (x : TopCat.sphere (k + 1)) :
    x ∈ sphereEquatorLocus k ↔
      ∃ v : Fin (k + 1) → ℝ, realProjectiveSpaceSuccLinearMap k v = x.down.1 := by
  constructor
  · intro hx
    -- Truncating the equatorial representative gives the unique ambient preimage.
    refine ⟨realProjectiveSpaceSuccHyperplaneLift k x.down.1, ?_⟩
    exact
      realProjectiveSpaceSuccLinearMap_lift_eq k
        (by
          change (((x.down.1 : EuclideanSpace ℝ (Fin (k + 2))) : Fin (k + 2) → ℝ) ∈
            realProjectiveSpaceSuccHyperplane k)
          simpa using (mem_sphereEquatorLocus_iff_mem_hyperplane k x).mp hx)
  · rintro ⟨v, hv⟩
    -- Any ambient zero-extension has last coordinate `0`, so it lies on the equator.
    rw [sphereEquatorLocus]
    exact
      (((realProjectiveSpaceSuccLinearMap_apply_last k v).symm.trans
        (congrArg (fun f : Fin (k + 2) → ℝ ↦ f (Fin.last (k + 1))) hv)).symm)

/-- Helper for Example 10.1.11: a concrete basepoint on the equator of `S^(k + 1)`. -/
private def sphereEquatorBasepoint (k : ℕ) : TopCat.sphere (k + 1) :=
  ULift.up <| ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩

/-- Helper for Example 10.1.11: the chosen sphere basepoint lies on the equator. -/
private theorem sphereEquatorBasepoint_mem (k : ℕ) :
    sphereEquatorBasepoint k ∈ sphereEquatorLocus k := by
  -- The last coordinate of the first basis vector vanishes, so it lies in the equator.
  simp [sphereEquatorBasepoint, sphereEquatorLocus]

/-- Helper for Example 10.1.11: the equatorial copy of `RP^k` inside `RP^(k + 1)`, obtained by
projectivizing the equator of `S^(k + 1)`. -/
private def realProjectiveSpaceEquatorLocus (k : ℕ) : Set (RealProjectiveSpace (k + 1)) :=
  (sphereToRealProjectiveSpace (k + 1)) '' sphereEquatorLocus k

/-- Helper for Example 10.1.11: the chosen projective-space basepoint lies on the equatorial copy
of `RP^k` inside `RP^(k + 1)`. -/
private theorem realProjectiveSpaceEquatorBasepoint_mem (k : ℕ) :
    sphereToRealProjectiveSpace (k + 1) (sphereEquatorBasepoint k) ∈
      realProjectiveSpaceEquatorLocus k := by
  -- The projective basepoint is represented by an equatorial sphere point.
  exact ⟨sphereEquatorBasepoint k, sphereEquatorBasepoint_mem k, rfl⟩

/-- Helper for Example 10.1.11: a distinguished point on the equatorial copy of `RP^k`. -/
private def realProjectiveSpaceEquatorBasepoint (k : ℕ) :
    realProjectiveSpaceEquatorLocus k :=
  ⟨sphereToRealProjectiveSpace (k + 1) (sphereEquatorBasepoint k),
    realProjectiveSpaceEquatorBasepoint_mem k⟩

/-- Helper for Example 10.1.11: the equatorial copy of `RP^k` inside `RP^(k + 1)` is nonempty. -/
private theorem realProjectiveSpaceEquatorLocus_nonempty (k : ℕ) :
    (realProjectiveSpaceEquatorLocus k).Nonempty :=
  ⟨_, realProjectiveSpaceEquatorBasepoint_mem k⟩

/-- Helper for Example 10.1.11: the standard double-cover quotient map `Sⁿ → RPⁿ` is surjective. -/
private theorem sphereToRealProjectiveSpace_surjective (n : ℕ) :
    Function.Surjective (sphereToRealProjectiveSpace n) := by
  -- Unpack a projective point into one chosen sphere representative.
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  exact ⟨y, rfl⟩

/-- Helper for Example 10.1.11: the standard double-cover quotient map `Sⁿ → RPⁿ` is a quotient
map. -/
private theorem sphereToRealProjectiveSpace_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (sphereToRealProjectiveSpace n) := by
  -- A surjective covering map is automatically a quotient map.
  exact (sphereToRealProjectiveSpace_isCoveringMap n).isQuotientMap
    (sphereToRealProjectiveSpace_surjective n)

/-- Helper for Example 10.1.11: the relation collapsing a subset `A ⊆ X` to a single point. -/
private def collapseSubsetRel {X : Type*} [TopologicalSpace X] (A : Set X) : X → X → Prop :=
  fun x y ↦ x = y ∨ (x ∈ A ∧ y ∈ A)

/-- Helper for Example 10.1.11: the quotient setoid collapsing `A ⊆ X` to one point. -/
private abbrev collapseSubsetSetoid {X : Type*} [TopologicalSpace X] (A : Set X) : Setoid X :=
  Relation.EqvGen.setoid (collapseSubsetRel A)

/-- Helper for Example 10.1.11: the quotient of `RP^(k + 1)` obtained by collapsing the
equatorial copy of `RP^k` to a point. -/
private abbrev realProjectiveSpaceEquatorQuotient (k : ℕ) :=
  Quotient (collapseSubsetSetoid (realProjectiveSpaceEquatorLocus k))

/-- Helper for Example 10.1.11: the distinguished collapsed point of the equatorial quotient. -/
private abbrev realProjectiveSpaceEquatorQuotientBasepoint (k : ℕ) :
    realProjectiveSpaceEquatorQuotient k :=
  Quotient.mk'' (realProjectiveSpaceEquatorBasepoint k).1

/-- Helper for Example 10.1.11: the canonical quotient map collapsing the equatorial copy of
`RP^k` inside `RP^(k + 1)`. -/
private def realProjectiveSpaceEquatorQuotientMap (k : ℕ) :
    C(RealProjectiveSpace (k + 1), realProjectiveSpaceEquatorQuotient k) :=
  ⟨fun x ↦ Quotient.mk'' x, continuous_quotient_mk'⟩

/-- Helper for Example 10.1.11: the equator-collapse map carries the quotient topology of
`realProjectiveSpaceEquatorQuotient k`. -/
private theorem realProjectiveSpaceEquatorQuotientMap_isQuotientMap (k : ℕ) :
    Topology.IsQuotientMap (realProjectiveSpaceEquatorQuotientMap k) := by
  -- This is the canonical quotient map to a setoid quotient.
  simpa [realProjectiveSpaceEquatorQuotientMap] using
    (isQuotientMap_quotient_mk' :
      Topology.IsQuotientMap
        (Quotient.mk'' :
          RealProjectiveSpace (k + 1) → realProjectiveSpaceEquatorQuotient k))

/-- Helper for Example 10.1.11: the quotient map sends the equator to the collapsed basepoint. -/
private theorem realProjectiveSpaceEquatorQuotientMap_mapsEquator (k : ℕ) :
    Set.MapsTo
      (realProjectiveSpaceEquatorQuotientMap k)
      (realProjectiveSpaceEquatorLocus k)
      ({realProjectiveSpaceEquatorQuotientBasepoint k} :
        Set (realProjectiveSpaceEquatorQuotient k)) := by
  intro x hx
  -- Any equatorial point is identified with the chosen equatorial basepoint in the collapse.
  change Quotient.mk'' x = realProjectiveSpaceEquatorQuotientBasepoint k
  exact Quot.sound <|
    Relation.EqvGen.rel x (realProjectiveSpaceEquatorBasepoint k).1 <|
      Or.inr ⟨hx, realProjectiveSpaceEquatorBasepoint_mem k⟩

/-- Helper for Example 10.1.11: any two equatorial points have the same image in the collapse
quotient. -/
private theorem realProjectiveSpaceEquatorQuotientMap_eq_of_mem_equator
    (k : ℕ) {x y : RealProjectiveSpace (k + 1)}
    (hx : x ∈ realProjectiveSpaceEquatorLocus k)
    (hy : y ∈ realProjectiveSpaceEquatorLocus k) :
    realProjectiveSpaceEquatorQuotientMap k x =
      realProjectiveSpaceEquatorQuotientMap k y := by
  -- Both points are sent to the distinguished collapsed equator class.
  have hx' : realProjectiveSpaceEquatorQuotientMap k x =
      realProjectiveSpaceEquatorQuotientBasepoint k := by
    simpa using realProjectiveSpaceEquatorQuotientMap_mapsEquator k hx
  have hy' : realProjectiveSpaceEquatorQuotientMap k y =
      realProjectiveSpaceEquatorQuotientBasepoint k := by
    simpa using realProjectiveSpaceEquatorQuotientMap_mapsEquator k hy
  exact hx'.trans hy'.symm

/-- Helper for Example 10.1.11: if a quotient map identifies exactly the classes of a setoid,
then the setoid quotient is homeomorphic to the codomain. -/
private noncomputable def quotientHomeomorphOfRelIff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : C(X, Y)) (hq : Topology.IsQuotientMap q) (r : Setoid X)
    (hrel : ∀ x y : X, r x y ↔ q x = q y) :
    Quotient r ≃ₜ Y := by
  have hker : Setoid.ker q = r := by
    -- Replace the explicit setoid by the kernel relation of the quotient map.
    ext x y
    exact (hrel x y).symm
  exact hker ▸ Topology.IsQuotientMap.homeomorph hq

/-- Helper for Example 10.1.11: the ambient zero-extension map is continuous. -/
private theorem realProjectiveSpaceSuccLinearMap_continuous (k : ℕ) :
    Continuous (realProjectiveSpaceSuccLinearMap k) := by
  -- Each coordinate is either a source coordinate or the constant zero map.
  refine continuous_pi fun i ↦ ?_
  cases i using Fin.lastCases with
  | last =>
      simpa [realProjectiveSpaceSuccLinearMap]
        using (continuous_const : Continuous fun _ : Fin (k + 1) → ℝ ↦ (0 : ℝ))
  | cast j =>
      have hle : (j : ℕ) ≤ k := Nat.le_of_lt_succ j.is_lt
      simpa [realProjectiveSpaceSuccLinearMap, hle] using
        (continuous_apply j : Continuous fun f : Fin (k + 1) → ℝ ↦ f j)

/-- Helper for Example 10.1.11: zero-extension is the `Fin.snoc` operation appending a final
zero coordinate. -/
private theorem realProjectiveSpaceSuccLinearMap_eq_snoc (k : ℕ)
    (v : Fin (k + 1) → ℝ) :
    realProjectiveSpaceSuccLinearMap k v = Fin.snoc v 0 := by
  -- Compare the first `k + 1` coordinates and the final coordinate separately.
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp
  | cast j =>
      simp

/-- Helper for Example 10.1.11: zero-extension preserves the Euclidean norm. -/
private theorem realProjectiveSpaceSuccLinearMap_toLp_norm (k : ℕ)
    (v : Fin (k + 1) → ℝ) :
    ‖WithLp.toLp 2 (realProjectiveSpaceSuccLinearMap k v)‖ = ‖WithLp.toLp 2 v‖ := by
  -- Compare squared Euclidean norms so that the last zero coordinate contributes trivially.
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp

/-- Helper for Example 10.1.11: zero-extension carries `S^k` into `S^(k + 1)`. -/
private theorem realProjectiveSpaceSuccSphereModel_mem (k : ℕ) (x : TopCat.SphereModel k) :
    WithLp.toLp 2 (realProjectiveSpaceSuccLinearMap k x.1) ∈ TopCat.SphereModel (k + 1) := by
  -- Rewrite both sphere conditions as unit-norm statements and transport them through the
  -- zero-extension norm identity.
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using x.2
  have hmapnorm : ‖WithLp.toLp 2 (realProjectiveSpaceSuccLinearMap k x.1)‖ = 1 := by
    rw [realProjectiveSpaceSuccLinearMap_toLp_norm]
    exact hxnorm
  simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using hmapnorm

/-- Helper for Example 10.1.11: zero-extension defines the equatorial sphere inclusion
`S^k → S^(k + 1)`. -/
private noncomputable def realProjectiveSpaceSuccSphereMap (k : ℕ) :
    TopCat.sphere k → TopCat.sphere (k + 1) :=
  fun x ↦
    ULift.up
      ⟨WithLp.toLp 2 (realProjectiveSpaceSuccLinearMap k x.down.1),
        realProjectiveSpaceSuccSphereModel_mem k x.down⟩

/-- Helper for Example 10.1.11: the antipodal involution on `S^n` negates the concrete
representative. -/
private theorem sphereModel_ofLp_neg (n : ℕ) (x : TopCat.sphere n) :
    ((-x).down.1).ofLp = -x.down.1.ofLp := by
  rfl

/-- Helper for Example 10.1.11: the representative-level zero-extension map between concrete
sphere models is continuous. -/
private theorem realProjectiveSpaceSuccSphereModelMap_continuous (k : ℕ) :
    Continuous
      (fun x : TopCat.SphereModel k ↦
        WithLp.toLp 2 (realProjectiveSpaceSuccLinearMap k x.1)) := by
  -- Move to the raw function model, apply the ambient linear-map continuity there, then return to
  -- the `EuclideanSpace` model.
  exact
    (show Continuous (WithLp.toLp 2 : (Fin (k + 2) → ℝ) → EuclideanSpace ℝ (Fin (k + 2))) from
      PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin (k + 2) ↦ ℝ)).comp <|
      (realProjectiveSpaceSuccLinearMap_continuous k).comp <|
        (show Continuous
            (WithLp.ofLp : EuclideanSpace ℝ (Fin (k + 1)) → (Fin (k + 1) → ℝ)) from
          PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin (k + 1) ↦ ℝ)).comp
          continuous_subtype_val

/-- Helper for Example 10.1.11: the sphere-level zero-extension map is continuous. -/
private theorem realProjectiveSpaceSuccSphereMap_continuous (k : ℕ) :
    Continuous (realProjectiveSpaceSuccSphereMap k) := by
  -- The representative-level map is the continuous linear zero-extension, repackaged in the
  -- `ULift`/subtype model of `TopCat.sphere`.
  simpa [realProjectiveSpaceSuccSphereMap] using
    (continuous_uliftUp.comp
      ((Continuous.subtype_mk
          (realProjectiveSpaceSuccSphereModelMap_continuous k)
          (fun x ↦ realProjectiveSpaceSuccSphereModel_mem k x)).comp continuous_uliftDown))

/-- Helper for Example 10.1.11: zero-extension commutes with the antipodal involution on spheres.
-/
private theorem realProjectiveSpaceSuccSphereMap_neg (k : ℕ) (x : TopCat.sphere k) :
    realProjectiveSpaceSuccSphereMap k (-x) = -realProjectiveSpaceSuccSphereMap k x := by
  -- Compare the two sphere representatives coordinatewise.
  apply ULift.ext
  apply Subtype.ext
  apply WithLp.ofLp_injective
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [realProjectiveSpaceSuccSphereMap, sphereModel_ofLp_neg]
  | cast j =>
      simp [realProjectiveSpaceSuccSphereMap, sphereModel_ofLp_neg]

/-- Helper for Example 10.1.11: the sphere-level zero-extension map is injective. -/
private theorem realProjectiveSpaceSuccSphereMap_injective (k : ℕ) :
    Function.Injective (realProjectiveSpaceSuccSphereMap k) := by
  intro x y hxy
  -- Reduce to injectivity of the ambient linear zero-extension map on representatives.
  apply ULift.ext
  apply Subtype.ext
  apply WithLp.ofLp_injective
  exact realProjectiveSpaceSuccLinearMap_injective k <|
    congrArg (fun z : TopCat.sphere (k + 1) ↦ z.down.1.ofLp) hxy

/-- Helper for Example 10.1.11: zero-extension lands in the equatorial sphere locus. -/
private theorem realProjectiveSpaceSuccSphereMap_mem_equator (k : ℕ) (x : TopCat.sphere k) :
    realProjectiveSpaceSuccSphereMap k x ∈ sphereEquatorLocus k := by
  -- The last coordinate of a zero-extended vector vanishes by construction.
  simp [realProjectiveSpaceSuccSphereMap, sphereEquatorLocus]

/-- Helper for Example 10.1.11: the sphere-level zero-extension followed by projectivization. -/
private noncomputable abbrev realProjectiveSpaceSuccSphereQuotientMap (k : ℕ) :
    TopCat.sphere k → RealProjectiveSpace (k + 1) :=
  fun x ↦ sphereToRealProjectiveSpace (k + 1) (realProjectiveSpaceSuccSphereMap k x)

/-- Helper for Example 10.1.11: the sphere-level quotient map is constant on antipodal classes.
-/
private theorem realProjectiveSpaceSuccSphereQuotientMap_respects (k : ℕ)
    {x y : TopCat.sphere k}
    (hxy : sphereToRealProjectiveSpace k x = sphereToRealProjectiveSpace k y) :
    realProjectiveSpaceSuccSphereQuotientMap k x =
      realProjectiveSpaceSuccSphereQuotientMap k y := by
  -- Use the quotient characterization `x = y ∨ x = -y` and the compatibility with negation.
  rcases (sphereToRealProjectiveSpace_eq_iff k).1 hxy with hxy' | hxy'
  · simpa [realProjectiveSpaceSuccSphereQuotientMap, hxy']
  · rw [realProjectiveSpaceSuccSphereQuotientMap, realProjectiveSpaceSuccSphereQuotientMap]
    exact (sphereToRealProjectiveSpace_eq_iff (k + 1)).2 <|
      Or.inr <| by simpa [hxy', realProjectiveSpaceSuccSphereMap_neg]

/-- Helper for Example 10.1.11: the quotient-descended successor inclusion is continuous. -/
private theorem realProjectiveSpaceSuccInclusion_continuous (k : ℕ) :
    Continuous
      (fun x : RealProjectiveSpace k ↦
        Quotient.liftOn' x
          (realProjectiveSpaceSuccSphereQuotientMap k)
          (fun _ _ hab ↦
            realProjectiveSpaceSuccSphereQuotientMap_respects k (Quotient.sound hab))) := by
  -- Continuity descends from the sphere-level map via the antipodal quotient.
  simpa using
      (((sphereToRealProjectiveSpace_isCoveringMap (k + 1)).continuous.comp
          (realProjectiveSpaceSuccSphereMap_continuous k)).quotient_liftOn'
        (fun _ _ hab ↦
          realProjectiveSpaceSuccSphereQuotientMap_respects k (Quotient.sound hab)))

/-- Helper for Example 10.1.11: the projective zero-extension inclusion `RP^k → RP^(k + 1)`. -/
private noncomputable def realProjectiveSpaceSuccInclusion (k : ℕ) :
    C(RealProjectiveSpace k, RealProjectiveSpace (k + 1)) :=
  ⟨fun x ↦
      Quotient.liftOn' x
        (realProjectiveSpaceSuccSphereQuotientMap k)
        (fun _ _ hab ↦
          realProjectiveSpaceSuccSphereQuotientMap_respects k (Quotient.sound hab)),
    realProjectiveSpaceSuccInclusion_continuous k⟩

/-- Helper for Example 10.1.11: the successor inclusion acts on representatives by
projectivized zero-extension. -/
@[simp]
private theorem realProjectiveSpaceSuccInclusion_apply_mk (k : ℕ) (x : TopCat.sphere k) :
    realProjectiveSpaceSuccInclusion k (sphereToRealProjectiveSpace k x) =
      sphereToRealProjectiveSpace (k + 1) (realProjectiveSpaceSuccSphereMap k x) := by
  -- The quotient-descended map reduces to its defining representative-level formula.
  rfl

/-- Helper for Example 10.1.11: the projective zero-extension inclusion is injective. -/
private theorem realProjectiveSpaceSuccInclusion_injective (k : ℕ) :
    Function.Injective (realProjectiveSpaceSuccInclusion k) := by
  intro x y hxy
  -- Unfold both projective points to sphere representatives and compare their zero-extensions.
  revert hxy
  refine Quotient.inductionOn₂ x y ?_
  intro a b hxy
  have hxy' :
      sphereToRealProjectiveSpace (k + 1) (realProjectiveSpaceSuccSphereMap k a) =
        sphereToRealProjectiveSpace (k + 1) (realProjectiveSpaceSuccSphereMap k b) := by
    simpa [realProjectiveSpaceSuccInclusion, realProjectiveSpaceSuccSphereQuotientMap,
      sphereToRealProjectiveSpace] using hxy
  rcases (sphereToRealProjectiveSpace_eq_iff (k + 1)).1 hxy' with hab | hab
  · exact (sphereToRealProjectiveSpace_eq_iff k).2 <| Or.inl <|
      realProjectiveSpaceSuccSphereMap_injective k hab
  · exact (sphereToRealProjectiveSpace_eq_iff k).2 <| Or.inr <|
      realProjectiveSpaceSuccSphereMap_injective k <|
        hab.trans <| (realProjectiveSpaceSuccSphereMap_neg k b).symm

/-- Helper for Example 10.1.11: the range of projective zero-extension is the equatorial copy of
`RP^k` inside `RP^(k + 1)`. -/
private theorem realProjectiveSpaceSuccInclusion_range_eq_equator (k : ℕ) :
    Set.range (realProjectiveSpaceSuccInclusion k) = realProjectiveSpaceEquatorLocus k := by
  -- Compare the range against the equator by passing to sphere representatives in both
  -- directions.
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine Quotient.inductionOn x ?_
    intro y
    exact ⟨realProjectiveSpaceSuccSphereMap k y,
      realProjectiveSpaceSuccSphereMap_mem_equator k y,
      realProjectiveSpaceSuccInclusion_apply_mk k y⟩
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_sphereEquatorLocus_iff_exists_zeroExtend k x).1 hx with ⟨v, hv⟩
    have hxnorm : ‖x.down.1‖ = 1 := by
      simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using x.down.2
    have hvnorm : ‖WithLp.toLp 2 v‖ = 1 := by
      calc
        ‖WithLp.toLp 2 v‖ = ‖WithLp.toLp 2 (realProjectiveSpaceSuccLinearMap k v)‖ := by
          rw [realProjectiveSpaceSuccLinearMap_toLp_norm]
        _ = ‖x.down.1‖ := by simpa [hv]
        _ = 1 := hxnorm
    have hvSphere : WithLp.toLp 2 v ∈ TopCat.SphereModel k := by
      simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using hvnorm
    let y : TopCat.sphere k := ULift.up ⟨WithLp.toLp 2 v, hvSphere⟩
    have hy : realProjectiveSpaceSuccSphereMap k y = x := by
      -- The chosen representative was built precisely so that zero-extension recovers `x`.
      apply ULift.ext
      apply Subtype.ext
      simpa [y, realProjectiveSpaceSuccSphereMap] using congrArg (WithLp.toLp 2) hv
    refine ⟨sphereToRealProjectiveSpace k y, ?_⟩
    rw [realProjectiveSpaceSuccInclusion_apply_mk, hy]

/-- Helper for Example 10.1.11: the equatorial copy of `RP^k` in `RP^(k + 1)` is homeomorphic to
`RP^k`. -/
private noncomputable abbrev realProjectiveSpaceEquatorLocusHomeomorph (k : ℕ) :
    realProjectiveSpaceEquatorLocus k ≃ₜ RealProjectiveSpace k :=
  -- Compactness upgrades the continuous injective inclusion to a homeomorphism onto its range,
  -- and the range is exactly the intrinsic equator subtype.
  ((realProjectiveSpaceSuccInclusion_continuous k).isClosedEmbedding
      (realProjectiveSpaceSuccInclusion_injective k)).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (realProjectiveSpaceSuccInclusion_range_eq_equator k)) |>.symm

/-- Helper for Example 10.1.11: the successor inclusion lands in the equatorial copy of
`RP^k ⊆ RP^(k + 1)`. -/
private theorem realProjectiveSpaceSuccInclusion_mem_equator (k : ℕ)
    (x : RealProjectiveSpace k) :
    realProjectiveSpaceSuccInclusion k x ∈ realProjectiveSpaceEquatorLocus k := by
  -- Rewrite the equator as the range of the successor inclusion and use the defining witness.
  rw [← realProjectiveSpaceSuccInclusion_range_eq_equator]
  exact ⟨x, rfl⟩

/-- Helper for Example 10.1.11: an old cell map may be transported into the equator subtype of
`RP^(k + 1)` via the successor inclusion. -/
private noncomputable def realProjectiveSpaceEquatorTransportCellMap
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m →
      PartialEquiv (Fin m → ℝ) (realProjectiveSpaceEquatorLocus k) :=
  fun j ↦
    (S.cwComplex.map m j).transEquiv (realProjectiveSpaceEquatorLocusHomeomorph k).symm.toEquiv

/-- Helper for Example 10.1.11: the transported equatorial cell map is exactly the old cell map
followed by the equator embedding. -/
@[simp]
private theorem realProjectiveSpaceEquatorTransportCellMap_apply
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) (x : Fin m → ℝ),
      realProjectiveSpaceEquatorTransportCellMap k S j x =
        (realProjectiveSpaceEquatorLocusHomeomorph k).symm (S.cwComplex.map m j x) := by
  intro j x
  rfl

/-- Helper for Example 10.1.11: transporting an inherited cell into the equator does not change
its open-ball source. -/
@[simp]
private theorem realProjectiveSpaceEquatorTransportCellMap_source
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
      (realProjectiveSpaceEquatorTransportCellMap k S j).source = Metric.ball 0 1 := by
  intro j
  -- Postcomposing with the equator homeomorphism does not alter the source of the old cell map.
  simpa [realProjectiveSpaceEquatorTransportCellMap, PartialEquiv.trans_source]
    using S.cwComplex.source_eq m j

/-- Helper for Example 10.1.11: forgetting the equator subtype turns a transported inherited cell
into an ambient partial equivalence whose target remembers exactly the coerced equator image. -/
private noncomputable def realProjectiveSpaceEquatorTransportCellMapAmbient
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m →
      PartialEquiv (Fin m → ℝ) (RealProjectiveSpace (k + 1)) :=
  fun j ↦
    let e := realProjectiveSpaceEquatorTransportCellMap k S j
    let _ : DecidablePred
        (fun y : RealProjectiveSpace (k + 1) ↦
          y ∈ (Subtype.val '' e.target : Set (RealProjectiveSpace (k + 1)))) :=
      Classical.decPred _
    { toFun := fun x ↦ (e x : RealProjectiveSpace (k + 1))
      invFun := fun y ↦
        if hy : y ∈ (Subtype.val '' e.target : Set (RealProjectiveSpace (k + 1))) then
          e.symm ⟨y, by
            rcases hy with ⟨z, hz, rfl⟩
            exact z.2⟩
        else default
      source := e.source
      target := Subtype.val '' e.target
      map_source' := by
        intro x hx
        exact ⟨e x, e.map_source hx, rfl⟩
      map_target' := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        -- On the ambient target, the inverse branch reduces back to the subtype-valued inverse.
        simp [hz, e.map_target hz]
      left_inv' := by
        intro x hx
        have hy :
            ((e x : realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1)) ∈
              (Subtype.val '' e.target : Set (RealProjectiveSpace (k + 1))) := by
          exact ⟨e x, e.map_source hx, rfl⟩
        -- Source points stay on the genuine inverse branch, so the old left-inverse closes.
        simp [hy, e.left_inv hx]
      right_inv' := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        have hy' :
            ((z : realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1)) ∈
              (Subtype.val '' e.target : Set (RealProjectiveSpace (k + 1))) := by
          exact ⟨z, hz, rfl⟩
        -- Target points also stay on the genuine inverse branch, so the old right-inverse closes.
        simp [hy', e.right_inv hz] }

/-- Helper for Example 10.1.11: the ambient inherited-cell adapter is literally the subtype-valued
transport followed by coercion to ambient projective space. -/
@[simp]
private theorem realProjectiveSpaceEquatorTransportCellMapAmbient_apply
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) (x : Fin m → ℝ),
      realProjectiveSpaceEquatorTransportCellMapAmbient k S j x =
        ((realProjectiveSpaceEquatorTransportCellMap k S j x :
          realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1)) := by
  intro j x
  rfl

/-- Helper for Example 10.1.11: ambientizing an inherited cell still uses the standard open ball
as its source. -/
@[simp]
private theorem realProjectiveSpaceEquatorTransportCellMapAmbient_source
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
      (realProjectiveSpaceEquatorTransportCellMapAmbient k S j).source = Metric.ball 0 1 := by
  intro j
  -- The ambient wrapper does not change the old cell source.
  simpa [realProjectiveSpaceEquatorTransportCellMapAmbient]
    using realProjectiveSpaceEquatorTransportCellMap_source k S j

/-- Helper for Example 10.1.11: the ambient inherited-cell target still lies in the equatorial
copy of `RP^k`. -/
private theorem realProjectiveSpaceEquatorTransportCellMapAmbient_target_subset_equator
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
      (realProjectiveSpaceEquatorTransportCellMapAmbient k S j).target ⊆
        realProjectiveSpaceEquatorLocus k := by
  intro j y hy
  rcases hy with ⟨z, hz, rfl⟩
  exact z.2

/-- Helper for Example 10.1.11: the ambient inherited-cell open image is just the coerced
subtype-level open image. -/
private theorem realProjectiveSpaceEquatorTransportCellMapAmbient_image_ball
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
    realProjectiveSpaceEquatorTransportCellMapAmbient k S j '' Metric.ball 0 1 =
      Subtype.val '' (realProjectiveSpaceEquatorTransportCellMap k S j '' Metric.ball 0 1) := by
  intro j
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Unfold the ambient wrapper once, then package the same point inside the subtype image.
    exact ⟨realProjectiveSpaceEquatorTransportCellMap k S j x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    -- Any coerced subtype-image point already comes from the same Euclidean source point.
    exact ⟨x, hx, rfl⟩

/-- Helper for Example 10.1.11: the ambient inherited-cell closed image is just the coerced
subtype-level closed image. -/
private theorem realProjectiveSpaceEquatorTransportCellMapAmbient_image_closedBall
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
    realProjectiveSpaceEquatorTransportCellMapAmbient k S j '' Metric.closedBall 0 1 =
      Subtype.val '' (realProjectiveSpaceEquatorTransportCellMap k S j '' Metric.closedBall 0 1) :=
    by
  intro j
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- The ambient wrapper and the subtype-valued map have the same closed-ball image point.
    exact ⟨realProjectiveSpaceEquatorTransportCellMap k S j x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    -- Forgetting the subtype recovers the same closed-ball witness in ambient projective space.
    exact ⟨x, hx, rfl⟩

/-- Helper for Example 10.1.11: inherited ambient open cells still land inside the equator. -/
private theorem realProjectiveSpaceEquatorTransportCellMapAmbient_mapsTo_equator
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
      Set.MapsTo
        (realProjectiveSpaceEquatorTransportCellMapAmbient k S j)
        (Metric.ball 0 1)
        (realProjectiveSpaceEquatorLocus k) := by
  intro j x hx
  exact
    realProjectiveSpaceEquatorTransportCellMapAmbient_target_subset_equator k S j <|
      (realProjectiveSpaceEquatorTransportCellMapAmbient k S j).map_source <|
        by
          simpa using hx

/-- Helper for Example 10.1.11: the inherited closed cells ambientized in `RP^(k + 1)` cover
exactly the equatorial copy of `RP^k`. -/
private theorem realProjectiveSpaceSuccInheritedClosedCells_eq_equator
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
      realProjectiveSpaceEquatorTransportCellMapAmbient k S j '' Metric.closedBall 0 1) =
      realProjectiveSpaceEquatorLocus k := by
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.1 hy with ⟨m, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨j, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    -- Every ambientized inherited cell is defined through the equator subtype.
    exact (realProjectiveSpaceEquatorTransportCellMap k S j x).2
  · intro hy
    let x : realProjectiveSpaceEquatorLocus k := ⟨y, hy⟩
    let z : RealProjectiveSpace k := realProjectiveSpaceEquatorLocusHomeomorph k x
    have hz :
        z ∈
          (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
            S.cwComplex.map m j '' Metric.closedBall 0 1) := by
      -- The predecessor CW complex already covers all of `RP^k`.
      have hzUniv : z ∈ (Set.univ : Set (RealProjectiveSpace k)) := by
        simp
      rw [← S.cwComplex.union] at hzUniv
      simpa [Topology.CWComplex.closedCell] using hzUniv
    rcases Set.mem_iUnion.1 hz with ⟨m, hz⟩
    rcases Set.mem_iUnion.1 hz with ⟨j, hz⟩
    rcases hz with ⟨v, hv, hvz⟩
    refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    refine ⟨v, hv, ?_⟩
    -- Transport the predecessor closed-cell witness through the equator homeomorphism.
    calc
      realProjectiveSpaceEquatorTransportCellMapAmbient k S j v =
          (((realProjectiveSpaceEquatorLocusHomeomorph k).symm (S.cwComplex.map m j v) :
            realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1)) := by
            rfl
      _ =
          (((realProjectiveSpaceEquatorLocusHomeomorph k).symm z :
            realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1)) := by
            rw [hvz]
      _ = y := by
            simp [x, z]

/-- Helper for Example 10.1.11: a boundary point of the standard attaching sphere canonically
lies in the corresponding closed unit ball. -/
private theorem realProjectiveSpaceAttachingSphere_mem_closedBall (k : ℕ)
    (x : TopCat.sphere k) :
    x.down.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
  -- The sphere equation `‖x‖ = 1` immediately implies the closed-ball inequality `‖x‖ ≤ 1`.
  rw [Metric.mem_closedBall, dist_zero_right]
  have hxnorm : ‖x.down.1‖ = 1 := by
    simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using x.down.2
  exact hxnorm.le

/-- Helper for Example 10.1.11: the boundary sphere includes into the corresponding closed unit
ball. -/
private def realProjectiveSpaceAttachingSphereToClosedBall (k : ℕ) :
    TopCat.sphere k → Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  fun x ↦ ⟨x.down.1, realProjectiveSpaceAttachingSphere_mem_closedBall k x⟩

/-- Helper for Example 10.1.11: the positive hemisphere of `S^(k + 1)` is the
last-coordinate-positive locus. -/
private def realProjectiveSpacePositiveHemisphere (k : ℕ) : Set (TopCat.sphere (k + 1)) :=
  { x | 0 < x.down.1.ofLp (Fin.last (k + 1)) }

/-- Helper for Example 10.1.11: the positive hemisphere is open inside `S^(k + 1)`. -/
private theorem isOpen_realProjectiveSpacePositiveHemisphere (k : ℕ) :
    IsOpen (realProjectiveSpacePositiveHemisphere k) := by
  -- The defining last-coordinate function is continuous on the concrete sphere model.
  refine isOpen_lt continuous_const ?_
  exact
    (continuous_apply (Fin.last (k + 1))).comp <|
      (show Continuous
          (WithLp.ofLp : EuclideanSpace ℝ (Fin (k + 2)) → (Fin (k + 2) → ℝ)) from
        PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin (k + 2) ↦ ℝ)).comp <|
        continuous_subtype_val.comp continuous_uliftDown

/-- Helper for Example 10.1.11: a projective class represented by a point in the positive
hemisphere cannot lie on the equator. -/
private theorem sphereToRealProjectiveSpace_not_mem_equator_of_mem_positiveHemisphere (k : ℕ)
    {x : TopCat.sphere (k + 1)} (hx : x ∈ realProjectiveSpacePositiveHemisphere k) :
    sphereToRealProjectiveSpace (k + 1) x ∉ realProjectiveSpaceEquatorLocus k := by
  have hxLast : 0 < x.down.1.ofLp (Fin.last (k + 1)) := by
    simpa [realProjectiveSpacePositiveHemisphere] using hx
  intro hmem
  rcases hmem with ⟨y, hy, hxy⟩
  have hyLast : y.down.1.ofLp (Fin.last (k + 1)) = 0 := by
    simpa [sphereEquatorLocus] using hy
  rcases (sphereToRealProjectiveSpace_eq_iff (k + 1)).1 hxy with hsame | hneg
  · subst hsame
    have : 0 < (0 : ℝ) := by
      simpa [hyLast] using hxLast
    exact (lt_irrefl (0 : ℝ)) this
  · have hlast :=
      congrArg (fun z : TopCat.sphere (k + 1) ↦ z.down.1.ofLp (Fin.last (k + 1))) hneg
    have : x.down.1.ofLp (Fin.last (k + 1)) = 0 := by
      simpa [sphereModel_ofLp_neg, hyLast] using hlast
    have : 0 < (0 : ℝ) := by
      simpa [this] using hxLast
    exact (lt_irrefl (0 : ℝ)) this

/-- Helper for Example 10.1.11: the antipodal quotient is injective on the positive hemisphere. -/
private theorem sphereToRealProjectiveSpace_injectiveOn_positiveHemisphere (k : ℕ) :
    Set.InjOn (sphereToRealProjectiveSpace (k + 1))
      (realProjectiveSpacePositiveHemisphere k) := by
  intro x hx y hy hxy
  have hxLast : 0 < x.down.1.ofLp (Fin.last (k + 1)) := by
    simpa [realProjectiveSpacePositiveHemisphere] using hx
  have hyLast : 0 < y.down.1.ofLp (Fin.last (k + 1)) := by
    simpa [realProjectiveSpacePositiveHemisphere] using hy
  rcases (sphereToRealProjectiveSpace_eq_iff (k + 1)).1 hxy with hsame | hneg
  · exact hsame
  · have hlast :=
      congrArg (fun z : TopCat.sphere (k + 1) ↦ z.down.1.ofLp (Fin.last (k + 1))) hneg
    have hcoord :
        x.down.1.ofLp (Fin.last (k + 1)) = -y.down.1.ofLp (Fin.last (k + 1)) := by
      simpa [sphereModel_ofLp_neg] using hlast
    linarith

/-- Helper for Example 10.1.11: the antipodal quotient sends the positive hemisphere onto the
complement of the equator in `RP^(k + 1)`. -/
private theorem sphereToRealProjectiveSpace_image_positiveHemisphere_eq_compl (k : ℕ) :
    sphereToRealProjectiveSpace (k + 1) '' realProjectiveSpacePositiveHemisphere k =
      ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact sphereToRealProjectiveSpace_not_mem_equator_of_mem_positiveHemisphere k hy
  · intro hx
    rcases sphereToRealProjectiveSpace_surjective (k + 1) x with ⟨y, rfl⟩
    by_cases hyPos : 0 < y.down.1.ofLp (Fin.last (k + 1))
    · exact ⟨y, hyPos, rfl⟩
    have hyNeZero : y.down.1.ofLp (Fin.last (k + 1)) ≠ 0 := by
      intro hyZero
      apply hx
      exact ⟨y, by simpa [sphereEquatorLocus] using hyZero, rfl⟩
    have hyNeg :
        0 < (-y : TopCat.sphere (k + 1)).down.1.ofLp (Fin.last (k + 1)) := by
      have hyNonpos : y.down.1.ofLp (Fin.last (k + 1)) ≤ 0 := le_of_not_gt hyPos
      have hyStrict :
          y.down.1.ofLp (Fin.last (k + 1)) < 0 := lt_of_le_of_ne hyNonpos hyNeZero
      simpa [sphereModel_ofLp_neg] using neg_pos.mpr hyStrict
    refine ⟨-y, hyNeg, ?_⟩
    exact (sphereToRealProjectiveSpace_eq_iff (k + 1)).2 <| Or.inr rfl

/-- Helper for Example 10.1.11: restricting the antipodal quotient to the positive hemisphere
identifies it homeomorphically with the complement of the equator in `RP^(k + 1)`. -/
private noncomputable def realProjectiveSpacePositiveHemisphereHomeomorphCompl (k : ℕ) :
    realProjectiveSpacePositiveHemisphere k ≃ₜ
      { y : RealProjectiveSpace (k + 1) | y ∉ realProjectiveSpaceEquatorLocus k } := by
  let f : realProjectiveSpacePositiveHemisphere k → RealProjectiveSpace (k + 1) :=
    fun x ↦ sphereToRealProjectiveSpace (k + 1) x.1
  have hfCont : Continuous f := by
    -- The restricted quotient map is just the ambient covering map composed with subtype
    -- inclusion into the sphere.
    simpa [f] using
      ((sphereToRealProjectiveSpace_isCoveringMap (k + 1)).continuous.comp continuous_subtype_val)
  have hfInj : Function.Injective f := by
    intro x y hxy
    -- On the positive hemisphere, projectivization has no antipodal identifications left.
    apply Subtype.ext
    exact sphereToRealProjectiveSpace_injectiveOn_positiveHemisphere k x.2 y.2 hxy
  have hfOpen : IsOpenMap f := by
    -- Openness is inherited from the covering map after restricting to the open hemisphere.
    exact (sphereToRealProjectiveSpace_isCoveringMap (k + 1)).isOpenMap.comp
      (isOpen_realProjectiveSpacePositiveHemisphere k).isOpenMap_subtype_val
  have hfRange :
      Set.range f = ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact sphereToRealProjectiveSpace_not_mem_equator_of_mem_positiveHemisphere k x.2
    · intro hy
      rw [← sphereToRealProjectiveSpace_image_positiveHemisphere_eq_compl k] at hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let hOpenEmbedding : Topology.IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hfCont hfInj hfOpen
  -- Replace the range of the open embedding by the already identified complement.
  exact (hOpenEmbedding.toIsEmbedding.toHomeomorph).trans (Homeomorph.setCongr hfRange)

/-- Helper for Example 10.1.11: the hemisphere-to-complement homeomorphism still evaluates by
projectivizing the underlying sphere representative. -/
private theorem realProjectiveSpacePositiveHemisphereHomeomorphCompl_apply (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) :
    (realProjectiveSpacePositiveHemisphereHomeomorphCompl k x :
      RealProjectiveSpace (k + 1)) =
      sphereToRealProjectiveSpace (k + 1) x.1 := by
  -- Unfold the composite homeomorphism: both stages preserve the ambient projective value.
  rfl

/-- Helper for Example 10.1.11: the explicit upper-hemisphere representative appends the
square-root coordinate to a point of the closed unit ball. -/
private def realProjectiveSpaceSuccTopCellRepresentative (k : ℕ)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    Fin (k + 2) → ℝ :=
  Fin.snoc z.1.ofLp (Real.sqrt (1 - ‖z.1‖ ^ 2))

/-- Helper for Example 10.1.11: the explicit upper-hemisphere representative keeps the first
`k + 1` coordinates unchanged. -/
@[simp]
private theorem realProjectiveSpaceSuccTopCellRepresentative_castSucc (k : ℕ)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (i : Fin (k + 1)) :
    realProjectiveSpaceSuccTopCellRepresentative k z i.castSucc = z.1.ofLp i := by
  -- The appended representative agrees with the original vector away from the last coordinate.
  simp [realProjectiveSpaceSuccTopCellRepresentative]

/-- Helper for Example 10.1.11: the last coordinate of the explicit upper-hemisphere
representative is the square-root term. -/
@[simp]
private theorem realProjectiveSpaceSuccTopCellRepresentative_last (k : ℕ)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    realProjectiveSpaceSuccTopCellRepresentative k z (Fin.last (k + 1)) =
      Real.sqrt (1 - ‖z.1‖ ^ 2) := by
  -- The last coordinate is exactly the coordinate appended by `Fin.snoc`.
  simp [realProjectiveSpaceSuccTopCellRepresentative]

/-- Helper for Example 10.1.11: on the boundary sphere, the explicit upper-hemisphere
representative collapses to the ambient zero-extension representative. -/
private theorem realProjectiveSpaceSuccTopCellRepresentative_boundary_eq (k : ℕ)
    (x : TopCat.sphere k) :
    realProjectiveSpaceSuccTopCellRepresentative k
        (realProjectiveSpaceAttachingSphereToClosedBall k x) =
      realProjectiveSpaceSuccLinearMap k x.down.1.ofLp := by
  -- On the boundary, the norm equation forces the square-root coordinate to vanish.
  ext i
  cases i using Fin.lastCases with
  | last =>
      have hxnorm : ‖x.down.1‖ = 1 := by
        simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using x.down.2
      have hsqrt :
          1 - ‖(realProjectiveSpaceAttachingSphereToClosedBall k x).1‖ ^ 2 = 0 := by
        have hsqrt' : 1 - ‖x.down.1‖ ^ 2 = 0 := by
          nlinarith [hxnorm]
        simpa [realProjectiveSpaceAttachingSphereToClosedBall] using hsqrt'
      simp [realProjectiveSpaceSuccTopCellRepresentative, hsqrt]
  | cast j =>
      -- Away from the last coordinate, both representatives are literally the original vector.
      simp [realProjectiveSpaceAttachingSphereToClosedBall]

/-- Helper for Example 10.1.11: an interior point of the closed ball has a nonzero square-root
coordinate in the explicit upper-hemisphere representative. -/
private theorem realProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz : z ∈ Metric.ball 0 1) :
    realProjectiveSpaceSuccTopCellRepresentative k
        ⟨z, Metric.ball_subset_closedBall hz⟩ (Fin.last (k + 1)) ≠ 0 := by
  -- Inside the open ball, `1 - ‖z‖^2` is strictly positive, so its square root is nonzero.
  have hz' : ‖z‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    simpa using hz
  have hsqrt : Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg z]
  simpa [realProjectiveSpaceSuccTopCellRepresentative] using hsqrt

/-- Helper for Example 10.1.11: the explicit upper-hemisphere representative lies on
`S^(k + 1)`. -/
private theorem realProjectiveSpaceSuccTopCellRepresentative_mem_sphere (k : ℕ)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    WithLp.toLp 2 (realProjectiveSpaceSuccTopCellRepresentative k z) ∈ TopCat.SphereModel (k + 1) := by
  -- Compare squared norms: the first `k + 1` coordinates contribute `‖z‖²`, and the last
  -- coordinate contributes the complementary term `1 - ‖z‖²`.
  rw [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm]
  have hzle : ‖z.1‖ ≤ 1 := by
    have hzmem : z.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := z.2
    rw [Metric.mem_closedBall] at hzmem
    simpa [dist_eq_norm] using hzmem
  have hsq :
      ‖WithLp.toLp 2 (realProjectiveSpaceSuccTopCellRepresentative k z)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    calc
      (∑ i : Fin (k + 1),
          (realProjectiveSpaceSuccTopCellRepresentative k z i.castSucc) ^ 2) +
          (realProjectiveSpaceSuccTopCellRepresentative k z (Fin.last (k + 1))) ^ 2
          = (∑ i : Fin (k + 1), (z.1 i) ^ 2) + (Real.sqrt (1 - ‖z.1‖ ^ 2)) ^ 2 := by
            simp [realProjectiveSpaceSuccTopCellRepresentative]
      _ = ‖z.1‖ ^ 2 + (Real.sqrt (1 - ‖z.1‖ ^ 2)) ^ 2 := by
            rw [← EuclideanSpace.real_norm_sq_eq]
      _ = ‖z.1‖ ^ 2 + (1 - ‖z.1‖ ^ 2) := by
            rw [Real.sq_sqrt]
            nlinarith [norm_nonneg z.1]
      _ = 1 := by ring
  have hnonneg :
      0 ≤ ‖WithLp.toLp 2 (realProjectiveSpaceSuccTopCellRepresentative k z)‖ := norm_nonneg _
  have hnorm :
      ‖WithLp.toLp 2 (realProjectiveSpaceSuccTopCellRepresentative k z)‖ = 1 := by
    exact (sq_eq_sq₀ hnonneg zero_le_one).mp (by simpa [pow_two] using hsq)
  simpa using hnorm

/-- Helper for Example 10.1.11: the explicit upper-hemisphere representative determines a point of
`S^(k + 1)`. -/
private noncomputable def realProjectiveSpaceSuccTopCellSpherePoint (k : ℕ)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    TopCat.sphere (k + 1) :=
  ULift.up <| ⟨WithLp.toLp 2 (realProjectiveSpaceSuccTopCellRepresentative k z),
    realProjectiveSpaceSuccTopCellRepresentative_mem_sphere k z⟩

/-- Helper for Example 10.1.11: the sphere point built from the upper-hemisphere representative
has exactly that concrete representative. -/
@[simp]
private theorem realProjectiveSpaceSuccTopCellSpherePoint_ofLp (k : ℕ)
    (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (realProjectiveSpaceSuccTopCellSpherePoint k z).down.1.ofLp =
      realProjectiveSpaceSuccTopCellRepresentative k z := by
  rfl

/-- Helper for Example 10.1.11: every point of the top-cell chart over the open ball lies in the
positive hemisphere. -/
private theorem realProjectiveSpaceSuccTopCellSpherePoint_mem_positiveHemisphere (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz : z ∈ Metric.ball 0 1) :
    realProjectiveSpaceSuccTopCellSpherePoint k ⟨z, Metric.ball_subset_closedBall hz⟩ ∈
      realProjectiveSpacePositiveHemisphere k := by
  -- The appended square-root coordinate is nonzero on the open ball and is always nonnegative.
  have hnonzero :=
    realProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball k hz
  have hsqrt : 0 < Real.sqrt (1 - ‖z‖ ^ 2) := by
    exact lt_of_le_of_ne (by positivity) <| by
      intro hzero
      exact hnonzero <| by
        simpa [realProjectiveSpaceSuccTopCellRepresentative] using hzero.symm
  simpa [realProjectiveSpacePositiveHemisphere, realProjectiveSpaceSuccTopCellSpherePoint,
    realProjectiveSpaceSuccTopCellRepresentative] using hsqrt

/-- Helper for Example 10.1.11: truncate a point in the positive hemisphere to its first
`k + 1` coordinates. -/
private def realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) :
    EuclideanSpace ℝ (Fin (k + 1)) :=
  WithLp.toLp 2 fun i ↦ x.1.down.1.ofLp i.castSucc

/-- Helper for Example 10.1.11: truncation from the positive hemisphere remembers exactly the
first `k + 1` coordinates. -/
@[simp]
private theorem realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_apply (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) (i : Fin (k + 1)) :
    realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x i =
      x.1.down.1.ofLp i.castSucc := by
  -- The truncation is defined coordinatewise.
  simp [realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc]

/-- Helper for Example 10.1.11: on the positive hemisphere, the truncated squared norm and the
last-coordinate square add up to `1`. -/
private theorem realProjectiveSpaceSuccPositiveHemisphereTrunc_norm_sq_add_last_sq (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) :
    ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2 +
        (x.1.down.1.ofLp (Fin.last (k + 1))) ^ 2 =
      1 := by
  -- Compare the sphere norm with the sum of the truncated coordinates and the last coordinate.
  have hxnorm : ‖x.1.down.1‖ = 1 := by
    simpa [TopCat.SphereModel, Metric.mem_sphere, dist_eq_norm] using x.1.down.2
  have hxnormsq : ‖x.1.down.1‖ ^ 2 = 1 := by
    nlinarith [hxnorm]
  calc
    ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2 +
        (x.1.down.1.ofLp (Fin.last (k + 1))) ^ 2
        =
          (∑ i : Fin (k + 1), (x.1.down.1.ofLp i.castSucc) ^ 2) +
            (x.1.down.1.ofLp (Fin.last (k + 1))) ^ 2 := by
              simp [EuclideanSpace.real_norm_sq_eq,
                realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc]
    _ = ∑ i : Fin (k + 2), (x.1.down.1.ofLp i) ^ 2 := by
          simpa using
            (Fin.sum_univ_castSucc (fun i : Fin (k + 2) ↦ (x.1.down.1.ofLp i) ^ 2)).symm
    _ = ‖x.1.down.1‖ ^ 2 := by
          simpa using (EuclideanSpace.real_norm_sq_eq (x.1.down.1)).symm
    _ = 1 := hxnormsq

/-- Helper for Example 10.1.11: truncating a positive-hemisphere point lands in the open unit
ball. -/
private theorem realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) :
    realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x ∈
      Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
  -- The positive last coordinate forces the truncated norm to be strictly smaller than `1`.
  have hsum :=
    realProjectiveSpaceSuccPositiveHemisphereTrunc_norm_sq_add_last_sq k x
  have hlastPos : 0 < x.1.down.1.ofLp (Fin.last (k + 1)) := by
    exact x.2
  have hnormLt :
      ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ < 1 := by
    have hlastSq : 0 < (x.1.down.1.ofLp (Fin.last (k + 1))) ^ 2 := by
      exact sq_pos_of_pos hlastPos
    have hnormNonneg :
        0 ≤ ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ := norm_nonneg _
    nlinarith
  simpa [Metric.mem_ball, dist_eq_norm] using hnormLt

/-- Helper for Example 10.1.11: a point of the positive hemisphere determines the unique open-ball
preimage of the standard top-cell chart. -/
private def realProjectiveSpaceSuccTopCellPositiveHemispherePreimage (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
  ⟨realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x,
    realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball k x⟩

/-- Helper for Example 10.1.11: the explicit top-cell sphere point recovers a positive-hemisphere
point from its truncated preimage. -/
private theorem realProjectiveSpaceSuccTopCellSpherePoint_of_positiveHemispherePreimage (k : ℕ)
    (x : realProjectiveSpacePositiveHemisphere k) :
    realProjectiveSpaceSuccTopCellSpherePoint k
        ⟨(realProjectiveSpaceSuccTopCellPositiveHemispherePreimage k x).1,
          Metric.ball_subset_closedBall
            (realProjectiveSpaceSuccTopCellPositiveHemispherePreimage k x).2⟩ =
      x.1 := by
  -- Compare the explicit sphere representatives coordinatewise.
  have hsum :=
    realProjectiveSpaceSuccPositiveHemisphereTrunc_norm_sq_add_last_sq k x
  have hlastPos : 0 < x.1.down.1.ofLp (Fin.last (k + 1)) := by
    exact x.2
  have hlastNonneg : 0 ≤ x.1.down.1.ofLp (Fin.last (k + 1)) := le_of_lt hlastPos
  have hradNonneg :
      0 ≤
        1 -
          ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2 := by
    have hnormLe :
        ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ≤ 1 := by
      have hmem := realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball k x
      exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hmem)
    nlinarith
  have hsqrtEq :
      Real.sqrt
          (1 - ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2) =
        x.1.down.1.ofLp (Fin.last (k + 1)) := by
    have hsqrtSq :
        (Real.sqrt
            (1 - ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2)) ^ 2 =
          (x.1.down.1.ofLp (Fin.last (k + 1))) ^ 2 := by
      calc
        (Real.sqrt
            (1 - ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2)) ^ 2
            =
              1 - ‖realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x‖ ^ 2 := by
                rw [Real.sq_sqrt hradNonneg]
        _ = (x.1.down.1.ofLp (Fin.last (k + 1))) ^ 2 := by
              nlinarith [hsum]
    exact (sq_eq_sq₀ (by positivity) hlastNonneg).mp hsqrtSq
  apply ULift.ext
  apply Subtype.ext
  apply WithLp.ofLp_injective
  ext i
  cases i using Fin.lastCases with
  | last =>
      -- The final coordinate is recovered from the sphere norm and positivity.
      simpa [realProjectiveSpaceSuccTopCellSpherePoint,
        realProjectiveSpaceSuccTopCellPositiveHemispherePreimage,
        realProjectiveSpaceSuccTopCellRepresentative,
        realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc] using hsqrtEq
  | cast j =>
      -- Away from the last coordinate, truncation simply records the original coordinates.
      simp [realProjectiveSpaceSuccTopCellSpherePoint,
        realProjectiveSpaceSuccTopCellPositiveHemispherePreimage,
        realProjectiveSpaceSuccTopCellRepresentative,
        realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc]

/-- Helper for Example 10.1.11: projectivizing the closed-ball representative gives the concrete
successor top-cell extension on the whole closed unit ball. -/
private noncomputable def realProjectiveSpaceSuccTopCellClosedBallMap (k : ℕ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 →
      RealProjectiveSpace (k + 1) :=
  fun z ↦ sphereToRealProjectiveSpace (k + 1) (realProjectiveSpaceSuccTopCellSpherePoint k z)

/-- Helper for Example 10.1.11: the closed-ball top-cell extension is continuous. -/
private theorem realProjectiveSpaceSuccTopCellClosedBallMap_continuous (k : ℕ) :
    Continuous (realProjectiveSpaceSuccTopCellClosedBallMap k) := by
  -- The explicit representative is coordinatewise continuous on the closed ball, so
  -- projectivizing it stays continuous.
  have hRepresentative :
      Continuous fun z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 ↦
        realProjectiveSpaceSuccTopCellRepresentative k z := by
    refine continuous_pi fun i ↦ ?_
    cases i using Fin.lastCases with
    | last =>
        -- The final coordinate is the square-root term from the standard hemisphere chart.
        simpa [realProjectiveSpaceSuccTopCellRepresentative] using
          (Real.continuous_sqrt.comp <|
            (continuous_const.sub <|
              (continuous_norm.comp continuous_subtype_val).pow 2))
    | cast j =>
        -- The first `k + 1` coordinates are the original Euclidean coordinates.
        simpa [realProjectiveSpaceSuccTopCellRepresentative] using
          (continuous_apply j).comp
            ((show Continuous
                (WithLp.ofLp : EuclideanSpace ℝ (Fin (k + 1)) → (Fin (k + 1) → ℝ)) from
              PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin (k + 1) ↦ ℝ)).comp
              continuous_subtype_val)
  have hSpherePoint : Continuous (realProjectiveSpaceSuccTopCellSpherePoint k) := by
    -- Repackage the continuous representative inside the concrete sphere model.
    simpa [realProjectiveSpaceSuccTopCellSpherePoint] using
      (continuous_uliftUp.comp
        (Continuous.subtype_mk
          ((show
              Continuous (WithLp.toLp 2 : (Fin (k + 2) → ℝ) → EuclideanSpace ℝ (Fin (k + 2)))
              from PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin (k + 2) ↦ ℝ)).comp
            hRepresentative)
          (fun z ↦ realProjectiveSpaceSuccTopCellRepresentative_mem_sphere k z)))
  exact (sphereToRealProjectiveSpace_isCoveringMap (k + 1)).continuous.comp hSpherePoint

/-- Helper for Example 10.1.11: on the attaching sphere, the explicit upper-hemisphere point is
the zero-extension sphere point. -/
private theorem realProjectiveSpaceSuccTopCellSpherePoint_boundary_eq (k : ℕ)
    (x : TopCat.sphere k) :
    realProjectiveSpaceSuccTopCellSpherePoint k
        (realProjectiveSpaceAttachingSphereToClosedBall k x) =
      realProjectiveSpaceSuccSphereMap k x := by
  -- The two sphere points have the same concrete representative after the square-root
  -- coordinate vanishes on the boundary.
  apply ULift.ext
  apply Subtype.ext
  apply WithLp.ofLp_injective
  simpa [realProjectiveSpaceSuccTopCellSpherePoint, realProjectiveSpaceSuccSphereMap] using
    realProjectiveSpaceSuccTopCellRepresentative_boundary_eq k x

/-- Helper for Example 10.1.11: the raw successor top-cell map projectivizes the explicit
upper-hemisphere representative on the closed unit ball and collapses the exterior to a basepoint.
-/
private noncomputable def realProjectiveSpaceSuccTopCellFun (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 1)) → RealProjectiveSpace (k + 1) :=
  let _ : DecidablePred
      (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦ z ∈ Metric.closedBall 0 1) := Classical.decPred _
  fun z ↦
      if hz : z ∈ Metric.closedBall 0 1 then
        realProjectiveSpaceSuccTopCellClosedBallMap k ⟨z, hz⟩
      else
        sphereToRealProjectiveSpace (k + 1) (sphereEquatorBasepoint k)

/-- Helper for Example 10.1.11: on the closed unit ball, the raw successor top-cell map is the
projectivized upper-hemisphere representative. -/
@[simp]
private theorem realProjectiveSpaceSuccTopCellFun_apply_of_mem_closedBall (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz : z ∈ Metric.closedBall 0 1) :
    realProjectiveSpaceSuccTopCellFun k z =
      realProjectiveSpaceSuccTopCellClosedBallMap k ⟨z, hz⟩ := by
  -- On the closed ball, the defining `if` takes the geometric branch.
  have hnorm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  simp [realProjectiveSpaceSuccTopCellFun, Metric.mem_closedBall, dist_eq_norm,
    hnorm, realProjectiveSpaceSuccTopCellClosedBallMap]

/-- Helper for Example 10.1.11: on the open ball, the raw successor top-cell map is given by the
explicit upper-hemisphere representative. -/
@[simp]
private theorem realProjectiveSpaceSuccTopCellFun_apply_of_mem_ball (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz : z ∈ Metric.ball 0 1) :
    realProjectiveSpaceSuccTopCellFun k z =
      sphereToRealProjectiveSpace (k + 1)
        (realProjectiveSpaceSuccTopCellSpherePoint k ⟨z, Metric.ball_subset_closedBall hz⟩) := by
  -- Inside the open ball, this is just the closed-ball branch specialized to the same point.
  simpa [realProjectiveSpaceSuccTopCellClosedBallMap] using
    realProjectiveSpaceSuccTopCellFun_apply_of_mem_closedBall k (Metric.ball_subset_closedBall hz)

/-- Helper for Example 10.1.11: on the attaching sphere, the raw successor top-cell map is the
standard projective zero-extension. -/
private theorem realProjectiveSpaceSuccTopCellFun_boundary_eq (k : ℕ)
    (x : TopCat.sphere k) :
    realProjectiveSpaceSuccTopCellFun k x.down.1 =
      realProjectiveSpaceSuccInclusion k (sphereToRealProjectiveSpace k x) := by
  -- The closed-ball branch agrees with the boundary zero-extension representative.
  rw [realProjectiveSpaceSuccTopCellFun_apply_of_mem_closedBall]
  rw [realProjectiveSpaceSuccInclusion_apply_mk]
  rw [realProjectiveSpaceSuccTopCellClosedBallMap]
  change
    sphereToRealProjectiveSpace (k + 1)
      (realProjectiveSpaceSuccTopCellSpherePoint k
        (realProjectiveSpaceAttachingSphereToClosedBall k x)) =
      sphereToRealProjectiveSpace (k + 1) (realProjectiveSpaceSuccSphereMap k x)
  exact congrArg (sphereToRealProjectiveSpace (k + 1))
    (realProjectiveSpaceSuccTopCellSpherePoint_boundary_eq k x)

/-- Helper for Example 10.1.11: the raw successor top-cell map is injective on the open ball. -/
private theorem realProjectiveSpaceSuccTopCellInjOn (k : ℕ) :
    Set.InjOn (realProjectiveSpaceSuccTopCellFun k) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  have hxy' :
      sphereToRealProjectiveSpace (k + 1)
        (realProjectiveSpaceSuccTopCellSpherePoint k ⟨x, Metric.ball_subset_closedBall hx⟩) =
      sphereToRealProjectiveSpace (k + 1)
        (realProjectiveSpaceSuccTopCellSpherePoint k ⟨y, Metric.ball_subset_closedBall hy⟩) := by
    calc
      sphereToRealProjectiveSpace (k + 1)
          (realProjectiveSpaceSuccTopCellSpherePoint k ⟨x, Metric.ball_subset_closedBall hx⟩)
          = realProjectiveSpaceSuccTopCellFun k x := by
            exact (realProjectiveSpaceSuccTopCellFun_apply_of_mem_ball k hx).symm
      _ = realProjectiveSpaceSuccTopCellFun k y := hxy
      _ = sphereToRealProjectiveSpace (k + 1)
          (realProjectiveSpaceSuccTopCellSpherePoint k ⟨y, Metric.ball_subset_closedBall hy⟩) := by
            exact realProjectiveSpaceSuccTopCellFun_apply_of_mem_ball k hy
  rcases (sphereToRealProjectiveSpace_eq_iff (k + 1)).1 hxy' with hsame | hneg
  · -- In the direct branch, equality of projective points forces equality of representatives.
    have hrepr :
        realProjectiveSpaceSuccTopCellRepresentative k ⟨x, Metric.ball_subset_closedBall hx⟩ =
          realProjectiveSpaceSuccTopCellRepresentative k ⟨y, Metric.ball_subset_closedBall hy⟩ := by
      have hcoord :=
        congrArg (fun w : TopCat.sphere (k + 1) ↦ w.down.1.ofLp) hsame
      simpa [realProjectiveSpaceSuccTopCellSpherePoint] using hcoord
    ext i
    have hcoord := congrArg (fun f : Fin (k + 2) → ℝ ↦ f i.castSucc) hrepr
    simpa [realProjectiveSpaceSuccTopCellRepresentative] using hcoord
  · -- In the antipodal branch, the last coordinate would have to be both nonnegative and
    -- negative, forcing it to vanish, which contradicts open-ball membership.
    have hlast :
        realProjectiveSpaceSuccTopCellRepresentative k ⟨x, Metric.ball_subset_closedBall hx⟩
            (Fin.last (k + 1)) =
          -realProjectiveSpaceSuccTopCellRepresentative k ⟨y, Metric.ball_subset_closedBall hy⟩
            (Fin.last (k + 1)) := by
      have hcoord :=
        congrArg (fun w : TopCat.sphere (k + 1) ↦ w.down.1.ofLp (Fin.last (k + 1))) hneg
      simpa [realProjectiveSpaceSuccTopCellSpherePoint, sphereModel_ofLp_neg] using hcoord
    have hxnonzero :=
      realProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball k hx
    have hxnonneg :
        0 ≤ realProjectiveSpaceSuccTopCellRepresentative k ⟨x, Metric.ball_subset_closedBall hx⟩
          (Fin.last (k + 1)) := by
      simp [realProjectiveSpaceSuccTopCellRepresentative]
    have hynonneg :
        0 ≤ realProjectiveSpaceSuccTopCellRepresentative k ⟨y, Metric.ball_subset_closedBall hy⟩
          (Fin.last (k + 1)) := by
      simp [realProjectiveSpaceSuccTopCellRepresentative]
    have hxzero :
        realProjectiveSpaceSuccTopCellRepresentative k ⟨x, Metric.ball_subset_closedBall hx⟩
          (Fin.last (k + 1)) = 0 := by
      nlinarith
    exact (hxnonzero hxzero).elim

/-- Helper for Example 10.1.11: the raw successor top-cell map packages into a thin
`PartialEquiv` whose target is just its open-ball image. -/
private noncomputable def realProjectiveSpaceSuccTopCellMap (k : ℕ) :
    PartialEquiv (EuclideanSpace ℝ (Fin (k + 1))) (RealProjectiveSpace (k + 1)) :=
  -- Route correction: keep the target as the raw image of the open ball so that target
  -- identification with the equator complement can be proved separately.
  let _ : DecidablePred
      (fun y : RealProjectiveSpace (k + 1) ↦
        y ∈ realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1) := Classical.decPred _
  { toFun := realProjectiveSpaceSuccTopCellFun k
    invFun := fun y ↦
      if hy : y ∈ realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1 then
        Classical.choose hy
      else
        0
    source := Metric.ball 0 1
    target := realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1
    map_source' := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    map_target' := by
      intro y hy
      rw [dif_pos hy]
      exact (Classical.choose_spec hy).1
    left_inv' := by
      intro x hx
      have hy : realProjectiveSpaceSuccTopCellFun k x ∈
          realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1 := ⟨x, hx, rfl⟩
      have hchoose_mem : Classical.choose hy ∈ Metric.ball 0 1 :=
        (Classical.choose_spec hy).1
      have hchoose_eq :
          realProjectiveSpaceSuccTopCellFun k (Classical.choose hy) =
            realProjectiveSpaceSuccTopCellFun k x :=
        (Classical.choose_spec hy).2
      rw [dif_pos hy]
      exact realProjectiveSpaceSuccTopCellInjOn k hchoose_mem hx hchoose_eq
    right_inv' := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx' : realProjectiveSpaceSuccTopCellFun k x ∈
          realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1 := ⟨x, hx, rfl⟩
      -- On the target, the chosen inverse branch returns a genuine preimage from the source ball.
      rw [dif_pos hx']
      exact (Classical.choose_spec hx').2 }

/-- Helper for Example 10.1.11: the raw successor top-cell image misses the equator. -/
private theorem realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball (k : ℕ)
    {z : EuclideanSpace ℝ (Fin (k + 1))} (hz : z ∈ Metric.ball 0 1) :
    realProjectiveSpaceSuccTopCellFun k z ∉ realProjectiveSpaceEquatorLocus k := by
  intro hmem
  rcases hmem with ⟨x, hx, hxproj⟩
  have hproj :
      sphereToRealProjectiveSpace (k + 1)
        (realProjectiveSpaceSuccTopCellSpherePoint k ⟨z, Metric.ball_subset_closedBall hz⟩) =
      sphereToRealProjectiveSpace (k + 1) x := by
    calc
      sphereToRealProjectiveSpace (k + 1)
          (realProjectiveSpaceSuccTopCellSpherePoint k ⟨z, Metric.ball_subset_closedBall hz⟩)
          = realProjectiveSpaceSuccTopCellFun k z := by
            exact (realProjectiveSpaceSuccTopCellFun_apply_of_mem_ball k hz).symm
      _ = sphereToRealProjectiveSpace (k + 1) x := hxproj.symm
  rcases (sphereToRealProjectiveSpace_eq_iff (k + 1)).1 hproj with hsame | hneg
  · have hlast :
        realProjectiveSpaceSuccTopCellRepresentative k ⟨z, Metric.ball_subset_closedBall hz⟩
            (Fin.last (k + 1)) = 0 := by
      have hcoord :=
        congrArg (fun w : TopCat.sphere (k + 1) ↦ w.down.1.ofLp (Fin.last (k + 1))) hsame
      simpa [realProjectiveSpaceSuccTopCellSpherePoint, sphereEquatorLocus] using hcoord.trans hx
    exact realProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball k hz hlast
  · have hlast :
        realProjectiveSpaceSuccTopCellRepresentative k ⟨z, Metric.ball_subset_closedBall hz⟩
            (Fin.last (k + 1)) = 0 := by
      have hcoord :=
        congrArg (fun w : TopCat.sphere (k + 1) ↦ w.down.1.ofLp (Fin.last (k + 1))) hneg
      have hxlast : x.down.1.ofLp (Fin.last (k + 1)) = 0 := by
        simpa [sphereEquatorLocus] using hx
      simpa [realProjectiveSpaceSuccTopCellSpherePoint, sphereModel_ofLp_neg, hxlast] using hcoord
    exact realProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball k hz hlast

/-- Helper for Example 10.1.11: the thin top-cell chart already lands in the complement of the
equatorial copy of `RP^k`. -/
private theorem realProjectiveSpaceSuccTopCellMap_target_subset_compl (k : ℕ) :
    (realProjectiveSpaceSuccTopCellMap k).target ⊆
      ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) := by
  intro y hy hyEquator
  rcases hy with ⟨z, hz, rfl⟩
  exact realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball k hz hyEquator

/-- Helper for Example 10.1.11: the raw successor top-cell open image is exactly the complement of
the equatorial copy of `RP^k`. -/
private theorem realProjectiveSpaceSuccTopCellFun_image_ball_eq_compl (k : ℕ) :
    realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1 =
      ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball k hz
  · intro hy
    let x :
        realProjectiveSpacePositiveHemisphere k :=
      (realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm ⟨y, hy⟩
    let z := realProjectiveSpaceSuccTopCellPositiveHemispherePreimage k x
    refine ⟨z.1, z.2, ?_⟩
    -- Recover the ambient projective point by lifting through the positive hemisphere.
    calc
      realProjectiveSpaceSuccTopCellFun k z.1 =
          sphereToRealProjectiveSpace (k + 1)
            (realProjectiveSpaceSuccTopCellSpherePoint k
              ⟨z.1, Metric.ball_subset_closedBall z.2⟩) := by
                exact realProjectiveSpaceSuccTopCellFun_apply_of_mem_ball k z.2
      _ = sphereToRealProjectiveSpace (k + 1) x.1 := by
            exact congrArg (sphereToRealProjectiveSpace (k + 1))
              (realProjectiveSpaceSuccTopCellSpherePoint_of_positiveHemispherePreimage k x)
      _ = y := by
            have hxRight :
                realProjectiveSpacePositiveHemisphereHomeomorphCompl k x = ⟨y, hy⟩ := by
              simpa [x] using
                ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).right_inv ⟨y, hy⟩)
            calc
              sphereToRealProjectiveSpace (k + 1) x.1 =
                  (realProjectiveSpacePositiveHemisphereHomeomorphCompl k x :
                    RealProjectiveSpace (k + 1)) := by
                      symm
                      exact realProjectiveSpacePositiveHemisphereHomeomorphCompl_apply k x
              _ = y := congrArg Subtype.val hxRight

/-- Helper for Example 10.1.11: choose a genuine coordinate bridge from the function-model open
unit ball to the Euclidean open unit ball used by the geometric successor top-cell chart. -/
private noncomputable def realProjectiveSpaceSuccFunctionBallToEuclideanBall (k : ℕ) :
    OpenPartialHomeomorph (Fin (k + 1) → ℝ) (EuclideanSpace ℝ (Fin (k + 1))) := by
  -- Route correction: the old `EuclideanSpace.equiv` image-equality route was false because the
  -- function model uses the ambient `Pi` norm while `EuclideanSpace` uses the `L2` norm.
  -- TODO: construct the bridge by a boundary-preserving radial homeomorphism between the two norm
  -- models, then package its open-ball restriction as the required partial homeomorphism.
  sorry

/-- Helper for Example 10.1.11: the source bridge starts exactly on the standard open unit ball in
function coordinates. -/
@[simp]
private theorem realProjectiveSpaceSuccFunctionBallToEuclideanBall_source (k : ℕ) :
    (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).source =
      Metric.ball (0 : Fin (k + 1) → ℝ) 1 := by
  -- TODO: this should reduce definitionally once the radial bridge above is implemented.
  sorry

/-- Helper for Example 10.1.11: the source bridge lands exactly in the Euclidean open unit ball
used by the raw top-cell chart. -/
@[simp]
private theorem realProjectiveSpaceSuccFunctionBallToEuclideanBall_target (k : ℕ) :
    (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).target =
      Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
  -- TODO: this should reduce definitionally once the radial bridge above is implemented.
  sorry

/-- Helper for Example 10.1.11: the complement-side inverse of the successor top-cell chart is the
positive-hemisphere truncation, written in the CW-standard function-space coordinates. -/
private noncomputable def realProjectiveSpaceSuccTopCellInverseOnCompl (k : ℕ) :
    { y : RealProjectiveSpace (k + 1) | y ∉ realProjectiveSpaceEquatorLocus k } →
      Fin (k + 1) → ℝ :=
  fun y ↦
    (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).symm
      (realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
        ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm y))

/-- Helper for Example 10.1.11: the truncation map from the positive hemisphere is continuous. -/
private theorem realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_continuous (k : ℕ) :
    Continuous (realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k) := by
  -- The truncation is just the first `k + 1` coordinates of the sphere representative, repackaged
  -- in Euclidean coordinates.
  have hCoords :
      Continuous fun x : realProjectiveSpacePositiveHemisphere k ↦
        (((x.1.down.1 : EuclideanSpace ℝ (Fin (k + 2))) : Fin (k + 2) → ℝ)) := by
    exact
      (show Continuous
          (WithLp.ofLp : EuclideanSpace ℝ (Fin (k + 2)) → (Fin (k + 2) → ℝ)) from
        PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin (k + 2) ↦ ℝ)).comp
        (continuous_subtype_val.comp <|
          continuous_uliftDown.comp continuous_subtype_val)
  simpa [realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc] using
    (show Continuous (WithLp.toLp 2 : (Fin (k + 1) → ℝ) → EuclideanSpace ℝ (Fin (k + 1))) from
      PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin (k + 1) ↦ ℝ)).comp
      (continuous_pi fun i ↦ (continuous_apply i.castSucc).comp hCoords)

/-- Helper for Example 10.1.11: the complement-side inverse lands back in the standard open
source ball. -/
private theorem realProjectiveSpaceSuccTopCellInverseOnCompl_mem_ball (k : ℕ)
    (y : { y : RealProjectiveSpace (k + 1) | y ∉ realProjectiveSpaceEquatorLocus k }) :
    realProjectiveSpaceSuccTopCellInverseOnCompl k y ∈
      Metric.ball (0 : Fin (k + 1) → ℝ) 1 := by
  -- The positive-hemisphere truncation already lands in the Euclidean source ball, and the source
  -- bridge sends that target ball back to the standard function-space ball.
  have hTarget :
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
          ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm y) ∈
        (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).target := by
    simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball k
        ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm y)
  simpa [realProjectiveSpaceSuccTopCellInverseOnCompl,
    realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using
    (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).map_target hTarget

/-- Helper for Example 10.1.11: evaluating the normalized inverse on a complement point returns the
ambient Euclidean preimage used by the raw top-cell chart. -/
private theorem realProjectiveSpaceSuccTopCellMapOnFunctions_inverse_apply (k : ℕ)
    (y : { y : RealProjectiveSpace (k + 1) | y ∉ realProjectiveSpaceEquatorLocus k }) :
    realProjectiveSpaceSuccTopCellFun k
        ((realProjectiveSpaceSuccFunctionBallToEuclideanBall k)
          (realProjectiveSpaceSuccTopCellInverseOnCompl k y)) =
      y.1 := by
  -- Move to the positive-hemisphere representative, undo the source bridge on the Euclidean ball,
  -- and then return to the ambient complement point via the homeomorphism.
  let x : realProjectiveSpacePositiveHemisphere k :=
    (realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm y
  have hxBall :
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 :=
    realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball k x
  have hxTarget :
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x ∈
        (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).target := by
    simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using hxBall
  have hxRight :
      realProjectiveSpacePositiveHemisphereHomeomorphCompl k x = y := by
    simpa [x] using (realProjectiveSpacePositiveHemisphereHomeomorphCompl k).right_inv y
  calc
    realProjectiveSpaceSuccTopCellFun k
        ((realProjectiveSpaceSuccFunctionBallToEuclideanBall k)
          (realProjectiveSpaceSuccTopCellInverseOnCompl k y)) =
      realProjectiveSpaceSuccTopCellFun k
        (realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x) := by
          exact congrArg (realProjectiveSpaceSuccTopCellFun k) <|
            (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).right_inv hxTarget
    _ =
      sphereToRealProjectiveSpace (k + 1)
        (realProjectiveSpaceSuccTopCellSpherePoint k
          ⟨realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k x,
            Metric.ball_subset_closedBall hxBall⟩) := by
            exact realProjectiveSpaceSuccTopCellFun_apply_of_mem_ball k hxBall
    _ = sphereToRealProjectiveSpace (k + 1) x.1 := by
          exact congrArg (sphereToRealProjectiveSpace (k + 1))
            (realProjectiveSpaceSuccTopCellSpherePoint_of_positiveHemispherePreimage k x)
    _ =
      (realProjectiveSpacePositiveHemisphereHomeomorphCompl k x :
        RealProjectiveSpace (k + 1)) := by
          symm
          exact realProjectiveSpacePositiveHemisphereHomeomorphCompl_apply k x
    _ = y.1 := congrArg Subtype.val hxRight

/-- Helper for Example 10.1.11: on the standard source ball, the normalized complement inverse
really is the inverse of the function-coordinate top-cell chart. -/
private theorem realProjectiveSpaceSuccTopCellInverseOnCompl_apply_image (k : ℕ)
    {x : Fin (k + 1) → ℝ} (hx : x ∈ Metric.ball 0 1) :
    realProjectiveSpaceSuccTopCellInverseOnCompl k
        ⟨realProjectiveSpaceSuccTopCellFun k
            ((realProjectiveSpaceSuccFunctionBallToEuclideanBall k) x),
          by
            have hz :
                (realProjectiveSpaceSuccFunctionBallToEuclideanBall k) x ∈
                  Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
              simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using
                (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).map_source <|
                  by simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using hx
            exact realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball k hz⟩ = x := by
  -- The raw top-cell inverse recovers the Euclidean source point, and the source bridge then
  -- returns to the original function-space coordinates.
  let z : EuclideanSpace ℝ (Fin (k + 1)) :=
    (realProjectiveSpaceSuccFunctionBallToEuclideanBall k) x
  have hz :
      z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
    simpa [z, realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using
      (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).map_source <|
        by simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using hx
  have hy :
      realProjectiveSpaceSuccTopCellFun k z ∉ realProjectiveSpaceEquatorLocus k :=
    realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball k hz
  have hrawBall :
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
          ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm
            ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩) ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
    exact realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball k
      ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm
        ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩)
  have hTarget :
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
          ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm
            ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩) ∈
        (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).target := by
    simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using hrawBall
  have hrawEq :
      realProjectiveSpaceSuccTopCellFun k
          (realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
            ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm
              ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩)) =
        realProjectiveSpaceSuccTopCellFun k z := by
    calc
      realProjectiveSpaceSuccTopCellFun k
          (realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
            ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm
              ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩)) =
        realProjectiveSpaceSuccTopCellFun k
          ((realProjectiveSpaceSuccFunctionBallToEuclideanBall k)
            (realProjectiveSpaceSuccTopCellInverseOnCompl k
              ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩)) := by
              exact congrArg (realProjectiveSpaceSuccTopCellFun k) <|
                ((realProjectiveSpaceSuccFunctionBallToEuclideanBall k).right_inv hTarget).symm
      _ = realProjectiveSpaceSuccTopCellFun k z := by
            simpa [z] using
              realProjectiveSpaceSuccTopCellMapOnFunctions_inverse_apply k
                ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩
  have hrawInv :
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
          ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm
            ⟨realProjectiveSpaceSuccTopCellFun k z, hy⟩) = z := by
    exact realProjectiveSpaceSuccTopCellInjOn k hrawBall hz hrawEq
  calc
    realProjectiveSpaceSuccTopCellInverseOnCompl k
        ⟨realProjectiveSpaceSuccTopCellFun k
            ((realProjectiveSpaceSuccFunctionBallToEuclideanBall k) x), hy⟩ =
      (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).symm z := by
        exact congrArg
          (fun w ↦ (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).symm w) hrawInv
    _ = x := by
      have hxSource :
          x ∈ (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).source := by
        simpa [realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using hx
      simpa [z] using (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).left_inv hxSource

/-- Helper for Example 10.1.11: the normalized successor top-cell chart is the final
function-source/complement-target `PartialEquiv` needed by the CW constructor. -/
private noncomputable def realProjectiveSpaceSuccTopCellMapOnFunctions (k : ℕ) :
    PartialEquiv (Fin (k + 1) → ℝ) (RealProjectiveSpace (k + 1)) :=
  let e := realProjectiveSpaceSuccFunctionBallToEuclideanBall k
  let _ :
      DecidablePred
        (fun y : RealProjectiveSpace (k + 1) ↦
          y ∈ ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ)) :=
    Classical.decPred _
  { toFun := fun x ↦ realProjectiveSpaceSuccTopCellFun k (e x)
    invFun := fun y ↦
      if hy : y ∈
          ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) then
        realProjectiveSpaceSuccTopCellInverseOnCompl k ⟨y, hy⟩
      else
        0
    source := Metric.ball 0 1
    target := (realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ
    map_source' := by
      intro x hx
      have hxSource : x ∈ e.source := by
        simpa [e, realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using hx
      have hzTarget : e x ∈ e.target := e.map_source hxSource
      have hz :
          e x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
        simpa [e, realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using hzTarget
      exact realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball k hz
    map_target' := by
      intro y hy
      rw [dif_pos hy]
      simpa using realProjectiveSpaceSuccTopCellInverseOnCompl_mem_ball k ⟨y, hy⟩
    left_inv' := by
      intro x hx
      have hxSource : x ∈ e.source := by
        simpa [e, realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using hx
      have hy :
          realProjectiveSpaceSuccTopCellFun k (e x) ∈
            ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) :=
        by
          have hzTarget : e x ∈ e.target := e.map_source hxSource
          have hz :
              e x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 := by
            simpa [e, realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using hzTarget
          exact realProjectiveSpaceSuccTopCellFun_not_mem_equator_of_mem_ball k hz
      rw [dif_pos hy]
      simpa [e] using realProjectiveSpaceSuccTopCellInverseOnCompl_apply_image k hx
    right_inv' := by
      intro y hy
      rw [dif_pos hy]
      exact realProjectiveSpaceSuccTopCellMapOnFunctions_inverse_apply k ⟨y, hy⟩
    }

/-- Helper for Example 10.1.11: choose the boundary identification between `TopCat.sphere k` and
the function-coordinate attaching sphere so that the source-ball bridge recovers the Euclidean
boundary point used by the geometric top-cell chart. -/
private noncomputable abbrev realProjectiveSpaceSuccTopCellBoundaryHomeomorph (k : ℕ) :
    TopCat.sphere k ≃ₜ Metric.sphere (0 : Fin (k + 1) → ℝ) 1 := by
  -- TODO: obtain this homeomorphism from the same radial closed-ball model as the open-ball
  -- bridge, so that it matches the Euclidean boundary chart by construction.
  sorry

/-- Helper for Example 10.1.11: the chosen function/Euclidean source-ball bridge agrees with the
boundary identification on the attaching sphere. -/
private theorem realProjectiveSpaceSuccFunctionBallToEuclideanBall_boundary_eq
    (k : ℕ) (x : TopCat.sphere k) :
    realProjectiveSpaceSuccFunctionBallToEuclideanBall k
        (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k x).1 =
      x.down.1 := by
  -- TODO: prove this from the radial coordinate construction of the bridge and the boundary
  -- homeomorphism; it is the exact compatibility needed by the top-cell boundary formula.
  sorry

/-- Helper for Example 10.1.11: after rigidly identifying the function-space boundary with the
Euclidean attaching sphere, the normalized top-cell map reduces to the raw Euclidean boundary
value. -/
private theorem realProjectiveSpaceSuccTopCellMapOnFunctions_boundary_eq_raw
    (k : ℕ) (x : TopCat.sphere k) :
    realProjectiveSpaceSuccTopCellMapOnFunctions k
        (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k x).1 =
      realProjectiveSpaceSuccTopCellFun k x.down.1 := by
  -- Route correction: the corrected source-ball bridge is required only through its boundary
  -- compatibility with the chosen sphere identification.
  change
    realProjectiveSpaceSuccTopCellFun k
        (realProjectiveSpaceSuccFunctionBallToEuclideanBall k
          (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k x).1) =
      realProjectiveSpaceSuccTopCellFun k x.down.1
  rw [realProjectiveSpaceSuccFunctionBallToEuclideanBall_boundary_eq k x]

/-- Helper for Example 10.1.11: the rigid boundary homeomorphism makes the function-coordinate
top-cell chart restrict to the standard double-cover inclusion on the attaching sphere. -/
private theorem realProjectiveSpaceSuccTopCellMapOnFunctions_boundary_eq
    (k : ℕ) (x : TopCat.sphere k) :
    realProjectiveSpaceSuccTopCellMapOnFunctions k
        (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k x).1 =
      realProjectiveSpaceSuccInclusion k (sphereToRealProjectiveSpace k x) := by
  -- The corrected boundary formula now matches the raw Euclidean top-cell boundary computation.
  calc
    realProjectiveSpaceSuccTopCellMapOnFunctions k
        (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k x).1 =
      realProjectiveSpaceSuccTopCellFun k x.down.1 :=
        realProjectiveSpaceSuccTopCellMapOnFunctions_boundary_eq_raw k x
    _ =
      realProjectiveSpaceSuccInclusion k (sphereToRealProjectiveSpace k x) :=
        realProjectiveSpaceSuccTopCellFun_boundary_eq k x

/-- Helper for Example 10.1.11: the raw Euclidean top-cell chart is continuous on the closed unit
ball. -/
private theorem realProjectiveSpaceSuccTopCellFun_continuousOn_closedBall (k : ℕ) :
    ContinuousOn (realProjectiveSpaceSuccTopCellFun k)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict :
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1).restrict
          (realProjectiveSpaceSuccTopCellFun k) =
        realProjectiveSpaceSuccTopCellClosedBallMap k := by
    funext z
    have hz :
        ((z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
          EuclideanSpace ℝ (Fin (k + 1))) ∈ Metric.closedBall 0 1 := z.2
    simp only [Set.restrict, realProjectiveSpaceSuccTopCellFun]
    rw [dif_pos hz]
  -- On the closed ball, the `if`-branch in `realProjectiveSpaceSuccTopCellFun` is definitionally
  -- the explicit closed-ball chart.
  rw [hrestrict]
  exact realProjectiveSpaceSuccTopCellClosedBallMap_continuous k

/-- Helper for Example 10.1.11: the inverse of the normalized top-cell chart is continuous on the
complement target. -/
private theorem realProjectiveSpaceSuccTopCellMapOnFunctionsContinuousOnSymm (k : ℕ) :
    ContinuousOn (realProjectiveSpaceSuccTopCellMapOnFunctions k).symm
      ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) := by
  -- On the complement target, the inverse is the explicit positive-hemisphere inverse followed by
  -- the source-ball homeomorphism back to function coordinates.
  rw [continuousOn_iff_continuous_restrict]
  let g :
      { y : RealProjectiveSpace (k + 1) //
          y ∈ ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) } →
        EuclideanSpace ℝ (Fin (k + 1)) :=
    fun y ↦
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc k
        ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm y)
  have hg : Continuous g := by
    -- The complement-side inverse to the raw top-cell chart is continuous before we return to
    -- function-space coordinates.
    exact (realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_continuous k).comp
      (realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm.continuous
  have hgTarget :
      ∀ y,
        g y ∈ (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).target := by
    intro y
    simpa [g, realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using
      realProjectiveSpaceSuccTopCellPositiveHemisphereTrunc_mem_ball k
        ((realProjectiveSpacePositiveHemisphereHomeomorphCompl k).symm y)
  simpa [Set.restrict, realProjectiveSpaceSuccTopCellMapOnFunctions,
    realProjectiveSpaceSuccTopCellInverseOnCompl, g] using
    (realProjectiveSpaceSuccFunctionBallToEuclideanBall k).continuousOn_symm.comp_continuous
      hg hgTarget

/-- Helper for Example 10.1.11: the successor cell family reuses every inherited equatorial
`m`-cell and adds one new top cell in degree `k + 1`. -/
private abbrev realProjectiveSpaceSuccCell (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k)
    (m : ℕ) :=
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
  Sum (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) (PLift (m = k + 1))

/-- Helper for Example 10.1.11: the successor cell family uses inherited equatorial cells together
with the single normalized top cell in degree `k + 1`. -/
private noncomputable def realProjectiveSpaceSuccCellMap (k : ℕ)
    (S : RealProjectiveSpaceStandardCWStructure k) {m : ℕ} :
    realProjectiveSpaceSuccCell k S m →
      PartialEquiv (Fin m → ℝ) (RealProjectiveSpace (k + 1))
  | Sum.inl j => realProjectiveSpaceEquatorTransportCellMapAmbient k S j
  | Sum.inr hm => by
      rcases hm with ⟨hm⟩
      subst hm
      exact realProjectiveSpaceSuccTopCellMapOnFunctions k

/-- Helper for Example 10.1.11: each degree of the successor cell family is finite. -/
private theorem realProjectiveSpaceSuccCell_finite (k : ℕ)
    (S : RealProjectiveSpaceStandardCWStructure k) (m : ℕ) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    Finite (realProjectiveSpaceSuccCell k S m) := by
  -- This is the finite inherited cell set plus at most one new top cell.
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
  letI : Finite (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) :=
    S.finite.finite_cell m
  infer_instance

/-- Helper for Example 10.1.11: above degree `k + 1`, the successor cell family is empty. -/
private theorem realProjectiveSpaceSuccCell_eventuallyIsEmpty (k : ℕ)
    (S : RealProjectiveSpaceStandardCWStructure k) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    ∀ᶠ m in Filter.atTop, IsEmpty (realProjectiveSpaceSuccCell k S m) := by
  -- For `m ≥ k + 2`, the inherited family is already empty and the extra top-cell summand no
  -- longer appears.
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
  rw [Filter.eventually_atTop]
  refine ⟨k + 2, ?_⟩
  intro m hm
  have hInherited :
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) :=
    S.isEmpty_cell_of_lt m <|
      lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ k)) hm
  have hTop :
      IsEmpty (PLift (m = k + 1)) := by
    refine ⟨fun h ↦ ?_⟩
    exact (Nat.ne_of_gt <| lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) hm) h.down
  letI := hInherited
  letI := hTop
  infer_instance

/-- Helper for Example 10.1.11: the successor cell family has no cells above degree `k + 1`. -/
private theorem realProjectiveSpaceSuccCell_isEmpty_of_lt (k : ℕ)
    (S : RealProjectiveSpaceStandardCWStructure k) (m : ℕ) (hm : k + 1 < m) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    IsEmpty (realProjectiveSpaceSuccCell k S m) := by
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
  have hInherited :
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) :=
    S.isEmpty_cell_of_lt m (lt_trans (Nat.lt_succ_self k) hm)
  have hTop : IsEmpty (PLift (m = k + 1)) := by
    refine ⟨fun h ↦ ?_⟩
    exact (Nat.ne_of_gt hm) h.down
  letI := hInherited
  letI := hTop
  infer_instance

/-- Helper for Example 10.1.11: the successor cell family still has exactly one `m`-cell in each
dimension `m ≤ k + 1`. -/
private theorem realProjectiveSpaceSuccCellCard_eq_one (k : ℕ)
    (S : RealProjectiveSpaceStandardCWStructure k) (m : ℕ) (hm : m ≤ k + 1) :
    letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
    Nat.card (realProjectiveSpaceSuccCell k S m) = 1 := by
  letI : Topology.CWComplex (Set.univ : Set (RealProjectiveSpace k)) := S.cwComplex
  rcases lt_or_eq_of_le hm with hmk | rfl
  · have hTop : IsEmpty (PLift (m = k + 1)) := by
      refine ⟨fun h ↦ ?_⟩
      exact (Nat.ne_of_lt hmk) h.down
    letI : Finite (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) :=
      S.finite.finite_cell m
    -- Below the top degree, the extra summand disappears and the inherited unique cell remains.
    calc
      Nat.card (realProjectiveSpaceSuccCell k S m) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) +
            Nat.card (PLift (m = k + 1)) := by
              simpa [realProjectiveSpaceSuccCell] using
                (Nat.card_sum :
                  Nat.card
                      ((Topology.CWComplex.cell
                          (Set.univ : Set (RealProjectiveSpace k)) m) ⊕
                        PLift (m = k + 1)) =
                    Nat.card (Topology.CWComplex.cell
                      (Set.univ : Set (RealProjectiveSpace k)) m) +
                      Nat.card (PLift (m = k + 1)))
      _ = 1 + 0 := by
            rw [S.cellCard_eq_one m (Nat.le_of_lt_succ hmk)]
            have hTopCard : Nat.card (PLift (m = k + 1)) = 0 := by
              letI := hTop
              simpa using (Nat.card_congr (Equiv.equivPEmpty (PLift (m = k + 1))))
            rw [hTopCard]
      _ = 1 := by norm_num
  · have hInherited :
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) (k + 1)) :=
      S.isEmpty_cell_of_lt (k + 1) (Nat.lt_succ_self k)
    letI : Finite (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) (k + 1)) :=
      S.finite.finite_cell (k + 1)
    -- In the top degree, the inherited summand vanishes and the new top cell is unique.
    calc
      Nat.card (realProjectiveSpaceSuccCell k S (k + 1)) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) (k + 1)) +
            Nat.card (PLift ((k + 1) = k + 1)) := by
              simpa [realProjectiveSpaceSuccCell] using
                (Nat.card_sum :
                  Nat.card
                      ((Topology.CWComplex.cell
                          (Set.univ : Set (RealProjectiveSpace k)) (k + 1)) ⊕
                        PLift ((k + 1) = k + 1)) =
                    Nat.card (Topology.CWComplex.cell
                      (Set.univ : Set (RealProjectiveSpace k)) (k + 1)) +
                      Nat.card (PLift ((k + 1) = k + 1)))
      _ = 0 + 1 := by
            have hInheritedCard :
                Nat.card (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k))
                  (k + 1)) = 0 := by
              letI := hInherited
              simpa using
                (Nat.card_congr
                  (Equiv.equivPEmpty
                    (Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) (k + 1))))
            have hTopCard : Nat.card (PLift ((k + 1) = k + 1)) = 1 := by
              refine Nat.card_eq_one_iff_exists.2 ?_
              refine ⟨⟨rfl⟩, ?_⟩
              intro x
              cases x
              rfl
            rw [hInheritedCard, hTopCard]
      _ = 1 := by norm_num

/-- Helper for Example 10.1.11: ambientizing the inherited open cells preserves the pairwise
disjointness already present in the lower-dimensional CW structure. -/
private theorem realProjectiveSpaceSuccInheritedOpenCell_pairwiseDisjoint
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) :
    letI := S.cwComplex
    (Set.univ :
      Set (Σ m, Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m)).PairwiseDisjoint
        (fun mj ↦
          realProjectiveSpaceEquatorTransportCellMapAmbient k S mj.2 '' Metric.ball 0 1) := by
  letI := S.cwComplex
  intro a _ b _ hab
  refine Set.disjoint_left.2 ?_
  intro y hyA hyB
  rcases hyA with ⟨xA, hxA, hA⟩
  rcases hyB with ⟨xB, hxB, hB⟩
  have hsubEq :
      realProjectiveSpaceEquatorTransportCellMap k S a.2 xA =
        realProjectiveSpaceEquatorTransportCellMap k S b.2 xB := by
    apply Subtype.ext
    -- Compare the two ambient images at the ambient projective-space level.
    calc
      (((realProjectiveSpaceEquatorTransportCellMap k S a.2 xA :
            realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1))) = y := by
            simpa [realProjectiveSpaceEquatorTransportCellMapAmbient_apply] using hA
      _ =
          (((realProjectiveSpaceEquatorTransportCellMap k S b.2 xB :
              realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1))) := by
              simpa [realProjectiveSpaceEquatorTransportCellMapAmbient_apply] using hB.symm
  have hOldEq :
      S.cwComplex.map a.1 a.2 xA = S.cwComplex.map b.1 b.2 xB := by
    -- Pull the equality back through the equator homeomorphism to the predecessor CW complex.
    have hEq := congrArg (realProjectiveSpaceEquatorLocusHomeomorph k) hsubEq
    simpa [realProjectiveSpaceEquatorTransportCellMap_apply] using hEq
  have hdisj :=
    S.cwComplex.pairwiseDisjoint'
      (show a ∈ (Set.univ :
        Set (Σ m, Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m)) by simp)
      (show b ∈ (Set.univ :
        Set (Σ m, Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m)) by simp)
      hab
  have hmemA :
      S.cwComplex.map b.1 b.2 xB ∈ S.cwComplex.map a.1 a.2 '' Metric.ball 0 1 := by
    exact ⟨xA, hxA, hOldEq⟩
  have hmemB :
      S.cwComplex.map b.1 b.2 xB ∈ S.cwComplex.map b.1 b.2 '' Metric.ball 0 1 := by
    exact ⟨xB, hxB, rfl⟩
  exact Set.disjoint_left.1 hdisj hmemA hmemB

/-- Helper for Example 10.1.11: every inherited open cell stays disjoint from the new top open
cell because inherited points lie in the equator and top-cell points lie in its complement. -/
private theorem realProjectiveSpaceSuccInheritedOpenCell_disjoint_topCell
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) :
    letI := S.cwComplex
    ∀ {m : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
      Disjoint
        (realProjectiveSpaceEquatorTransportCellMapAmbient k S j '' Metric.ball 0 1)
        (realProjectiveSpaceSuccTopCellMapOnFunctions k '' Metric.ball 0 1) := by
  letI := S.cwComplex
  intro m j
  refine Set.disjoint_left.2 ?_
  intro y hyInherited hyTop
  have hyEquator : y ∈ realProjectiveSpaceEquatorLocus k := by
    rcases hyInherited with ⟨x, hx, rfl⟩
    exact realProjectiveSpaceEquatorTransportCellMapAmbient_mapsTo_equator k S j hx
  have hyCompl :
      y ∈ ((realProjectiveSpaceEquatorLocus k : Set (RealProjectiveSpace (k + 1)))ᶜ) := by
    rcases hyTop with ⟨x, hx, rfl⟩
    exact (realProjectiveSpaceSuccTopCellMapOnFunctions k).map_source hx
  exact hyCompl hyEquator

/-- Helper for Example 10.1.11: the full successor open-cell family is pairwise disjoint once the
inherited/inherited and inherited/top cases are separated. -/
private theorem realProjectiveSpaceSuccCell_pairwiseDisjoint
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) :
    letI := S.cwComplex
    (Set.univ : Set (Σ m, realProjectiveSpaceSuccCell k S m)).PairwiseDisjoint
      (fun mj ↦ realProjectiveSpaceSuccCellMap k S mj.2 '' Metric.ball 0 1) := by
  letI := S.cwComplex
  intro a _ b _ hab
  rcases a with ⟨ma, a⟩
  rcases b with ⟨mb, b⟩
  cases a with
  | inl ja =>
      cases b with
      | inl jb =>
          -- Two inherited cells reduce to the predecessor pairwise-disjointness statement.
          have habInherited :
              (Sigma.mk ma ja :
                Σ m, Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m) ≠
                Sigma.mk mb jb := by
            intro hEq
            apply hab
            cases hEq
            rfl
          simpa [realProjectiveSpaceSuccCellMap] using
            (realProjectiveSpaceSuccInheritedOpenCell_pairwiseDisjoint k S
              (show Sigma.mk ma ja ∈
                (Set.univ : Set (Σ m,
                  Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m)) by simp)
              (show Sigma.mk mb jb ∈
                (Set.univ : Set (Σ m,
                  Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m)) by simp)
              habInherited)
      | inr hb =>
          -- The mixed branch is exactly inherited/top disjointness.
          rcases hb with ⟨hb⟩
          subst hb
          show Disjoint
            (realProjectiveSpaceSuccCellMap k S (Sum.inl ja) '' Metric.ball 0 1)
            (realProjectiveSpaceSuccCellMap k S (Sum.inr ⟨rfl⟩) '' Metric.ball 0 1)
          simpa [realProjectiveSpaceSuccCellMap] using
            realProjectiveSpaceSuccInheritedOpenCell_disjoint_topCell k S ja
  | inr ha =>
      cases b with
      | inl jb =>
          -- Symmetry handles the top/inherited branch.
          rcases ha with ⟨ha⟩
          subst ha
          show Disjoint
            (realProjectiveSpaceSuccCellMap k S (Sum.inr ⟨rfl⟩) '' Metric.ball 0 1)
            (realProjectiveSpaceSuccCellMap k S (Sum.inl jb) '' Metric.ball 0 1)
          simpa [realProjectiveSpaceSuccCellMap] using
            (realProjectiveSpaceSuccInheritedOpenCell_disjoint_topCell k S jb).symm
      | inr hb =>
          -- There is only one top summand, so distinct sigma-indices cannot both be top cells.
          rcases ha with ⟨ha⟩
          rcases hb with ⟨hb⟩
          subst ha
          subst hb
          exact False.elim (hab rfl)

/-- Helper for Example 10.1.11: each top-cell boundary point already lands in the
lower-dimensional successor closed cells, since the boundary is the equatorial copy of `RP^k`. -/
private theorem realProjectiveSpaceSuccTopCellBoundary_memLowerClosedCells
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) (x : TopCat.sphere k) :
    letI := S.cwComplex
    realProjectiveSpaceSuccTopCellFun k x.down.1 ∈
      (⋃ (m : ℕ) (_ : m < k + 1) (j : realProjectiveSpaceSuccCell k S m),
        realProjectiveSpaceSuccCellMap k S j '' Metric.closedBall 0 1) := by
  letI := S.cwComplex
  have hyEquator :
      realProjectiveSpaceSuccTopCellFun k x.down.1 ∈ realProjectiveSpaceEquatorLocus k := by
    -- On the boundary, the top chart collapses to the standard equatorial inclusion.
    let x0 : TopCat.sphere k := ULift.up x.down
    let hboundary := realProjectiveSpaceSuccTopCellFun_boundary_eq k x0
    exact hboundary.symm ▸
      realProjectiveSpaceSuccInclusion_mem_equator k (sphereToRealProjectiveSpace k x0)
  have hyInherited :
      realProjectiveSpaceSuccTopCellFun k x.down.1 ∈
        (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
          realProjectiveSpaceEquatorTransportCellMapAmbient k S j '' Metric.closedBall 0 1) := by
    -- Replace the inherited closed-cell union by the equator description.
    rw [realProjectiveSpaceSuccInheritedClosedCells_eq_equator k S]
    exact hyEquator
  rcases Set.mem_iUnion.1 hyInherited with ⟨m, hyInherited⟩
  rcases Set.mem_iUnion.1 hyInherited with ⟨j, hyInherited⟩
  have hm_lt : m < k + 1 := by
    by_contra hm_ge
    have hm_ge' : k + 1 ≤ m := Nat.le_of_not_gt hm_ge
    have hm_gt : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hm_ge'
    exact (S.isEmpty_cell_of_lt m hm_gt).false j
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hm_lt, Set.mem_iUnion.2 ⟨Sum.inl j, ?_⟩⟩⟩
  simpa [realProjectiveSpaceSuccCellMap] using hyInherited

/-- Helper for Example 10.1.11: the successor cell family satisfies the `CWComplex.mkFinite`
boundary condition once inherited cells are transported into the equator and the top cell uses the
rigid boundary homeomorphism. -/
private theorem realProjectiveSpaceSuccCell_mapsTo
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) :
    letI := S.cwComplex
    ∀ {m : ℕ} (j : realProjectiveSpaceSuccCell k S m),
      Set.MapsTo
        (realProjectiveSpaceSuccCellMap k S j)
        (Metric.sphere 0 1)
        (⋃ (l : ℕ) (_ : l < m) (i : realProjectiveSpaceSuccCell k S l),
          realProjectiveSpaceSuccCellMap k S i '' Metric.closedBall 0 1) := by
  letI := S.cwComplex
  intro m j
  cases j with
  | inl j =>
      intro x hx
      -- Reindex the predecessor boundary witness into the inherited branch of the successor
      -- family, then transport the resulting equality through the equator homeomorphism.
      rcases S.cwComplex.mapsTo m j with ⟨I, hI⟩
      have hOld :
          S.cwComplex.map m j x ∈
            (⋃ (m' : ℕ) (_ : m' < m)
              (j' : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m'),
              S.cwComplex.map m' j' '' Metric.closedBall 0 1) := by
        have hOldFinite :
            S.cwComplex.map m j x ∈
              (⋃ (m' : ℕ) (_ : m' < m) (j' ∈ I m'),
                S.cwComplex.map m' j' '' Metric.closedBall 0 1) :=
          hI hx
        rcases Set.mem_iUnion.1 hOldFinite with ⟨m', hOldFinite⟩
        rcases Set.mem_iUnion.1 hOldFinite with ⟨hm', hOldFinite⟩
        rcases Set.mem_iUnion.1 hOldFinite with ⟨j', hOldFinite⟩
        rcases Set.mem_iUnion.1 hOldFinite with ⟨_, hOldFinite⟩
        exact Set.mem_iUnion.2
          ⟨m', Set.mem_iUnion.2 ⟨hm', Set.mem_iUnion.2 ⟨j', hOldFinite⟩⟩⟩
      rcases Set.mem_iUnion.1 hOld with ⟨m', hOld⟩
      rcases Set.mem_iUnion.1 hOld with ⟨hm', hOld⟩
      rcases Set.mem_iUnion.1 hOld with ⟨j', hOld⟩
      rcases hOld with ⟨u, hu, huEq⟩
      refine Set.mem_iUnion.2
        ⟨m', Set.mem_iUnion.2 ⟨hm', Set.mem_iUnion.2 ⟨Sum.inl j', ?_⟩⟩⟩
      refine ⟨u, hu, ?_⟩
      -- Compare the ambientized inherited cells by pushing the predecessor equality through the
      -- fixed equator homeomorphism once.
      simpa [realProjectiveSpaceEquatorTransportCellMapAmbient_apply,
        realProjectiveSpaceEquatorTransportCellMap_apply] using
        congrArg
          (fun y ↦
            (((realProjectiveSpaceEquatorLocusHomeomorph k).symm y :
                realProjectiveSpaceEquatorLocus k) : RealProjectiveSpace (k + 1)))
          huEq
  | inr h =>
      cases h with
      | up hm =>
          subst hm
          intro x hx
          let xSphere : ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
            (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k).symm ⟨x, hx⟩
          have hxDef :
              (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k xSphere).1 = x := by
            simpa [xSphere] using
              (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k).apply_symm_apply ⟨x, hx⟩
          have hBoundary :
              realProjectiveSpaceSuccTopCellMapOnFunctions k x =
                realProjectiveSpaceSuccTopCellFun k xSphere.down.1 := by
            calc
              realProjectiveSpaceSuccTopCellMapOnFunctions k x =
                  realProjectiveSpaceSuccTopCellMapOnFunctions k
                    (realProjectiveSpaceSuccTopCellBoundaryHomeomorph k xSphere).1 := by
                      rw [hxDef.symm]
              _ = realProjectiveSpaceSuccTopCellFun k xSphere.down.1 :=
                  realProjectiveSpaceSuccTopCellMapOnFunctions_boundary_eq_raw k xSphere
          have hLower :
              realProjectiveSpaceSuccTopCellFun k xSphere.down.1 ∈
                (⋃ (l : ℕ) (_ : l < k + 1) (i : realProjectiveSpaceSuccCell k S l),
                  realProjectiveSpaceSuccCellMap k S i '' Metric.closedBall 0 1) := by
            exact realProjectiveSpaceSuccTopCellBoundary_memLowerClosedCells k S xSphere
          -- Once the boundary point is rewritten through the chosen sphere identification, the
          -- explicit equator-landing theorem finishes the `mapsTo` clause.
          exact hBoundary ▸ hLower

/-- Helper for Example 10.1.11: the successor closed-cell family covers all of `RP^(k + 1)` by
splitting into the equatorial inherited part and the complementary top cell. -/
private theorem realProjectiveSpaceSuccCellMap_union
    (k : ℕ) (S : RealProjectiveSpaceStandardCWStructure k) :
    letI := S.cwComplex
    (⋃ (m : ℕ) (j : realProjectiveSpaceSuccCell k S m),
      realProjectiveSpaceSuccCellMap k S j '' Metric.closedBall 0 1) =
      (Set.univ : Set (RealProjectiveSpace (k + 1))) := by
  letI := S.cwComplex
  ext y
  constructor
  · intro _
    simp
  · intro _
    by_cases hyEquator : y ∈ realProjectiveSpaceEquatorLocus k
    · have hyInherited :
        y ∈
          (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (RealProjectiveSpace k)) m),
            realProjectiveSpaceEquatorTransportCellMapAmbient k S j '' Metric.closedBall 0 1) := by
          rw [realProjectiveSpaceSuccInheritedClosedCells_eq_equator k S]
          exact hyEquator
      rcases Set.mem_iUnion.1 hyInherited with ⟨m, hyInherited⟩
      rcases Set.mem_iUnion.1 hyInherited with ⟨j, hyInherited⟩
      refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Sum.inl j, ?_⟩⟩
      simpa [realProjectiveSpaceSuccCellMap] using hyInherited
    · have hyTop :
        y ∈ realProjectiveSpaceSuccTopCellFun k '' Metric.ball 0 1 := by
          rw [realProjectiveSpaceSuccTopCellFun_image_ball_eq_compl]
          simpa using hyEquator
      rcases hyTop with ⟨z, hz, rfl⟩
      let e := realProjectiveSpaceSuccFunctionBallToEuclideanBall k
      have hzTarget : z ∈ e.target := by
        simpa [e, realProjectiveSpaceSuccFunctionBallToEuclideanBall_target] using hz
      have hxSource : e.symm z ∈ e.source := e.map_target hzTarget
      have hxClosed :
          e.symm z ∈ Metric.closedBall (0 : Fin (k + 1) → ℝ) 1 := by
        have hxBall : e.symm z ∈ Metric.ball (0 : Fin (k + 1) → ℝ) 1 := by
          simpa [e, realProjectiveSpaceSuccFunctionBallToEuclideanBall_source] using hxSource
        exact Metric.ball_subset_closedBall hxBall
      refine Set.mem_iUnion.2 ⟨k + 1, Set.mem_iUnion.2 ⟨Sum.inr ⟨rfl⟩, ?_⟩⟩
      refine ⟨e.symm z, hxClosed, ?_⟩
      -- Convert the complement witness back through the source-ball homeomorphism.
      calc
        realProjectiveSpaceSuccCellMap k S (Sum.inr ⟨rfl⟩) (e.symm z) =
            realProjectiveSpaceSuccTopCellFun k (e (e.symm z)) := by
              simp [realProjectiveSpaceSuccCellMap, realProjectiveSpaceSuccTopCellMapOnFunctions, e]
        _ = realProjectiveSpaceSuccTopCellFun k z := by
              rw [e.right_inv hzTarget]

/-- Helper for Example 10.1.11: a chosen standard CW structure on `RP^k` extends to one on
`RP^(k + 1)`. -/
private theorem realProjectiveSpaceSuccStandardCWStructure {k : ℕ}
    (S : RealProjectiveSpaceStandardCWStructure k) :
    Nonempty (RealProjectiveSpaceStandardCWStructure (k + 1)) :=
  -- TODO: assemble the corrected successor `CWComplex.mkFinite` from the rigid top-cell boundary
  -- data proved above, then transport predecessor skeleta through the equator inclusion to define
  -- the remaining `skeletonHomeomorph` fields and the top attaching-map comparison.
  sorry

/-- Existence companion for the standard CW structure on `RP^n`. -/
theorem realProjectiveSpaceHasStandardCWStructure (n : ℕ) :
    Nonempty (RealProjectiveSpaceStandardCWStructure n) := by
  induction n with
  | zero =>
      -- Start the induction from the explicit one-point CW structure on `RP⁰`.
      exact ⟨realProjectiveSpaceStandardCWStructureZero⟩
  | succ n ih =>
      -- The successor step delegates to the standard cell-attachment constructor.
      obtain ⟨S⟩ := ih
      exact realProjectiveSpaceSuccStandardCWStructure S

/-- For any chosen standard CW structure on `RP^(n + 1)`, the top attaching map agrees with the
standard double cover `sphereToRealProjectiveSpace n`. -/
theorem realProjectiveSpaceStandardAttachingMapIsDoubleCover
    (S : RealProjectiveSpaceStandardCWStructure (n + 1)) :
    S.topAttachingMap rfl = sphereToRealProjectiveSpace n :=
  S.topAttachingMap_eq rfl
