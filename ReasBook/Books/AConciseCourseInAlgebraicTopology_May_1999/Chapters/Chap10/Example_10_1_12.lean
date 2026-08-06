import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ComplexProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_1

noncomputable section

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex` is the canonical owner for
-- cell-by-cell CW structures, while local Chapter 9 precedent already models `CP^n` by the
-- projectivization `ℙ ℂ (Fin (n + 1) → ℂ)`.

/-- The complex unit sphere in `ℂ^(n + 1)`, used as the standard model of `S^(2n + 1)`. -/
abbrev ComplexProjectiveAttachingSphere (n : ℕ) :=
  Metric.sphere (0 : Fin (n + 1) → ℂ) 1

/-- The standard quotient map from the complex unit sphere in `ℂ^(n + 1)` to `CP^n`. -/
def complexProjectiveSpaceAttachingMap (n : ℕ) :
    ComplexProjectiveAttachingSphere n → ComplexProjectiveSpace n :=
  fun z ↦ Projectivization.mk ℂ z.1 <| by
    intro hz
    have hz1 : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    simp [hz] at hz1

/-- Helper for Example 10.1.12: a point on the complex unit sphere is a nonzero vector. -/
private theorem complexProjectiveAttachingSphere_ne_zero (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    z.1 ≠ 0 := by
  -- A zero vector cannot lie on the unit sphere because its norm would be `0`, not `1`.
  intro hz
  have hz1 : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  simp [hz] at hz1

/-- Helper for Example 10.1.12: the standard quotient map is represented by the underlying sphere
vector. -/
private theorem complexProjectiveSpaceAttachingMap_eq_mk (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    complexProjectiveSpaceAttachingMap n z =
      Projectivization.mk ℂ z.1 (complexProjectiveAttachingSphere_ne_zero n z) := by
  -- Both sides are the same projective class of the same nonzero representative.
  simpa [complexProjectiveSpaceAttachingMap]

/-- Example 10.1.12. A chosen standard classical CW structure on `CP^n`, with one `2m`-cell for
each `m ≤ n`, no odd cells and no cells above dimension `2n`, `2m`- and `(2m + 1)`-skeleta
homeomorphic to `CP^m`, and top attaching map `complexProjectiveSpaceAttachingMap (n - 1)`,
which is an `S¹`-bundle for `n ≥ 1`. -/
structure ComplexProjectiveCWStructure (n : ℕ) where
  cwComplex : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n))
  evenCellUnique :
    ∀ m, m ≤ n →
      letI := cwComplex
      Unique (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m))
  oddCellEmpty :
    ∀ m,
      letI := cwComplex
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m + 1))
  highCellEmpty :
    ∀ k, 2 * n < k →
      letI := cwComplex
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) k)
  evenSkeletonHomeomorph :
    ∀ m, m ≤ n →
      letI := cwComplex
      Topology.CWComplex.skeleton
          (Set.univ : Set (ComplexProjectiveSpace n))
          (2 * m : ℕ∞) ≃ₜ
        ComplexProjectiveSpace m
  oddSkeletonHomeomorph :
    ∀ m, m ≤ n →
      letI := cwComplex
      Topology.CWComplex.skeleton
          (Set.univ : Set (ComplexProjectiveSpace n))
          (2 * m + 1 : ℕ∞) ≃ₜ
        ComplexProjectiveSpace m
  topCellBoundaryHomeomorph :
    ∀ _ : 1 ≤ n,
      letI := cwComplex
      ComplexProjectiveAttachingSphere (n - 1) ≃ₜ Metric.sphere (0 : Fin (2 * n) → ℝ) 1
  topCellAttachingMap :
    ∀ _ : 1 ≤ n,
      letI := cwComplex
      ComplexProjectiveAttachingSphere (n - 1) →
        { x : ComplexProjectiveSpace n //
            x ∈
              (Topology.CWComplex.skeleton
                (Set.univ : Set (ComplexProjectiveSpace n))
                (2 * (n - 1) + 1 : ℕ∞) : Set (ComplexProjectiveSpace n)) }
  topCellAttachingMap_spec :
    ∀ hn : 1 ≤ n,
      letI := cwComplex
      let topCell :
          Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * n) :=
        (evenCellUnique n le_rfl).default
      ∀ x : ComplexProjectiveAttachingSphere (n - 1),
        (topCellAttachingMap hn x).1 =
          cwComplex.map (2 * n) topCell (topCellBoundaryHomeomorph hn x).1
  topCellAttachingMap_eq :
    ∀ hn : 1 ≤ n,
      oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1) ∘ topCellAttachingMap hn =
        complexProjectiveSpaceAttachingMap (n - 1)
  topCellAttachingMap_isFiberBundle :
    ∀ hn : 1 ≤ n,
      IsFiberBundleMap Circle
        (oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1) ∘ topCellAttachingMap hn)

namespace ComplexProjectiveCWStructure

/-- A chosen standard CW structure on `CP^n` supplies the underlying classical CW-complex
instance. -/
instance instCWComplex (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) :=
  S.cwComplex

variable {n : ℕ}

/-- The top attaching map of a chosen CW structure on `CP^n`, viewed through the canonical
identification of the odd skeleton with `CP^(n - 1)`. -/
def topAttachingMap (S : ComplexProjectiveCWStructure n) (hn : 1 ≤ n) :
    ComplexProjectiveAttachingSphere (n - 1) → ComplexProjectiveSpace (n - 1) :=
  S.oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1) ∘ S.topCellAttachingMap hn

/-- Viewed back inside the odd skeleton, `topAttachingMap` agrees with the actual top-cell
attaching map of the underlying CW complex. -/
theorem topAttachingMap_spec (S : ComplexProjectiveCWStructure n) (hn : 1 ≤ n)
    (x : ComplexProjectiveAttachingSphere (n - 1)) :
    letI := S.cwComplex
    ((S.oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1)).symm (S.topAttachingMap hn x)).1 =
      S.cwComplex.map (2 * n) ((S.evenCellUnique n le_rfl).default)
        (S.topCellBoundaryHomeomorph hn x).1 := by
  letI := S.cwComplex
  have hsymm :
      (S.oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1)).symm (S.topAttachingMap hn x) =
        S.topCellAttachingMap hn x := by
    simpa [topAttachingMap] using
      (S.oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1)).symm_apply_apply
        (S.topCellAttachingMap hn x)
  calc
    ((S.oddSkeletonHomeomorph (n - 1) (Nat.sub_le n 1)).symm (S.topAttachingMap hn x)).1 =
        (S.topCellAttachingMap hn x).1 := congrArg Subtype.val hsymm
    _ = S.cwComplex.map (2 * n) ((S.evenCellUnique n le_rfl).default)
          (S.topCellBoundaryHomeomorph hn x).1 :=
        S.topCellAttachingMap_spec hn x

/-- For `n ≥ 1`, in a chosen standard classical CW structure on `CP^n` the top attaching map is
`complexProjectiveSpaceAttachingMap (n - 1)`. -/
theorem topAttachingMap_eq (S : ComplexProjectiveCWStructure n) (hn : 1 ≤ n) :
    S.topAttachingMap hn = complexProjectiveSpaceAttachingMap (n - 1) :=
  S.topCellAttachingMap_eq hn

/-- The top attaching map in a chosen standard CW structure on `CP^n` is a fiber bundle with
fiber `S¹`. -/
theorem topAttachingMap_isFiberBundle (S : ComplexProjectiveCWStructure n) (hn : 1 ≤ n) :
    IsFiberBundleMap Circle (S.topAttachingMap hn) := by
  simpa [topAttachingMap] using S.topCellAttachingMap_isFiberBundle hn

/-- A chosen standard CW structure on `CP^n` exposes the Prop-valued clauses from the source,
while the skeletal identifications remain explicit owner data via `S`. -/
theorem spec (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    (∀ m : ℕ,
      m ≤ n →
        Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) =
          1) ∧
    (∀ m : ℕ,
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m + 1))) ∧
    (∀ k : ℕ,
      2 * n < k →
        IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) k)) ∧
    (∀ hn : 1 ≤ n, S.topAttachingMap hn = complexProjectiveSpaceAttachingMap (n - 1)) ∧
    (∀ hn : 1 ≤ n, IsFiberBundleMap Circle (S.topAttachingMap hn)) := by
  letI := S.cwComplex
  refine
    ⟨?_, S.oddCellEmpty, S.highCellEmpty, S.topAttachingMap_eq,
      S.topAttachingMap_isFiberBundle⟩
  intro m hm
  let h := S.evenCellUnique m hm
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun a b ↦ by rw [h.uniq a, h.uniq b]⟩, ⟨h.default⟩⟩

end ComplexProjectiveCWStructure

universe u

/-- Helper for Example 10.1.12: the canonical quotient `ComplexProjectiveAttachingSphere n → CP^n`
is continuous. -/
private theorem complexProjectiveSpaceAttachingMap_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceAttachingMap n) := by
  -- First lift a sphere point to the nonzero-vector subtype underlying projectivization.
  let nonzeroVector : ComplexProjectiveAttachingSphere n → { v : Fin (n + 1) → ℂ // v ≠ 0 } :=
    fun z ↦ ⟨z.1, by
      intro hz
      have hz1 : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
      simp [hz] at hz1⟩
  have hnonzeroVector : Continuous nonzeroVector :=
    Continuous.subtype_mk continuous_subtype_val fun z ↦ (nonzeroVector z).2
  -- Then the projectivization map is just the ambient quotient map on nonzero vectors.
  simpa [complexProjectiveSpaceAttachingMap, Projectivization.mk', nonzeroVector,
    Projectivization.mk'_eq_mk] using
    (continuous_quotient_mk'.comp hnonzeroVector)

/-- Helper for Example 10.1.12: the standard attaching map packaged as a bundled continuous map.
-/
private def complexProjectiveAttachingContinuousMap (n : ℕ) :
    C(ComplexProjectiveAttachingSphere n, ComplexProjectiveSpace n) :=
  ⟨complexProjectiveSpaceAttachingMap n, complexProjectiveSpaceAttachingMap_continuous n⟩

/-- Helper for Example 10.1.12: the one-point cell family has one `0`-cell and no higher cells. -/
private abbrev pointSpaceCell (n : ℕ) :=
  ULift.{u} (PLift (n = 0))

/-- Helper for Example 10.1.12: the unique `0`-cell index in the one-point cell family. -/
private theorem pointSpaceCell_zero_eq (c : pointSpaceCell 0) :
    c = ⟨⟨rfl⟩⟩ := by
  -- The `0`-cell index type is `PLift True`, so every inhabitant is the canonical one.
  cases c with
  | up c =>
      cases c
      rfl

/-- Helper for Example 10.1.12: positive-dimensional cells are absent in the one-point cell
family. -/
private theorem pointSpaceCell_false_of_pos {n : ℕ} (hn : 0 < n) (c : pointSpaceCell n) :
    False :=
  (Nat.ne_of_gt hn) c.down.down

/-- Helper for Example 10.1.12: the one-point cell family has a unique `0`-cell. -/
private abbrev pointSpaceZeroCellUnique : Unique (pointSpaceCell 0) where
  default := ⟨⟨rfl⟩⟩
  uniq := pointSpaceCell_zero_eq

/-- Helper for Example 10.1.12: the distinguished `0`-cell index in the one-point CW model. -/
private abbrev pointSpaceZeroCell : pointSpaceCell 0 :=
  pointSpaceZeroCellUnique.default

/-- Helper for Example 10.1.12: the one-point cell family has no positive-dimensional cells. -/
private abbrev pointSpaceCellIsEmptyOfPos {n : ℕ} (hn : 0 < n) : IsEmpty (pointSpaceCell n) where
  false := pointSpaceCell_false_of_pos hn

/-- Helper for Example 10.1.12: the one-point cell family only has a single total cell index. -/
private theorem pointSpaceCells_subsingleton :
    Subsingleton (Σ n, pointSpaceCell n) := by
  -- Any cell index must lie in degree `0`, and the degree-`0` index is itself unique.
  refine ⟨fun a b ↦ ?_⟩
  rcases a with ⟨na, ⟨⟨ha⟩⟩⟩
  rcases b with ⟨nb, ⟨⟨hb⟩⟩⟩
  subst ha
  subst hb
  rfl

/-- Helper for Example 10.1.12: the unique `0`-cell on a one-point space is the constant
characteristic map. -/
private def pointSpaceCellMap (X : Type*) [TopologicalSpace X] [Unique X] (n : ℕ)
    (c : pointSpaceCell n) : PartialEquiv (Fin n → ℝ) X := by
  -- There is only a `0`-cell; all other degrees are impossible.
  cases n with
  | zero =>
      exact PartialEquiv.single 0 (default : X)
  | succ n =>
      exact False.elim (Nat.succ_ne_zero n c.down.down)

/-- Helper for Example 10.1.12: only degree `0` survives in the one-point cell family. -/
private theorem pointSpaceCell_eventuallyIsEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (pointSpaceCell n) := by
  -- Beyond degree `0`, every cell index is impossible.
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  exact pointSpaceCellIsEmptyOfPos (Nat.succ_le_iff.mp hn)

/-- Helper for Example 10.1.12: each degree of the one-point cell family is finite. -/
private theorem pointSpaceCell_finite (n : ℕ) : Finite (pointSpaceCell n) := by
  exact Finite.of_subsingleton

/-- Helper for Example 10.1.12: the one-point characteristic map has the standard open-ball
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

/-- Helper for Example 10.1.12: the one-point characteristic map is continuous on the closed unit
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

/-- Helper for Example 10.1.12: the inverse of the one-point characteristic map is continuous on
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

/-- Helper for Example 10.1.12: the one-point open cells are pairwise disjoint because there is
only one total cell index. -/
private theorem pointSpaceCell_pairwiseDisjoint (X : Type*) [TopologicalSpace X] [Unique X] :
    (Set.univ : Set (Σ n, pointSpaceCell n)).PairwiseDisjoint
      (fun ni ↦ pointSpaceCellMap X ni.1 ni.2 '' Metric.ball 0 1) := by
  -- Distinct sigma-indices cannot occur in the one-point cell family.
  intro a _ b _ hab
  exact (hab (pointSpaceCells_subsingleton.elim a b)).elim

/-- Helper for Example 10.1.12: the boundary condition for the one-point CW model is vacuous
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

/-- Helper for Example 10.1.12: the closed `0`-cell covers any one-point space. -/
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

/-- Helper for Example 10.1.12: any one-point space carries the obvious CW complex with one
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

/-- Helper for Example 10.1.12: in the one-point CW model, the unique point lies in the closed
`0`-cell. -/
private theorem pointSpace_default_mem_closedCell (X : Type*) [TopologicalSpace X] [Unique X] :
    letI := pointSpaceCWComplex X
    (default : X) ∈
      Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0
        (by
          change pointSpaceCell 0
          exact pointSpaceZeroCell) := by
  letI := pointSpaceCWComplex X
  -- The unique point is the image of the center of the closed `0`-ball.
  refine ⟨0, ?_, ?_⟩
  · simp
  · rfl

/-- Helper for Example 10.1.12: every skeleton of the one-point CW model contains the unique
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
      (C := (Set.univ : Set X))
      0
      (by
        change pointSpaceCell 0
        exact pointSpaceZeroCell)
      (pointSpace_default_mem_closedCell X)
  exact Topology.CWComplex.skeleton_mono (C := (Set.univ : Set X)) (show (0 : ℕ∞) ≤ q by exact bot_le)
    hzero

/-- Helper for Example 10.1.12: a nonempty subtype of a one-point space is again a one-point
space. -/
private noncomputable abbrev uniqueSubtypeOfUnique {X : Type*} [Unique X] {s : Set X}
    (hs : (default : X) ∈ s) : Unique s :=
  { default := ⟨default, hs⟩
    uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _) }

/-- Helper for Example 10.1.12: every skeleton of the one-point CW model is homeomorphic to the
ambient one-point space. -/
private noncomputable def pointSpaceSkeletonHomeomorph (X : Type*) [TopologicalSpace X] [Unique X]
    (q : ℕ∞) :
    letI := pointSpaceCWComplex X
    Topology.CWComplex.skeleton (Set.univ : Set X) q ≃ₜ X :=
  letI := pointSpaceCWComplex X
  letI : Unique (Topology.CWComplex.skeleton (Set.univ : Set X) q) :=
    uniqueSubtypeOfUnique (pointSpace_default_mem_skeleton X q)
  Homeomorph.homeomorphOfUnique _ X

/-- Helper for Example 10.1.12: `CP^0` has a single projective point. -/
private theorem complexProjectiveSpaceZero_subsingleton :
    Subsingleton (ComplexProjectiveSpace 0) := by
  -- Both projective points correspond to one-dimensional subspaces of a one-dimensional vector
  -- space, so each must be the top subspace.
  refine ⟨fun x y ↦ ?_⟩
  apply Projectivization.submodule_injective
  have hfin : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by
    simpa using (LinearEquiv.finrank_eq (LinearEquiv.funUnique (Fin 1) ℂ ℂ))
  have hx : Projectivization.submodule x = (⊤ : Submodule ℂ (Fin 1 → ℂ)) := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Projectivization.finrank_submodule, hfin]
  have hy : Projectivization.submodule y = (⊤ : Submodule ℂ (Fin 1 → ℂ)) := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Projectivization.finrank_submodule, hfin]
  simpa [hx, hy]

/-- Helper for Example 10.1.12: `CP^0` is a one-point space. -/
private noncomputable abbrev complexProjectiveSpaceZero_unique :
    Unique (ComplexProjectiveSpace 0) :=
  letI := complexProjectiveSpaceZero_subsingleton
  { default := complexProjectiveSpaceBasepoint 0
    uniq := fun _ ↦ Subsingleton.elim _ _ }

/-- Helper for Example 10.1.12: the explicit one-point CW complex specialized to `CP^0`. -/
private noncomputable abbrev complexProjectiveSpaceZeroCWComplex :
    Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace 0)) :=
  letI : Unique (ComplexProjectiveSpace 0) := complexProjectiveSpaceZero_unique
  pointSpaceCWComplex (ComplexProjectiveSpace 0)

/-- Helper for Example 10.1.12: the one-point CW model on `CP^0` has a unique even cell in the
only possible degree. -/
private noncomputable abbrev complexProjectiveCWStructureZero_evenCellUnique
    (m : ℕ) (hm : m ≤ 0) :
    letI := complexProjectiveSpaceZeroCWComplex
    Unique (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace 0)) (2 * m)) :=
  match m with
  | 0 => pointSpaceZeroCellUnique
  | k + 1 => False.elim (Nat.not_succ_le_zero k hm)

/-- Helper for Example 10.1.12: the one-point CW model on `CP^0` has no odd-dimensional cells. -/
private noncomputable abbrev complexProjectiveCWStructureZero_oddCellEmpty
    (m : ℕ) :
    letI := complexProjectiveSpaceZeroCWComplex
    IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace 0)) (2 * m + 1)) :=
  pointSpaceCellIsEmptyOfPos (Nat.succ_pos _)

/-- Helper for Example 10.1.12: the one-point CW model on `CP^0` has no positive-dimensional
cells. -/
private noncomputable abbrev complexProjectiveCWStructureZero_highCellEmpty
    (k : ℕ) (hk : 0 < k) :
    letI := complexProjectiveSpaceZeroCWComplex
    IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace 0)) k) :=
  pointSpaceCellIsEmptyOfPos hk

/-- Helper for Example 10.1.12: the even skeleton clause for `CP^0` is the one-point
homeomorphism. -/
private noncomputable def complexProjectiveCWStructureZero_evenSkeletonHomeomorph
    (m : ℕ) (hm : m ≤ 0) :
    letI := complexProjectiveSpaceZeroCWComplex
    Topology.CWComplex.skeleton
        (Set.univ : Set (ComplexProjectiveSpace 0))
        (2 * m : ℕ∞) ≃ₜ
      ComplexProjectiveSpace m :=
  letI : Unique (ComplexProjectiveSpace 0) := complexProjectiveSpaceZero_unique
  match m with
  | 0 => pointSpaceSkeletonHomeomorph (X := ComplexProjectiveSpace 0) (q := (0 : ℕ∞))
  | k + 1 => False.elim (Nat.not_succ_le_zero k hm)

/-- Helper for Example 10.1.12: the odd skeleton clause for `CP^0` is again the one-point
homeomorphism. -/
private noncomputable def complexProjectiveCWStructureZero_oddSkeletonHomeomorph
    (m : ℕ) (hm : m ≤ 0) :
    letI := complexProjectiveSpaceZeroCWComplex
    Topology.CWComplex.skeleton
        (Set.univ : Set (ComplexProjectiveSpace 0))
        (2 * m + 1 : ℕ∞) ≃ₜ
      ComplexProjectiveSpace m :=
  letI : Unique (ComplexProjectiveSpace 0) := complexProjectiveSpaceZero_unique
  match m with
  | 0 => pointSpaceSkeletonHomeomorph (X := ComplexProjectiveSpace 0) (q := (1 : ℕ∞))
  | k + 1 => False.elim (Nat.not_succ_le_zero k hm)

/-- Helper for Example 10.1.12: the base case `CP^0` carries the unique one-point CW structure. -/
private noncomputable def complexProjectiveCWStructureZero :
    ComplexProjectiveCWStructure 0 :=
  letI : Unique (ComplexProjectiveSpace 0) := complexProjectiveSpaceZero_unique
  { cwComplex := complexProjectiveSpaceZeroCWComplex
    evenCellUnique := complexProjectiveCWStructureZero_evenCellUnique
    oddCellEmpty := complexProjectiveCWStructureZero_oddCellEmpty
    highCellEmpty := complexProjectiveCWStructureZero_highCellEmpty
    evenSkeletonHomeomorph := complexProjectiveCWStructureZero_evenSkeletonHomeomorph
    oddSkeletonHomeomorph := complexProjectiveCWStructureZero_oddSkeletonHomeomorph
    topCellBoundaryHomeomorph := fun hn ↦ False.elim (Nat.not_succ_le_zero 0 hn)
    topCellAttachingMap := fun hn ↦ False.elim (Nat.not_succ_le_zero 0 hn)
    topCellAttachingMap_spec := fun hn ↦ False.elim (Nat.not_succ_le_zero 0 hn)
    topCellAttachingMap_eq := fun hn ↦ False.elim (Nat.not_succ_le_zero 0 hn)
    topCellAttachingMap_isFiberBundle := fun hn ↦ False.elim (Nat.not_succ_le_zero 0 hn) }

/-- Helper for Example 10.1.12: the successor-step projective inclusion is induced by the
zero-extension linear map `ℂ^(n + 1) → ℂ^(n + 2)`. -/
private noncomputable def complexProjectiveSpaceSuccLinearMap (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 2) → ℂ) :=
  LinearMap.pi fun i : Fin (n + 2) ↦
    if h : i < n + 1 then LinearMap.proj (Fin.castLT i h) else 0

/-- Helper for Example 10.1.12: the zero-extension linear map agrees with the original vector on
the first `n + 1` coordinates. -/
@[simp]
private theorem complexProjectiveSpaceSuccLinearMap_apply_castSucc (n : ℕ)
    (v : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    complexProjectiveSpaceSuccLinearMap n v i.castSucc = v i := by
  -- The first coordinates are read off by the corresponding coordinate projection.
  have hle : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.is_lt
  simp [complexProjectiveSpaceSuccLinearMap, hle]

/-- Helper for Example 10.1.12: the zero-extension linear map sends the last coordinate to `0`.
-/
@[simp]
private theorem complexProjectiveSpaceSuccLinearMap_apply_last (n : ℕ)
    (v : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccLinearMap n v (Fin.last (n + 1)) = 0 := by
  -- The last coordinate lands in the zero summand of the extension.
  simp [complexProjectiveSpaceSuccLinearMap]

/-- Helper for Example 10.1.12: the zero-extension linear map is the same as appending a zero last
coordinate. -/
@[simp]
private theorem complexProjectiveSpaceSuccLinearMap_eq_snoc (n : ℕ)
    (v : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccLinearMap n v = Fin.snoc v 0 := by
  -- Compare the first `n + 1` coordinates and the final coordinate separately.
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp
  | cast j =>
      simp

/-- Helper for Example 10.1.12: zero-extension is injective on vectors. -/
private theorem complexProjectiveSpaceSuccLinearMap_injective (n : ℕ) :
    Function.Injective (complexProjectiveSpaceSuccLinearMap n) := by
  intro x y hxy
  -- Compare the images on the first `n + 1` coordinates to recover the source vectors.
  ext i
  have hcoord := congrArg (fun f : Fin (n + 2) → ℂ ↦ f i.castSucc) hxy
  simpa using hcoord

/-- Helper for Example 10.1.12: zero-extension preserves nonzeroness of vectors. -/
private theorem complexProjectiveSpaceSuccLinearMap_ne_zero (n : ℕ)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    complexProjectiveSpaceSuccLinearMap n v ≠ 0 := by
  -- An injective linear map can only send `0` to `0`.
  intro hzero
  apply hv
  have hmap : complexProjectiveSpaceSuccLinearMap n v = complexProjectiveSpaceSuccLinearMap n 0 := by
    calc
      complexProjectiveSpaceSuccLinearMap n v = 0 := hzero
      _ = complexProjectiveSpaceSuccLinearMap n 0 := by
        ext i
        cases i using Fin.lastCases with
        | last =>
            simp [complexProjectiveSpaceSuccLinearMap]
        | cast j =>
            simp [complexProjectiveSpaceSuccLinearMap]
  exact complexProjectiveSpaceSuccLinearMap_injective n hmap

/-- Helper for Example 10.1.12: zero-extension induces the standard inclusion `CP^n → CP^(n + 1)`.
-/
private noncomputable abbrev complexProjectiveSpaceSuccInclusion (n : ℕ) :
    ComplexProjectiveSpace n → ComplexProjectiveSpace (n + 1) :=
  Projectivization.map
    (complexProjectiveSpaceSuccLinearMap n)
    (complexProjectiveSpaceSuccLinearMap_injective n)

/-- Helper for Example 10.1.12: the projective zero-extension inclusion is injective. -/
private theorem complexProjectiveSpaceSuccInclusion_injective (n : ℕ) :
    Function.Injective (complexProjectiveSpaceSuccInclusion n) := by
  -- Injectivity is inherited from `Projectivization.map` for an injective linear map.
  simpa [complexProjectiveSpaceSuccInclusion] using
    (Projectivization.map_injective
      (f := complexProjectiveSpaceSuccLinearMap n)
      (hf := complexProjectiveSpaceSuccLinearMap_injective n))

/-- Helper for Example 10.1.12: on representatives, the successor inclusion is exactly
projectivization of zero-extension. -/
@[simp]
private theorem complexProjectiveSpaceSuccInclusion_mk (n : ℕ)
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    complexProjectiveSpaceSuccInclusion n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ
        (complexProjectiveSpaceSuccLinearMap n v)
        (complexProjectiveSpaceSuccLinearMap_ne_zero n hv) := by
  -- This is the defining behavior of `Projectivization.map` on nonzero representatives.
  simpa [complexProjectiveSpaceSuccInclusion] using
    (Projectivization.map_mk
      (f := complexProjectiveSpaceSuccLinearMap n)
      (hf := complexProjectiveSpaceSuccLinearMap_injective n)
      v
      hv)

/-- Helper for Example 10.1.12: the lower stratum in `CP^(n + 1)` is the projectivization of the
last-coordinate-zero hyperplane. -/
private noncomputable def complexProjectiveSpaceSuccHyperplane (n : ℕ) :
    Submodule ℂ (Fin (n + 2) → ℂ) :=
  LinearMap.ker (LinearMap.proj (Fin.last (n + 1)))

/-- Helper for Example 10.1.12: membership in the successor hyperplane means vanishing last
coordinate. -/
@[simp]
private theorem mem_complexProjectiveSpaceSuccHyperplane (n : ℕ) (v : Fin (n + 2) → ℂ) :
    v ∈ complexProjectiveSpaceSuccHyperplane n ↔ v (Fin.last (n + 1)) = 0 := by
  -- The hyperplane is defined as the kernel of the last-coordinate projection.
  rfl

/-- Helper for Example 10.1.12: zero-extension lands in the last-coordinate-zero hyperplane. -/
private theorem complexProjectiveSpaceSuccLinearMap_mem_hyperplane (n : ℕ)
    (v : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccLinearMap n v ∈ complexProjectiveSpaceSuccHyperplane n := by
  -- The defining last coordinate of a zero-extended vector is `0`.
  simp [complexProjectiveSpaceSuccHyperplane]

/-- Helper for Example 10.1.12: truncate a vector in the successor hyperplane back to its first
`n + 1` coordinates. -/
private noncomputable def complexProjectiveSpaceSuccHyperplaneLift (n : ℕ)
    (v : Fin (n + 2) → ℂ) : Fin (n + 1) → ℂ :=
  fun i ↦ v i.castSucc

/-- Helper for Example 10.1.12: truncating a hyperplane vector and then zero-extending recovers
the original vector. -/
private theorem complexProjectiveSpaceSuccLinearMap_lift_eq (n : ℕ)
    {v : Fin (n + 2) → ℂ} (hv : v ∈ complexProjectiveSpaceSuccHyperplane n) :
    complexProjectiveSpaceSuccLinearMap n (complexProjectiveSpaceSuccHyperplaneLift n v) = v := by
  -- Compare the first `n + 1` coordinates and the last coordinate separately.
  ext i
  cases i using Fin.lastCases with
  | last =>
      simpa [complexProjectiveSpaceSuccHyperplane,
        complexProjectiveSpaceSuccHyperplaneLift] using hv.symm
  | cast j =>
      simp [complexProjectiveSpaceSuccHyperplaneLift]

/-- Helper for Example 10.1.12: a nonzero vector in the successor hyperplane has nonzero
truncation to the first `n + 1` coordinates. -/
private theorem complexProjectiveSpaceSuccHyperplaneLift_ne_zero (n : ℕ)
    {v : Fin (n + 2) → ℂ} (hv : v ∈ complexProjectiveSpaceSuccHyperplane n) (hvnz : v ≠ 0) :
    complexProjectiveSpaceSuccHyperplaneLift n v ≠ 0 := by
  -- Otherwise zero-extension would recover the zero vector, contradicting `v ≠ 0`.
  intro hlift
  apply hvnz
  calc
    v = complexProjectiveSpaceSuccLinearMap n (complexProjectiveSpaceSuccHyperplaneLift n v) :=
      (complexProjectiveSpaceSuccLinearMap_lift_eq n hv).symm
    _ = 0 := by
      ext i
      cases i using Fin.lastCases with
      | last =>
          simp [complexProjectiveSpaceSuccLinearMap_eq_snoc, hlift]
      | cast j =>
          simp [complexProjectiveSpaceSuccLinearMap_eq_snoc, hlift]

/-- Helper for Example 10.1.12: the successor inclusion lands in the canonical hyperplane copy
of `CP^n`. -/
private theorem complexProjectiveSpaceSuccInclusion_mem_hyperplaneProjectivization (n : ℕ)
    (x : ComplexProjectiveSpace n) :
    complexProjectiveSpaceSuccInclusion n x ∈
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- Unfold the projective point to a representative and use the vector-level hyperplane lemma.
  induction x using Projectivization.ind with
  | h v hv =>
      rw [complexProjectiveSpaceSuccInclusion_mk]
      exact (Submodule.mk_mem_projectivization_iff
        (complexProjectiveSpaceSuccHyperplane n)
        (complexProjectiveSpaceSuccLinearMap_ne_zero n hv)).2
        (complexProjectiveSpaceSuccLinearMap_mem_hyperplane n v)

/-- Helper for Example 10.1.12: every projective point in the canonical hyperplane copy comes
from the successor inclusion `CP^n → CP^(n + 1)`. -/
private theorem mem_range_complexProjectiveSpaceSuccInclusion_of_mem_hyperplaneProjectivization
    (n : ℕ) {x : ComplexProjectiveSpace (n + 1)}
    (hx : x ∈ (complexProjectiveSpaceSuccHyperplane n).projectivization) :
    x ∈ Set.range (complexProjectiveSpaceSuccInclusion n) := by
  -- Choose a representative in the hyperplane and truncate its first `n + 1` coordinates.
  induction x using Projectivization.ind with
  | h v hv =>
      rw [(Submodule.mk_mem_projectivization_iff
        (complexProjectiveSpaceSuccHyperplane n)
        hv)] at hx
      let w : Fin (n + 1) → ℂ := complexProjectiveSpaceSuccHyperplaneLift n v
      have hw : w ≠ 0 :=
        complexProjectiveSpaceSuccHyperplaneLift_ne_zero n hx hv
      refine ⟨Projectivization.mk ℂ w hw, ?_⟩
      calc
        complexProjectiveSpaceSuccInclusion n (Projectivization.mk ℂ w hw)
            = Projectivization.mk ℂ
                (complexProjectiveSpaceSuccLinearMap n w)
                (complexProjectiveSpaceSuccLinearMap_ne_zero n hw) :=
          complexProjectiveSpaceSuccInclusion_mk n w hw
        _ = Projectivization.mk ℂ v hv := by
          simp [w, complexProjectiveSpaceSuccLinearMap_lift_eq n hx]

/-- Helper for Example 10.1.12: the range of the successor inclusion is exactly the canonical
hyperplane projectivization in `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccInclusion_range_eq_hyperplaneProjectivization (n : ℕ) :
    Set.range (complexProjectiveSpaceSuccInclusion n) =
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- The two inclusions are the direct image statement and its converse.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact complexProjectiveSpaceSuccInclusion_mem_hyperplaneProjectivization n y
  · exact
      mem_range_complexProjectiveSpaceSuccInclusion_of_mem_hyperplaneProjectivization n

/-- Helper for Example 10.1.12: projectivization carries the quotient topology induced from the
nonzero-vector subtype. -/
private abbrev projectivizationTopologicalSpace (V : Type*)
    [TopologicalSpace V] [AddCommGroup V] [Module ℂ V] :
    TopologicalSpace (Projectivization ℂ V) :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℂ V)))

/-- Helper for Example 10.1.12: a continuous linear equivalence induces a homeomorphism of
projectivizations. -/
private noncomputable def projectivizationHomeomorphOfContinuousLinearEquiv
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (e : V ≃L[ℂ] W) :
    letI := projectivizationTopologicalSpace V
    letI := projectivizationTopologicalSpace W
    Projectivization ℂ V ≃ₜ Projectivization ℂ W := by
  letI := projectivizationTopologicalSpace V
  letI := projectivizationTopologicalSpace W
  refine
    { toEquiv :=
        { toFun := Projectivization.map (e : V →ₗ[ℂ] W) e.injective
          invFun := Projectivization.map (e.symm : W →ₗ[ℂ] V) e.symm.injective
          left_inv := ?_
          right_inv := ?_ 
        }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro x
    -- Compose the two induced maps and simplify to the identity projectivization map.
    calc
      Projectivization.map (e.symm : W →ₗ[ℂ] V) e.symm.injective
          (Projectivization.map (e : V →ₗ[ℂ] W) e.injective x) =
        Projectivization.map
          ((e.symm : W →ₗ[ℂ] V).comp (e : V →ₗ[ℂ] W))
          (e.symm.injective.comp e.injective) x := by
            simpa [Function.comp] using
              (congrFun
                (Projectivization.map_comp
                  (f := (e : V →ₗ[ℂ] W))
                  (hf := e.injective)
                  (g := (e.symm : W →ₗ[ℂ] V))
                  (hg := e.symm.injective)
                  (hgf := e.symm.injective.comp e.injective))
                x).symm
      _ = Projectivization.map (LinearMap.id : V →ₗ[ℂ] V)
            (LinearEquiv.refl ℂ V).injective x := by
            congr 1
            ext v
            exact e.left_inv v
      _ = x := by
            simpa using congrFun (Projectivization.map_id (K := ℂ) (V := V)) x
  · intro x
    -- The opposite composite reduces to the identity by the same projectivization API.
    calc
      Projectivization.map (e : V →ₗ[ℂ] W) e.injective
          (Projectivization.map (e.symm : W →ₗ[ℂ] V) e.symm.injective x) =
        Projectivization.map
          ((e : V →ₗ[ℂ] W).comp (e.symm : W →ₗ[ℂ] V))
          (e.injective.comp e.symm.injective) x := by
            simpa [Function.comp] using
              (congrFun
                (Projectivization.map_comp
                  (f := (e.symm : W →ₗ[ℂ] V))
                  (hf := e.symm.injective)
                  (g := (e : V →ₗ[ℂ] W))
                  (hg := e.injective)
                  (hgf := e.injective.comp e.symm.injective))
                x).symm
      _ = Projectivization.map (LinearMap.id : W →ₗ[ℂ] W)
            (LinearEquiv.refl ℂ W).injective x := by
            congr 1
            ext v
            exact e.right_inv v
      _ = x := by
            simpa using congrFun (Projectivization.map_id (K := ℂ) (V := W)) x
  · let nonzeroMap : { v : V // v ≠ 0 } → { w : W // w ≠ 0 } :=
      fun v ↦ ⟨e v, fun hzero ↦ v.2 (e.injective (by simpa using hzero))⟩
    have hnonzeroMap : Continuous nonzeroMap := by
      -- The induced map on nonzero representatives is just the continuous linear equivalence.
      exact
        Continuous.subtype_mk
          (e.continuous.comp continuous_subtype_val)
          (fun v ↦ (nonzeroMap v).2)
    -- The quotient topology descends continuity of the nonzero-representative map.
    simpa [Projectivization.map, nonzeroMap] using
      (Continuous.quotient_map'
        (s := projectivizationSetoid ℂ V)
        (t := projectivizationSetoid ℂ W)
        hnonzeroMap
        (by
          rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
          refine ⟨a, ?_⟩
          dsimp at ha ⊢
          simpa [Units.smul_def] using congrArg e ha))
  · let nonzeroMap : { w : W // w ≠ 0 } → { v : V // v ≠ 0 } :=
      fun w ↦ ⟨e.symm w, fun hzero ↦ w.2 (e.symm.injective (by simpa using hzero))⟩
    have hnonzeroMap : Continuous nonzeroMap := by
      -- Apply the same quotient-continuity argument to the inverse linear equivalence.
      exact
        Continuous.subtype_mk
          (e.symm.continuous.comp continuous_subtype_val)
          (fun w ↦ (nonzeroMap w).2)
    simpa [Projectivization.map, nonzeroMap] using
      (Continuous.quotient_map'
        (s := projectivizationSetoid ℂ W)
        (t := projectivizationSetoid ℂ V)
        hnonzeroMap
        (by
          rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
          refine ⟨a, ?_⟩
          dsimp at ha ⊢
          simpa [Units.smul_def] using congrArg e.symm ha))

/-- Helper for Example 10.1.12: zero-extension identifies `ℂ^(n + 1)` linearly with the
last-coordinate-zero hyperplane in `ℂ^(n + 2)`. -/
private noncomputable def complexProjectiveSpaceSuccHyperplaneLinearEquiv (n : ℕ) :
    (Fin (n + 1) → ℂ) ≃ₗ[ℂ] complexProjectiveSpaceSuccHyperplane n where
  toFun := fun v ↦
    ⟨complexProjectiveSpaceSuccLinearMap n v,
      complexProjectiveSpaceSuccLinearMap_mem_hyperplane n v⟩
  invFun := fun v ↦ complexProjectiveSpaceSuccHyperplaneLift n v.1
  left_inv := by
    intro v
    -- Truncating the zero-extended vector recovers the original coordinates.
    ext i
    simp [complexProjectiveSpaceSuccHyperplaneLift]
  right_inv := by
    intro v
    -- A hyperplane vector is recovered by truncation followed by zero-extension.
    apply Subtype.ext
    exact complexProjectiveSpaceSuccLinearMap_lift_eq n v.2
  map_add' := by
    intro v w
    -- The zero-extension map is linear coordinatewise.
    apply Subtype.ext
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [complexProjectiveSpaceSuccLinearMap]
    | cast j =>
        simp [complexProjectiveSpaceSuccLinearMap]
  map_smul' := by
    intro c v
    -- Scalar multiplication is preserved on each coordinate of the zero-extension.
    apply Subtype.ext
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [complexProjectiveSpaceSuccLinearMap]
    | cast j =>
        simp [complexProjectiveSpaceSuccLinearMap]

/-- Helper for Example 10.1.12: the explicit zero-extension map to the successor hyperplane is
continuous. -/
private theorem complexProjectiveSpaceSuccHyperplaneLinearEquiv_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccHyperplaneLinearEquiv n) := by
  -- Each coordinate of the zero-extension is either a source coordinate or the constant zero map.
  refine Continuous.subtype_mk ?_ fun v ↦
    (complexProjectiveSpaceSuccHyperplaneLinearEquiv n v).2
  refine continuous_pi fun i ↦ ?_
  cases i using Fin.lastCases with
  | last =>
      simpa [complexProjectiveSpaceSuccHyperplaneLinearEquiv]
        using (continuous_const : Continuous fun _ : Fin (n + 1) → ℂ ↦ (0 : ℂ))
  | cast j =>
      simpa [complexProjectiveSpaceSuccHyperplaneLinearEquiv]
        using (continuous_apply j)

/-- Helper for Example 10.1.12: truncation from the successor hyperplane to the first `n + 1`
coordinates is continuous. -/
private theorem complexProjectiveSpaceSuccHyperplaneLinearEquiv_symm_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccHyperplaneLinearEquiv n).symm := by
  -- The inverse only reads the first `n + 1` coordinates of a hyperplane vector.
  refine continuous_pi fun i ↦ ?_
  exact (continuous_apply i.castSucc).comp continuous_subtype_val

/-- Helper for Example 10.1.12: the explicit hyperplane linear equivalence is automatically
continuous in finite dimensions. -/
private noncomputable def complexProjectiveSpaceSuccHyperplaneContinuousLinearEquiv (n : ℕ) :
    (Fin (n + 1) → ℂ) ≃L[ℂ] complexProjectiveSpaceSuccHyperplane n where
  toLinearEquiv := complexProjectiveSpaceSuccHyperplaneLinearEquiv n
  continuous_toFun := by
    -- The forward map is the explicit coordinatewise zero-extension.
    exact complexProjectiveSpaceSuccHyperplaneLinearEquiv_continuous n
  continuous_invFun := by
    -- The inverse is the explicit truncation to the first `n + 1` coordinates.
    exact complexProjectiveSpaceSuccHyperplaneLinearEquiv_symm_continuous n

/-- Helper for Example 10.1.12: `CP^n` is homeomorphic to the projectivization of the canonical
hyperplane in `CP^(n + 1)`. -/
private noncomputable def complexProjectiveSpaceSuccHyperplaneHomeomorph (n : ℕ) :
    letI := projectivizationTopologicalSpace (complexProjectiveSpaceSuccHyperplane n)
    ComplexProjectiveSpace n ≃ₜ Projectivization ℂ (complexProjectiveSpaceSuccHyperplane n) := by
  letI := projectivizationTopologicalSpace (complexProjectiveSpaceSuccHyperplane n)
  -- First transport projective lines along the explicit hyperplane linear equivalence.
  exact
    projectivizationHomeomorphOfContinuousLinearEquiv
      (complexProjectiveSpaceSuccHyperplaneContinuousLinearEquiv n)

/-- Helper for Example 10.1.12: the sphere quotient `ComplexProjectiveAttachingSphere n → CP^n`
is surjective. -/
private theorem complexProjectiveSpaceAttachingMap_surjective (n : ℕ) :
    Function.Surjective (complexProjectiveSpaceAttachingMap n) := by
  intro x
  let v : Fin (n + 1) → ℂ := Projectivization.rep x
  have hv : v ≠ 0 := Projectivization.rep_nonzero x
  have hv_norm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hv_norm_ne' : ((‖v‖ : ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast hv_norm_ne
  let z : Fin (n + 1) → ℂ := ((‖v‖ : ℂ)⁻¹) • v
  have hz : z ≠ 0 := by
    -- Normalizing by a nonzero scalar preserves nonzeroness.
    dsimp [z]
    exact smul_ne_zero (inv_ne_zero hv_norm_ne') hv
  have hz_norm : ‖z‖ = 1 := by
    -- The chosen normalization scales the representative onto the unit sphere.
    dsimp [z]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v)]
    field_simp [hv_norm_ne]
  refine ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz_norm⟩, ?_⟩
  -- Projectivization is invariant under nonzero complex rescaling.
  calc
    complexProjectiveSpaceAttachingMap n ⟨z, mem_sphere_zero_iff_norm.mpr hz_norm⟩ =
        Projectivization.mk ℂ z hz := rfl
    _ = Projectivization.mk ℂ v hv := by
        apply (Projectivization.mk_eq_mk_iff' ℂ z v hz hv).2
        refine ⟨((‖v‖ : ℂ)⁻¹), ?_⟩
        dsimp [z]
    _ = x := Projectivization.mk_rep x

/-- Helper for Example 10.1.12: `CP^n` is compact as a quotient of the unit sphere in `ℂ^(n + 1)`.
-/
private theorem complexProjectiveSpace_compactSpace (n : ℕ) :
    CompactSpace (ComplexProjectiveSpace n) := by
  letI : CompactSpace (ComplexProjectiveAttachingSphere n) := inferInstance
  -- The quotient map from the compact unit sphere has full range.
  have hrange : Set.range (complexProjectiveSpaceAttachingMap n) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases complexProjectiveSpaceAttachingMap_surjective n x with ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have huniv : IsCompact (Set.univ : Set (ComplexProjectiveSpace n)) := by
    simpa [hrange] using isCompact_range (complexProjectiveSpaceAttachingMap_continuous n)
  exact isCompact_univ_iff.mp huniv

/-- Helper for Example 10.1.12: functions with values in a product split continuously into a
product of function spaces. -/
private noncomputable def arrowProdContinuousLinearEquivProdArrow
    (α : Type*) (β γ : α → Type*)
    [∀ a, TopologicalSpace (β a)] [∀ a, AddCommMonoid (β a)] [∀ a, Module ℝ (β a)]
    [∀ a, TopologicalSpace (γ a)] [∀ a, AddCommMonoid (γ a)] [∀ a, Module ℝ (γ a)] :
    ((a : α) → β a × γ a) ≃L[ℝ] ((a : α) → β a) × ((a : α) → γ a) where
  toLinearEquiv :=
    { toFun := Equiv.arrowProdEquivProdArrow α β γ
      invFun := (Equiv.arrowProdEquivProdArrow α β γ).symm
      left_inv := (Equiv.arrowProdEquivProdArrow α β γ).left_inv
      right_inv := (Equiv.arrowProdEquivProdArrow α β γ).right_inv
      map_add' := fun f g ↦ rfl
      map_smul' := fun c f ↦ rfl }
  continuous_toFun := by
    -- Both component function families are obtained by reading the corresponding product coordinate.
    exact
      (continuous_pi fun a ↦ (continuous_apply a).fst).prodMk
        (continuous_pi fun a ↦ (continuous_apply a).snd)
  continuous_invFun := by
    -- Reassemble a pair of function families coordinatewise into a product-valued family.
    exact
      continuous_pi fun a ↦
        ((continuous_apply a).comp continuous_fst).prodMk
          ((continuous_apply a).comp continuous_snd)

/-- Helper for Example 10.1.12: `ℂ^(n + 1)` is canonically homeomorphic to `ℝ^(2n + 2)` by
splitting each complex coordinate into real and imaginary parts and then appending the two real
blocks. -/
private noncomputable def complexCoordinateContinuousLinearEquiv (n : ℕ) :
    (Fin (n + 1) → ℂ) ≃L[ℝ] (Fin (2 * (n + 1)) → ℝ) := by
  let complexToPairs :
      (Fin (n + 1) → ℂ) ≃L[ℝ] (Fin (n + 1) → ℝ × ℝ) :=
    ContinuousLinearEquiv.piCongrRight fun _ ↦ Complex.equivRealProdCLM
  let pairsToBlocks :
      (Fin (n + 1) → ℝ × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) :=
    arrowProdContinuousLinearEquivProdArrow
      (α := Fin (n + 1))
      (β := fun _ ↦ ℝ)
      (γ := fun _ ↦ ℝ)
  let blocksToReal :
      ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) ≃L[ℝ] (Fin ((n + 1) + (n + 1)) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (n + 1)) (Fin (n + 1))
        (fun _ ↦ ℝ)).symm.trans
      (ContinuousLinearEquiv.piCongrLeft ℝ
        (fun _ : Fin ((n + 1) + (n + 1)) ↦ ℝ) finSumFinEquiv)
  let reindexDouble :
      (Fin ((n + 1) + (n + 1)) → ℝ) ≃L[ℝ] (Fin (2 * (n + 1)) → ℝ) :=
    (ContinuousLinearEquiv.piCongrLeft ℝ
      (fun _ : Fin ((n + 1) + (n + 1)) ↦ ℝ)
      (finCongr (two_mul (n + 1)))).symm
  -- This is the stable ambient coordinate bridge needed before any boundary normalization.
  exact complexToPairs.trans <| pairsToBlocks.trans <| blocksToReal.trans reindexDouble

/-- Helper for Example 10.1.12: the ambient complex-to-real coordinate bridge is a homeomorphism.
-/
private noncomputable abbrev complexCoordinateHomeomorph (n : ℕ) :
    (Fin (n + 1) → ℂ) ≃ₜ (Fin (2 * (n + 1)) → ℝ) :=
  (complexCoordinateContinuousLinearEquiv n).toHomeomorph

/-- Helper for Example 10.1.12: the ambient complex-to-real coordinate bridge preserves
nonzeroness. -/
private theorem complexCoordinateContinuousLinearEquiv_ne_zero_iff (n : ℕ)
    {z : Fin (n + 1) → ℂ} :
    complexCoordinateContinuousLinearEquiv n z ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro hz hzero
    apply hz
    simpa [hzero]
  · intro hz hzReal
    apply hz
    exact (complexCoordinateContinuousLinearEquiv n).injective (by simpa using hzReal)

/-- Helper for Example 10.1.12: the inverse complex-to-real coordinate bridge also preserves
nonzeroness. -/
private theorem complexCoordinateContinuousLinearEquiv_symm_ne_zero_iff (n : ℕ)
    {x : Fin (2 * (n + 1)) → ℝ} :
    (complexCoordinateContinuousLinearEquiv n).symm x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hx hx0
    apply hx
    simpa [hx0] using
      (complexCoordinateContinuousLinearEquiv n).left_inv x
  · intro hx hx0
    apply hx
    exact by
      simpa using congrArg (complexCoordinateContinuousLinearEquiv n) hx0

/-- Helper for Example 10.1.12: normalizing a nonzero vector lands on the unit sphere. -/
private theorem normalize_mem_unitSphere {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : V} (hv : v ≠ 0) :
    NormedSpace.normalize v ∈ Metric.sphere (0 : V) 1 := by
  -- Turn the claim into the norm-one characterization of the unit sphere.
  simpa [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv

/-- Helper for Example 10.1.12: radial normalization of the real coordinate image of the complex
attaching sphere lands on the real unit sphere. -/
private def complexCoordinateUnitSphereMap (n : ℕ) :
    ComplexProjectiveAttachingSphere n → Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 :=
  fun z ↦
    ⟨NormedSpace.normalize (complexCoordinateContinuousLinearEquiv n z.1),
      normalize_mem_unitSphere
        ((complexCoordinateContinuousLinearEquiv_ne_zero_iff n).2
          (complexProjectiveAttachingSphere_ne_zero n z))⟩

/-- Helper for Example 10.1.12: radial normalization of the inverse real coordinate image of the
real unit sphere lands back on the complex unit sphere. -/
private def complexCoordinateUnitSphereMapSymm (n : ℕ) :
    Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 → ComplexProjectiveAttachingSphere n :=
  fun x ↦
    ⟨NormedSpace.normalize ((complexCoordinateContinuousLinearEquiv n).symm x.1),
      normalize_mem_unitSphere
        ((complexCoordinateContinuousLinearEquiv_symm_ne_zero_iff n).2
          (by
            intro hx0
            have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
            have : ‖x.1‖ = 0 := by simp [hx0]
            linarith))⟩

/-- Helper for Example 10.1.12: radial normalization commutes with the inverse coordinate bridge
on the complex sphere. -/
private theorem complexCoordinateUnitSphereMap_left_inv (n : ℕ) :
    Function.LeftInverse (complexCoordinateUnitSphereMapSymm n) (complexCoordinateUnitSphereMap n) := by
  intro z
  -- The inverse coordinate bridge sends the normalized real image to a positive real multiple of
  -- the original complex vector, so normalizing again recovers the original sphere point.
  apply Subtype.ext
  let y : Fin (2 * (n + 1)) → ℝ := complexCoordinateContinuousLinearEquiv n z.1
  have hy : y ≠ 0 := by
    exact (complexCoordinateContinuousLinearEquiv_ne_zero_iff n).2
      (complexProjectiveAttachingSphere_ne_zero n z)
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hz1 : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  -- Rewrite the composite as normalization of a positive scalar multiple of `z.1`.
  change
    NormedSpace.normalize
        ((complexCoordinateContinuousLinearEquiv n).symm
          (NormedSpace.normalize ((complexCoordinateContinuousLinearEquiv n) z.1))) = z.1
  have hinner :
      (complexCoordinateContinuousLinearEquiv n).symm
          (NormedSpace.normalize ((complexCoordinateContinuousLinearEquiv n) z.1)) =
        (‖y‖⁻¹ : ℝ) • z.1 := by
    simp [NormedSpace.normalize, y, hy, smul_smul]
  have hnormalize :
      NormedSpace.normalize ((‖y‖⁻¹ : ℝ) • z.1) = NormedSpace.normalize z.1 := by
    simpa using NormedSpace.normalize_smul_of_pos (inv_pos.mpr hypos) z.1
  rw [hinner, hnormalize]
  simpa [hz1] using NormedSpace.normalize_eq_self_of_norm_eq_one hz1

/-- Helper for Example 10.1.12: radial normalization commutes with the coordinate bridge on the
real sphere. -/
private theorem complexCoordinateUnitSphereMap_right_inv (n : ℕ) :
    Function.RightInverse (complexCoordinateUnitSphereMapSymm n) (complexCoordinateUnitSphereMap n) := by
  intro x
  -- The forward coordinate bridge sends the normalized inverse image to a positive real multiple
  -- of the original real vector, so the second normalization returns the original sphere point.
  apply Subtype.ext
  let z : Fin (n + 1) → ℂ := (complexCoordinateContinuousLinearEquiv n).symm x.1
  have hz : z ≠ 0 := by
    refine (complexCoordinateContinuousLinearEquiv_symm_ne_zero_iff n).2 ?_
    intro hx0
    have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have : ‖x.1‖ = 0 := by simp [hx0]
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  -- Route correction: compare only the normalized ambient vectors; avoid subtype-level transport.
  change
    NormedSpace.normalize
        ((complexCoordinateContinuousLinearEquiv n)
          (NormedSpace.normalize ((complexCoordinateContinuousLinearEquiv n).symm x.1))) = x.1
  have hinner :
      (complexCoordinateContinuousLinearEquiv n)
          (NormedSpace.normalize ((complexCoordinateContinuousLinearEquiv n).symm x.1)) =
        (‖z‖⁻¹ : ℝ) • x.1 := by
    simp [NormedSpace.normalize, z, hz, smul_smul]
  have hnormalize :
      NormedSpace.normalize ((‖z‖⁻¹ : ℝ) • x.1) = NormedSpace.normalize x.1 := by
    simpa using NormedSpace.normalize_smul_of_pos (inv_pos.mpr hzpos) x.1
  rw [hinner, hnormalize]
  simpa [hx1] using NormedSpace.normalize_eq_self_of_norm_eq_one hx1

/-- Helper for Example 10.1.12: radial normalization of the real coordinate image varies
continuously on the complex attaching sphere. -/
private theorem complexCoordinateUnitSphereMap_continuous (n : ℕ) :
    Continuous (complexCoordinateUnitSphereMap n) := by
  -- Continuity comes from the explicit formula `normalize y = ‖y‖⁻¹ • y`.
  apply Continuous.subtype_mk
  let f : ComplexProjectiveAttachingSphere n → Fin (2 * (n + 1)) → ℝ :=
    fun z ↦ complexCoordinateContinuousLinearEquiv n z.1
  have hf : Continuous f := by
    simpa [f] using
      (complexCoordinateContinuousLinearEquiv n).continuous.comp continuous_subtype_val
  have hf0 : ∀ z, f z ≠ 0 := by
    intro z
    exact (complexCoordinateContinuousLinearEquiv_ne_zero_iff n).2
      (complexProjectiveAttachingSphere_ne_zero n z)
  simpa [complexCoordinateUnitSphereMap, f, NormedSpace.normalize] using
    ((continuous_norm.comp hf).inv₀ fun z ↦ norm_ne_zero_iff.mpr (hf0 z)).smul hf

/-- Helper for Example 10.1.12: radial normalization of the inverse real coordinate image varies
continuously on the real unit sphere. -/
private theorem complexCoordinateUnitSphereMapSymm_continuous (n : ℕ) :
    Continuous (complexCoordinateUnitSphereMapSymm n) := by
  -- Continuity is the same normalization formula, now applied to the inverse coordinate bridge.
  let f : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 → Fin (n + 1) → ℂ :=
    fun x ↦ (complexCoordinateContinuousLinearEquiv n).symm x.1
  have hf : Continuous f := by
    simpa [f] using
      (complexCoordinateContinuousLinearEquiv n).symm.continuous.comp continuous_subtype_val
  have hf0 : ∀ x, f x ≠ 0 := by
    intro x
    refine (complexCoordinateContinuousLinearEquiv_symm_ne_zero_iff n).2 ?_
    intro hx0
    have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have : ‖x.1‖ = 0 := by simp [hx0]
    linarith
  refine Continuous.subtype_mk
    (f := fun x : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 =>
      (NormedSpace.normalize (f x) : Fin (n + 1) → ℂ))
    ?_
    (fun x ↦ normalize_mem_unitSphere (hf0 x))
  refine continuous_pi fun i : Fin (n + 1) ↦ ?_
  -- Work coordinatewise to avoid asking Lean for a global `ContinuousSMul` instance on the whole
  -- complex-valued function space.
  have hfi : Continuous fun x ↦ f x i := by
    simpa [f] using continuous_apply i |>.comp hf
  have hscalar : Continuous fun x ↦ (((‖f x‖⁻¹ : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((continuous_norm.comp hf).inv₀ fun x ↦ norm_ne_zero_iff.mpr (hf0 x))
  change Continuous fun a : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 =>
    (((‖(complexCoordinateContinuousLinearEquiv n).symm a.1‖⁻¹ : ℝ) : ℂ) *
      ((complexCoordinateContinuousLinearEquiv n).symm a.1 i))
  simpa [f] using hscalar.mul hfi

/-- Helper for Example 10.1.12: radial normalization transports the complex unit sphere in
`ℂ^(n + 1)` to the real unit sphere in `ℝ^(2n + 2)`. -/
private noncomputable def complexCoordinateUnitSphereHomeomorph (n : ℕ) :
    ComplexProjectiveAttachingSphere n ≃ₜ Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 :=
  { toEquiv :=
      { toFun := complexCoordinateUnitSphereMap n
        invFun := complexCoordinateUnitSphereMapSymm n
        left_inv := complexCoordinateUnitSphereMap_left_inv n
        right_inv := complexCoordinateUnitSphereMap_right_inv n }
    continuous_toFun := complexCoordinateUnitSphereMap_continuous n
    continuous_invFun := complexCoordinateUnitSphereMapSymm_continuous n }

/-- Helper for Example 10.1.12: the new top-cell boundary sphere is already identified with the
standard real sphere by the ambient complex-to-real coordinate homeomorphism. -/
private noncomputable abbrev complexProjectiveSpaceSuccTopCellBoundaryHomeomorph (n : ℕ) :
    ComplexProjectiveAttachingSphere n ≃ₜ
      Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 :=
  -- This is exactly the sphere homeomorphism used to compare the complex and real top-cell
  -- boundary models.
  complexCoordinateUnitSphereHomeomorph n

/-- Helper for Example 10.1.12: the zero-extension linear map is continuous. -/
private theorem complexProjectiveSpaceSuccLinearMap_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccLinearMap n) := by
  -- Each coordinate is either a source coordinate or the constant zero map.
  refine continuous_pi fun i ↦ ?_
  cases i using Fin.lastCases with
  | last =>
      simpa [complexProjectiveSpaceSuccLinearMap]
        using (continuous_const : Continuous fun _ : Fin (n + 1) → ℂ ↦ (0 : ℂ))
  | cast j =>
      have hle : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.is_lt
      simpa [complexProjectiveSpaceSuccLinearMap, hle] using
        (continuous_apply j : Continuous fun f : Fin (n + 1) → ℂ ↦ f j)

/-- Helper for Example 10.1.12: the successor inclusion `CP^n → CP^(n + 1)` is continuous. -/
private theorem complexProjectiveSpaceSuccInclusion_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccInclusion n) := by
  let nonzeroMap :
      { v : Fin (n + 1) → ℂ // v ≠ 0 } → { w : Fin (n + 2) → ℂ // w ≠ 0 } :=
    fun v ↦
      ⟨complexProjectiveSpaceSuccLinearMap n v,
        complexProjectiveSpaceSuccLinearMap_ne_zero n v.2⟩
  have hnonzeroMap : Continuous nonzeroMap := by
    -- On nonzero representatives, the inclusion is the continuous zero-extension linear map.
    exact
      Continuous.subtype_mk
        (complexProjectiveSpaceSuccLinearMap_continuous n |>.comp continuous_subtype_val)
        (fun v ↦ (nonzeroMap v).2)
  -- Then descend that representative-level map to projectivization.
  simpa [complexProjectiveSpaceSuccInclusion, Projectivization.map, nonzeroMap] using
    (Continuous.quotient_map'
      (s := projectivizationSetoid ℂ (Fin (n + 1) → ℂ))
      (t := projectivizationSetoid ℂ (Fin (n + 2) → ℂ))
      hnonzeroMap
      (by
        rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
        refine ⟨a, ?_⟩
        dsimp at ha ⊢
        change ↑a • complexProjectiveSpaceSuccLinearMap n v =
          complexProjectiveSpaceSuccLinearMap n u
        simpa [Units.smul_def] using congrArg (complexProjectiveSpaceSuccLinearMap n) ha))

/-- Helper for Example 10.1.12: the successor inclusion identifies `CP^n` homeomorphically with
its range in `CP^(n + 1)`. -/
private noncomputable abbrev complexProjectiveSpaceSuccInclusionHomeomorphRange (n : ℕ) :
    ComplexProjectiveSpace n ≃ₜ Set.range (complexProjectiveSpaceSuccInclusion n) :=
  -- Compactness of `CP^n` upgrades the continuous injective inclusion to a closed embedding.
  letI : CompactSpace (ComplexProjectiveSpace n) := complexProjectiveSpace_compactSpace n
  ((complexProjectiveSpaceSuccInclusion_continuous n).isClosedEmbedding
    (complexProjectiveSpaceSuccInclusion_injective n)).toIsEmbedding.toHomeomorph

/-- Helper for Example 10.1.12: the successor inclusion identifies `CP^n` with the canonical
hyperplane projectivization inside `CP^(n + 1)`. -/
private noncomputable abbrev complexProjectiveSpaceSuccInclusionHomeomorphHyperplane (n : ℕ) :
    ComplexProjectiveSpace n ≃ₜ
      ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1))) :=
  -- Rewrite the range model of the inclusion into the intrinsic hyperplane-projectivization model.
  (complexProjectiveSpaceSuccInclusionHomeomorphRange n).trans <|
    Homeomorph.setCongr
      (complexProjectiveSpaceSuccInclusion_range_eq_hyperplaneProjectivization n)

/-- Helper for Example 10.1.12: the canonical hyperplane copy of `CP^n` is closed inside
`CP^(n + 1)`. -/
private theorem isClosed_complexProjectiveSpaceSuccHyperplane_projectivization (n : ℕ) :
    IsClosed
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))) := by
  letI : CompactSpace (ComplexProjectiveSpace n) := complexProjectiveSpace_compactSpace n
  -- First realize the hyperplane copy as the compact range of the successor inclusion.
  have hcompact :
      IsCompact (Set.range (complexProjectiveSpaceSuccInclusion n)) := by
    have huniv : IsCompact (Set.univ : Set (ComplexProjectiveSpace n)) := isCompact_univ
    simpa [Set.image_univ] using
      huniv.image (complexProjectiveSpaceSuccInclusion_continuous n)
  -- Then rewrite that range into the intrinsic projectivized-hyperplane model.
  rw [← complexProjectiveSpaceSuccInclusion_range_eq_hyperplaneProjectivization n]
  exact hcompact.isClosed

/-- Helper for Example 10.1.12: an inherited cell of `CP^n` transports into the hyperplane copy
of `CP^(n + 1)` via the successor inclusion homeomorphism. -/
private noncomputable def complexProjectiveSpaceSuccHyperplaneTransportCellMap
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m →
      PartialEquiv (Fin m → ℝ)
        (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))) :=
  fun j ↦
    (S.cwComplex.map m j).transEquiv
      (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n).toEquiv

/-- Helper for Example 10.1.12: the transported hyperplane cell map is the old cell map followed
by the hyperplane embedding. -/
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)
      (x : Fin m → ℝ),
      complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j x =
        (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n)
          (S.cwComplex.map m j x) := by
  intro j x
  rfl

/-- Helper for Example 10.1.12: transporting an inherited cell into the hyperplane copy preserves
the standard open-ball source. -/
@[simp]
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMap_source
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j).source = Metric.ball 0 1 := by
  intro j
  -- Postcomposing with the hyperplane homeomorphism does not change the old cell source.
  simpa [complexProjectiveSpaceSuccHyperplaneTransportCellMap, PartialEquiv.trans_source]
    using S.cwComplex.source_eq m j

/-- Helper for Example 10.1.12: a point in the coerced image target of a subtype-valued partial
equivalence really lies in the underlying subtype set. -/
private theorem partialEquivSubtypeValImage_mem_subtype
    {α β : Type*} [Inhabited α] {s : Set β} (e : PartialEquiv α s) {y : β}
    (hy : y ∈ (Subtype.val '' e.target : Set β)) :
    y ∈ s := by
  -- Unpack the coerced target point and read off its subtype membership.
  rcases hy with ⟨z, hz, rfl⟩
  exact z.2

/-- Helper for Example 10.1.12: source points of a subtype-valued partial equivalence map into
the coerced ambient target. -/
private theorem partialEquivSubtypeValImage_map_source
    {α β : Type*} [Inhabited α] {s : Set β} (e : PartialEquiv α s) {x : α}
    (hx : x ∈ e.source) :
    ((e x : s) : β) ∈ (Subtype.val '' e.target : Set β) := by
  -- The original target witness becomes the ambient-image witness after forgetting the subtype.
  exact ⟨e x, e.map_source hx, rfl⟩

/-- Helper for Example 10.1.12: target points of the ambientized partial equivalence return to the
original source. -/
private theorem partialEquivSubtypeValImage_map_target
    {α β : Type*} [Inhabited α] {s : Set β} (e : PartialEquiv α s)
    [DecidablePred fun y : β ↦ y ∈ (Subtype.val '' e.target : Set β)] {y : β}
    (hy : y ∈ (Subtype.val '' e.target : Set β)) :
    (if hy' : y ∈ (Subtype.val '' e.target : Set β) then
        e.symm ⟨y, partialEquivSubtypeValImage_mem_subtype e hy'⟩
      else default) ∈ e.source := by
  rcases hy with ⟨z, hz, rfl⟩
  -- On the ambient target, the inverse branch reduces to the original subtype-valued inverse.
  change
    (if hy' : ((z : s) : β) ∈ (Subtype.val '' e.target : Set β) then
        e.symm ⟨((z : s) : β), partialEquivSubtypeValImage_mem_subtype e hy'⟩
      else default) ∈ e.source
  have hy' :
      ((z : s) : β) ∈ (Subtype.val '' e.target : Set β) := ⟨z, hz, rfl⟩
  simp [hy']
  simpa using e.map_target hz

/-- Helper for Example 10.1.12: source points stay on the genuine inverse branch after forgetting
the subtype target. -/
private theorem partialEquivSubtypeValImage_left_inv
    {α β : Type*} [Inhabited α] {s : Set β} (e : PartialEquiv α s)
    [DecidablePred fun y : β ↦ y ∈ (Subtype.val '' e.target : Set β)] {x : α}
    (hx : x ∈ e.source) :
    (if hy : (((e x : s) : β) ∈ (Subtype.val '' e.target : Set β)) then
        e.symm ⟨((e x : s) : β), partialEquivSubtypeValImage_mem_subtype e hy⟩
      else default) = x := by
  have hy :
      ((e x : s) : β) ∈ (Subtype.val '' e.target : Set β) :=
    partialEquivSubtypeValImage_map_source e hx
  -- Source points use the genuine inverse branch, so the old left-inverse closes unchanged.
  change
    (if hy' : ((e x : s) : β) ∈ (Subtype.val '' e.target : Set β) then
        e.symm ⟨((e x : s) : β), partialEquivSubtypeValImage_mem_subtype e hy'⟩
      else default) = x
  simp [hy]
  simpa using e.left_inv hx

/-- Helper for Example 10.1.12: ambient target points also stay on the genuine inverse branch of
the subtype-valued partial equivalence. -/
private theorem partialEquivSubtypeValImage_right_inv
    {α β : Type*} [Inhabited α] {s : Set β} (e : PartialEquiv α s)
    [DecidablePred fun y : β ↦ y ∈ (Subtype.val '' e.target : Set β)] {y : β}
    (hy : y ∈ (Subtype.val '' e.target : Set β)) :
    ((e
        (if hy' : y ∈ (Subtype.val '' e.target : Set β) then
          e.symm ⟨y, partialEquivSubtypeValImage_mem_subtype e hy'⟩
        else default) : s) : β) = y := by
  rcases hy with ⟨z, hz, rfl⟩
  have hy' :
      ((z : s) : β) ∈ (Subtype.val '' e.target : Set β) := by
    exact ⟨z, hz, rfl⟩
  -- Target points likewise use the genuine inverse branch, so the old right-inverse applies.
  change
    ((e
        (if hy'' : ((z : s) : β) ∈ (Subtype.val '' e.target : Set β) then
          e.symm ⟨((z : s) : β), partialEquivSubtypeValImage_mem_subtype e hy''⟩
        else default) : s) : β) = ((z : s) : β)
  simp [hy']
  simpa using congrArg Subtype.val (e.right_inv hz)

/-- Helper for Example 10.1.12: forgetting a subtype target turns a subtype-valued partial
equivalence into an ambient partial equivalence with the coerced image target. -/
private noncomputable def partialEquivSubtypeValImage
    {α β : Type*} [Inhabited α] {s : Set β} (e : PartialEquiv α s) :
    PartialEquiv α β :=
  let _ : DecidablePred (fun y : β ↦ y ∈ (Subtype.val '' e.target : Set β)) :=
    Classical.decPred _
  { toFun := fun x ↦ (e x : β)
    invFun := fun y ↦
      if hy : y ∈ (Subtype.val '' e.target : Set β) then
        e.symm ⟨y, partialEquivSubtypeValImage_mem_subtype e hy⟩
      else default
    source := e.source
    target := Subtype.val '' e.target
    map_source' := fun {_} hx ↦ partialEquivSubtypeValImage_map_source e hx
    map_target' := fun {_} hy ↦ partialEquivSubtypeValImage_map_target e hy
    left_inv' := fun {_} hx ↦ partialEquivSubtypeValImage_left_inv e hx
    right_inv' := fun {_} hy ↦ partialEquivSubtypeValImage_right_inv e hy }

/-- Helper for Example 10.1.12: postcomposing a partial equivalence with a homeomorphism preserves
inverse continuity on the transported target. -/
private theorem partialEquiv_transHomeomorph_continuousOnSymm
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    (e : PartialEquiv α β) (h : β ≃ₜ γ)
    (he : ContinuousOn e.symm e.target) :
    ContinuousOn (e.transEquiv h.toEquiv).symm (e.transEquiv h.toEquiv).target := by
  -- On the transported target, the inverse is just `e.symm` after the homeomorphism inverse.
  rw [continuousOn_iff_continuous_restrict]
  have hsymm : Continuous fun y : (e.transEquiv h.toEquiv).target ↦ h.symm y.1 :=
    h.symm.continuous.comp continuous_subtype_val
  have hsymm_mapsTo : ∀ y : (e.transEquiv h.toEquiv).target, h.symm y.1 ∈ e.target := by
    intro y
    exact y.2
  have hcont : Continuous fun y : (e.transEquiv h.toEquiv).target ↦ e.symm (h.symm y.1) :=
    he.comp_continuous hsymm hsymm_mapsTo
  simpa [Set.restrict, PartialEquiv.transEquiv] using hcont

/-- Helper for Example 10.1.12: forgetting a subtype target preserves forward continuity of a
partial equivalence on a fixed source set. -/
private theorem partialEquivSubtypeValImage_continuousOn
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Inhabited α] {s : Set β}
    (e : PartialEquiv α s) {t : Set α} (he : ContinuousOn e t) :
    ContinuousOn (partialEquivSubtypeValImage e) t := by
  -- The ambientized map is the subtype-valued map followed by the continuous coercion.
  simpa [partialEquivSubtypeValImage] using
    continuous_subtype_val.comp_continuousOn he

/-- Helper for Example 10.1.12: forgetting a subtype target preserves inverse continuity on the
ambient image target. -/
private theorem partialEquivSubtypeValImage_continuousOnSymm
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Inhabited α] {s : Set β}
    (e : PartialEquiv α s) (he : ContinuousOn e.symm e.target) :
    ContinuousOn (partialEquivSubtypeValImage e).symm (partialEquivSubtypeValImage e).target := by
  -- Restrict to the ambient image target and then lift back to the subtype target once.
  rw [continuousOn_iff_continuous_restrict]
  have hlift :
      Continuous fun y : (partialEquivSubtypeValImage e).target ↦
        (⟨y.1, partialEquivSubtypeValImage_mem_subtype e y.2⟩ : s) :=
    continuous_subtype_val.subtype_mk
      (fun y ↦ partialEquivSubtypeValImage_mem_subtype e y.2)
  have hlift_mapsTo :
      ∀ y : (partialEquivSubtypeValImage e).target,
        (⟨y.1, partialEquivSubtypeValImage_mem_subtype e y.2⟩ : s) ∈ e.target := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨z, hz, rfl⟩
    simpa using hz
  have hcont :
      Continuous fun y : (partialEquivSubtypeValImage e).target ↦
        e.symm (⟨y.1, partialEquivSubtypeValImage_mem_subtype e y.2⟩ : s) :=
    he.comp_continuous hlift hlift_mapsTo
  simpa [Set.restrict, partialEquivSubtypeValImage] using hcont

/-- Helper for Example 10.1.12: ambientizing a transported inherited hyperplane cell forgets the
hyperplane subtype and remembers only its coerced ambient image. -/
private noncomputable abbrev complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m →
      PartialEquiv (Fin m → ℝ) (ComplexProjectiveSpace (n + 1)) :=
  fun j ↦ partialEquivSubtypeValImage (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j)

/-- Helper for Example 10.1.12: the ambient inherited-cell adapter is the subtype-valued
transport followed by coercion to ambient projective space. -/
@[simp]
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_apply
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)
      (x : Fin m → ℝ),
      complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j x =
        ((complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j x :
          ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
            (ComplexProjectiveSpace (n + 1)))) : ComplexProjectiveSpace (n + 1)) := by
  intro j x
  rfl

/-- Helper for Example 10.1.12: ambientizing an inherited hyperplane cell still uses the standard
open-ball source. -/
@[simp]
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_source
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      (complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j).source =
        Metric.ball 0 1 := by
  intro j
  -- Forgetting the subtype target does not change the inherited cell source.
  simpa [complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient, partialEquivSubtypeValImage]
    using complexProjectiveSpaceSuccHyperplaneTransportCellMap_source n S j

/-- Helper for Example 10.1.12: ambientized inherited cells still land inside the canonical
hyperplane copy of `CP^n` in `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_target_subset_hyperplane
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      (complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j).target ⊆
        ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1))) := by
  intro j y hy
  rcases hy with ⟨z, hz, rfl⟩
  exact z.2

/-- Helper for Example 10.1.12: the ambient inherited-cell open image is exactly the coerced
subtype-level open image in the hyperplane stratum. -/
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_image_ball
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j '' Metric.ball 0 1 =
        Subtype.val '' (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j '' Metric.ball 0 1) := by
  intro j
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Unfold the ambient wrapper once, then package the same point in the subtype-level image.
    exact
      ⟨complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    -- Any coerced subtype-image point already comes from the same Euclidean source point.
    exact ⟨x, hx, rfl⟩

/-- Helper for Example 10.1.12: inherited ambient open cells map into the closed hyperplane
stratum of the successor projective space. -/
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_mapsTo_hyperplane
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      Set.MapsTo
        (complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j)
        (Metric.ball 0 1)
        (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))) := by
  intro j x hx
  exact
    complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_target_subset_hyperplane n S j <|
      (complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j).map_source <|
        by
          simpa using hx

/-- Helper for Example 10.1.12: fiber-bundle trivializations transport across source and target
homeomorphisms. -/
private theorem isFiberBundleMap_congrHomeomorph
    {E E' B B' F : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace B']
    [TopologicalSpace F] {p : E → B} (hE : E' ≃ₜ E) (hB : B ≃ₜ B')
    (hp : IsFiberBundleMap F p) :
    IsFiberBundleMap F (hB ∘ p ∘ hE) := by
  intro b'
  -- Pull a trivialization back to the old base point, then transport it through the homeomorphisms.
  obtain ⟨e, hb⟩ := hp (hB.symm b')
  refine ⟨(e.compHomeomorph hE).homeomorphComp hB, ?_⟩
  simpa [Function.comp_def] using hb

/-- Helper for Example 10.1.12: a point of the real unit sphere canonically gives a point of the
corresponding closed unit ball. -/
private theorem complexCoordinateUnitSphere_mem_closedBall (n : ℕ)
    (x : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    x.1 ∈ Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1 := by
  -- The sphere equation `‖x‖ = 1` immediately implies the closed-ball inequality `‖x‖ ≤ 1`.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (mem_sphere_zero_iff_norm.mp x.2).le

/-- Helper for Example 10.1.12: the real unit sphere includes into the corresponding closed unit
ball. -/
private def complexCoordinateUnitSphereToClosedBall (n : ℕ) :
    Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 →
      Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1 :=
  fun x ↦ ⟨x.1, complexCoordinateUnitSphere_mem_closedBall n x⟩

/-- Helper for Example 10.1.12: the real-source successor top-cell representative is built
directly on the closed real ball expected by the CW source. -/
private def complexProjectiveSpaceSuccTopCellRepresentativeReal (n : ℕ)
    (x : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    Fin (n + 2) → ℂ :=
  Fin.snoc ((complexCoordinateContinuousLinearEquiv n).symm x.1)
    (Real.sqrt (1 - ‖x.1‖ ^ 2))

/-- Helper for Example 10.1.12: the same real-source successor representative extends to the whole
ambient real coordinate space. -/
private def complexProjectiveSpaceSuccTopCellRepresentativeRealTotal (n : ℕ)
    (x : Fin (2 * (n + 1)) → ℝ) :
    Fin (n + 2) → ℂ :=
  Fin.snoc ((complexCoordinateContinuousLinearEquiv n).symm x)
    (Real.sqrt (1 - ‖x‖ ^ 2))

/-- Helper for Example 10.1.12: the total real-source successor representative restricts to the
closed-ball representative already used for the CW chart. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentativeReal_eq_total (n : ℕ)
    (x : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentativeReal n x =
      complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x.1 := by
  -- Both representatives are the same `Fin.snoc` formula after forgetting the closed-ball proof.
  rfl

/-- Helper for Example 10.1.12: away from the last coordinate, the total real-source successor
representative keeps the inverse complex-coordinate bridge. -/
@[simp]
private theorem complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_castSucc (n : ℕ)
    (x : Fin (2 * (n + 1)) → ℝ) (i : Fin (n + 1)) :
    complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x i.castSucc =
      (complexCoordinateContinuousLinearEquiv n).symm x i := by
  -- Away from the last coordinate, the representative is literally the inverse coordinate image.
  simp [complexProjectiveSpaceSuccTopCellRepresentativeRealTotal]

/-- Helper for Example 10.1.12: the last coordinate of the total real-source successor
representative is the square-root term. -/
@[simp]
private theorem complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_last (n : ℕ)
    (x : Fin (2 * (n + 1)) → ℝ) :
    complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x (Fin.last (n + 1)) =
      Real.sqrt (1 - ‖x‖ ^ 2) := by
  -- The last coordinate is exactly the one appended by `Fin.snoc`.
  simp [complexProjectiveSpaceSuccTopCellRepresentativeRealTotal]

/-- Helper for Example 10.1.12: the total real-source successor representative is never zero. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero (n : ℕ)
    (x : Fin (2 * (n + 1)) → ℝ) :
    complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x ≠ 0 := by
  -- If the appended vector were zero, then all real coordinates would vanish, forcing the last
  -- coordinate to be `1`, a contradiction.
  intro hzero
  have hx0 :
      (complexCoordinateContinuousLinearEquiv n).symm x = 0 := by
    ext i
    have hcoord :=
      congrArg (fun f : Fin (n + 2) → ℂ ↦ f i.castSucc) hzero
    simpa using hcoord
  have hxReal : x = 0 := by
    exact (complexCoordinateContinuousLinearEquiv n).symm.injective hx0
  have hlast :=
    congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) hzero
  have hone : (1 : ℂ) = 0 := by
    simpa [complexProjectiveSpaceSuccTopCellRepresentativeRealTotal, hxReal] using hlast
  norm_num at hone

/-- Helper for Example 10.1.12: projectivizing the total real-source successor representative
gives a globally defined ambient extension of the top-cell chart. -/
private def complexProjectiveSpaceSuccTopCellMapRealTotal (n : ℕ) :
    (Fin (2 * (n + 1)) → ℝ) → ComplexProjectiveSpace (n + 1) :=
  fun x ↦
    Projectivization.mk ℂ
      (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x)
      (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n x)

/-- Helper for Example 10.1.12: the real-source successor representative keeps the first
`n + 1` complex coordinates. -/
@[simp]
private theorem complexProjectiveSpaceSuccTopCellRepresentativeReal_castSucc (n : ℕ)
    (x : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1) (i : Fin (n + 1)) :
    complexProjectiveSpaceSuccTopCellRepresentativeReal n x i.castSucc =
      (complexCoordinateContinuousLinearEquiv n).symm x.1 i := by
  -- Away from the last coordinate, the representative is literally the inverse coordinate image.
  simp [complexProjectiveSpaceSuccTopCellRepresentativeReal]

/-- Helper for Example 10.1.12: the last coordinate of the real-source successor representative
is the square-root term. -/
@[simp]
private theorem complexProjectiveSpaceSuccTopCellRepresentativeReal_last (n : ℕ)
    (x : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentativeReal n x (Fin.last (n + 1)) =
      Real.sqrt (1 - ‖x.1‖ ^ 2) := by
  -- The last coordinate is exactly the one appended by `Fin.snoc`.
  simp [complexProjectiveSpaceSuccTopCellRepresentativeReal]

/-- Helper for Example 10.1.12: the real-source successor representative is never zero. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentativeReal_ne_zero (n : ℕ)
    (x : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentativeReal n x ≠ 0 := by
  -- If the appended vector were zero, then the real coordinates would also vanish, forcing the
  -- last coordinate to be `1`, a contradiction.
  intro hzero
  have hx0 :
      (complexCoordinateContinuousLinearEquiv n).symm x.1 = 0 := by
    ext i
    have hcoord :=
      congrArg (fun f : Fin (n + 2) → ℂ ↦ f i.castSucc) hzero
    simpa using hcoord
  have hxReal : x.1 = 0 := by
    exact (complexCoordinateContinuousLinearEquiv n).symm.injective hx0
  have hlast :=
    congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) hzero
  have hone : (1 : ℂ) = 0 := by
    simpa [complexProjectiveSpaceSuccTopCellRepresentativeReal, hxReal] using hlast
  norm_num at hone

/-- Helper for Example 10.1.12: the real-source top cell for `CP^(n + 1)` is obtained by
projectivizing the explicit real-source successor representative on the closed unit ball. -/
private def complexProjectiveSpaceSuccTopCellMapReal (n : ℕ) :
    Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1 →
      ComplexProjectiveSpace (n + 1) :=
  fun x ↦
    Projectivization.mk ℂ
      (complexProjectiveSpaceSuccTopCellRepresentativeReal n x)
      (complexProjectiveSpaceSuccTopCellRepresentativeReal_ne_zero n x)

/-- Helper for Example 10.1.12: the closed-ball top-cell chart is the restriction of the total
ambient real chart. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_eq_total (n : ℕ)
    (x : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellMapReal n x =
      complexProjectiveSpaceSuccTopCellMapRealTotal n x.1 := by
  -- The subtype and ambient charts use the same projective representative after forgetting the
  -- closed-ball witness.
  simp [complexProjectiveSpaceSuccTopCellMapReal, complexProjectiveSpaceSuccTopCellMapRealTotal,
    complexProjectiveSpaceSuccTopCellRepresentativeReal_eq_total]

/-- Helper for Example 10.1.12: the total real-source successor representative varies
continuously with the ambient real coordinates. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n) := by
  -- Check continuity coordinatewise: the first block is the inverse linear equivalence, and the
  -- last coordinate is the square-root scalar.
  refine continuous_pi fun i ↦ ?_
  cases i using Fin.lastCases with
  | last =>
      have hsqrt :
          Continuous fun x : Fin (2 * (n + 1)) → ℝ ↦
            ((Real.sqrt (1 - ‖x‖ ^ 2) : ℝ) : ℂ) := by
        exact Complex.continuous_ofReal.comp <|
          Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))
      simpa [complexProjectiveSpaceSuccTopCellRepresentativeRealTotal] using hsqrt
  | cast j =>
      simpa [complexProjectiveSpaceSuccTopCellRepresentativeRealTotal] using
        continuous_apply j |>.comp (complexCoordinateContinuousLinearEquiv n).symm.continuous

/-- Helper for Example 10.1.12: the total ambient real top-cell chart is continuous. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealTotal_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccTopCellMapRealTotal n) := by
  -- Lift the continuous representative into the nonzero-vector subtype and then apply the
  -- projectivization quotient map.
  let representative :
      (Fin (2 * (n + 1)) → ℝ) → { v : Fin (n + 2) → ℂ // v ≠ 0 } :=
    fun x ↦
      ⟨complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x,
        complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n x⟩
  have hRepresentative : Continuous representative := by
    exact
      (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_continuous n).subtype_mk
        (fun x ↦ (representative x).2)
  simpa [complexProjectiveSpaceSuccTopCellMapRealTotal, representative,
    Projectivization.mk'_eq_mk] using
    (continuous_quotient_mk'.comp hRepresentative)

/-- Helper for Example 10.1.12: on the real boundary sphere, the real-source successor
representative collapses to projectivized zero-extension of the inverse coordinate image. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentativeReal_boundary_eq (n : ℕ)
    (x : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentativeReal n
        (complexCoordinateUnitSphereToClosedBall n x) =
      complexProjectiveSpaceSuccLinearMap n
        ((complexCoordinateContinuousLinearEquiv n).symm x.1) := by
  -- On the boundary, the norm equation forces the square-root coordinate to vanish.
  ext i
  cases i using Fin.lastCases with
  | last =>
      have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
      have hx1' :
          ‖(complexCoordinateUnitSphereToClosedBall n x).1‖ = 1 := by
        simpa [complexCoordinateUnitSphereToClosedBall] using hx1
      simp [complexProjectiveSpaceSuccTopCellRepresentativeReal, hx1']
  | cast j =>
      simp [complexCoordinateUnitSphereToClosedBall]

/-- Helper for Example 10.1.12: the real-source top cell lands in the canonical hyperplane copy
on the boundary sphere. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_mem_hyperplane_on_boundary (n : ℕ)
    (x : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellMapReal n
        (complexCoordinateUnitSphereToClosedBall n x) ∈
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- After the square-root coordinate vanishes, the boundary representative is a zero-extension.
  let z : Fin (n + 1) → ℂ := (complexCoordinateContinuousLinearEquiv n).symm x.1
  have hz : z ≠ 0 := by
    refine (complexCoordinateContinuousLinearEquiv_symm_ne_zero_iff n).2 ?_
    intro hx0
    have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have : ‖x.1‖ = 0 := by simp [hx0]
    linarith
  have hrep :
      complexProjectiveSpaceSuccTopCellRepresentativeReal n
          (complexCoordinateUnitSphereToClosedBall n x) =
        complexProjectiveSpaceSuccLinearMap n z :=
    complexProjectiveSpaceSuccTopCellRepresentativeReal_boundary_eq n x
  have hmap :
      complexProjectiveSpaceSuccTopCellMapReal n
          (complexCoordinateUnitSphereToClosedBall n x) =
        Projectivization.mk ℂ
          (complexProjectiveSpaceSuccLinearMap n z)
          (complexProjectiveSpaceSuccLinearMap_ne_zero n hz) := by
    simpa [complexProjectiveSpaceSuccTopCellMapReal, z, hrep]
  have hzmem :
      Projectivization.mk ℂ
          (complexProjectiveSpaceSuccLinearMap n z)
          (complexProjectiveSpaceSuccLinearMap_ne_zero n hz) ∈
        (complexProjectiveSpaceSuccHyperplane n).projectivization :=
    (Submodule.mk_mem_projectivization_iff
      (complexProjectiveSpaceSuccHyperplane n)
      (complexProjectiveSpaceSuccLinearMap_ne_zero n hz)).2
      (complexProjectiveSpaceSuccLinearMap_mem_hyperplane n z)
  exact hmap ▸ hzmem

/-- Helper for Example 10.1.12: after transporting the complex boundary sphere to the real
boundary sphere by radial normalization, the real-source top cell is the standard projective
zero-extension attaching map. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_boundary_eq (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    complexProjectiveSpaceSuccTopCellMapReal n
        (complexCoordinateUnitSphereToClosedBall n (complexCoordinateUnitSphereHomeomorph n z)) =
      complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) := by
  let y : Fin (2 * (n + 1)) → ℝ := complexCoordinateContinuousLinearEquiv n z.1
  have hy : y ≠ 0 := by
    exact (complexCoordinateContinuousLinearEquiv_ne_zero_iff n).2
      (complexProjectiveAttachingSphere_ne_zero n z)
  have hzscaled : (‖y‖⁻¹ : ℝ) • z.1 ≠ 0 := by
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hy)) (complexProjectiveAttachingSphere_ne_zero n z)
  have hsymm :
      (complexCoordinateContinuousLinearEquiv n).symm
          (complexCoordinateUnitSphereHomeomorph n z).1 =
        (‖y‖⁻¹ : ℝ) • z.1 := by
    -- The sphere homeomorphism is defined by radial normalization of the ambient coordinate image.
    change
      (complexCoordinateContinuousLinearEquiv n).symm
          (NormedSpace.normalize ((complexCoordinateContinuousLinearEquiv n) z.1)) =
        (‖y‖⁻¹ : ℝ) • z.1
    simp [NormedSpace.normalize, y]
  have hrep :
      complexProjectiveSpaceSuccTopCellRepresentativeReal n
          (complexCoordinateUnitSphereToClosedBall n (complexCoordinateUnitSphereHomeomorph n z)) =
        complexProjectiveSpaceSuccLinearMap n ((‖y‖⁻¹ : ℝ) • z.1) := by
    -- On the real boundary sphere, the square-root coordinate vanishes and only zero-extension
    -- of the normalized complex representative remains.
    calc
      complexProjectiveSpaceSuccTopCellRepresentativeReal n
          (complexCoordinateUnitSphereToClosedBall n (complexCoordinateUnitSphereHomeomorph n z)) =
          complexProjectiveSpaceSuccLinearMap n
            ((complexCoordinateContinuousLinearEquiv n).symm
              (complexCoordinateUnitSphereHomeomorph n z).1) :=
        complexProjectiveSpaceSuccTopCellRepresentativeReal_boundary_eq n
          (complexCoordinateUnitSphereHomeomorph n z)
      _ = complexProjectiveSpaceSuccLinearMap n ((‖y‖⁻¹ : ℝ) • z.1) := by
        rw [hsymm]
  -- Route correction: now that the sphere bridge is available, finish by comparing the two
  -- projective representatives through a nonzero complex scalar.
  rw [complexProjectiveSpaceAttachingMap_eq_mk, complexProjectiveSpaceSuccInclusion_mk]
  have hmap :
      complexProjectiveSpaceSuccTopCellMapReal n
          (complexCoordinateUnitSphereToClosedBall n (complexCoordinateUnitSphereHomeomorph n z)) =
        Projectivization.mk ℂ
          (complexProjectiveSpaceSuccLinearMap n ((‖y‖⁻¹ : ℝ) • z.1))
          (complexProjectiveSpaceSuccLinearMap_ne_zero n hzscaled) := by
    simpa [complexProjectiveSpaceSuccTopCellMapReal, hrep]
  refine hmap.trans ?_
  apply
    (Projectivization.mk_eq_mk_iff' ℂ
      (complexProjectiveSpaceSuccLinearMap n ((‖y‖⁻¹ : ℝ) • z.1))
      (complexProjectiveSpaceSuccLinearMap n z.1)
      (complexProjectiveSpaceSuccLinearMap_ne_zero n hzscaled)
      (complexProjectiveSpaceSuccLinearMap_ne_zero n
        (complexProjectiveAttachingSphere_ne_zero n z))).2
  refine ⟨((‖y‖⁻¹ : ℝ) : ℂ), ?_⟩
  calc
    (((‖y‖⁻¹ : ℝ) : ℂ) • complexProjectiveSpaceSuccLinearMap n z.1) =
        complexProjectiveSpaceSuccLinearMap n ((((‖y‖⁻¹ : ℝ) : ℂ) • z.1)) := by
          simpa using (complexProjectiveSpaceSuccLinearMap n).map_smul (((‖y‖⁻¹ : ℝ) : ℂ)) z.1
    _ = complexProjectiveSpaceSuccLinearMap n ((‖y‖⁻¹ : ℝ) • z.1) := by
          rfl

/-- Helper for Example 10.1.12: an interior point of the real closed ball has nonzero
square-root coordinate in the real-source successor representative. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentativeReal_last_ne_zero_of_mem_ball
    (n : ℕ) {x : Fin (2 * (n + 1)) → ℝ}
    (hx : x ∈ Metric.ball (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentativeReal n
        ⟨x, Metric.ball_subset_closedBall hx⟩ (Fin.last (n + 1)) ≠ 0 := by
  -- The open-ball inequality makes `1 - ‖x‖^2` strictly positive, so its square root is nonzero.
  have hx' : ‖x‖ < 1 := by
    simpa [mem_ball_zero_iff] using hx
  have hsqrt : Real.sqrt (1 - ‖x‖ ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg x]
  simpa [complexProjectiveSpaceSuccTopCellRepresentativeReal] using hsqrt

/-- Helper for Example 10.1.12: the real-source top-cell model sends the open unit ball into the
complement of the successor hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_not_mem_hyperplane_of_mem_ball
    (n : ℕ) {x : Fin (2 * (n + 1)) → ℝ}
    (hx : x ∈ Metric.ball (0 : Fin (2 * (n + 1)) → ℝ) 1) :
    complexProjectiveSpaceSuccTopCellMapReal n ⟨x, Metric.ball_subset_closedBall hx⟩ ∉
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- Membership in the projectivized hyperplane would force the last coordinate to vanish,
  -- contradicting the open-ball computation above.
  intro hmem
  rw [complexProjectiveSpaceSuccTopCellMapReal] at hmem
  rw [(Submodule.mk_mem_projectivization_iff
    (complexProjectiveSpaceSuccHyperplane n)
    (complexProjectiveSpaceSuccTopCellRepresentativeReal_ne_zero n
      ⟨x, Metric.ball_subset_closedBall hx⟩))] at hmem
  have hlast :
      complexProjectiveSpaceSuccTopCellRepresentativeReal n
          ⟨x, Metric.ball_subset_closedBall hx⟩ (Fin.last (n + 1)) = 0 := by
    simpa [complexProjectiveSpaceSuccHyperplane] using hmem
  exact
    complexProjectiveSpaceSuccTopCellRepresentativeReal_last_ne_zero_of_mem_ball n hx hlast

/-- Helper for Example 10.1.12: the real-source top-cell open image already lies in the
complement of the successor hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_image_ball_subset_hyperplaneCompl
    (n : ℕ) :
    complexProjectiveSpaceSuccTopCellMapReal n '' Metric.ball 0 1 ⊆
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact complexProjectiveSpaceSuccTopCellMapReal_not_mem_hyperplane_of_mem_ball n hx

/-- Helper for Example 10.1.12: every point off the canonical hyperplane copy has a preimage in
the real top-cell open ball. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_preimageOfHyperplaneCompl
    (n : ℕ) {x : ComplexProjectiveSpace (n + 1)}
    (hx : x ∉ (complexProjectiveSpaceSuccHyperplane n).projectivization) :
    ∃ y : Fin (2 * (n + 1)) → ℝ, ∃ hy : y ∈ Metric.ball 0 1,
      complexProjectiveSpaceSuccTopCellMapReal n
        ⟨y, Metric.ball_subset_closedBall hy⟩ = x := by
  let v : Fin (n + 2) → ℂ := Projectivization.rep x
  have hv : v ≠ 0 := Projectivization.rep_nonzero x
  have hlast_ne : v (Fin.last (n + 1)) ≠ 0 := by
    -- A representative with vanishing last coordinate would place `x` back in the hyperplane.
    intro hlast
    have hmem :
        Projectivization.mk ℂ v hv ∈
          (complexProjectiveSpaceSuccHyperplane n).projectivization := by
      exact
        (Submodule.mk_mem_projectivization_iff
          (complexProjectiveSpaceSuccHyperplane n)
          hv).2 <|
          by simpa [complexProjectiveSpaceSuccHyperplane] using hlast
    exact hx <| by simpa [v] using (Projectivization.mk_rep x ▸ hmem)
  let b : ℂ := v (Fin.last (n + 1))
  let w : Fin (n + 1) → ℂ := b⁻¹ • complexProjectiveSpaceSuccHyperplaneLift n v
  let u : Fin (2 * (n + 1)) → ℝ := complexCoordinateContinuousLinearEquiv n w
  let y : Fin (2 * (n + 1)) → ℝ := OpenPartialHomeomorph.univUnitBall u
  have hy : y ∈ Metric.ball 0 1 := by
    -- The `univUnitBall` chart lands in the open ball by construction.
    simpa [y, OpenPartialHomeomorph.univUnitBall, mem_ball_zero_iff] using
      (OpenPartialHomeomorph.univUnitBall.map_source (x := u) (by simp : u ∈ Set.univ))
  let yClosed : Metric.closedBall (0 : Fin (2 * (n + 1)) → ℝ) 1 :=
    ⟨y, Metric.ball_subset_closedBall hy⟩
  let t : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  have ht_ne : t ≠ 0 := by
    -- Interior points of the unit ball have a positive inverse-radial denominator.
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]
  have hy_inv :
      (t⁻¹ : ℝ) • y = u := by
    -- `univUnitBall.left_inv` gives the exact inverse-radial formula on the real chart.
    simpa [OpenPartialHomeomorph.univUnitBall, y, u, t] using
      (OpenPartialHomeomorph.univUnitBall.left_inv (x := u) (by simp : u ∈ Set.univ))
  have hw_from_y :
      (t⁻¹ : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y = w := by
    -- Apply the inverse coordinate bridge to the radial identity and simplify.
    calc
      (t⁻¹ : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y =
          (complexCoordinateContinuousLinearEquiv n).symm ((t⁻¹ : ℝ) • y) := by
            simp
      _ = w := by
            rw [hy_inv]
            exact (complexCoordinateContinuousLinearEquiv n).left_inv w
  have hfirst :
      (complexCoordinateContinuousLinearEquiv n).symm y = t • w := by
    -- Multiply the inverse-radial identity by `t` to recover the affine coordinate itself.
    let a : Fin (n + 1) → ℂ := (complexCoordinateContinuousLinearEquiv n).symm y
    have hmul : t • ((t⁻¹ : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y) =
        (complexCoordinateContinuousLinearEquiv n).symm y := by
      change t • ((t⁻¹ : ℝ) • a) = a
      have hsmul : t • ((t⁻¹ : ℝ) • a) = ((t * t⁻¹ : ℝ)) • a := by
        simpa using (smul_smul t (t⁻¹ : ℝ) a)
      have hinv : (t * t⁻¹ : ℝ) = 1 := by
        field_simp [ht_ne]
      calc
        t • ((t⁻¹ : ℝ) • a) = ((t * t⁻¹ : ℝ)) • a := hsmul
        _ = (1 : ℝ) • a := by
              rw [hinv]
        _ = a := one_smul ℝ a
    calc
      (complexCoordinateContinuousLinearEquiv n).symm y =
          t • ((t⁻¹ : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y) := by
            exact hmul.symm
      _ = t • w := by rw [hw_from_y]
  have hfirstComplex :
      (complexCoordinateContinuousLinearEquiv n).symm y = ((t : ℂ)) • w := by
    -- Reinterpret the real scalar on the complex vector space as a complex scalar.
    simpa using hfirst
  have hb_ne : b ≠ 0 := by
    simpa [b] using hlast_ne
  have hscalar :
      (((t : ℂ) / b) • v) =
        complexProjectiveSpaceSuccTopCellRepresentativeReal n yClosed := by
    -- Compare the first `n + 1` coordinates through the affine inverse, then match the last
    -- coordinate to the square-root denominator.
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [complexProjectiveSpaceSuccTopCellRepresentativeReal, yClosed, b, t, hb_ne]
    | cast j =>
        have hfirstj :=
          congrArg (fun f : Fin (n + 1) → ℂ ↦ f j) hfirstComplex
        calc
          (((t : ℂ) / b) • v) j.castSucc = (((t : ℂ)) • w) j := by
            simp [w, b, complexProjectiveSpaceSuccHyperplaneLift, div_eq_mul_inv, mul_assoc]
          _ = ((complexCoordinateContinuousLinearEquiv n).symm y) j := by
            simpa using hfirstj.symm
          _ =
              complexProjectiveSpaceSuccTopCellRepresentativeReal n yClosed j.castSucc := by
            simp [complexProjectiveSpaceSuccTopCellRepresentativeReal, yClosed]
  refine ⟨y, hy, ?_⟩
  -- The explicit real-source representative is a nonzero scalar multiple of `Projectivization.rep x`.
  calc
    complexProjectiveSpaceSuccTopCellMapReal n yClosed =
        Projectivization.mk ℂ
          (complexProjectiveSpaceSuccTopCellRepresentativeReal n yClosed)
          (complexProjectiveSpaceSuccTopCellRepresentativeReal_ne_zero n yClosed) := by
            rfl
    _ = Projectivization.mk ℂ v hv := by
          apply
            (Projectivization.mk_eq_mk_iff' ℂ
              (complexProjectiveSpaceSuccTopCellRepresentativeReal n yClosed)
              v
              (complexProjectiveSpaceSuccTopCellRepresentativeReal_ne_zero n yClosed)
              hv).2
          exact ⟨(t : ℂ) / b, hscalar⟩
    _ = x := Projectivization.mk_rep x

/-- Helper for Example 10.1.12: the real affine top cell covers exactly the complement of the
canonical hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellMapReal_image_ball_eq_hyperplaneCompl
    (n : ℕ) :
    complexProjectiveSpaceSuccTopCellMapReal n '' Metric.ball 0 1 =
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  ext x
  constructor
  · -- The forward inclusion is the existing pointwise separation from the hyperplane.
    intro hx
    exact complexProjectiveSpaceSuccTopCellMapReal_image_ball_subset_hyperplaneCompl n hx
  · intro hx
    -- The new affine inverse on the real chart supplies the missing reverse inclusion.
    rcases complexProjectiveSpaceSuccTopCellMapReal_preimageOfHyperplaneCompl n hx with
      ⟨y, hy, rfl⟩
    refine ⟨⟨y, Metric.ball_subset_closedBall hy⟩, ?_, rfl⟩
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hy

/-- Helper for Example 10.1.12: choose the ambient real preimage of a point in the complement of
the canonical hyperplane under the real top-cell chart. -/
private noncomputable def complexProjectiveSpaceSuccTopCellMapRealPreimage (n : ℕ)
    (x : ComplexProjectiveSpace (n + 1)) :
    Fin (2 * (n + 1)) → ℝ :=
  let _ : Decidable
      (x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :=
    Classical.decPred _ x
  if hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) then
    (complexProjectiveSpaceSuccTopCellMapReal_preimageOfHyperplaneCompl n hx).choose
  else 0

/-- Helper for Example 10.1.12: the chosen ambient real preimage of a complement point lies in the
open unit ball. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball (n : ℕ)
    {x : ComplexProjectiveSpace (n + 1)}
    (hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :
    complexProjectiveSpaceSuccTopCellMapRealPreimage n x ∈ Metric.ball 0 1 := by
  -- Unfold the chosen witness from the complement-surjectivity theorem.
  simpa [complexProjectiveSpaceSuccTopCellMapRealPreimage, hx] using
    (complexProjectiveSpaceSuccTopCellMapReal_preimageOfHyperplaneCompl n hx).choose_spec.choose

/-- Helper for Example 10.1.12: the chosen ambient real preimage really maps back to the original
complement point. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealPreimage_spec (n : ℕ)
    {x : ComplexProjectiveSpace (n + 1)}
    (hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :
    complexProjectiveSpaceSuccTopCellMapReal n
        ⟨complexProjectiveSpaceSuccTopCellMapRealPreimage n x,
          Metric.ball_subset_closedBall
            (complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball n hx)⟩ =
      x := by
  -- The nested `choose_spec` stores exactly the chart equation returned by the preimage theorem.
  simpa [complexProjectiveSpaceSuccTopCellMapRealPreimage, hx] using
    (complexProjectiveSpaceSuccTopCellMapReal_preimageOfHyperplaneCompl n hx).choose_spec.choose_spec

/-- Helper for Example 10.1.12: the total ambient real top-cell chart carries the chosen preimage
back to the original complement point. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealPreimage_right_inv (n : ℕ)
    {x : ComplexProjectiveSpace (n + 1)}
    (hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :
    complexProjectiveSpaceSuccTopCellMapRealTotal n
        (complexProjectiveSpaceSuccTopCellMapRealPreimage n x) =
      x := by
  -- Rewrite the total chart back to the closed-ball chart already computed by the chosen witness.
  calc
    complexProjectiveSpaceSuccTopCellMapRealTotal n
        (complexProjectiveSpaceSuccTopCellMapRealPreimage n x) =
      complexProjectiveSpaceSuccTopCellMapReal n
        ⟨complexProjectiveSpaceSuccTopCellMapRealPreimage n x,
          Metric.ball_subset_closedBall
            (complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball n hx)⟩ := by
            symm
            exact complexProjectiveSpaceSuccTopCellMapReal_eq_total n
              ⟨complexProjectiveSpaceSuccTopCellMapRealPreimage n x,
                Metric.ball_subset_closedBall
                  (complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball n hx)⟩
    _ = x := complexProjectiveSpaceSuccTopCellMapRealPreimage_spec n hx

/-- Helper for Example 10.1.12: the ambient real top-cell chart is injective on the open unit
ball. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealTotal_injectiveOn_ball (n : ℕ) :
    Set.InjOn (complexProjectiveSpaceSuccTopCellMapRealTotal n) (Metric.ball 0 1) := by
  intro x hx y hy hxy
  let tx : ℝ := Real.sqrt (1 - ‖x‖ ^ 2)
  let ty : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  let rx := complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n x
  let ry := complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n y
  have htx_ne : tx ≠ 0 := by
    -- Interior points of the unit ball have a strictly positive radial denominator.
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg x, mem_ball_zero_iff.mp hx]
  have hty_ne : ty ≠ 0 := by
    -- The same positivity holds for the second open-ball point.
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]
  have hxy_mk :
      Projectivization.mk ℂ rx (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n x) =
        Projectivization.mk ℂ ry (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n y) := by
    -- This is just the equality of projective classes after unfolding the ambient chart.
    simpa [complexProjectiveSpaceSuccTopCellMapRealTotal, rx, ry] using hxy
  rcases
      (Projectivization.mk_eq_mk_iff' ℂ
        rx
        ry
        (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n x)
        (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n y)).1 hxy_mk with
    ⟨a, ha⟩
  have hlast :
      a * ty = tx := by
    -- Comparing the last coordinate identifies the projective scalar with the ratio of the
    -- positive radial denominators.
    have hlast' :=
      congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) ha
    simpa [rx, ry, tx, ty, complexProjectiveSpaceSuccTopCellRepresentativeRealTotal] using hlast'
  have hty_ne_complex : (ty : ℂ) ≠ 0 := by
    exact_mod_cast hty_ne
  have ha_eq_complex :
      a = (tx : ℂ) / ty := by
    -- The last-coordinate equation solves the projective scalar explicitly.
    exact (eq_div_iff hty_ne_complex).2 (by simpa [tx, ty, mul_comm] using hlast)
  have hfirst :
      a • (complexCoordinateContinuousLinearEquiv n).symm y =
        (complexCoordinateContinuousLinearEquiv n).symm x := by
    -- On the first `n + 1` coordinates, the projective scalar acts on the affine coordinate.
    ext j
    have hcoord := congrArg (fun f : Fin (n + 2) → ℂ ↦ f j.castSucc) ha
    simpa [rx, ry, complexProjectiveSpaceSuccTopCellRepresentativeRealTotal] using hcoord
  have hfirstComplex :
      ((tx : ℂ) / ty) • (complexCoordinateContinuousLinearEquiv n).symm y =
        (complexCoordinateContinuousLinearEquiv n).symm x := by
    -- The scalar from the last coordinate is actually real, so the affine coordinate identity
    -- lives over the real structure used by the coordinate equivalence.
    simpa [ha_eq_complex] using hfirst
  have hscaledSource :
      ((tx / ty : ℝ)) • y = x := by
    -- Transport the affine-coordinate identity back through the ambient real-coordinate bridge.
    have hcoord := congrArg (complexCoordinateContinuousLinearEquiv n) hfirstComplex
    have hmapReal :
        (complexCoordinateContinuousLinearEquiv n)
            (((tx / ty : ℝ)) • (complexCoordinateContinuousLinearEquiv n).symm y) =
          ((tx / ty : ℝ)) • y := by
      simpa using
        (complexCoordinateContinuousLinearEquiv n).map_smul
          (tx / ty : ℝ)
          ((complexCoordinateContinuousLinearEquiv n).symm y)
    have hcastSmul :
        (((tx / ty : ℝ)) • (complexCoordinateContinuousLinearEquiv n).symm y) =
          (((tx : ℂ) / ty) • (complexCoordinateContinuousLinearEquiv n).symm y) := by
      have hcast : ((tx : ℂ) / ty) = (((tx / ty : ℝ)) : ℂ) := by
        simp [div_eq_mul_inv]
      rw [hcast]
      rfl
    calc
      ((tx / ty : ℝ)) • y =
          (complexCoordinateContinuousLinearEquiv n)
            (((tx / ty : ℝ)) • (complexCoordinateContinuousLinearEquiv n).symm y) := by
              simpa using hmapReal.symm
      _ =
          (complexCoordinateContinuousLinearEquiv n)
            (((tx : ℂ) / ty) • (complexCoordinateContinuousLinearEquiv n).symm y) := by
              rw [hcastSmul]
      _ = x := by simpa using hcoord
  have hradial :
      (tx⁻¹ : ℝ) • x = (ty⁻¹ : ℝ) • y := by
    -- Dividing by the positive radial denominators gives the same point in the unrestricted
    -- affine chart `OpenPartialHomeomorph.univUnitBall.symm`.
    have hmul : (tx⁻¹ : ℝ) * (tx / ty) = ty⁻¹ := by
      field_simp [htx_ne, hty_ne]
    calc
      (tx⁻¹ : ℝ) • x = (tx⁻¹ : ℝ) • (((tx / ty : ℝ)) • y) := by rw [hscaledSource]
      _ = (((tx⁻¹ : ℝ) * (tx / ty : ℝ)) : ℝ) • y := by
            simp [smul_smul]
      _ = (ty⁻¹ : ℝ) • y := by rw [hmul]
  have hx_univ :
      OpenPartialHomeomorph.univUnitBall ((tx⁻¹ : ℝ) • x) = x := by
    -- The open unit ball is the target of the standard partial homeomorphism from the whole
    -- ambient real coordinate space.
    simpa [OpenPartialHomeomorph.univUnitBall, tx] using
      (OpenPartialHomeomorph.univUnitBall.right_inv (x := x) hx)
  have hy_univ :
      OpenPartialHomeomorph.univUnitBall ((ty⁻¹ : ℝ) • y) = y := by
    -- Apply the same inverse-chart identity to the second open-ball point.
    simpa [OpenPartialHomeomorph.univUnitBall, ty] using
      (OpenPartialHomeomorph.univUnitBall.right_inv (x := y) hy)
  calc
    x = OpenPartialHomeomorph.univUnitBall ((tx⁻¹ : ℝ) • x) := hx_univ.symm
    _ = OpenPartialHomeomorph.univUnitBall ((ty⁻¹ : ℝ) • y) := by rw [hradial]
    _ = y := hy_univ

/-- Helper for Example 10.1.12: on the open unit ball, the chosen ambient real preimage should
recover the original source point. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealPreimage_left_inv (n : ℕ)
    {x : Fin (2 * (n + 1)) → ℝ} (hx : x ∈ Metric.ball 0 1) :
    complexProjectiveSpaceSuccTopCellMapRealPreimage n
        (complexProjectiveSpaceSuccTopCellMapRealTotal n x) =
      x := by
  have hxTarget :
      complexProjectiveSpaceSuccTopCellMapRealTotal n x ∈
        (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))ᶜ) := by
    -- The open-ball chart already avoids the canonical hyperplane copy.
    have hxImage :
        complexProjectiveSpaceSuccTopCellMapReal n ⟨x, Metric.ball_subset_closedBall hx⟩ ∈
          (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
            (ComplexProjectiveSpace (n + 1)))ᶜ) :=
      complexProjectiveSpaceSuccTopCellMapReal_image_ball_subset_hyperplaneCompl n
        ⟨⟨x, Metric.ball_subset_closedBall hx⟩,
          by
            simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hx,
          rfl⟩
    simpa [complexProjectiveSpaceSuccTopCellMapReal_eq_total] using hxImage
  have hpreimageBall :
      complexProjectiveSpaceSuccTopCellMapRealPreimage n
          (complexProjectiveSpaceSuccTopCellMapRealTotal n x) ∈ Metric.ball 0 1 :=
    complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball n hxTarget
  have hsame :
      complexProjectiveSpaceSuccTopCellMapRealTotal n
          (complexProjectiveSpaceSuccTopCellMapRealPreimage n
            (complexProjectiveSpaceSuccTopCellMapRealTotal n x)) =
        complexProjectiveSpaceSuccTopCellMapRealTotal n x := by
    -- Both points map to the same projective point, and the preimage is already known to be in
    -- the open-ball source of the chart.
    exact complexProjectiveSpaceSuccTopCellMapRealPreimage_right_inv n hxTarget
  have hinj :
      x =
        complexProjectiveSpaceSuccTopCellMapRealPreimage n
          (complexProjectiveSpaceSuccTopCellMapRealTotal n x) :=
    complexProjectiveSpaceSuccTopCellMapRealTotal_injectiveOn_ball n
      hx
      hpreimageBall
      hsame.symm
  exact hinj.symm

/-- Helper for Example 10.1.12: the real affine top cell is now packaged as a partial
equivalence from the open Euclidean ball onto the complement of the canonical hyperplane copy. -/
private noncomputable def complexProjectiveSpaceSuccTopCellPartialEquiv (n : ℕ) :
    PartialEquiv (Fin (2 * (n + 1)) → ℝ) (ComplexProjectiveSpace (n + 1)) where
  toFun := complexProjectiveSpaceSuccTopCellMapRealTotal n
  invFun := complexProjectiveSpaceSuccTopCellMapRealPreimage n
  source := Metric.ball 0 1
  target :=
    (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
      (ComplexProjectiveSpace (n + 1)))ᶜ)
  map_source' := by
    intro x hx
    -- The open-ball image is already known to land in the complement of the hyperplane copy.
    have hxImage :
        complexProjectiveSpaceSuccTopCellMapReal n ⟨x, Metric.ball_subset_closedBall hx⟩ ∈
          (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
            (ComplexProjectiveSpace (n + 1)))ᶜ) :=
      complexProjectiveSpaceSuccTopCellMapReal_image_ball_subset_hyperplaneCompl n
        ⟨⟨x, Metric.ball_subset_closedBall hx⟩,
          by
            simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hx,
          rfl⟩
    simpa [complexProjectiveSpaceSuccTopCellMapReal_eq_total] using hxImage
  map_target' := by
    intro x hx
    -- The chosen complement preimage lies in the open unit ball by construction.
    exact complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball n hx
  left_inv' := by
    intro x hx
    -- The only remaining chart-interface gap is proving injectivity of the affine chart.
    exact complexProjectiveSpaceSuccTopCellMapRealPreimage_left_inv n hx
  right_inv' := by
    intro x hx
    -- The chosen preimage theorem already provides the right-inverse equation on the target.
    exact complexProjectiveSpaceSuccTopCellMapRealPreimage_right_inv n hx

/-- Helper for Example 10.1.12: the packaged real top-cell chart is continuous on the closed unit
ball expected by `CWComplex.mkFinite`. -/
private theorem complexProjectiveSpaceSuccTopCellPartialEquiv_continuousOn (n : ℕ) :
    ContinuousOn (complexProjectiveSpaceSuccTopCellPartialEquiv n) (Metric.closedBall 0 1) := by
  -- The packaged chart uses the globally continuous ambient extension of the real top-cell map.
  simpa [complexProjectiveSpaceSuccTopCellPartialEquiv] using
    (complexProjectiveSpaceSuccTopCellMapRealTotal_continuous n).continuousOn

/-- Helper for Example 10.1.12: the affine chart representative on the hyperplane complement uses
last coordinate `1`. -/
private def complexProjectiveSpaceSuccAffineRepresentative (n : ℕ)
    (w : Fin (n + 1) → ℂ) :
    Fin (n + 2) → ℂ :=
  Fin.snoc w 1

/-- Helper for Example 10.1.12: the affine chart representative keeps the first `n + 1`
coordinates. -/
@[simp]
private theorem complexProjectiveSpaceSuccAffineRepresentative_castSucc (n : ℕ)
    (w : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    complexProjectiveSpaceSuccAffineRepresentative n w i.castSucc = w i := by
  -- Appending the last coordinate `1` leaves the old coordinates unchanged.
  simp [complexProjectiveSpaceSuccAffineRepresentative]

/-- Helper for Example 10.1.12: the affine chart representative has last coordinate `1`. -/
@[simp]
private theorem complexProjectiveSpaceSuccAffineRepresentative_last (n : ℕ)
    (w : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccAffineRepresentative n w (Fin.last (n + 1)) = 1 := by
  -- The affine chart is normalized by fixing the last homogeneous coordinate.
  simp [complexProjectiveSpaceSuccAffineRepresentative]

/-- Helper for Example 10.1.12: the affine chart representative is never zero. -/
private theorem complexProjectiveSpaceSuccAffineRepresentative_ne_zero (n : ℕ)
    (w : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccAffineRepresentative n w ≠ 0 := by
  -- The last coordinate is always `1`.
  intro hzero
  have hlast :=
    congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) hzero
  simpa [complexProjectiveSpaceSuccAffineRepresentative] using hlast

/-- Helper for Example 10.1.12: the affine chart on the hyperplane complement of `CP^(n + 1)` is
represented by homogeneous coordinates with last entry `1`. -/
private def complexProjectiveSpaceSuccAffineTotal (n : ℕ) :
    (Fin (n + 1) → ℂ) → ComplexProjectiveSpace (n + 1) :=
  fun w ↦
    Projectivization.mk ℂ
      (complexProjectiveSpaceSuccAffineRepresentative n w)
      (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w)

/-- Helper for Example 10.1.12: the affine chart representative varies continuously with the
affine coordinates. -/
private theorem complexProjectiveSpaceSuccAffineRepresentative_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccAffineRepresentative n) := by
  -- Each old coordinate is continuous, and the appended last coordinate is constant.
  refine continuous_pi fun i ↦ ?_
  cases i using Fin.lastCases with
  | last =>
      simpa [complexProjectiveSpaceSuccAffineRepresentative] using
        (continuous_const : Continuous fun _ : Fin (n + 1) → ℂ ↦ (1 : ℂ))
  | cast j =>
      simpa [complexProjectiveSpaceSuccAffineRepresentative] using
        (continuous_apply j : Continuous fun w : Fin (n + 1) → ℂ ↦ w j)

/-- Helper for Example 10.1.12: the affine chart on the hyperplane complement is continuous. -/
private theorem complexProjectiveSpaceSuccAffineTotal_continuous (n : ℕ) :
    Continuous (complexProjectiveSpaceSuccAffineTotal n) := by
  -- Lift the affine representative into the nonzero-vector subtype and descend through the
  -- projectivization quotient.
  let representative :
      (Fin (n + 1) → ℂ) → { v : Fin (n + 2) → ℂ // v ≠ 0 } :=
    fun w ↦
      ⟨complexProjectiveSpaceSuccAffineRepresentative n w,
        complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w⟩
  have hRepresentative : Continuous representative := by
    exact
      (complexProjectiveSpaceSuccAffineRepresentative_continuous n).subtype_mk
        (fun w ↦ (representative w).2)
  simpa [complexProjectiveSpaceSuccAffineTotal, representative, Projectivization.mk'_eq_mk] using
    (continuous_quotient_mk'.comp hRepresentative)

/-- Helper for Example 10.1.12: the affine chart avoids the canonical hyperplane because its last
homogeneous coordinate is nonzero. -/
private theorem complexProjectiveSpaceSuccAffineTotal_not_mem_hyperplane (n : ℕ)
    (w : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccAffineTotal n w ∉
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- Membership in the hyperplane projectivization would force the last coordinate to vanish.
  intro hmem
  rw [complexProjectiveSpaceSuccAffineTotal] at hmem
  rw [(Submodule.mk_mem_projectivization_iff
    (complexProjectiveSpaceSuccHyperplane n)
    (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w))] at hmem
  have hlast :
      complexProjectiveSpaceSuccAffineRepresentative n w (Fin.last (n + 1)) = 0 := by
    simpa [complexProjectiveSpaceSuccHyperplane] using hmem
  norm_num at hlast

/-- Helper for Example 10.1.12: each complement point has affine coordinates with last
homogeneous coordinate normalized to `1`. -/
private theorem complexProjectiveSpaceSuccAffineTotal_preimageOfHyperplaneCompl
    (n : ℕ) {x : ComplexProjectiveSpace (n + 1)}
    (hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :
    ∃ w : Fin (n + 1) → ℂ, complexProjectiveSpaceSuccAffineTotal n w = x := by
  let v : Fin (n + 2) → ℂ := Projectivization.rep x
  have hv : v ≠ 0 := Projectivization.rep_nonzero x
  have hlast_ne : v (Fin.last (n + 1)) ≠ 0 := by
    -- A representative with vanishing last coordinate would place `x` back in the hyperplane.
    intro hlast
    have hmem :
        Projectivization.mk ℂ v hv ∈
          (complexProjectiveSpaceSuccHyperplane n).projectivization := by
      exact
        (Submodule.mk_mem_projectivization_iff
          (complexProjectiveSpaceSuccHyperplane n)
          hv).2 <|
          by simpa [complexProjectiveSpaceSuccHyperplane] using hlast
    exact hx <| by simpa [v] using (Projectivization.mk_rep x ▸ hmem)
  let b : ℂ := v (Fin.last (n + 1))
  let w : Fin (n + 1) → ℂ := b⁻¹ • complexProjectiveSpaceSuccHyperplaneLift n v
  have hb_ne : b ≠ 0 := by
    simpa [b] using hlast_ne
  have hscalar :
      ((b⁻¹ : ℂ) • v) = complexProjectiveSpaceSuccAffineRepresentative n w := by
    -- Dividing by the nonzero last coordinate normalizes the representative into affine form.
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [complexProjectiveSpaceSuccAffineRepresentative, b, hb_ne]
    | cast j =>
        simp [complexProjectiveSpaceSuccAffineRepresentative, w, b,
          complexProjectiveSpaceSuccHyperplaneLift, smul_smul]
  refine ⟨w, ?_⟩
  -- The normalized affine representative is projectively equivalent to `Projectivization.rep x`.
  calc
    complexProjectiveSpaceSuccAffineTotal n w =
        Projectivization.mk ℂ
          (complexProjectiveSpaceSuccAffineRepresentative n w)
          (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w) := by
            rfl
    _ = Projectivization.mk ℂ v hv := by
          apply
            (Projectivization.mk_eq_mk_iff' ℂ
              (complexProjectiveSpaceSuccAffineRepresentative n w)
              v
              (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w)
              hv).2
          exact ⟨(b⁻¹ : ℂ), hscalar⟩
    _ = x := Projectivization.mk_rep x

/-- Helper for Example 10.1.12: the affine chart covers exactly the complement of the canonical
hyperplane copy. -/
private theorem complexProjectiveSpaceSuccAffineTotal_range_eq_hyperplaneCompl
    (n : ℕ) :
    Set.range (complexProjectiveSpaceSuccAffineTotal n) =
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact complexProjectiveSpaceSuccAffineTotal_not_mem_hyperplane n w
  · intro hx
    rcases complexProjectiveSpaceSuccAffineTotal_preimageOfHyperplaneCompl n hx with ⟨w, hw⟩
    exact ⟨w, hw⟩

/-- Helper for Example 10.1.12: the affine normalization divides a nonzero representative by its
last coordinate. -/
private def complexProjectiveSpaceSuccAffineNormalize (n : ℕ)
    (v : { w : Fin (n + 2) → ℂ // w ≠ 0 }) :
    Fin (n + 1) → ℂ :=
  ((v.1 (Fin.last (n + 1)))⁻¹ : ℂ) • complexProjectiveSpaceSuccHyperplaneLift n v.1

/-- Helper for Example 10.1.12: normalizing an affine-form representative recovers the original
affine coordinates. -/
@[simp]
private theorem complexProjectiveSpaceSuccAffineNormalize_rep (n : ℕ)
    (w : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccAffineNormalize n
        ⟨complexProjectiveSpaceSuccAffineRepresentative n w,
          complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w⟩ =
      w := by
  -- The affine chart already has last coordinate `1`, so normalization is trivial.
  ext i
  simp [complexProjectiveSpaceSuccAffineNormalize, complexProjectiveSpaceSuccHyperplaneLift,
    complexProjectiveSpaceSuccAffineRepresentative]

/-- Helper for Example 10.1.12: affine normalization is continuous on the locus where the last
homogeneous coordinate is nonzero. -/
private theorem complexProjectiveSpaceSuccAffineNormalize_continuousOn (n : ℕ) :
    ContinuousOn
      (complexProjectiveSpaceSuccAffineNormalize n)
      { v : { w : Fin (n + 2) → ℂ // w ≠ 0 } | v.1 (Fin.last (n + 1)) ≠ 0 } := by
  -- Divide the first coordinates by the last coordinate on the open set where that denominator is
  -- nonzero.
  let lastCoord :
      { w : Fin (n + 2) → ℂ // w ≠ 0 } → ℂ :=
    fun v ↦ v.1 (Fin.last (n + 1))
  have hlastCoord : Continuous lastCoord := by
    simpa [lastCoord] using
      (continuous_apply (Fin.last (n + 1))).comp continuous_subtype_val
  have hLift : Continuous fun v : { w : Fin (n + 2) → ℂ // w ≠ 0 } ↦
      complexProjectiveSpaceSuccHyperplaneLift n v.1 := by
    refine continuous_pi fun i ↦ ?_
    simpa [complexProjectiveSpaceSuccHyperplaneLift] using
      (continuous_apply i.castSucc).comp continuous_subtype_val
  have hInv :
      ContinuousOn
        (fun v : { w : Fin (n + 2) → ℂ // w ≠ 0 } ↦ (lastCoord v)⁻¹)
        { v : { w : Fin (n + 2) → ℂ // w ≠ 0 } | v.1 (Fin.last (n + 1)) ≠ 0 } := by
    exact hlastCoord.continuousOn.inv₀ fun v hv ↦ hv
  simpa [complexProjectiveSpaceSuccAffineNormalize, lastCoord] using hInv.smul hLift.continuousOn

/-- Helper for Example 10.1.12: pulling back an affine-chart image along projectivization exactly
records the nonzero last coordinate and the normalized affine coordinates. -/
private theorem complexProjectiveSpaceSuccAffineImagePreimage_eq (n : ℕ)
    (U : Set (Fin (n + 1) → ℂ)) :
    (Projectivization.mk' ℂ) ⁻¹' (complexProjectiveSpaceSuccAffineTotal n '' U) =
      { v : { w : Fin (n + 2) → ℂ // w ≠ 0 } |
          v.1 (Fin.last (n + 1)) ≠ 0 ∧ complexProjectiveSpaceSuccAffineNormalize n v ∈ U } := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨w, hwU, hwv⟩
    have hwv' :
        Projectivization.mk ℂ v.1 v.2 =
          Projectivization.mk ℂ
            (complexProjectiveSpaceSuccAffineRepresentative n w)
            (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w) := by
      simpa [complexProjectiveSpaceSuccAffineTotal, Projectivization.mk'_eq_mk] using hwv.symm
    rcases
        (Projectivization.mk_eq_mk_iff' ℂ
          v.1
          (complexProjectiveSpaceSuccAffineRepresentative n w)
          v.2
          (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w)).1 hwv' with
      ⟨a, ha⟩
    have hlast :
        a = v.1 (Fin.last (n + 1)) := by
      have hlast' := congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) ha
      simpa [complexProjectiveSpaceSuccAffineRepresentative] using hlast'
    have hvlast :
        v.1 (Fin.last (n + 1)) ≠ 0 := by
      intro hzero
      have hvzero : v.1 = 0 := by
        simpa [hlast, hzero] using ha.symm
      exact v.2 hvzero
    have hnormalize :
        complexProjectiveSpaceSuccAffineNormalize n v = w := by
      -- Comparing the first coordinates of the projective equality recovers the affine
      -- normalization formula.
      ext i
      have hcoord := congrArg (fun f : Fin (n + 2) → ℂ ↦ f i.castSucc) ha
      have hcoord' :
          v.1 i.castSucc = v.1 (Fin.last (n + 1)) * w i := by
        simpa [hlast, complexProjectiveSpaceSuccAffineRepresentative] using hcoord.symm
      calc
        complexProjectiveSpaceSuccAffineNormalize n v i =
            ((v.1 (Fin.last (n + 1)))⁻¹ : ℂ) * v.1 i.castSucc := by
              simp [complexProjectiveSpaceSuccAffineNormalize,
                complexProjectiveSpaceSuccHyperplaneLift]
        _ = ((v.1 (Fin.last (n + 1)))⁻¹ : ℂ) *
              (v.1 (Fin.last (n + 1)) * w i) := by
                rw [hcoord']
        _ = w i := by
              field_simp [hvlast]
    exact ⟨hvlast, hnormalize ▸ hwU⟩
  · rintro ⟨hvlast, hvU⟩
    refine ⟨complexProjectiveSpaceSuccAffineNormalize n v, hvU, ?_⟩
    have hEq :
        Projectivization.mk ℂ v.1 v.2 =
          complexProjectiveSpaceSuccAffineTotal n (complexProjectiveSpaceSuccAffineNormalize n v) := by
      -- Scaling the normalized affine representative by the last homogeneous coordinate returns
      -- the original nonzero representative.
      apply
        (Projectivization.mk_eq_mk_iff' ℂ
          v.1
          (complexProjectiveSpaceSuccAffineRepresentative n
            (complexProjectiveSpaceSuccAffineNormalize n v))
          v.2
          (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n
            (complexProjectiveSpaceSuccAffineNormalize n v))).2
      refine ⟨v.1 (Fin.last (n + 1)), ?_⟩
      ext i
      cases i using Fin.lastCases with
      | last =>
          simp [complexProjectiveSpaceSuccAffineRepresentative]
      | cast j =>
          have hcoord :
              v.1 (Fin.last (n + 1)) *
                  ((((v.1 (Fin.last (n + 1)))⁻¹ : ℂ) •
                      complexProjectiveSpaceSuccHyperplaneLift n v.1) j) =
                v.1 j.castSucc := by
            simp [complexProjectiveSpaceSuccHyperplaneLift, hvlast, mul_assoc]
          simpa [complexProjectiveSpaceSuccAffineRepresentative,
            complexProjectiveSpaceSuccAffineNormalize,
            complexProjectiveSpaceSuccHyperplaneLift, mul_assoc] using hcoord
    simpa [complexProjectiveSpaceSuccAffineTotal, Projectivization.mk'_eq_mk] using hEq.symm

/-- Helper for Example 10.1.12: the affine chart is an open map because quotient-open sets on
projectivization are detected on the saturated nonzero-representative locus. -/
private theorem complexProjectiveSpaceSuccAffineTotal_isOpenMap (n : ℕ) :
    IsOpenMap (complexProjectiveSpaceSuccAffineTotal n) := by
  intro U hU
  have hOpenLast :
      IsOpen
        { v : { w : Fin (n + 2) → ℂ // w ≠ 0 } |
            v.1 (Fin.last (n + 1)) ≠ 0 } := by
    -- The nonvanishing last-coordinate locus is an open complement of a closed singleton
    -- preimage.
    let lastCoord :
        { w : Fin (n + 2) → ℂ // w ≠ 0 } → ℂ :=
      fun v ↦ v.1 (Fin.last (n + 1))
    have hlastCoord : Continuous lastCoord := by
      simpa [lastCoord] using
        (continuous_apply (Fin.last (n + 1))).comp continuous_subtype_val
    have hClosedZero :
        IsClosed (lastCoord ⁻¹' ({0} : Set ℂ)) :=
      (isClosed_singleton : IsClosed (({0} : Set ℂ))).preimage hlastCoord
    have hOpenLastCoord :
        IsOpen { v : { w : Fin (n + 2) → ℂ // w ≠ 0 } | ¬ lastCoord v = 0 } :=
      hClosedZero.isOpen_compl
    simpa [lastCoord] using hOpenLastCoord
  have hpreimageOpen :
      IsOpen ((Projectivization.mk' ℂ) ⁻¹' (complexProjectiveSpaceSuccAffineTotal n '' U)) := by
    rw [complexProjectiveSpaceSuccAffineImagePreimage_eq]
    -- On the last-coordinate-nonzero locus, openness reduces to continuity of affine
    -- normalization.
    exact
      (complexProjectiveSpaceSuccAffineNormalize_continuousOn n).isOpen_inter_preimage
        hOpenLast hU
  exact isQuotientMap_quotient_mk'.isOpen_preimage.mp hpreimageOpen

/-- Helper for Example 10.1.12: the affine chart is injective because the last homogeneous
coordinate of every affine representative is `1`. -/
private theorem complexProjectiveSpaceSuccAffineTotal_injective (n : ℕ) :
    Function.Injective (complexProjectiveSpaceSuccAffineTotal n) := by
  intro w₁ w₂ hEq
  have hEq' :
      Projectivization.mk ℂ
          (complexProjectiveSpaceSuccAffineRepresentative n w₁)
          (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w₁) =
        Projectivization.mk ℂ
          (complexProjectiveSpaceSuccAffineRepresentative n w₂)
          (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w₂) := by
    simpa [complexProjectiveSpaceSuccAffineTotal] using hEq
  rcases
      (Projectivization.mk_eq_mk_iff' ℂ
        (complexProjectiveSpaceSuccAffineRepresentative n w₁)
        (complexProjectiveSpaceSuccAffineRepresentative n w₂)
        (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w₁)
        (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w₂)).1 hEq' with
    ⟨a, ha⟩
  have ha_eq : a = 1 := by
    have hlast := congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) ha
    simpa [complexProjectiveSpaceSuccAffineRepresentative] using hlast
  ext i
  have hcoord := congrArg (fun f : Fin (n + 2) → ℂ ↦ f i.castSucc) ha
  simpa [complexProjectiveSpaceSuccAffineRepresentative, ha_eq] using hcoord.symm

/-- Helper for Example 10.1.12: choose affine coordinates on the hyperplane complement. -/
private noncomputable def complexProjectiveSpaceSuccAffinePreimage (n : ℕ)
    (x : ComplexProjectiveSpace (n + 1)) :
    Fin (n + 1) → ℂ :=
  let _ : Decidable
      (x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :=
    Classical.decPred _ x
  if hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) then
    (complexProjectiveSpaceSuccAffineTotal_preimageOfHyperplaneCompl n hx).choose
  else 0

/-- Helper for Example 10.1.12: the chosen affine preimage maps back to the original complement
point. -/
private theorem complexProjectiveSpaceSuccAffinePreimage_right_inv (n : ℕ)
    {x : ComplexProjectiveSpace (n + 1)}
    (hx :
      x ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ)) :
    complexProjectiveSpaceSuccAffineTotal n
        (complexProjectiveSpaceSuccAffinePreimage n x) =
      x := by
  -- Unfold the chosen affine witness from the complement-surjectivity theorem.
  simpa [complexProjectiveSpaceSuccAffinePreimage, hx] using
    (complexProjectiveSpaceSuccAffineTotal_preimageOfHyperplaneCompl n hx).choose_spec

/-- Helper for Example 10.1.12: the chosen affine preimage is a left inverse to the affine chart.
-/
private theorem complexProjectiveSpaceSuccAffinePreimage_left_inv (n : ℕ) :
    Function.LeftInverse
      (complexProjectiveSpaceSuccAffinePreimage n)
      (complexProjectiveSpaceSuccAffineTotal n) := by
  intro w
  -- Both affine coordinates map to the same complement point, so injectivity recovers the
  -- original source point.
  exact (complexProjectiveSpaceSuccAffineTotal_injective n) <|
    complexProjectiveSpaceSuccAffinePreimage_right_inv n <|
      complexProjectiveSpaceSuccAffineTotal_not_mem_hyperplane n w

/-- Helper for Example 10.1.12: the chosen affine inverse is continuous on the hyperplane
complement. -/
private theorem complexProjectiveSpaceSuccAffinePreimage_continuousOn (n : ℕ) :
    ContinuousOn
      (complexProjectiveSpaceSuccAffinePreimage n)
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  -- The open affine chart has a continuous inverse on its range.
  simpa [complexProjectiveSpaceSuccAffineTotal_range_eq_hyperplaneCompl n] using
    (complexProjectiveSpaceSuccAffineTotal_isOpenMap n).continuousOn_range_of_leftInverse
      (complexProjectiveSpaceSuccAffinePreimage_left_inv n)

/-- Helper for Example 10.1.12: the real top-cell chart is the affine chart preceded by the
ambient ball homeomorphism and the fixed complex-to-real coordinate equivalence. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealTotal_eq_affineTotal (n : ℕ)
    (w : Fin (n + 1) → ℂ) :
    complexProjectiveSpaceSuccTopCellMapRealTotal n
        (OpenPartialHomeomorph.univUnitBall
          (complexCoordinateContinuousLinearEquiv n w)) =
      complexProjectiveSpaceSuccAffineTotal n w := by
  let u : Fin (2 * (n + 1)) → ℝ := complexCoordinateContinuousLinearEquiv n w
  let y : Fin (2 * (n + 1)) → ℝ := OpenPartialHomeomorph.univUnitBall u
  let t : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)
  have hy :
      y ∈ Metric.ball (0 : Fin (2 * (n + 1)) → ℝ) 1 := by
    simpa [y, OpenPartialHomeomorph.univUnitBall, mem_ball_zero_iff] using
      (OpenPartialHomeomorph.univUnitBall.map_source (x := u) (by simp : u ∈ Set.univ))
  have ht_ne : t ≠ 0 := by
    -- Interior points of the unit ball have nonzero inverse-radial denominator.
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]
  have hy_inv :
      (t⁻¹ : ℝ) • y = u := by
    -- `univUnitBall.left_inv` gives the inverse-radial formula on the ambient real ball.
    simpa [OpenPartialHomeomorph.univUnitBall, y, u, t] using
      (OpenPartialHomeomorph.univUnitBall.left_inv (x := u) (by simp : u ∈ Set.univ))
  have hfirst :
      (complexCoordinateContinuousLinearEquiv n).symm y = t • w := by
    -- Multiply the inverse-radial identity by `t` and transport it across the coordinate bridge.
    have hcoord :
        (t⁻¹ : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y = w := by
      calc
        (t⁻¹ : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y =
            (complexCoordinateContinuousLinearEquiv n).symm ((t⁻¹ : ℝ) • y) := by
              simp
        _ = w := by
              rw [hy_inv]
              exact (complexCoordinateContinuousLinearEquiv n).left_inv w
    let a : Fin (n + 1) → ℂ := (complexCoordinateContinuousLinearEquiv n).symm y
    have hmul : (t * t⁻¹ : ℝ) = 1 := by
      field_simp [ht_ne]
    calc
      (complexCoordinateContinuousLinearEquiv n).symm y =
          (1 : ℝ) • (complexCoordinateContinuousLinearEquiv n).symm y := by
            exact (one_smul ℝ ((complexCoordinateContinuousLinearEquiv n).symm y)).symm
      _ = ((t * t⁻¹ : ℝ)) • a := by
            rw [hmul]
      _ = t • ((t⁻¹ : ℝ) • a) := by
            simpa [a] using (smul_smul t (t⁻¹ : ℝ) a).symm
      _ = t • w := by
            simpa [a] using congrArg (fun z : Fin (n + 1) → ℂ ↦ t • z) hcoord
      _ = t • w := by rfl
  have hscalar :
      ((t : ℂ) • complexProjectiveSpaceSuccAffineRepresentative n w) =
        complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n y := by
    -- The real-source representative differs from the affine representative by the nonzero scalar
    -- `t`.
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [complexProjectiveSpaceSuccAffineRepresentative,
          complexProjectiveSpaceSuccTopCellRepresentativeRealTotal, y, t]
    | cast j =>
        have hfirstj :=
          congrArg (fun f : Fin (n + 1) → ℂ ↦ f j) (by simpa using hfirst)
        simpa [complexProjectiveSpaceSuccAffineRepresentative,
          complexProjectiveSpaceSuccTopCellRepresentativeRealTotal] using hfirstj.symm
  calc
    complexProjectiveSpaceSuccTopCellMapRealTotal n
        (OpenPartialHomeomorph.univUnitBall (complexCoordinateContinuousLinearEquiv n w)) =
      Projectivization.mk ℂ
        (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n y)
        (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n y) := by
          rfl
    _ =
      Projectivization.mk ℂ
        (complexProjectiveSpaceSuccAffineRepresentative n w)
        (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w) := by
          apply
            (Projectivization.mk_eq_mk_iff' ℂ
              (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal n y)
              (complexProjectiveSpaceSuccAffineRepresentative n w)
              (complexProjectiveSpaceSuccTopCellRepresentativeRealTotal_ne_zero n y)
              (complexProjectiveSpaceSuccAffineRepresentative_ne_zero n w)).2
          exact ⟨(t : ℂ), hscalar⟩
    _ = complexProjectiveSpaceSuccAffineTotal n w := by
          rfl

/-- Helper for Example 10.1.12: on the hyperplane complement, the chosen real inverse is the
fixed ball homeomorphism applied to the continuous affine inverse. -/
private theorem complexProjectiveSpaceSuccTopCellMapRealPreimage_eq_affinePreimage (n : ℕ) :
    Set.EqOn
      (complexProjectiveSpaceSuccTopCellMapRealPreimage n)
      (fun x ↦
        OpenPartialHomeomorph.univUnitBall
          (complexCoordinateContinuousLinearEquiv n
            (complexProjectiveSpaceSuccAffinePreimage n x)))
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  intro x hx
  have hexplicitBall :
      OpenPartialHomeomorph.univUnitBall
          (complexCoordinateContinuousLinearEquiv n
            (complexProjectiveSpaceSuccAffinePreimage n x)) ∈
        Metric.ball (0 : Fin (2 * (n + 1)) → ℝ) 1 := by
    simpa [OpenPartialHomeomorph.univUnitBall] using
      (OpenPartialHomeomorph.univUnitBall.map_source
        (x := complexCoordinateContinuousLinearEquiv n
          (complexProjectiveSpaceSuccAffinePreimage n x))
        (by simp : complexCoordinateContinuousLinearEquiv n
          (complexProjectiveSpaceSuccAffinePreimage n x) ∈ Set.univ))
  have hchooseBall :
      complexProjectiveSpaceSuccTopCellMapRealPreimage n x ∈
        Metric.ball (0 : Fin (2 * (n + 1)) → ℝ) 1 :=
    complexProjectiveSpaceSuccTopCellMapRealPreimage_mem_ball n hx
  have hexplicitMap :
      complexProjectiveSpaceSuccTopCellMapRealTotal n
          (OpenPartialHomeomorph.univUnitBall
            (complexCoordinateContinuousLinearEquiv n
              (complexProjectiveSpaceSuccAffinePreimage n x))) =
        x := by
    calc
      complexProjectiveSpaceSuccTopCellMapRealTotal n
          (OpenPartialHomeomorph.univUnitBall
            (complexCoordinateContinuousLinearEquiv n
              (complexProjectiveSpaceSuccAffinePreimage n x))) =
        complexProjectiveSpaceSuccAffineTotal n
          (complexProjectiveSpaceSuccAffinePreimage n x) :=
            complexProjectiveSpaceSuccTopCellMapRealTotal_eq_affineTotal n
              (complexProjectiveSpaceSuccAffinePreimage n x)
      _ = x := complexProjectiveSpaceSuccAffinePreimage_right_inv n hx
  have hchooseMap :
      complexProjectiveSpaceSuccTopCellMapRealTotal n
          (complexProjectiveSpaceSuccTopCellMapRealPreimage n x) =
        x :=
    complexProjectiveSpaceSuccTopCellMapRealPreimage_right_inv n hx
  exact
    complexProjectiveSpaceSuccTopCellMapRealTotal_injectiveOn_ball n
      hchooseBall hexplicitBall (hchooseMap.trans hexplicitMap.symm)

/-- Helper for Example 10.1.12: the inverse of the packaged real top-cell chart should be
continuous on the complement of the canonical hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellPartialEquiv_continuousOnSymm (n : ℕ) :
    ContinuousOn
      (complexProjectiveSpaceSuccTopCellPartialEquiv n).symm
      (complexProjectiveSpaceSuccTopCellPartialEquiv n).target := by
  -- Route correction: the real `if`/`choose` inverse has been reduced to the affine inverse on
  -- the hyperplane complement via
  -- `complexProjectiveSpaceSuccTopCellMapRealPreimage_eq_affinePreimage`.
  refine (continuousOn_congr (complexProjectiveSpaceSuccTopCellMapRealPreimage_eq_affinePreimage n)).2 ?_
  -- Compose the continuous affine inverse with the fixed coordinate equivalence and the standard
  -- unit-ball homeomorphism.
  have hcoordCont :
      ContinuousOn
        (fun x ↦ complexCoordinateContinuousLinearEquiv n
          (complexProjectiveSpaceSuccAffinePreimage n x))
        (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))ᶜ) :=
    (complexCoordinateContinuousLinearEquiv n).continuous.comp_continuousOn
      (complexProjectiveSpaceSuccAffinePreimage_continuousOn n)
  exact
    OpenPartialHomeomorph.univUnitBall.continuousOn.comp hcoordCont
      (fun _ _ ↦ by trivial)

/-- Helper for Example 10.1.12: the closed real top-cell image, together with the canonical
hyperplane copy, already covers all of `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccHyperplane_union_realTopCell_closedBall_eq_univ
    (n : ℕ) :
    (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1))) ∪
      complexProjectiveSpaceSuccTopCellMapReal n '' Metric.closedBall 0 1) =
      Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    by_cases hx :
        x ∈ ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))
    · exact Or.inl hx
    · have hxCompl :
          x ∈ complexProjectiveSpaceSuccTopCellMapReal n '' Metric.ball 0 1 := by
        rw [complexProjectiveSpaceSuccTopCellMapReal_image_ball_eq_hyperplaneCompl n]
        exact hx
      rcases hxCompl with ⟨y, hy, rfl⟩
      -- Promote the open-ball witness to the closed-ball image required by the CW constructor.
      refine Or.inr ⟨⟨y, Metric.ball_subset_closedBall hy⟩, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using (Metric.ball_subset_closedBall hy)

/-- Helper for Example 10.1.12: each cell family in a chosen standard CW structure on `CP^n` is
finite. -/
private theorem complexProjectiveCWStructure_cellFinite
    {n : ℕ} (S : ComplexProjectiveCWStructure n) (k : ℕ) :
    letI := S.cwComplex
    Finite (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) k) := by
  letI := S.cwComplex
  by_cases hk : 2 * n < k
  · -- Cells above dimension `2n` are absent by hypothesis.
    letI := S.highCellEmpty k hk
    exact Finite.of_subsingleton
  · have hk' : k ≤ 2 * n := le_of_not_gt hk
    by_cases hodd : Odd k
    · rcases hodd with ⟨m, rfl⟩
      -- Odd-dimensional cells are absent in every degree.
      letI := S.oddCellEmpty m
      exact Finite.of_subsingleton
    · have heven : Even k := by
        rcases Nat.even_or_odd k with hkEven | hkOdd
        · exact hkEven
        · exact False.elim (hodd hkOdd)
      rcases heven with ⟨m, rfl⟩
      have hm : m ≤ n := by
        omega
      have hUnique :
          Unique (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (m + m)) := by
        simpa [two_mul] using S.evenCellUnique m hm
      letI := hUnique
      exact Finite.of_fintype _

/-- Helper for Example 10.1.12: a chosen standard CW structure on `CP^n` has no cells above
dimension `2n`, hence its cell family is eventually empty. -/
private theorem complexProjectiveCWStructure_cell_eventuallyIsEmpty
    {n : ℕ} (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ᶠ k in Filter.atTop,
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) k) := by
  letI := S.cwComplex
  rw [Filter.eventually_atTop]
  refine ⟨2 * n + 1, ?_⟩
  intro k hk
  exact S.highCellEmpty k (lt_of_lt_of_le (Nat.lt_succ_self (2 * n)) hk)

/-- Helper for Example 10.1.12: once the cell family of `CP^n` has no cells above dimension
`2n`, every skeleton at or above `2n` is already all of `CP^n`. -/
private theorem complexProjectiveCWStructure_skeleton_eq_univ_of_top_le
    {n : ℕ} (S : ComplexProjectiveCWStructure n) {q : ℕ∞}
    (hq : (2 * n : ℕ∞) ≤ q) :
    letI := S.cwComplex
    (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q :
        Set (ComplexProjectiveSpace n)) =
      (Set.univ : Set (ComplexProjectiveSpace n)) := by
  letI := S.cwComplex
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hUnion :
        (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
          S.cwComplex.map m j '' Metric.closedBall 0 1) =
          (Set.univ : Set (ComplexProjectiveSpace n)) := by
      simpa [Topology.CWComplex.closedCell] using
        (Topology.CWComplex.union (C := (Set.univ : Set (ComplexProjectiveSpace n))))
    have hxUnion :
        x ∈ ⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
          S.cwComplex.map m j '' Metric.closedBall 0 1 := by
      rw [hUnion]
      simp
    rcases Set.mem_iUnion.1 hxUnion with ⟨m, hxUnion⟩
    rcases Set.mem_iUnion.1 hxUnion with ⟨j, hxUnion⟩
    have hmTop : m ≤ 2 * n := by
      by_contra hmTop
      letI := S.highCellEmpty m (lt_of_not_ge hmTop)
      exact
        (inferInstance :
          IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)).false j
    have hmq : (m : ℕ∞) ≤ q := le_trans (by exact_mod_cast hmTop) hq
    rcases hxUnion with ⟨u, hu, rfl⟩
    have hClosed :
        S.cwComplex.map m j u ∈
          Topology.CWComplex.closedCell
            (C := (Set.univ : Set (ComplexProjectiveSpace n)))
            m j := by
      exact ⟨u, hu, rfl⟩
    have hSkeleton :
        S.cwComplex.map m j u ∈
          (Topology.CWComplex.skeleton
            (Set.univ : Set (ComplexProjectiveSpace n)) (m : ℕ∞) :
              Set (ComplexProjectiveSpace n)) :=
      Topology.CWComplex.closedCell_subset_skeleton
        (C := (Set.univ : Set (ComplexProjectiveSpace n))) m j hClosed
    exact
      Topology.CWComplex.skeleton_mono
        (C := (Set.univ : Set (ComplexProjectiveSpace n))) hmq hSkeleton

/-- Helper for Example 10.1.12: the successor cell family reuses every inherited cell of `CP^n`
and adds one new top cell in degree `2 * (n + 1)`. -/
private abbrev complexProjectiveSpaceSuccCell (n : ℕ) (S : ComplexProjectiveCWStructure n)
    (m : ℕ) :=
  letI := S.cwComplex
  Sum (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)
    (PLift (m = 2 * (n + 1)))

/-- Helper for Example 10.1.12: each degree of the successor cell family is finite. -/
private theorem complexProjectiveSpaceSuccCell_finite (n : ℕ)
    (S : ComplexProjectiveCWStructure n) (m : ℕ) :
    letI := S.cwComplex
    Finite (complexProjectiveSpaceSuccCell n S m) := by
  letI := S.cwComplex
  letI :
      Finite (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m) :=
    complexProjectiveCWStructure_cellFinite S m
  infer_instance

/-- Helper for Example 10.1.12: above the new top degree `2 * (n + 1)`, the successor cell family
is empty. -/
private theorem complexProjectiveSpaceSuccCell_eventuallyIsEmpty (n : ℕ)
    (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ᶠ m in Filter.atTop, IsEmpty (complexProjectiveSpaceSuccCell n S m) := by
  letI := S.cwComplex
  rw [Filter.eventually_atTop]
  refine ⟨2 * (n + 1) + 1, ?_⟩
  intro m hm
  have hInherited :
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m) :=
    S.highCellEmpty m (by omega)
  have hTop : IsEmpty (PLift (m = 2 * (n + 1))) := by
    refine ⟨fun h ↦ ?_⟩
    exact (Nat.ne_of_gt (by omega)) h.down
  letI := hInherited
  letI := hTop
  infer_instance

/-- Helper for Example 10.1.12: above the new top degree `2 * (n + 1)`, the successor cell family
has no cells at all. -/
private theorem complexProjectiveSpaceSuccCell_isEmpty_of_high (n : ℕ)
    (S : ComplexProjectiveCWStructure n) (m : ℕ) (hm : 2 * (n + 1) < m) :
    letI := S.cwComplex
    IsEmpty (complexProjectiveSpaceSuccCell n S m) := by
  letI := S.cwComplex
  -- Both the inherited summand and the new top summand disappear above the top degree.
  have hInherited :
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m) :=
    S.highCellEmpty m (by omega)
  have hTop : IsEmpty (PLift (m = 2 * (n + 1))) := by
    refine ⟨fun h ↦ ?_⟩
    exact (Nat.ne_of_gt hm) h.down
  letI := hInherited
  letI := hTop
  infer_instance

/-- Helper for Example 10.1.12: the successor cell family still has no odd-dimensional cells. -/
private theorem complexProjectiveSpaceSuccCell_oddIsEmpty (n : ℕ)
    (S : ComplexProjectiveCWStructure n) (m : ℕ) :
    letI := S.cwComplex
    IsEmpty (complexProjectiveSpaceSuccCell n S (2 * m + 1)) := by
  letI := S.cwComplex
  -- The inherited odd cell is empty, and the new top cell only appears in an even degree.
  have hInherited :
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m + 1)) :=
    S.oddCellEmpty m
  have hTop : IsEmpty (PLift (2 * m + 1 = 2 * (n + 1))) := by
    refine ⟨fun h ↦ ?_⟩
    have hEq : 2 * m + 1 = 2 * (n + 1) := h.down
    omega
  letI := hInherited
  letI := hTop
  infer_instance

/-- Helper for Example 10.1.12: the successor cell family still has exactly one even cell in each
degree `2 * m` with `m ≤ n + 1`. -/
private theorem complexProjectiveSpaceSuccCell_evenCard_eq_one (n : ℕ)
    (S : ComplexProjectiveCWStructure n) (m : ℕ) (hm : m ≤ n + 1) :
    letI := S.cwComplex
    Nat.card (complexProjectiveSpaceSuccCell n S (2 * m)) = 1 := by
  letI := S.cwComplex
  rcases lt_or_eq_of_le hm with hm_lt | rfl
  · -- Below the top degree, only the inherited even cell survives.
    have hInheritedUnique :
        Unique (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) := by
      simpa using S.evenCellUnique m (Nat.le_of_lt_succ hm_lt)
    have hInheritedCard :
        Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨hInheritedUnique.default, hInheritedUnique.uniq⟩
    have hTop : IsEmpty (PLift (2 * m = 2 * (n + 1))) := by
      refine ⟨fun h ↦ ?_⟩
      have hEq : 2 * m = 2 * (n + 1) := h.down
      omega
    calc
      Nat.card (complexProjectiveSpaceSuccCell n S (2 * m)) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) +
            Nat.card (PLift (2 * m = 2 * (n + 1))) := by
              simpa [complexProjectiveSpaceSuccCell] using
                (Nat.card_sum :
                  Nat.card
                      ((Topology.CWComplex.cell
                          (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) ⊕
                        PLift (2 * m = 2 * (n + 1))) =
                    Nat.card (Topology.CWComplex.cell
                      (Set.univ : Set (ComplexProjectiveSpace n)) (2 * m)) +
                      Nat.card (PLift (2 * m = 2 * (n + 1))))
      _ = 1 + 0 := by
            have hTopCard : Nat.card (PLift (2 * m = 2 * (n + 1))) = 0 := by
              letI := hTop
              simpa using
                (Nat.card_of_isEmpty : Nat.card (PLift (2 * m = 2 * (n + 1))) = 0)
            rw [hInheritedCard, hTopCard]
      _ = 1 := by norm_num
  · -- In the top degree, the inherited summand vanishes and the new top cell is unique.
    have hInherited :
        IsEmpty (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n))
          (2 * (n + 1))) :=
      S.highCellEmpty (2 * (n + 1)) (by omega)
    have hInheritedCard :
        Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n))
          (2 * (n + 1))) = 0 := by
      letI := hInherited
      simpa using
        (Nat.card_of_isEmpty :
          Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n))
            (2 * (n + 1))) = 0)
    have hTopCard : Nat.card (PLift (2 * (n + 1) = 2 * (n + 1))) = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨rfl⟩, by
        intro x
        cases x
        rfl⟩
    calc
      Nat.card (complexProjectiveSpaceSuccCell n S (2 * (n + 1))) =
          Nat.card (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n))
              (2 * (n + 1))) +
            Nat.card (PLift (2 * (n + 1) = 2 * (n + 1))) := by
              simpa [complexProjectiveSpaceSuccCell] using
                (Nat.card_sum :
                  Nat.card
                      ((Topology.CWComplex.cell
                          (Set.univ : Set (ComplexProjectiveSpace n)) (2 * (n + 1))) ⊕
                        PLift (2 * (n + 1) = 2 * (n + 1))) =
                    Nat.card (Topology.CWComplex.cell
                      (Set.univ : Set (ComplexProjectiveSpace n)) (2 * (n + 1))) +
                      Nat.card (PLift (2 * (n + 1) = 2 * (n + 1))))
      _ = 0 + 1 := by
            rw [hInheritedCard, hTopCard]
      _ = 1 := by norm_num

/-- Helper for Example 10.1.12: the successor even-dimensional cell family is already in the
`Unique` form required by the structure field. -/
private noncomputable abbrev complexProjectiveSpaceSuccCell_evenUnique
    (n : ℕ) (S : ComplexProjectiveCWStructure n) (m : ℕ) (hm : m ≤ n + 1) :
    letI := S.cwComplex
    Unique (complexProjectiveSpaceSuccCell n S (2 * m)) := by
  letI := S.cwComplex
  -- Upgrade the proven cardinality-one statement to the canonical unique-cell interface.
  let hUnique :
      Subsingleton (complexProjectiveSpaceSuccCell n S (2 * m)) ∧
        Nonempty (complexProjectiveSpaceSuccCell n S (2 * m)) :=
    Nat.card_eq_one_iff_unique.mp (complexProjectiveSpaceSuccCell_evenCard_eq_one n S m hm)
  exact
    { default := Classical.choice hUnique.2
      uniq := fun a ↦ hUnique.1.elim a (Classical.choice hUnique.2) }

/-- Helper for Example 10.1.12: a point of the complex attaching sphere canonically gives a point
of the corresponding closed unit ball. -/
private theorem complexProjectiveAttachingSphere_mem_closedBall (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    z.1 ∈ Metric.closedBall (0 : Fin (n + 1) → ℂ) 1 := by
  -- The sphere equation `‖z‖ = 1` immediately implies the closed-ball bound `‖z‖ ≤ 1`.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (mem_sphere_zero_iff_norm.mp z.2).le

/-- Helper for Example 10.1.12: the complex attaching sphere includes into the corresponding
closed unit ball. -/
private def complexProjectiveAttachingSphereToClosedBall (n : ℕ) :
    ComplexProjectiveAttachingSphere n →
      Metric.closedBall (0 : Fin (n + 1) → ℂ) 1 :=
  fun z ↦ ⟨z.1, complexProjectiveAttachingSphere_mem_closedBall n z⟩

/-- Helper for Example 10.1.12: the explicit successor top-cell representative appends the
square-root coordinate to a point of the complex closed unit ball. -/
private def complexProjectiveSpaceSuccTopCellRepresentative (n : ℕ)
    (z : Metric.closedBall (0 : Fin (n + 1) → ℂ) 1) :
    Fin (n + 2) → ℂ :=
  Fin.snoc z.1 (Real.sqrt (1 - ‖z.1‖ ^ 2))

/-- Helper for Example 10.1.12: the successor top-cell representative agrees with the original
vector on the first `n + 1` coordinates. -/
@[simp]
private theorem complexProjectiveSpaceSuccTopCellRepresentative_castSucc (n : ℕ)
    (z : Metric.closedBall (0 : Fin (n + 1) → ℂ) 1) (i : Fin (n + 1)) :
    complexProjectiveSpaceSuccTopCellRepresentative n z i.castSucc = z.1 i := by
  -- The appended representative keeps the old coordinates unchanged.
  simp [complexProjectiveSpaceSuccTopCellRepresentative]

/-- Helper for Example 10.1.12: the last coordinate of the successor top-cell representative is
the square-root term. -/
@[simp]
private theorem complexProjectiveSpaceSuccTopCellRepresentative_last (n : ℕ)
    (z : Metric.closedBall (0 : Fin (n + 1) → ℂ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentative n z (Fin.last (n + 1)) =
      Real.sqrt (1 - ‖z.1‖ ^ 2) := by
  -- The appended final coordinate is exactly the square-root term.
  simp [complexProjectiveSpaceSuccTopCellRepresentative]

/-- Helper for Example 10.1.12: the explicit successor top-cell representative is never zero. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentative_ne_zero (n : ℕ)
    (z : Metric.closedBall (0 : Fin (n + 1) → ℂ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentative n z ≠ 0 := by
  -- If the appended vector were zero, then the original coordinates would all vanish, forcing the
  -- last coordinate to be `1`, a contradiction.
  intro hzero
  have hz0 : z.1 = 0 := by
    ext i
    have hcoord :=
      congrArg (fun f : Fin (n + 2) → ℂ ↦ f i.castSucc) hzero
    simpa using hcoord
  have hlast :=
    congrArg (fun f : Fin (n + 2) → ℂ ↦ f (Fin.last (n + 1))) hzero
  have hone : (1 : ℂ) = 0 := by
    simpa [hz0] using hlast
  norm_num at hone

/-- Helper for Example 10.1.12: the complex-model top cell for `CP^(n + 1)` is obtained by
projectivizing the explicit successor representative on the closed unit ball. -/
private def complexProjectiveSpaceSuccTopCellMapComplex (n : ℕ) :
    Metric.closedBall (0 : Fin (n + 1) → ℂ) 1 →
      ComplexProjectiveSpace (n + 1) :=
  fun z ↦
    Projectivization.mk ℂ
      (complexProjectiveSpaceSuccTopCellRepresentative n z)
      (complexProjectiveSpaceSuccTopCellRepresentative_ne_zero n z)

/-- Helper for Example 10.1.12: on the boundary sphere, the explicit top-cell representative
collapses to the zero-extension representative. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentative_boundary_eq (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    complexProjectiveSpaceSuccTopCellRepresentative n
        (complexProjectiveAttachingSphereToClosedBall n z) =
      complexProjectiveSpaceSuccLinearMap n z.1 := by
  -- The sphere equation forces the square-root coordinate to vanish, leaving only zero-extension.
  ext i
  cases i using Fin.lastCases with
  | last =>
      have hz1 : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
      have hz1' :
          ‖(complexProjectiveAttachingSphereToClosedBall n z).1‖ = 1 := by
        simpa [complexProjectiveAttachingSphereToClosedBall] using hz1
      simp [complexProjectiveSpaceSuccTopCellRepresentative, hz1']
  | cast j =>
      simp [complexProjectiveAttachingSphereToClosedBall]

/-- Helper for Example 10.1.12: on the boundary sphere, the complex-model top cell agrees with the
standard projective zero-extension of the attaching map. -/
private theorem complexProjectiveSpaceSuccTopCellMapComplex_boundary_eq (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    complexProjectiveSpaceSuccTopCellMapComplex n
        (complexProjectiveAttachingSphereToClosedBall n z) =
      complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) := by
  -- After the square-root coordinate vanishes, both sides are the same projective class of the
  -- zero-extended boundary representative.
  rw [complexProjectiveSpaceAttachingMap_eq_mk]
  simp [complexProjectiveSpaceSuccTopCellMapComplex,
    complexProjectiveSpaceSuccTopCellRepresentative_boundary_eq]

/-- Helper for Example 10.1.12: an interior point of the complex closed ball has nonzero
square-root coordinate in the explicit top-cell representative. -/
private theorem complexProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball (n : ℕ)
    {z : Fin (n + 1) → ℂ} (hz : z ∈ Metric.ball (0 : Fin (n + 1) → ℂ) 1) :
    complexProjectiveSpaceSuccTopCellRepresentative n
        ⟨z, Metric.ball_subset_closedBall hz⟩ (Fin.last (n + 1)) ≠ 0 := by
  -- The open-ball inequality makes `1 - ‖z‖^2` strictly positive, so its square root is nonzero.
  have hz' : ‖z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hz
  have hsqrt : Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg z]
  simpa [complexProjectiveSpaceSuccTopCellRepresentative] using hsqrt

/-- Helper for Example 10.1.12: the complex top-cell model sends the open unit ball into the
complement of the successor hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellMapComplex_not_mem_hyperplane_of_mem_ball
    (n : ℕ) {z : Fin (n + 1) → ℂ} (hz : z ∈ Metric.ball (0 : Fin (n + 1) → ℂ) 1) :
    complexProjectiveSpaceSuccTopCellMapComplex n ⟨z, Metric.ball_subset_closedBall hz⟩ ∉
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- Membership in the projectivized hyperplane would force the last coordinate of the explicit
  -- representative to vanish, contradicting the open-ball computation above.
  intro hmem
  rw [complexProjectiveSpaceSuccTopCellMapComplex] at hmem
  rw [(Submodule.mk_mem_projectivization_iff
    (complexProjectiveSpaceSuccHyperplane n)
    (complexProjectiveSpaceSuccTopCellRepresentative_ne_zero n
      ⟨z, Metric.ball_subset_closedBall hz⟩))] at hmem
  have hlast :
      complexProjectiveSpaceSuccTopCellRepresentative n
          ⟨z, Metric.ball_subset_closedBall hz⟩ (Fin.last (n + 1)) = 0 := by
    simpa [complexProjectiveSpaceSuccHyperplane] using hmem
  exact
    complexProjectiveSpaceSuccTopCellRepresentative_last_ne_zero_of_mem_ball n hz hlast

/-- Helper for Example 10.1.12: the boundary sphere of the complex top cell lands in the canonical
hyperplane copy of `CP^n` inside `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccTopCellMapComplex_mem_hyperplane_on_boundary (n : ℕ)
    (z : ComplexProjectiveAttachingSphere n) :
    complexProjectiveSpaceSuccTopCellMapComplex n
        (complexProjectiveAttachingSphereToClosedBall n z) ∈
      (complexProjectiveSpaceSuccHyperplane n).projectivization := by
  -- On the boundary, the explicit top cell is exactly the projective zero-extension map.
  rw [complexProjectiveSpaceSuccTopCellMapComplex_boundary_eq]
  exact complexProjectiveSpaceSuccInclusion_mem_hyperplaneProjectivization n
    (complexProjectiveSpaceAttachingMap n z)

/-- Helper for Example 10.1.12: every point off the canonical hyperplane copy has a preimage in
the complex top-cell open ball. -/
private theorem complexProjectiveSpaceSuccTopCellMapComplex_preimageOfHyperplaneCompl
    (n : ℕ) {x : ComplexProjectiveSpace (n + 1)}
    (hx : x ∉ (complexProjectiveSpaceSuccHyperplane n).projectivization) :
    ∃ z : Fin (n + 1) → ℂ, ∃ hz : z ∈ Metric.ball 0 1,
      complexProjectiveSpaceSuccTopCellMapComplex n
        ⟨z, Metric.ball_subset_closedBall hz⟩ = x := by
  let v : Fin (n + 2) → ℂ := Projectivization.rep x
  have hv : v ≠ 0 := Projectivization.rep_nonzero x
  have hlast_ne : v (Fin.last (n + 1)) ≠ 0 := by
    -- A representative in the hyperplane would force `x` back into the excluded lower stratum.
    intro hlast
    have hmem :
        Projectivization.mk ℂ v hv ∈
          (complexProjectiveSpaceSuccHyperplane n).projectivization := by
      exact
        (Submodule.mk_mem_projectivization_iff
          (complexProjectiveSpaceSuccHyperplane n)
          hv).2 <|
          by simpa [complexProjectiveSpaceSuccHyperplane] using hlast
    exact hx <| by simpa [v] using (Projectivization.mk_rep x ▸ hmem)
  let b : ℂ := v (Fin.last (n + 1))
  let w : Fin (n + 1) → ℂ := b⁻¹ • complexProjectiveSpaceSuccHyperplaneLift n v
  let z : Fin (n + 1) → ℂ := (((Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ : ℝ) : ℂ) • w
  have hz : z ∈ Metric.ball 0 1 := by
    -- The standard affine-chart normalization lands in the open unit ball.
    have hpos : 0 < 1 + ‖w‖ ^ 2 := by positivity
    rw [show z = ((((Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ : ℝ) : ℂ) • w) by rfl]
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      ← _root_.div_eq_inv_mul,
      div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr hpos), ← abs_norm w, ← sq_lt_sq,
      abs_norm, Real.sq_sqrt hpos.le]
    exact lt_one_add _
  let zClosed : Metric.closedBall (0 : Fin (n + 1) → ℂ) 1 :=
    ⟨z, Metric.ball_subset_closedBall hz⟩
  let t : ℝ := Real.sqrt (1 - ‖z‖ ^ 2)
  have ht_ne : t ≠ 0 := by
    -- Interior points of the unit ball have a positive square-root denominator for the inverse
    -- affine chart.
    apply Real.sqrt_ne_zero'.mpr
    nlinarith [norm_nonneg z, mem_ball_zero_iff.mp hz]
  have hz_inv :
      (t⁻¹ : ℝ) • z = w := by
    -- The standard `univUnitBall` inverse formula recovers the affine coordinate from `z`.
    simpa [OpenPartialHomeomorph.univUnitBall, z, w, t] using
      (OpenPartialHomeomorph.univUnitBall.left_inv (x := w) (by simp : w ∈ Set.univ))
  have hz_scalar :
      z = t • w := by
    -- Rewriting the inverse formula solves for `z` as a scalar multiple of the affine coordinate.
    have hmul : t * t⁻¹ = (1 : ℝ) := by
      field_simp [ht_ne]
    calc
      z = (1 : ℝ) • z := (one_smul ℝ z).symm
      _ = (t * t⁻¹) • z := by rw [hmul]
      _ = t • (t⁻¹ • z) := by simpa using (smul_smul t (t⁻¹) z).symm
      _ = t • w := by rw [hz_inv]
  have hz_scalar_complex :
      z = ((t : ℂ)) • w := by
    simpa using hz_scalar
  have hb_ne : b ≠ 0 := by
    simpa [b] using hlast_ne
  have hfirst :
      (((t : ℂ) / b) • complexProjectiveSpaceSuccHyperplaneLift n v) = z := by
    -- The first `n + 1` coordinates of the top-cell representative are the normalized affine
    -- coordinates obtained from the hyperplane lift.
    calc
      (((t : ℂ) / b) • complexProjectiveSpaceSuccHyperplaneLift n v) =
          ((t : ℂ)) • w := by
            simp [w, b, div_eq_mul_inv, smul_smul, mul_assoc]
      _ = z := hz_scalar_complex.symm
  have hscalar :
      (((t : ℂ) / b) • v) =
        complexProjectiveSpaceSuccTopCellRepresentative n zClosed := by
    -- Compare the first `n + 1` coordinates through `hfirst`, and the last coordinate directly.
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [complexProjectiveSpaceSuccTopCellRepresentative, zClosed, b, t, hb_ne]
    | cast j =>
        have hfirstj :=
          congrArg (fun f : Fin (n + 1) → ℂ ↦ f j) hfirst
        simpa [complexProjectiveSpaceSuccTopCellRepresentative, zClosed, b] using hfirstj
  refine ⟨z, hz, ?_⟩
  -- The explicit representative is a nonzero scalar multiple of `Projectivization.rep x`.
  calc
    complexProjectiveSpaceSuccTopCellMapComplex n zClosed =
        Projectivization.mk ℂ
          (complexProjectiveSpaceSuccTopCellRepresentative n zClosed)
          (complexProjectiveSpaceSuccTopCellRepresentative_ne_zero n zClosed) := by
            rfl
    _ = Projectivization.mk ℂ v hv := by
          apply
            (Projectivization.mk_eq_mk_iff' ℂ
              (complexProjectiveSpaceSuccTopCellRepresentative n zClosed)
              v
              (complexProjectiveSpaceSuccTopCellRepresentative_ne_zero n zClosed)
              hv).2
          exact ⟨(t : ℂ) / b, hscalar⟩
    _ = x := Projectivization.mk_rep x

/-- Helper for Example 10.1.12: the complex top-cell open image lies in the complement of the
canonical hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellMapComplex_image_ball_subset_hyperplaneCompl
    (n : ℕ) :
    complexProjectiveSpaceSuccTopCellMapComplex n '' Metric.ball 0 1 ⊆
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  -- Any open-ball point is excluded from the hyperplane by the explicit nonzero last coordinate.
  exact complexProjectiveSpaceSuccTopCellMapComplex_not_mem_hyperplane_of_mem_ball n hz

/-- Helper for Example 10.1.12: the complex affine top cell covers exactly the complement of the
canonical hyperplane copy. -/
private theorem complexProjectiveSpaceSuccTopCellMapComplex_image_ball_eq_hyperplaneCompl
    (n : ℕ) :
    complexProjectiveSpaceSuccTopCellMapComplex n '' Metric.ball 0 1 =
      (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) := by
  ext x
  constructor
  · -- The forward inclusion is the existing pointwise separation from the hyperplane.
    intro hx
    exact complexProjectiveSpaceSuccTopCellMapComplex_image_ball_subset_hyperplaneCompl n hx
  · intro hx
    -- Route correction: the remaining work now starts after the complex complement is covered;
    -- what still blocks the constructor is transporting this affine chart to the real CW source.
    rcases complexProjectiveSpaceSuccTopCellMapComplex_preimageOfHyperplaneCompl n hx with
      ⟨z, hz, rfl⟩
    refine ⟨⟨z, Metric.ball_subset_closedBall hz⟩, ?_, rfl⟩
    -- The ambient open-ball witness is exactly the subtype open-ball witness after coercion.
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hz

/-- Helper for Example 10.1.12: the closed complex top-cell image, together with the canonical
hyperplane copy, already covers all of `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccHyperplane_union_complexTopCell_closedBall_eq_univ
    (n : ℕ) :
    (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1))) ∪
      complexProjectiveSpaceSuccTopCellMapComplex n '' Metric.closedBall 0 1) =
      Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    by_cases hx :
        x ∈ ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))
    · exact Or.inl hx
    · have hxCompl :
          x ∈ complexProjectiveSpaceSuccTopCellMapComplex n '' Metric.ball 0 1 := by
        rw [complexProjectiveSpaceSuccTopCellMapComplex_image_ball_eq_hyperplaneCompl n]
        exact hx
      rcases hxCompl with ⟨z, hz, rfl⟩
      -- Promote the open-ball witness to the closed-ball image required by the CW constructor.
      refine Or.inr ⟨⟨z, Metric.ball_subset_closedBall hz⟩, ?_, rfl⟩
      -- The ambient closed-ball bound transports directly to the subtype closed ball.
      simpa [Metric.mem_closedBall, dist_zero_right] using (Metric.ball_subset_closedBall hz)

/-- Helper for Example 10.1.12: the union of the ambientized inherited closed cells is exactly the
canonical hyperplane copy inside `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccInheritedClosedCellUnion
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j '' Metric.closedBall 0 1) =
      ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1))) := by
  letI := S.cwComplex
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.1 hy with ⟨m, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨j, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    -- Forgetting the hyperplane subtype still leaves a point of the hyperplane copy.
    change
      (((complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j x :
            ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
              (ComplexProjectiveSpace (n + 1)))) :
          ComplexProjectiveSpace (n + 1)) ∈
        ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1))))
    simp
  · intro hy
    let x : ComplexProjectiveSpace n :=
      (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n).symm ⟨y, hy⟩
    have hOldUnion :
        (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
          S.cwComplex.map m j '' Metric.closedBall 0 1) =
          (Set.univ : Set (ComplexProjectiveSpace n)) := by
      simpa [Topology.CWComplex.closedCell] using
        (Topology.CWComplex.union (C := (Set.univ : Set (ComplexProjectiveSpace n))))
    have hx :
        x ∈ ⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
          S.cwComplex.map m j '' Metric.closedBall 0 1 := by
      -- The old CW complex already covers `CP^n` by its closed cells.
      rw [hOldUnion]
      simp [x]
    rcases Set.mem_iUnion.1 hx with ⟨m, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨j, hx⟩
    rcases hx with ⟨u, hu, hu_eq⟩
    refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    refine ⟨u, hu, ?_⟩
    -- Apply the hyperplane homeomorphism to the inherited closed-cell witness.
    have hsub :
        complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j u = ⟨y, hy⟩ := by
      calc
        complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j u =
            (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n)
              (S.cwComplex.map m j u) := by
                simpa using complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply
                  n S (j := j) (x := u)
        _ = (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n) x := by
              rw [hu_eq]
        _ = ⟨y, hy⟩ := by
              exact (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n).apply_symm_apply
                ⟨y, hy⟩
    change
      (((complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j u :
            ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
              (ComplexProjectiveSpace (n + 1)))) :
          ComplexProjectiveSpace (n + 1)) = y)
    exact congrArg Subtype.val hsub

/-- Helper for Example 10.1.12: ambientizing the inherited open cells preserves the pairwise
disjointness already present in the lower-dimensional CW structure. -/
private theorem complexProjectiveSpaceSuccInheritedOpenCell_pairwiseDisjoint
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    (Set.univ :
      Set (Σ m, Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)).PairwiseDisjoint
        (fun mj ↦
          complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S mj.2 '' Metric.ball 0 1) := by
  letI := S.cwComplex
  intro a _ b _ hab
  -- Pull an ambient intersection back across the hyperplane homeomorphism to the old open cells.
  refine Set.disjoint_left.2 ?_
  intro y hyA hyB
  rcases hyA with ⟨xA, hxA, hA⟩
  rcases hyB with ⟨xB, hxB, hB⟩
  have hsubEq :
      complexProjectiveSpaceSuccHyperplaneTransportCellMap n S a.2 xA =
        complexProjectiveSpaceSuccHyperplaneTransportCellMap n S b.2 xB := by
    apply Subtype.ext
    calc
      (((complexProjectiveSpaceSuccHyperplaneTransportCellMap n S a.2 xA :
            ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
              (ComplexProjectiveSpace (n + 1)))) :
          ComplexProjectiveSpace (n + 1))) = y := by
            simpa using hA
      _ =
          (((complexProjectiveSpaceSuccHyperplaneTransportCellMap n S b.2 xB :
              ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
                (ComplexProjectiveSpace (n + 1)))) :
            ComplexProjectiveSpace (n + 1))) := by
              simpa using hB.symm
  have hOldEq :
      S.cwComplex.map a.1 a.2 xA = S.cwComplex.map b.1 b.2 xB := by
    exact
      (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n).injective <|
        by
          simpa [complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply] using hsubEq
  have hdisj :=
    S.cwComplex.pairwiseDisjoint'
      (show a ∈ (Set.univ :
        Set (Σ m, Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)) by simp)
      (show b ∈ (Set.univ :
        Set (Σ m, Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)) by simp)
      hab
  have hmemA :
      S.cwComplex.map b.1 b.2 xB ∈ S.cwComplex.map a.1 a.2 '' Metric.ball 0 1 := by
    exact ⟨xA, hxA, hOldEq⟩
  have hmemB :
      S.cwComplex.map b.1 b.2 xB ∈ S.cwComplex.map b.1 b.2 '' Metric.ball 0 1 := by
    exact ⟨xB, hxB, rfl⟩
  exact Set.disjoint_left.1 hdisj hmemA hmemB

/-- Helper for Example 10.1.12: every inherited open cell stays disjoint from the new real top
cell because the former lies in the canonical hyperplane and the latter in its complement. -/
private theorem complexProjectiveSpaceSuccInheritedOpenCell_disjoint_realTopCell
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ {m : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
      Disjoint
        (complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j '' Metric.ball 0 1)
        (complexProjectiveSpaceSuccTopCellMapReal n '' Metric.ball 0 1) := by
  letI := S.cwComplex
  intro m j
  refine Set.disjoint_left.2 ?_
  intro y hyInherited hyTop
  have hyHyperplane :
      y ∈ ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1))) := by
    rcases hyInherited with ⟨x, hx, rfl⟩
    -- The inherited open cells are ambientized from the hyperplane subtype.
    change
      (((complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j x :
            ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
              (ComplexProjectiveSpace (n + 1)))) :
          ComplexProjectiveSpace (n + 1)) ∈
        ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1))))
    simp
  have hyCompl :
      y ∈ (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
        (ComplexProjectiveSpace (n + 1)))ᶜ) :=
    complexProjectiveSpaceSuccTopCellMapReal_image_ball_subset_hyperplaneCompl n hyTop
  exact hyCompl hyHyperplane

/-- Helper for Example 10.1.12: the real top-cell boundary already lands in the union of the
ambientized inherited closed cells, once that inherited stratum is identified with the hyperplane
copy of `CP^n`. -/
private theorem complexProjectiveSpaceSuccTopCellBoundary_mapsToInheritedClosedCells
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    Set.MapsTo
      (fun x : Metric.sphere (0 : Fin (2 * (n + 1)) → ℝ) 1 ↦
        complexProjectiveSpaceSuccTopCellMapReal n (complexCoordinateUnitSphereToClosedBall n x))
      Set.univ
      (⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m),
        complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j '' Metric.closedBall 0 1) := by
  letI := S.cwComplex
  intro x hx
  -- First land on the hyperplane boundary copy, then rewrite that stratum as the inherited
  -- closed-cell union.
  rw [complexProjectiveSpaceSuccInheritedClosedCellUnion n S]
  exact complexProjectiveSpaceSuccTopCellMapReal_mem_hyperplane_on_boundary n x

/-- Helper for Example 10.1.12: the successor cell family uses the inherited ambientized cell maps
in lower degrees and the packaged real top-cell chart in the new top degree. -/
private noncomputable def complexProjectiveSpaceSuccCellMap (n : ℕ)
    (S : ComplexProjectiveCWStructure n) (m : ℕ) :
    letI := S.cwComplex
    complexProjectiveSpaceSuccCell n S m →
      PartialEquiv (Fin m → ℝ) (ComplexProjectiveSpace (n + 1))
  | Sum.inl j => complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j
  | Sum.inr h =>
      show PartialEquiv (Fin m → ℝ) (ComplexProjectiveSpace (n + 1)) from
        h.down ▸ complexProjectiveSpaceSuccTopCellPartialEquiv n

/-- Helper for Example 10.1.12: on the open unit ball, the packaged top-cell partial equivalence
has the same image as the real-source top-cell chart. -/
private theorem complexProjectiveSpaceSuccTopCellPartialEquiv_image_ball (n : ℕ) :
    complexProjectiveSpaceSuccTopCellPartialEquiv n '' Metric.ball 0 1 =
      complexProjectiveSpaceSuccTopCellMapReal n '' Metric.ball 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Repackage the ambient open-ball point as a subtype point of the closed ball.
    refine ⟨⟨x, Metric.ball_subset_closedBall hx⟩, ?_, ?_⟩
    · simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hx
    · exact complexProjectiveSpaceSuccTopCellMapReal_eq_total n
        ⟨x, Metric.ball_subset_closedBall hx⟩
  · rintro ⟨x, hx, rfl⟩
    -- Forget the subtype witness to recover the ambient open-ball point.
    refine ⟨x.1, ?_, ?_⟩
    · simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hx
    · symm
      exact complexProjectiveSpaceSuccTopCellMapReal_eq_total n x

/-- Helper for Example 10.1.12: on the closed unit ball, the packaged top-cell partial
equivalence has the same image as the real-source top-cell chart. -/
private theorem complexProjectiveSpaceSuccTopCellPartialEquiv_image_closedBall (n : ℕ) :
    complexProjectiveSpaceSuccTopCellPartialEquiv n '' Metric.closedBall 0 1 =
      complexProjectiveSpaceSuccTopCellMapReal n '' Metric.closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Repackage the ambient closed-ball point as a point of the closed-ball subtype.
    refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, Subtype.dist_eq, dist_zero_right] using hx
    · exact complexProjectiveSpaceSuccTopCellMapReal_eq_total n ⟨x, hx⟩
  · rintro ⟨x, hx, rfl⟩
    -- Forget the subtype witness to recover the ambient closed-ball point.
    refine ⟨x.1, ?_, ?_⟩
    · exact x.2
    · symm
      exact complexProjectiveSpaceSuccTopCellMapReal_eq_total n x

/-- Helper for Example 10.1.12: the packaged top summand of the successor cell family has the
same open-ball image as the real top-cell chart. -/
private theorem complexProjectiveSpaceSuccCellMap_topImage_ball
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    complexProjectiveSpaceSuccCellMap n S (2 * (n + 1)) (Sum.inr ⟨rfl⟩) '' Metric.ball 0 1 =
      complexProjectiveSpaceSuccTopCellMapReal n '' Metric.ball 0 1 := by
  letI := S.cwComplex
  -- The top summand is definitionally the packaged top partial equivalence, so the existing
  -- open-image normalization applies directly.
  simpa [complexProjectiveSpaceSuccCellMap] using
    complexProjectiveSpaceSuccTopCellPartialEquiv_image_ball n

/-- Helper for Example 10.1.12: the successor cell family already has pairwise disjoint open
cells once the inherited hyperplane cells and the new top cell are packaged together. -/
private theorem complexProjectiveSpaceSuccCellMap_pairwiseDisjoint
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    (Set.univ : Set (Σ m, complexProjectiveSpaceSuccCell n S m)).PairwiseDisjoint
      (fun mj ↦ complexProjectiveSpaceSuccCellMap n S mj.1 mj.2 '' Metric.ball 0 1) := by
  letI := S.cwComplex
  intro a _ b _ hab
  rcases a with ⟨ma, a⟩
  rcases b with ⟨mb, b⟩
  cases a with
  | inl ja =>
      cases b with
      | inl jb =>
          -- Two inherited cells reduce directly to the predecessor open-cell disjointness.
          have habInherited :
              (Sigma.mk ma ja :
                Σ m, Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m) ≠
                  Sigma.mk mb jb := by
            intro hEq
            apply hab
            cases hEq
            rfl
          simpa [complexProjectiveSpaceSuccCellMap] using
            (complexProjectiveSpaceSuccInheritedOpenCell_pairwiseDisjoint n S
              (show Sigma.mk ma ja ∈
                (Set.univ : Set (Σ m,
                  Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)) by simp)
              (show Sigma.mk mb jb ∈
                (Set.univ : Set (Σ m,
                  Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)) by simp)
              habInherited)
      | inr hb =>
          -- In the mixed case, normalize the packaged top branch to the real top-cell image.
          rcases hb with ⟨hb⟩
          subst hb
          change Disjoint
            (complexProjectiveSpaceSuccCellMap n S ma (Sum.inl ja) '' Metric.ball 0 1)
            (complexProjectiveSpaceSuccCellMap n S (2 * (n + 1)) (Sum.inr ⟨rfl⟩) ''
              Metric.ball 0 1)
          rw [complexProjectiveSpaceSuccCellMap_topImage_ball n S]
          simpa [complexProjectiveSpaceSuccCellMap] using
            complexProjectiveSpaceSuccInheritedOpenCell_disjoint_realTopCell n S ja
  | inr ha =>
      cases b with
      | inl jb =>
          -- The opposite mixed case is the same disjointness statement with the factors swapped.
          rcases ha with ⟨ha⟩
          subst ha
          change Disjoint
            (complexProjectiveSpaceSuccCellMap n S (2 * (n + 1)) (Sum.inr ⟨rfl⟩) ''
              Metric.ball 0 1)
            (complexProjectiveSpaceSuccCellMap n S mb (Sum.inl jb) '' Metric.ball 0 1)
          rw [complexProjectiveSpaceSuccCellMap_topImage_ball n S]
          simpa [complexProjectiveSpaceSuccCellMap] using
            (complexProjectiveSpaceSuccInheritedOpenCell_disjoint_realTopCell n S jb).symm
      | inr hb =>
          -- The top summand is unique, so distinct sigma-indices cannot both be top cells.
          rcases ha with ⟨ha⟩
          rcases hb with ⟨hb⟩
          subst ha
          subst hb
          exact False.elim (hab rfl)

/-- Helper for Example 10.1.12: the successor closed cells already cover all of `CP^(n + 1)` once
the inherited hyperplane stratum and the new top cell are combined. -/
private theorem complexProjectiveSpaceSuccCellMap_union
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    (⋃ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
      complexProjectiveSpaceSuccCellMap n S m j '' Metric.closedBall 0 1) =
      (Set.univ : Set (ComplexProjectiveSpace (n + 1))) := by
  letI := S.cwComplex
  have hdecomp :
      (⋃ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
        complexProjectiveSpaceSuccCellMap n S m j '' Metric.closedBall 0 1) =
        (⋃ (m : ℕ) (j : Topology.CWComplex.cell
            (Set.univ : Set (ComplexProjectiveSpace n)) m),
          complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j '' Metric.closedBall 0 1) ∪
          complexProjectiveSpaceSuccTopCellMapReal n '' Metric.closedBall 0 1 := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨m, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨j, hx⟩
      cases j with
      | inl j =>
          -- Inherited closed-cell witnesses stay on the inherited side of the union.
          exact Or.inl <|
            Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨j, by
              simpa [complexProjectiveSpaceSuccCellMap] using hx⟩⟩
      | inr h =>
          -- The top summand is exactly the real closed top cell after re-subtyping the witness.
          cases h with
          | up hm =>
              subst hm
              rcases hx with ⟨u, hu, rfl⟩
              refine Or.inr ⟨⟨u, hu⟩, ?_, ?_⟩
              · simpa [Metric.mem_closedBall, Subtype.dist_eq, dist_zero_right] using hu
              · exact complexProjectiveSpaceSuccTopCellMapReal_eq_total n ⟨u, hu⟩
    · rintro (hx | hx)
      · rcases Set.mem_iUnion.1 hx with ⟨m, hx⟩
        rcases Set.mem_iUnion.1 hx with ⟨j, hx⟩
        refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨Sum.inl j, ?_⟩⟩
        -- The inherited branch of the successor cell family is literally the ambientized old cell.
        simpa [complexProjectiveSpaceSuccCellMap] using hx
      · rcases hx with ⟨u, hu, hx⟩
        refine Set.mem_iUnion.2 ⟨2 * (n + 1), Set.mem_iUnion.2 ⟨Sum.inr ⟨rfl⟩, ?_⟩⟩
        refine ⟨u.1, u.2, ?_⟩
        -- Forgetting the subtype witness turns the real closed top cell back into the ambient map
        -- used by the successor cell family.
        simpa [complexProjectiveSpaceSuccCellMap] using
          (complexProjectiveSpaceSuccTopCellMapReal_eq_total n u).symm.trans hx
  -- Rewrite the inherited side as the hyperplane copy and finish with the existing cover theorem.
  calc
    (⋃ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
      complexProjectiveSpaceSuccCellMap n S m j '' Metric.closedBall 0 1) =
        (⋃ (m : ℕ) (j : Topology.CWComplex.cell
            (Set.univ : Set (ComplexProjectiveSpace n)) m),
          complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j '' Metric.closedBall 0 1) ∪
          complexProjectiveSpaceSuccTopCellMapReal n '' Metric.closedBall 0 1 := hdecomp
    _ =
        (((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1))) ∪
          complexProjectiveSpaceSuccTopCellMapReal n '' Metric.closedBall 0 1) := by
            rw [complexProjectiveSpaceSuccInheritedClosedCellUnion n S]
    _ = Set.univ := complexProjectiveSpaceSuccHyperplane_union_realTopCell_closedBall_eq_univ n

/-- Helper for Example 10.1.12: every branch of the packaged successor cell family uses the
standard open unit ball as its source. -/
private theorem complexProjectiveSpaceSuccCellMap_source_eq
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
      (complexProjectiveSpaceSuccCellMap n S m j).source = Metric.ball 0 1 := by
  letI := S.cwComplex
  intro m j
  cases j with
  | inl j =>
      -- Inherited cells keep the old source after transport and subtype-forgetting.
      simpa [complexProjectiveSpaceSuccCellMap] using
        complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_source n S j
  | inr h =>
      cases h with
      | up hm =>
          -- The top branch is literally the packaged real top-cell chart.
          subst hm
          simp [complexProjectiveSpaceSuccCellMap, complexProjectiveSpaceSuccTopCellPartialEquiv]

/-- Helper for Example 10.1.12: every branch of the packaged successor cell family is continuous
on the closed unit ball required by `CWComplex.mkFinite`. -/
private theorem complexProjectiveSpaceSuccCellMap_continuousOnClosedBall
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
      ContinuousOn (complexProjectiveSpaceSuccCellMap n S m j) (Metric.closedBall 0 1) := by
  letI := S.cwComplex
  intro m j
  cases j with
  | inl j =>
      -- First transport the predecessor cell through the hyperplane homeomorphism, then forget
      -- the subtype target once.
      have htransport :
          ContinuousOn (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j)
            (Metric.closedBall 0 1) := by
        have hcomp :
            ContinuousOn
              (fun x : Fin m → ℝ ↦
                (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n)
                  (S.cwComplex.map m j x))
              (Metric.closedBall 0 1) :=
          (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n).continuous.comp_continuousOn
            (S.cwComplex.continuousOn m j)
        simpa [complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply] using hcomp
      simpa [complexProjectiveSpaceSuccCellMap] using
        partialEquivSubtypeValImage_continuousOn
          (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j) htransport
  | inr h =>
      cases h with
      | up hm =>
          -- The top branch reuses the already-packaged real top-cell chart.
          subst hm
          simpa [complexProjectiveSpaceSuccCellMap] using
            complexProjectiveSpaceSuccTopCellPartialEquiv_continuousOn n

/-- Helper for Example 10.1.12: the inverse of every branch of the packaged successor cell family
is continuous on its target. -/
private theorem complexProjectiveSpaceSuccCellMap_continuousOnSymmTarget
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
      ContinuousOn (complexProjectiveSpaceSuccCellMap n S m j).symm
        (complexProjectiveSpaceSuccCellMap n S m j).target := by
  letI := S.cwComplex
  intro m j
  cases j with
  | inl j =>
      -- Transport inverse continuity across the hyperplane homeomorphism, then forget the
      -- subtype target.
      have htransport :
          ContinuousOn (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j).symm
            (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j).target := by
        simpa [complexProjectiveSpaceSuccHyperplaneTransportCellMap] using
          partialEquiv_transHomeomorph_continuousOnSymm
            (S.cwComplex.map m j)
            (complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n)
            (S.cwComplex.continuousOn_symm m j)
      simpa [complexProjectiveSpaceSuccCellMap] using
        partialEquivSubtypeValImage_continuousOnSymm
          (complexProjectiveSpaceSuccHyperplaneTransportCellMap n S j) htransport
  | inr h =>
      cases h with
      | up hm =>
          -- The top branch again reuses the real top-cell chart API directly.
          subst hm
          simpa [complexProjectiveSpaceSuccCellMap] using
            complexProjectiveSpaceSuccTopCellPartialEquiv_continuousOnSymm n

/-- Helper for Example 10.1.12: each successor cell sends its boundary into the union of lower
closed successor cells. -/
private theorem complexProjectiveSpaceSuccCellMap_mapsToBoundary
    (n : ℕ) (S : ComplexProjectiveCWStructure n) :
    letI := S.cwComplex
    ∀ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
      Set.MapsTo
        (complexProjectiveSpaceSuccCellMap n S m j)
        (Metric.sphere 0 1)
        (⋃ (m' : ℕ) (_ : m' < m) (j' : complexProjectiveSpaceSuccCell n S m'),
          complexProjectiveSpaceSuccCellMap n S m' j' '' Metric.closedBall 0 1) := by
  letI := S.cwComplex
  intro m j
  cases j with
  | inl j =>
      intro x hx
      -- Reindex the predecessor boundary witness into the inherited summand of the successor
      -- family.
      rcases S.cwComplex.mapsTo m j with ⟨I, hI⟩
      have hOld :
          S.cwComplex.map m j x ∈
            (⋃ (m' : ℕ) (_ : m' < m)
              (j' : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m'),
              S.cwComplex.map m' j' '' Metric.closedBall 0 1) :=
        by
          have hOldFinite :
              S.cwComplex.map m j x ∈
                (⋃ (m' : ℕ) (_ : m' < m)
                  (j' ∈ I m'),
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
      change
        complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j' u =
          complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j x
      rw [complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_apply,
        complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_apply,
        complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply,
        complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply]
      exact congrArg
        (fun y ↦
          ((complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n) y :
            ComplexProjectiveSpace (n + 1)))
        huEq
  | inr h =>
      cases h with
      | up hm =>
          subst hm
          intro x hx
          -- The top boundary already lands in the ambientized inherited closed cells; only the
          -- successor-family reindexing remains.
          have hTop :
              complexProjectiveSpaceSuccTopCellMapReal n
                  (complexCoordinateUnitSphereToClosedBall n ⟨x, hx⟩) ∈
                (⋃ (m' : ℕ)
                  (j' : Topology.CWComplex.cell
                    (Set.univ : Set (ComplexProjectiveSpace n)) m'),
                  complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j' ''
                    Metric.closedBall 0 1) :=
            (complexProjectiveSpaceSuccTopCellBoundary_mapsToInheritedClosedCells n S)
              (x := ⟨x, hx⟩) (by simp)
          rcases Set.mem_iUnion.1 hTop with ⟨m', hTop⟩
          rcases Set.mem_iUnion.1 hTop with ⟨j', hTop⟩
          have hm' : m' < 2 * (n + 1) := by
            by_contra hm'
            have hm'le : 2 * (n + 1) ≤ m' := le_of_not_gt hm'
            letI :=
              S.highCellEmpty m' (by omega)
            exact (inferInstance : IsEmpty
              (Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m')).false j'
          rcases hTop with ⟨u, hu, huEq⟩
          refine Set.mem_iUnion.2
            ⟨m', Set.mem_iUnion.2 ⟨hm', Set.mem_iUnion.2 ⟨Sum.inl j', ?_⟩⟩⟩
          refine ⟨u, hu, ?_⟩
          calc
            complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j' u =
                complexProjectiveSpaceSuccTopCellMapReal n
                  (complexCoordinateUnitSphereToClosedBall n ⟨x, hx⟩) := huEq
            _ = complexProjectiveSpaceSuccCellMap n S (2 * (n + 1)) (Sum.inr ⟨rfl⟩) x := by
                  symm
                  simpa [complexProjectiveSpaceSuccCellMap] using
                    complexProjectiveSpaceSuccTopCellMapReal_eq_total n
                      (complexCoordinateUnitSphereToClosedBall n ⟨x, hx⟩)

/-- Helper for Example 10.1.12: the packaged successor cell family already defines the underlying
finite CW complex on `CP^(n + 1)`. -/
private noncomputable abbrev complexProjectiveSpaceSuccCWComplex {n : ℕ}
    (S : ComplexProjectiveCWStructure n) :
    Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
  Topology.CWComplex.mkFinite
    (Set.univ : Set (ComplexProjectiveSpace (n + 1)))
    (complexProjectiveSpaceSuccCell n S)
    (complexProjectiveSpaceSuccCellMap n S)
    (complexProjectiveSpaceSuccCell_eventuallyIsEmpty n S)
    (complexProjectiveSpaceSuccCell_finite n S)
    (complexProjectiveSpaceSuccCellMap_source_eq n S)
    (complexProjectiveSpaceSuccCellMap_continuousOnClosedBall n S)
    (complexProjectiveSpaceSuccCellMap_continuousOnSymmTarget n S)
    (complexProjectiveSpaceSuccCellMap_pairwiseDisjoint n S)
    (complexProjectiveSpaceSuccCellMap_mapsToBoundary n S)
    (complexProjectiveSpaceSuccCellMap_union n S)

/-- Helper for Example 10.1.12: forgetting the hyperplane subtype of the canonical inclusion
homeomorphism recovers the ambient successor inclusion. -/
@[simp]
private theorem complexProjectiveSpaceSuccInclusionHomeomorphHyperplane_coe
    (n : ℕ) (x : ComplexProjectiveSpace n) :
    ((complexProjectiveSpaceSuccInclusionHomeomorphHyperplane n x :
        ((complexProjectiveSpaceSuccHyperplane n).projectivization : Set
          (ComplexProjectiveSpace (n + 1)))) : ComplexProjectiveSpace (n + 1)) =
      complexProjectiveSpaceSuccInclusion n x := by
  -- The range-to-hyperplane `setCongr` only changes the membership proof, not the ambient point.
  rfl

/-- Helper for Example 10.1.12: ambientized inherited cell maps are exactly the old cell maps
followed by the canonical successor inclusion. -/
@[simp]
private theorem complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_eq_inclusion
    (n : ℕ) (S : ComplexProjectiveCWStructure n) {m : ℕ} :
    letI := S.cwComplex
    ∀ (j : Topology.CWComplex.cell (Set.univ : Set (ComplexProjectiveSpace n)) m)
      (x : Fin m → ℝ),
      complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient n S j x =
        complexProjectiveSpaceSuccInclusion n (S.cwComplex.map m j x) := by
  intro j x
  -- First rewrite the ambientized map through the subtype-valued transport, then forget the
  -- hyperplane proof once.
  rw [complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_apply,
    complexProjectiveSpaceSuccHyperplaneTransportCellMap_apply,
    complexProjectiveSpaceSuccInclusionHomeomorphHyperplane_coe]

/-- Helper for Example 10.1.12: below the new top degree, the successor skeleton is exactly the
image of the predecessor skeleton under the canonical inclusion `CP^n → CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccSkeletonBelowTop_eq_inclusionImage
    {n : ℕ} (S : ComplexProjectiveCWStructure n) {q : ℕ∞}
    (hq : q < (2 * (n + 1) : ℕ∞)) :
    letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
    let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
      complexProjectiveSpaceSuccCWComplex S
    letI := cw
    (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace (n + 1))) q :
        Set (ComplexProjectiveSpace (n + 1))) =
      complexProjectiveSpaceSuccInclusion n ''
        (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q :
          Set (ComplexProjectiveSpace n)) := by
  letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  ext x
  constructor
  · intro hx
    -- Route correction: use `mem_skeleton_iff` directly so the unique new top-cell branch can be
    -- excluded before any subtype transport is introduced.
    rcases Topology.CWComplex.exists_mem_openCell_of_mem_skeleton.mp hx with ⟨m, hm, j, hj⟩
    change x ∈ complexProjectiveSpaceSuccCellMap n S m j '' Metric.ball 0 1 at hj
    cases j with
    | inl j =>
        rcases hj with ⟨u, hu, rfl⟩
        refine ⟨S.cwComplex.map m j u, ?_, ?_⟩
        · -- The predecessor open-cell witness already lies in the predecessor `q`-skeleton.
          letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
          have hOldM :
              S.cwComplex.map m j u ∈
                (Topology.CWComplex.skeleton
                  (Set.univ : Set (ComplexProjectiveSpace n)) (m : ℕ∞) :
                    Set (ComplexProjectiveSpace n)) :=
            Topology.CWComplex.openCell_subset_skeleton
              (C := (Set.univ : Set (ComplexProjectiveSpace n))) m j ⟨u, hu, rfl⟩
          exact
            Topology.CWComplex.skeleton_mono
              (C := (Set.univ : Set (ComplexProjectiveSpace n))) hm hOldM
        · -- The inherited successor branch is literally the predecessor cell followed by the
          -- canonical successor inclusion.
          simpa using complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_eq_inclusion
            n S j u
    | inr hTop =>
        -- The unique new cell lives in degree `2 * (n + 1)`, so it cannot occur below the top
        -- degree.
        have hTopLe : (2 * (n + 1) : ℕ∞) ≤ q := by
          simpa [hTop.down] using hm
        exact False.elim ((not_le_of_gt hq) hTopLe)
  · rintro ⟨y, hy, rfl⟩
    rcases Topology.CWComplex.exists_mem_openCell_of_mem_skeleton.mp hy with ⟨m, hm, j, hj⟩
    have hOpen :
        complexProjectiveSpaceSuccInclusion n y ∈
          Topology.CWComplex.openCell
            (C := (Set.univ : Set (ComplexProjectiveSpace (n + 1))))
            m (Sum.inl j) := by
      change
        complexProjectiveSpaceSuccInclusion n y ∈
          complexProjectiveSpaceSuccCellMap n S m (Sum.inl j) '' Metric.ball 0 1
      rcases hj with ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      -- The same Euclidean source point defines the inherited successor open-cell witness.
      simpa using
        (complexProjectiveSpaceSuccHyperplaneTransportCellMapAmbient_eq_inclusion n S j u).symm
    -- Once the inherited open cell is identified, the standard open-cell-to-skeleton lemma
    -- finishes the transport back into the successor skeleton.
    have hSuccM :
        complexProjectiveSpaceSuccInclusion n y ∈
          (Topology.CWComplex.skeleton
            (Set.univ : Set (ComplexProjectiveSpace (n + 1))) (m : ℕ∞) :
              Set (ComplexProjectiveSpace (n + 1))) :=
      Topology.CWComplex.openCell_subset_skeleton
        (C := (Set.univ : Set (ComplexProjectiveSpace (n + 1)))) m (Sum.inl j) hOpen
    exact
      Topology.CWComplex.skeleton_mono
        (C := (Set.univ : Set (ComplexProjectiveSpace (n + 1)))) hm hSuccM

/-- Helper for Example 10.1.12: below the new top degree, the successor skeleton is homeomorphic
to the predecessor skeleton through the canonical hyperplane inclusion. -/
private noncomputable def complexProjectiveSpaceSuccSkeletonBelowTop_homeomorph
    {n : ℕ} (S : ComplexProjectiveCWStructure n) {q : ℕ∞}
    (hq : q < (2 * (n + 1) : ℕ∞)) :
    letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
    let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
      complexProjectiveSpaceSuccCWComplex S
    letI := cw
    Topology.CWComplex.skeleton
        (Set.univ : Set (ComplexProjectiveSpace (n + 1))) q ≃ₜ
      Topology.CWComplex.skeleton
        (Set.univ : Set (ComplexProjectiveSpace n)) q := by
  letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  letI : CompactSpace (ComplexProjectiveSpace n) := complexProjectiveSpace_compactSpace n
  let hEmbedding : Topology.IsEmbedding (complexProjectiveSpaceSuccInclusion n) :=
    ((complexProjectiveSpaceSuccInclusion_continuous n).isClosedEmbedding
      (complexProjectiveSpaceSuccInclusion_injective n)).toIsEmbedding
  let hImage :
      Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q ≃ₜ
        complexProjectiveSpaceSuccInclusion n ''
          (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q :
            Set (ComplexProjectiveSpace n)) :=
    hEmbedding.homeomorphImage
      (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q :
        Set (ComplexProjectiveSpace n))
  -- First identify the successor skeleton with the image of the predecessor skeleton, then use
  -- the embedding homeomorphism onto that image.
  exact
    (Homeomorph.setCongr
      (complexProjectiveSpaceSuccSkeletonBelowTop_eq_inclusionImage S hq)).trans
      hImage.symm

/-- Helper for Example 10.1.12: the inverse below-top skeleton transport is the canonical
successor inclusion on ambient points. -/
private theorem complexProjectiveSpaceSuccSkeletonBelowTop_homeomorph_symm_apply
    {n : ℕ} (S : ComplexProjectiveCWStructure n) {q : ℕ∞}
    (hq : q < (2 * (n + 1) : ℕ∞)) :
    letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
    let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
      complexProjectiveSpaceSuccCWComplex S
    letI := cw
    ∀ y : Topology.CWComplex.skeleton
        (Set.univ : Set (ComplexProjectiveSpace n)) q,
      ((complexProjectiveSpaceSuccSkeletonBelowTop_homeomorph S hq).symm y).1 =
        complexProjectiveSpaceSuccInclusion n y.1 := by
  letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  letI : CompactSpace (ComplexProjectiveSpace n) := complexProjectiveSpace_compactSpace n
  let hEmbedding : Topology.IsEmbedding (complexProjectiveSpaceSuccInclusion n) :=
    ((complexProjectiveSpaceSuccInclusion_continuous n).isClosedEmbedding
      (complexProjectiveSpaceSuccInclusion_injective n)).toIsEmbedding
  let hImage :
      Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q ≃ₜ
        complexProjectiveSpaceSuccInclusion n ''
          (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q :
            Set (ComplexProjectiveSpace n)) :=
    hEmbedding.homeomorphImage
      (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace n)) q :
        Set (ComplexProjectiveSpace n))
  refine fun y ↦ ?_
  -- Route correction: unfold the packaged transport only once and then keep only the ambient
  -- point, where `setCongr` is proof-irrelevant and `homeomorphImage` is the inclusion.
  change (((Homeomorph.setCongr
      (complexProjectiveSpaceSuccSkeletonBelowTop_eq_inclusionImage S hq)).trans
        hImage.symm).symm y).1 =
      complexProjectiveSpaceSuccInclusion n y.1
  rfl

/-- Helper for Example 10.1.12: once the top-degree cells are attached, every skeleton at or
above degree `2 * (n + 1)` is already all of `CP^(n + 1)`. -/
private theorem complexProjectiveSpaceSuccSkeleton_eq_univ_of_top_le
    {n : ℕ} (S : ComplexProjectiveCWStructure n) {q : ℕ∞}
    (hq : (2 * (n + 1) : ℕ∞) ≤ q) :
    let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
      complexProjectiveSpaceSuccCWComplex S
    letI := cw
    (Topology.CWComplex.skeleton (Set.univ : Set (ComplexProjectiveSpace (n + 1))) q :
        Set (ComplexProjectiveSpace (n + 1))) =
      (Set.univ : Set (ComplexProjectiveSpace (n + 1))) := by
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hxUnion :
        x ∈ ⋃ (m : ℕ) (j : complexProjectiveSpaceSuccCell n S m),
          complexProjectiveSpaceSuccCellMap n S m j '' Metric.closedBall 0 1 := by
      rw [complexProjectiveSpaceSuccCellMap_union n S]
      simp
    rcases Set.mem_iUnion.1 hxUnion with ⟨m, hxUnion⟩
    rcases Set.mem_iUnion.1 hxUnion with ⟨j, hxUnion⟩
    have hmTop : m ≤ 2 * (n + 1) := by
      by_contra hmTop
      letI := complexProjectiveSpaceSuccCell_isEmpty_of_high n S m (lt_of_not_ge hmTop)
      exact (inferInstance : IsEmpty (complexProjectiveSpaceSuccCell n S m)).false j
    have hmq : (m : ℕ∞) ≤ q := le_trans (by exact_mod_cast hmTop) hq
    rcases hxUnion with ⟨u, hu, rfl⟩
    have hClosed :
        complexProjectiveSpaceSuccCellMap n S m j u ∈
          Topology.CWComplex.closedCell
            (C := (Set.univ : Set (ComplexProjectiveSpace (n + 1))))
            m j := by
      exact ⟨u, hu, rfl⟩
    have hSkeleton :
        complexProjectiveSpaceSuccCellMap n S m j u ∈
          (Topology.CWComplex.skeleton
            (Set.univ : Set (ComplexProjectiveSpace (n + 1))) (m : ℕ∞) :
              Set (ComplexProjectiveSpace (n + 1))) :=
      Topology.CWComplex.closedCell_subset_skeleton m j hClosed
    exact Topology.CWComplex.skeleton_mono hmq hSkeleton

/-- Helper for Example 10.1.12: the explicit top-cell boundary formula already lands in the
successor odd skeleton. -/
private theorem complexProjectiveSpaceSuccTopBoundaryIntoOddSkeleton
    {n : ℕ} (S : ComplexProjectiveCWStructure n)
    (z : ComplexProjectiveAttachingSphere n) :
    letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
    let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
      complexProjectiveSpaceSuccCWComplex S
    letI := cw
    complexProjectiveSpaceSuccTopCellMapReal n
        (complexCoordinateUnitSphereToClosedBall n
          (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z)) ∈
      (Topology.CWComplex.skeleton
        (Set.univ : Set (ComplexProjectiveSpace (n + 1)))
        (2 * n + 1 : ℕ∞) : Set (ComplexProjectiveSpace (n + 1))) := by
  letI : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace n)) := S.cwComplex
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  have hBoundary :
      complexProjectiveSpaceSuccTopCellMapReal n
          (complexCoordinateUnitSphereToClosedBall n
            (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z)) =
        complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) := by
    -- The boundary normalization theorem is stated using the same fixed boundary homeomorphism.
    simpa [complexProjectiveSpaceSuccTopCellBoundaryHomeomorph] using
      complexProjectiveSpaceSuccTopCellMapReal_boundary_eq n z
  have hOld :
      complexProjectiveSpaceAttachingMap n z ∈
        (Topology.CWComplex.skeleton
          (Set.univ : Set (ComplexProjectiveSpace n))
          (2 * n + 1 : ℕ∞) : Set (ComplexProjectiveSpace n)) := by
    -- The predecessor odd top skeleton is already all of `CP^n` because there are no cells above
    -- degree `2n`.
    have hTopLe : (2 * n : ℕ∞) ≤ (2 * n + 1 : ℕ∞) := by
      exact_mod_cast (show 2 * n ≤ 2 * n + 1 by omega)
    rw [complexProjectiveCWStructure_skeleton_eq_univ_of_top_le S (q := (2 * n + 1 : ℕ∞)) hTopLe]
    simp
  have hq : (2 * n + 1 : ℕ∞) < (2 * (n + 1) : ℕ∞) := by
    exact_mod_cast (show 2 * n + 1 < 2 * (n + 1) by omega)
  have hImage :
      complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) ∈
        complexProjectiveSpaceSuccInclusion n ''
          (Topology.CWComplex.skeleton
            (Set.univ : Set (ComplexProjectiveSpace n))
            (2 * n + 1 : ℕ∞) : Set (ComplexProjectiveSpace n)) := by
    exact ⟨complexProjectiveSpaceAttachingMap n z, hOld, rfl⟩
  -- Rewrite the successor odd skeleton by the below-top transport helper, then apply the
  -- normalized boundary formula.
  have hSucc :
      complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) ∈
        (Topology.CWComplex.skeleton
          (Set.univ : Set (ComplexProjectiveSpace (n + 1)))
          (2 * n + 1 : ℕ∞) : Set (ComplexProjectiveSpace (n + 1))) := by
    -- The below-top skeleton identity turns the inclusion-image witness into a successor
    -- skeleton witness.
    simpa [complexProjectiveSpaceSuccSkeletonBelowTop_eq_inclusionImage S hq] using hImage
  exact hBoundary ▸ hSucc

/-- Helper for Example 10.1.12: the unique top successor cell evaluates on the boundary sphere to
the canonical projective inclusion of the attaching map. -/
private theorem complexProjectiveSpaceSuccTopCellCwMap_eq_inclusion
    {n : ℕ} (S : ComplexProjectiveCWStructure n)
    (z : ComplexProjectiveAttachingSphere n) :
    letI := S.cwComplex
    let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
      complexProjectiveSpaceSuccCWComplex S
    letI := cw
    cw.map (2 * (n + 1))
        ((complexProjectiveSpaceSuccCell_evenUnique n S (n + 1) le_rfl).default)
        (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z).1 =
      complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) := by
  letI := S.cwComplex
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  have hTopCell :
      ((complexProjectiveSpaceSuccCell_evenUnique n S (n + 1) le_rfl).default :
        complexProjectiveSpaceSuccCell n S (2 * (n + 1))) =
        Sum.inr ⟨rfl⟩ := by
    simpa using
      ((complexProjectiveSpaceSuccCell_evenUnique n S (n + 1) le_rfl).uniq
        (Sum.inr ⟨rfl⟩)).symm
  -- Route correction: rewrite to the literal top summand before simplifying `cw.map`, so the
  -- packaged `mkFinite` constructor reduces to the explicit real top-cell branch.
  rw [hTopCell]
  calc
    cw.map (2 * (n + 1)) (Sum.inr ⟨rfl⟩)
        (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z).1 =
      complexProjectiveSpaceSuccTopCellMapReal n
        (complexCoordinateUnitSphereToClosedBall n
          (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z)) := by
            simpa [cw, complexProjectiveSpaceSuccCWComplex, complexProjectiveSpaceSuccCellMap]
              using
                complexProjectiveSpaceSuccTopCellMapReal_eq_total n
                  (complexCoordinateUnitSphereToClosedBall n
                    (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z))
    _ = complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) := by
          simpa [complexProjectiveSpaceSuccTopCellBoundaryHomeomorph] using
            complexProjectiveSpaceSuccTopCellMapReal_boundary_eq n z

/-- Helper for Example 10.1.12: once the standard Hopf attachment model of `CP^(n + 1)` is
packaged, it upgrades a chosen standard CW structure on `CP^n` to one on `CP^(n + 1)`. -/
private noncomputable def complexProjectiveSpaceSuccStandardCWStructure {n : ℕ}
    (S : ComplexProjectiveCWStructure n) :
    ComplexProjectiveCWStructure (n + 1) := by
  -- Route correction: the successor cell family now assembles into the underlying CW complex, so
  -- the remaining frontier is only the low-skeleton transport and top attaching-map packaging.
  let cw : Topology.CWComplex (Set.univ : Set (ComplexProjectiveSpace (n + 1))) :=
    complexProjectiveSpaceSuccCWComplex S
  letI := cw
  refine
    { cwComplex := cw
      evenCellUnique := ?_
      oddCellEmpty := ?_
      highCellEmpty := ?_
      evenSkeletonHomeomorph := ?_
      oddSkeletonHomeomorph := ?_
      topCellBoundaryHomeomorph := ?_
      topCellAttachingMap := ?_
      topCellAttachingMap_spec := ?_
      topCellAttachingMap_eq := ?_
      topCellAttachingMap_isFiberBundle := ?_ }
  · intro m hm
    -- The `mkFinite` CW complex keeps the explicit successor even-cell family definitionally.
    change Unique (complexProjectiveSpaceSuccCell n S (2 * m))
    exact complexProjectiveSpaceSuccCell_evenUnique n S m hm
  · intro m
    -- Odd-dimensional successor cells are still empty because only inherited odd cells and the
    -- new even top cell are available.
    change IsEmpty (complexProjectiveSpaceSuccCell n S (2 * m + 1))
    exact complexProjectiveSpaceSuccCell_oddIsEmpty n S m
  · intro k hk
    -- Above the new top degree there are no successor cells at all.
    change IsEmpty (complexProjectiveSpaceSuccCell n S k)
    exact complexProjectiveSpaceSuccCell_isEmpty_of_high n S k hk
  · intro m hm
    by_cases hTop : m = n + 1
    · subst hTop
      -- At the top even degree, no higher cells remain, so the skeleton is already all of
      -- `CP^(n + 1)`.
      refine
        (Homeomorph.setCongr
          (complexProjectiveSpaceSuccSkeleton_eq_univ_of_top_le S
            (q := (2 * (n + 1) : ℕ∞)) le_rfl)).trans
          (Homeomorph.Set.univ _)
    · have hm' : m ≤ n := by omega
      have hq : (2 * m : ℕ∞) < (2 * (n + 1) : ℕ∞) := by
        exact_mod_cast (show 2 * m < 2 * (n + 1) by omega)
      -- Below the top degree, the successor skeleton is just the predecessor skeleton sitting in
      -- the canonical hyperplane copy.
      exact
        (complexProjectiveSpaceSuccSkeletonBelowTop_homeomorph S (q := (2 * m : ℕ∞)) hq).trans
          (S.evenSkeletonHomeomorph m hm')
  · intro m hm
    by_cases hTop : m = n + 1
    · subst hTop
      -- The top odd skeleton is also everything because no cell lies above degree
      -- `2 * (n + 1)`.
      have hq : (2 * (n + 1) : ℕ∞) ≤ (2 * (n + 1) + 1 : ℕ∞) := by
        exact_mod_cast (show 2 * (n + 1) ≤ 2 * (n + 1) + 1 by omega)
      refine
        (Homeomorph.setCongr
          (complexProjectiveSpaceSuccSkeleton_eq_univ_of_top_le S
            (q := (2 * (n + 1) + 1 : ℕ∞)) hq)).trans
          (Homeomorph.Set.univ _)
    · have hm' : m ≤ n := by omega
      have hq : (2 * m + 1 : ℕ∞) < (2 * (n + 1) : ℕ∞) := by
        exact_mod_cast (show 2 * m + 1 < 2 * (n + 1) by omega)
      -- The odd successor skeleton uses the same below-top transport as the even case.
      exact
        (complexProjectiveSpaceSuccSkeletonBelowTop_homeomorph S
          (q := (2 * m + 1 : ℕ∞)) hq).trans
          (S.oddSkeletonHomeomorph m hm')
  · intro hn
    -- The new top-cell boundary model is already the fixed real sphere used by the chart package.
    simpa [cw, complexProjectiveSpaceSuccCWComplex] using
      complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n
  · intro hn
    refine fun z ↦ ⟨
      complexProjectiveSpaceSuccTopCellMapReal n
        (complexCoordinateUnitSphereToClosedBall n
          (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z)),
      ?_⟩
    -- The boundary point lands in the successor odd skeleton by transport from the predecessor
    -- attaching map.
    simpa [cw, complexProjectiveSpaceSuccCWComplex] using
      complexProjectiveSpaceSuccTopBoundaryIntoOddSkeleton S z
  · intro hn
    dsimp
    intro z
    -- Route correction: compare both sides to the same explicit boundary formula for the unique
    -- top successor cell.
    calc
      (complexProjectiveSpaceSuccTopCellMapReal n
          (complexCoordinateUnitSphereToClosedBall n
            (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z))) =
        complexProjectiveSpaceSuccInclusion n (complexProjectiveSpaceAttachingMap n z) := by
            simpa [complexProjectiveSpaceSuccTopCellBoundaryHomeomorph] using
              complexProjectiveSpaceSuccTopCellMapReal_boundary_eq n z
      _ =
        cw.map (2 * (n + 1))
          ((complexProjectiveSpaceSuccCell_evenUnique n S (n + 1) le_rfl).default)
          (complexProjectiveSpaceSuccTopCellBoundaryHomeomorph n z).1 := by
            symm
            exact complexProjectiveSpaceSuccTopCellCwMap_eq_inclusion S z
  · intro hn
    -- TODO: the remaining blocker is structural, not local algebra: the successor odd-skeleton
    -- homeomorphism below the top degree is transported through the arbitrary predecessor field
    -- `S.oddSkeletonHomeomorph n le_rfl`, while the explicit boundary formula lands at the raw
    -- point `complexProjectiveSpaceAttachingMap n z`. Closing this requires an owner-level bridge
    -- identifying the predecessor top odd-skeleton homeomorphism with the canonical univ model,
    -- or a strengthened induction invariant carrying that normalization.
    sorry
  · intro hn
    -- TODO: the final bundle clause still needs a standalone theorem
    -- `IsFiberBundleMap Circle (complexProjectiveSpaceAttachingMap n)` proved from the affine
    -- chart model, so the structure literal can consume it without re-entangling bundle geometry
    -- with the successor CW assembly.
    sorry

/-- As a secondary existence statement, `CP^n` admits a standard classical CW structure. -/
theorem complexProjectiveSpaceHasStandardCWStructure (n : ℕ) :
    Nonempty (ComplexProjectiveCWStructure n) := by
  induction n with
  | zero =>
      -- The base case is the explicit one-point CW structure on `CP^0`.
      exact ⟨complexProjectiveCWStructureZero⟩
  | succ n ih =>
      -- Route correction: the induction now delegates all remaining geometry to the successor
      -- attachment-model constructor.
      obtain ⟨S⟩ := ih
      exact ⟨complexProjectiveSpaceSuccStandardCWStructure S⟩

/-- The top attaching map of `CP^n` is a fiber bundle over `CP^(n - 1)` with fiber `S¹`. -/
theorem complexProjectiveSpaceAttachingMap_isFiberBundle {n : ℕ} (hn : 1 ≤ n) :
    IsFiberBundleMap Circle (complexProjectiveSpaceAttachingMap (n - 1)) := by
  obtain ⟨S⟩ := complexProjectiveSpaceHasStandardCWStructure n
  simpa [S.topAttachingMap_eq hn] using S.topAttachingMap_isFiberBundle hn
