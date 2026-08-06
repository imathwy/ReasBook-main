import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

universe u

open Topology
open scoped Topology.Homotopy unitInterval

-- Semantic recall via `lean_leansearch`: `Topology.RelCWComplex` and
-- `Topology.CWComplex.skeleton` are the canonical owners for the source's relative cell and
-- skeleton language. Local Chapter 11 precedent also records low-dimensional cell-vanishing
-- hypotheses by emptiness of the corresponding `cell` types.

namespace Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- A relative CW structure has no cells in dimensions at most `n` when each `m`-cell type is
empty for `m ≤ n`. -/
def NoCellsLE (C D : Set X) [RelCWComplex C D] (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → IsEmpty (cell C m)

/-- A `NoCellsLE` hypothesis eliminates any relative `m`-cell type in the prescribed range. -/
theorem noCellsLE_isEmptyCell {m n : ℕ} (h_noCells : NoCellsLE C D n) (hmn : m ≤ n) :
    IsEmpty (cell C m) :=
  h_noCells m hmn

/-- `NoCellsLEOf h_rel n` restates `NoCellsLE C D n` with the relative CW structure supplied as
an ordinary argument, so the chosen structure and its low-cell vanishing clause can be exported
together without public instance-installation scaffolding. -/
abbrev NoCellsLEOf (h_rel : RelCWComplex C D) (n : ℕ) : Prop :=
  letI : RelCWComplex C D := h_rel
  NoCellsLE C D n

/-- Vanishing of relative cells up to degree `n` implies vanishing up to any smaller degree. -/
theorem NoCellsLE.mono {m n : ℕ} (h_noCells : NoCellsLE C D n) (hmn : m ≤ n) :
    NoCellsLE C D m := fun k hkm ↦ h_noCells k (Nat.le_trans hkm hmn)

end Topology.RelCWComplex

/-- A CW structure on the whole space supplies the Hausdorffness needed by the classical
subcomplex API for skeleta. -/
instance instT2SpaceOfUnivCWComplex
    {X : Type u} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] : T2Space X := by
  -- Reuse the existing CW-to-Hausdorff bridge rather than duplicating the Chapter 13 argument.
  exact instT2SpaceOfCWComplexUniv X

namespace Topology.CWComplex

/-- The underlying subset `X^n` of the canonical `n`-skeleton of a CW complex `X`. This bridge
matches subset-valued source statements about pairs `(X, X^n)`. -/
abbrev skeletonSet (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) : Set X :=
  skeleton (Set.univ : Set X) n

end Topology.CWComplex

namespace Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] (A : Set X)
variable [RelCWComplex (Set.univ : Set X) A]

/-- Helper for Lemma 10.4.4: every point of a positive-dimensional open cell is joined to some
point on that cell's frontier. -/
theorem exists_joined_frontierPoint_of_memOpenCell
    {m : ℕ} (hm : 0 < m) (j : cell (Set.univ : Set X) m) {x : X}
    (hx : x ∈ openCell (C := (Set.univ : Set X)) m j) :
    ∃ y, y ∈ cellFrontier (C := (Set.univ : Set X)) m j ∧ Joined x y := by
  rcases hx with ⟨v, hv, rfl⟩
  have hwNorm : ‖(fun _ : Fin m => (1 : ℝ))‖ = 1 := by
    -- Local instance justification (finite index nonempty): `pi_norm_const'` needs a witness in
    -- `Fin m`, and positive dimension provides one.
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    simpa using (pi_norm_const' (ι := Fin m) (a := (1 : ℝ)))
  have hw :
      (fun _ : Fin m => (1 : ℝ)) ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
    exact mem_sphere_zero_iff_norm.mpr hwNorm
  have hvClosed : v ∈ Metric.closedBall (0 : Fin m → ℝ) 1 :=
    Metric.ball_subset_closedBall hv
  have hwClosed : (fun _ : Fin m => (1 : ℝ)) ∈ Metric.closedBall (0 : Fin m → ℝ) 1 :=
    Metric.sphere_subset_closedBall hw
  have hJoinedClosedBall :
      JoinedIn (Metric.closedBall (0 : Fin m → ℝ) 1) v (fun _ : Fin m => (1 : ℝ)) := by
    let hPathConnected :
        IsPathConnected (Metric.closedBall (0 : Fin m → ℝ) 1) :=
      (convex_closedBall (0 : Fin m → ℝ) 1).isPathConnected ⟨v, hvClosed⟩
    exact hPathConnected.joinedIn v hvClosed (fun _ : Fin m => (1 : ℝ)) hwClosed
  refine ⟨map m j (fun _ : Fin m => (1 : ℝ)), ⟨(fun _ : Fin m => (1 : ℝ)), hw, rfl⟩, ?_⟩
  -- Map the straight-line path in the model closed ball into the closed cell.
  exact (hJoinedClosedBall.map_continuousOn (continuousOn (C := (Set.univ : Set X)) m j)).joined

/-- Helper for Lemma 10.4.4: if a relative CW pair has no relative `0`-cells, every point of an
open cell is joined to some basepoint in `A`. -/
theorem exists_joined_basepoint_of_memOpenCell
    (h_noCells : NoCellsLE (Set.univ : Set X) A 0) :
    ∀ {m : ℕ} (j : cell (Set.univ : Set X) m) {x : X},
      x ∈ openCell (C := (Set.univ : Set X)) m j → ∃ a : A, Joined x a.1 := by
  intro m
  induction m using Nat.case_strong_induction_on with
  | hz =>
      intro j x hx
      exact False.elim <|
        (noCellsLE_isEmptyCell (C := (Set.univ : Set X)) (D := A) h_noCells le_rfl).false j
  | hi m ih =>
      intro j x hx
      obtain ⟨y, hyFrontier, hxy⟩ :=
        exists_joined_frontierPoint_of_memOpenCell (A := A) (Nat.succ_pos m) j hx
      obtain ⟨cells, hI⟩ :=
        cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) (D := A) (m + 1) j
      have hyCover :
          y ∈ A ∪ ⋃ (l < m + 1) (i ∈ cells l), openCell (C := (Set.univ : Set X)) l i :=
        hI hyFrontier
      simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hyCover
      rcases hyCover with hyA | ⟨l, hl, i, _, hyOpen⟩
      · refine ⟨⟨y, hyA⟩, ?_⟩
        simpa using hxy
      · rcases ih l (Nat.le_of_lt_succ hl) i hyOpen with ⟨a, hya⟩
        exact ⟨a, hxy.trans hya⟩

/-- Helper for Lemma 10.4.4: the absence of relative `0`-cells already forces the inclusion
`π₀(A) → π₀(X)` to be surjective. -/
theorem zerothHomotopySurjective_of_noCellsLE
    (h_noCells : NoCellsLE (Set.univ : Set X) A 0) :
    Function.Surjective (zerothHomotopyInclusion A) := by
  intro z
  refine Quotient.inductionOn z ?_
  intro x
  have hxCover :
      x ∈ A ∪ ⋃ (m : ℕ) (j : cell (Set.univ : Set X) m),
        openCell (C := (Set.univ : Set X)) m j := by
    simpa [union_iUnion_openCell_eq_complex (C := (Set.univ : Set X)) (D := A)] using
      (show x ∈ (Set.univ : Set X) from trivial)
  simp only [Set.mem_union, Set.mem_iUnion] at hxCover
  rcases hxCover with hxA | ⟨m, j, hxOpen⟩
  · refine ⟨⟦⟨x, hxA⟩⟧, ?_⟩
    simp [zerothHomotopyInclusion_mk]
  · rcases exists_joined_basepoint_of_memOpenCell (A := A) h_noCells j hxOpen with ⟨a, hxa⟩
    refine ⟨⟦a⟧, ?_⟩
    rw [zerothHomotopyInclusion_mk]
    exact Quotient.sound hxa.symm

/-- Helper for Lemma 10.4.4: the Chapter 9 disk-boundary model presents the relative homotopy
group `π_q(X, A, a)` as the quotient of relative disk-boundary maps. -/
noncomputable def relativeHomotopyGroupEquivRelativeDiskBoundaryPointedHomotopyClass
    (q : ℕ+) (a : A) :
    relativeHomotopyGroup q A a ≃ relativeDiskBoundaryPointedHomotopyClass q A a :=
  let hModel := relativeHomotopyGroupHasDiskBoundaryModel q A a
  let forward := Classical.choose hModel
  let backward := Classical.choose (Classical.choose_spec hModel)
  let hInverse := Classical.choose_spec (Classical.choose_spec hModel)
  -- Package the chosen comparison maps into the explicit equivalence used below.
  { toFun := forward
    invFun := backward
    left_inv := hInverse.1
    right_inv := hInverse.2 }

/-- Helper for Lemma 10.4.4: the constant map at the basepoint is a relative disk-boundary triple
map. -/
theorem isRelativeDiskBoundaryPointedTripleMap_const
    (q : ℕ+) (a : A) :
    IsRelativeDiskBoundaryPointedTripleMap q A a (ContinuousMap.const _ a.1) := by
  constructor
  · intro y
    exact a.2
  · rfl

/-- Helper for Lemma 10.4.4: the constant disk-boundary representative at the chosen basepoint. -/
abbrev constantRelativeDiskBoundaryPointedMap
    (q : ℕ+) (a : A) :
    relativeDiskBoundaryPointedMap q A a :=
  ⟨ContinuousMap.const _ a.1, isRelativeDiskBoundaryPointedTripleMap_const (A := A) q a⟩

/-- Helper for Lemma 10.4.4: the frontier of a relative cell already lies in the base together
with finitely many lower-dimensional closed cells. -/
private theorem cellFrontier_subset_base_union_lowerClosedCells
    {m : ℕ} (j : cell (Set.univ : Set X) m) :
    ∃ J : Π l, Finset (cell (Set.univ : Set X) l),
      cellFrontier (C := (Set.univ : Set X)) m j ⊆
        A ∪ ⋃ (l < m) (i ∈ J l), closedCell (C := (Set.univ : Set X)) l i := by
  -- Reuse the owner lemma already stated in the closed-cell normal form needed by the induction.
  simpa using
    (cellFrontier_subset_base_union_finite_closedCell
      (C := (Set.univ : Set X)) (D := A) m j)

/-- Helper for Lemma 10.4.4: a relative cell frontier is disjoint from its own open cell. -/
private theorem disjoint_cellFrontier_openCell
    {m : ℕ} (j : cell (Set.univ : Set X) m) :
    Disjoint (cellFrontier (C := (Set.univ : Set X)) m j)
      (openCell (C := (Set.univ : Set X)) m j) := by
  induction m using Nat.case_strong_induction_on with
  | hz =>
      -- In degree `0`, the frontier is empty.
      rw [RelCWComplex.cellFrontier_zero_eq_empty]
      exact Set.empty_disjoint _
  | hi m _ =>
      -- Every frontier point either lies in the base or in a lower-dimensional open cell, both of
      -- which are disjoint from the chosen `(m + 1)`-cell.
      obtain ⟨cells, hI⟩ :=
        cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) (D := A) (m + 1) j
      refine Set.disjoint_left.2 ?_
      intro x hxFrontier hxOpen
      have hxCover :
          x ∈ A ∪ ⋃ (l < m + 1) (i ∈ cells l), openCell (C := (Set.univ : Set X)) l i :=
        hI hxFrontier
      simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hxCover
      rcases hxCover with hxBase | ⟨l, hl, i, _, hxLower⟩
      · exact Set.disjoint_left.mp (disjointBase (C := (Set.univ : Set X)) (D := A) (m + 1) j)
          hxOpen hxBase
      · have hne :
            (⟨l, i⟩ : Σ n, cell (Set.univ : Set X) n) ≠ ⟨m + 1, j⟩ := by
          intro hEq
          cases hEq
          exact Nat.lt_irrefl _ hl
        exact Set.disjoint_left.mp
          (disjoint_openCell_of_ne (C := (Set.univ : Set X)) hne) hxLower hxOpen

/-- Helper for Lemma 10.4.4: inside one closed cell, removing the frontier leaves exactly the open
cell. -/
private theorem closedCell_inter_compl_frontier_eq_openCell
    {m : ℕ} (j : cell (Set.univ : Set X) m) :
    closedCell (C := (Set.univ : Set X)) m j ∩
        (cellFrontier (C := (Set.univ : Set X)) m j)ᶜ =
      openCell (C := (Set.univ : Set X)) m j := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxClosed, hxNotFrontier⟩
    have hxUnion :
        x ∈ cellFrontier (C := (Set.univ : Set X)) m j ∪
          openCell (C := (Set.univ : Set X)) m j := by
      simpa [RelCWComplex.cellFrontier_union_openCell_eq_closedCell
        (C := (Set.univ : Set X)) m j] using hxClosed
    rcases hxUnion with hxFrontier | hxOpen
    · exact False.elim (hxNotFrontier hxFrontier)
    · exact hxOpen
  · intro hxOpen
    refine ⟨openCell_subset_closedCell (C := (Set.univ : Set X)) m j hxOpen, ?_⟩
    intro hxFrontier
    exact Set.disjoint_left.mp (disjoint_cellFrontier_openCell (A := A) j) hxFrontier hxOpen

/-- Helper for Lemma 10.4.4: if there are no relative `m`-cells, then every finite owner family in
that degree is empty. -/
private theorem finiteCellFamily_eq_empty_of_noCellsLE
    {n m : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n) (hmn : m ≤ n)
    (cells : Finset (cell (Set.univ : Set X) m)) :
    cells = ∅ := by
  -- Turn the `NoCellsLE` hypothesis into an `IsEmpty` instance and eliminate all possible members.
  let _ : IsEmpty (cell (Set.univ : Set X) m) :=
    noCellsLE_isEmptyCell (C := (Set.univ : Set X)) (D := A) h_noCells hmn
  ext i
  constructor
  · intro hi
    simpa using (IsEmpty.false i)
  · intro hi
    simpa using hi

/-- Helper for Lemma 10.4.4: the lower-dimensional frontier cover can be repackaged as one finite
sigma-family of cells. -/
private theorem cellFrontier_subset_base_union_finiteClosedCellSigma
    {m : ℕ} (j : cell (Set.univ : Set X) m) :
    ∃ S : Finset (Σ l, cell (Set.univ : Set X) l),
      (∀ s ∈ S, s.1 < m) ∧
        cellFrontier (C := (Set.univ : Set X)) m j ⊆
          A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  classical
  obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_lowerClosedCells (A := A) j
  let S : Finset (Σ l, cell (Set.univ : Set X) l) := (Finset.range m).sigma fun l ↦ J l
  refine ⟨S, ?_, ?_⟩
  · intro s hs
    -- Membership in the sigma-family records the original `< m` bound.
    exact (Finset.mem_range.mp ((Finset.mem_sigma.mp hs).1))
  · intro x hx
    -- Rewrite the original frontier cover into the sigma-family normal form.
    have hx' := hJ hx
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hx' ⊢
    rcases hx' with hxA | ⟨l, hl, i, hi, hxi⟩
    · exact Or.inl hxA
    · refine Or.inr ⟨⟨l, i⟩, ?_, hxi⟩
      -- The sigma-family membership is exactly the original `l < m` and `i ∈ J l` data.
      simp [S, Finset.mem_range, hl, hi]

/-- Helper for Lemma 10.4.4: choose a finite sigma-family that covers the frontier of a fixed
sigma-indexed cell. -/
private noncomputable def frontierSupportOfSigmaCell
    (s : Σ m, cell (Set.univ : Set X) m) :
    Finset (Σ l, cell (Set.univ : Set X) l) :=
  Classical.choose
    (cellFrontier_subset_base_union_finiteClosedCellSigma (A := A) (m := s.1) s.2)

/-- Helper for Lemma 10.4.4: every chosen frontier-support cell has strictly smaller dimension
than the original sigma-indexed cell. -/
private theorem frontierSupportOfSigmaCell_lt
    (s : Σ m, cell (Set.univ : Set X) m) :
    ∀ t ∈ frontierSupportOfSigmaCell (A := A) s, t.1 < s.1 := by
  exact
    (Classical.choose_spec
      (cellFrontier_subset_base_union_finiteClosedCellSigma (A := A) (m := s.1) s.2)).1

/-- Helper for Lemma 10.4.4: the chosen sigma-family covers the frontier of the original
sigma-indexed cell. -/
private theorem cellFrontier_subset_base_union_frontierSupportOfSigmaCell
    (s : Σ m, cell (Set.univ : Set X) m) :
    cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
      A ∪ ⋃ t ∈ frontierSupportOfSigmaCell (A := A) s,
        closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  exact
    (Classical.choose_spec
      (cellFrontier_subset_base_union_finiteClosedCellSigma (A := A) (m := s.1) s.2)).2

/-- Helper for Lemma 10.4.4: the one-step frontier support of a finite sigma-family is again
finite. -/
private noncomputable def frontierUnionOfSigmaSupport
    (S : Finset (Σ m, cell (Set.univ : Set X) m)) :
    Finset (Σ l, cell (Set.univ : Set X) l) := by
  classical
  exact S.biUnion (frontierSupportOfSigmaCell (A := A))

/-- Helper for Lemma 10.4.4: any chosen frontier-support cell belongs to the one-step frontier
union of the ambient finite sigma-family. -/
private theorem mem_frontierUnionOfSigmaSupport
    {S : Finset (Σ m, cell (Set.univ : Set X) m)}
    {s t : Σ m, cell (Set.univ : Set X) m}
    (hs : s ∈ S) (ht : t ∈ frontierSupportOfSigmaCell (A := A) s) :
    t ∈ frontierUnionOfSigmaSupport (A := A) S := by
  classical
  exact Finset.mem_biUnion.mpr ⟨s, hs, ht⟩

/-- Helper for Lemma 10.4.4: the frontier of a `0`-cell already lies in the base. -/
private theorem cellFrontier_subset_base_of_zeroCell
    (j : cell (Set.univ : Set X) 0) :
    cellFrontier (C := (Set.univ : Set X)) 0 j ⊆ A := by
  intro x hx
  have hx' :=
    cellFrontier_subset_base_union_frontierSupportOfSigmaCell (A := A) ⟨0, j⟩ hx
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hx'
  rcases hx' with hxA | ⟨t, ht, _⟩
  · exact hxA
  · exact False.elim (Nat.not_lt_zero _ (frontierSupportOfSigmaCell_lt (A := A) ⟨0, j⟩ t ht))

/-- Helper for Lemma 10.4.4: recursively close a finite sigma-family of cells under frontier
support, keeping the same ambient dimension bound. -/
private theorem frontierClosedSigmaSupportAux
    (N : ℕ) (S : Finset (Σ m, cell (Set.univ : Set X) m))
    (hBound : ∀ s ∈ S, s.1 ≤ N) :
    ∃ T : Finset (Σ m, cell (Set.univ : Set X) m),
      S ⊆ T ∧
        (∀ t ∈ T, t.1 ≤ N) ∧
          ∀ s ∈ T,
            cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
              A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  classical
  induction N generalizing S with
  | zero =>
      refine ⟨S, subset_rfl, hBound, ?_⟩
      intro s hs
      rcases s with ⟨m, j⟩
      have hm : m = 0 := Nat.eq_zero_of_le_zero (hBound ⟨m, j⟩ hs)
      subst hm
      -- In degree `0`, the frontier contribution is already absorbed by the base.
      intro x hx
      exact Or.inl (cellFrontier_subset_base_of_zeroCell (A := A) j hx)
  | succ N ih =>
      let Shigh : Finset (Σ m, cell (Set.univ : Set X) m) :=
        S.filter (fun s ↦ s.1 = N + 1)
      let Slow : Finset (Σ m, cell (Set.univ : Set X) m) :=
        S.filter (fun s ↦ s.1 ≤ N)
      let Slow' : Finset (Σ m, cell (Set.univ : Set X) m) :=
        Slow ∪ frontierUnionOfSigmaSupport (A := A) Shigh
      have hSlow'Bound : ∀ s ∈ Slow', s.1 ≤ N := by
        intro s hs
        rcases Finset.mem_union.mp hs with hsSlow | hsFrontier
        · exact (Finset.mem_filter.mp hsSlow).2
        · rcases Finset.mem_biUnion.mp hsFrontier with ⟨u, huHigh, hsFrontier⟩
          have hslt : s.1 < u.1 :=
            frontierSupportOfSigmaCell_lt (A := A) u s hsFrontier
          have huEq : u.1 = N + 1 := (Finset.mem_filter.mp huHigh).2
          have hslt' : s.1 < N + 1 := by
            simpa [huEq] using hslt
          exact Nat.le_of_lt_succ hslt'
      obtain ⟨Tlow, hSlow'sub, hTlowBound, hTlowFrontier⟩ := ih Slow' hSlow'Bound
      let T : Finset (Σ m, cell (Set.univ : Set X) m) := Tlow ∪ Shigh
      refine ⟨T, ?_, ?_, ?_⟩
      · intro s hsS
        have hsBound' := hBound s hsS
        rcases Nat.eq_or_lt_of_le hsBound' with hsEq | hsLt
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hsS, hsEq⟩))
        · have hsSlow : s ∈ Slow := Finset.mem_filter.mpr ⟨hsS, Nat.le_of_lt_succ hsLt⟩
          exact Finset.mem_union.mpr (Or.inl (hSlow'sub (Finset.mem_union.mpr (Or.inl hsSlow))))
      · intro t ht
        rcases Finset.mem_union.mp ht with htTlow | htHigh
        · exact Nat.le_trans (hTlowBound t htTlow) (Nat.le_succ _)
        · exact (Finset.mem_filter.mp htHigh).2.le
      · intro s hsT
        rcases Finset.mem_union.mp hsT with hsTlow | hsHigh
        · -- Frontiers of the already-closed lower support stay inside the enlarged support.
          intro x hx
          have hx' := hTlowFrontier s hsTlow hx
          simp only [T, Set.mem_union, Set.mem_iUnion, exists_prop, Finset.mem_union] at hx' ⊢
          rcases hx' with hxA | ⟨t, htTlow, hxt⟩
          · exact Or.inl hxA
          · exact Or.inr ⟨t, Or.inl htTlow, hxt⟩
        · -- A top-dimensional cell contributes only the chosen lower-dimensional frontier support.
          intro x hx
          have hx' :=
            cellFrontier_subset_base_union_frontierSupportOfSigmaCell (A := A) s hx
          simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hx' ⊢
          rcases hx' with hxA | ⟨t, htFrontier, hxt⟩
          · exact Or.inl hxA
          · have htFrontierUnion :
                t ∈ frontierUnionOfSigmaSupport (A := A) Shigh :=
              mem_frontierUnionOfSigmaSupport (A := A) hsHigh htFrontier
            have htTlow : t ∈ Tlow :=
              hSlow'sub (Finset.mem_union.mpr (Or.inr htFrontierUnion))
            exact Or.inr ⟨t, Finset.mem_union.mpr (Or.inl htTlow), hxt⟩

/-- Helper for Lemma 10.4.4: every finite sigma-family of ambient closed cells can be enlarged to
a finite sigma-family whose frontier support is closed under further frontier expansion. -/
private theorem frontierClosedSigmaSupport_of_finiteClosedCellSigma
    (S : Finset (Σ m, cell (Set.univ : Set X) m)) :
    ∃ T : Finset (Σ m, cell (Set.univ : Set X) m),
      S ⊆ T ∧
        ∀ s ∈ T,
          cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
            A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  classical
  let N := S.sup fun s ↦ s.1
  have hBound : ∀ s ∈ S, s.1 ≤ N := by
    intro s hs
    exact Finset.le_sup hs
  obtain ⟨T, hST, _hTBound, hTFrontier⟩ :=
    frontierClosedSigmaSupportAux (A := A) N S hBound
  exact ⟨T, hST, hTFrontier⟩

/-- Helper for Lemma 10.4.4: under `NoCellsLE`, filtering a finite sigma-family to dimensions
strictly larger than `n` does not change the closed-cell union. -/
private theorem base_union_finiteClosedCellSigma_pruneLowDegrees_of_noCellsLE
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n)
    (S : Finset (Σ m, cell (Set.univ : Set X) m)) :
    A ∪ ⋃ s ∈ S.filter (fun s ↦ n < s.1),
        closedCell (C := (Set.univ : Set X)) s.1 s.2 =
      A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  classical
  ext x
  constructor
  · intro hx
    -- The filtered family is a subfamily of the original one.
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Finset.mem_filter, and_assoc] at hx ⊢
    rcases hx with hxA | ⟨s, hsS, hsdeg, hxs⟩
    · exact Or.inl hxA
    · exact Or.inr ⟨s, hsS, hxs⟩
  · intro hx
    -- Low-dimensional cells cannot occur, so every contributing cell survives the filter.
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Finset.mem_filter, and_assoc] at hx ⊢
    rcases hx with hxA | ⟨s, hsS, hxs⟩
    · exact Or.inl hxA
    · have hsdeg : n < s.1 := by
        by_contra hsdeg
        exact (noCellsLE_isEmptyCell (C := (Set.univ : Set X)) (D := A) h_noCells
          (Nat.le_of_not_gt hsdeg)).false s.2
      exact Or.inr ⟨s, hsS, hsdeg, hxs⟩

/-- Helper for Lemma 10.4.4: if a pointed relative disk-boundary representative has image
contained in `A`, then it is homotopic through pointed relative disk-boundary maps to the constant
representative at `a`.  The affine contraction is based at the chosen point of the boundary sphere,
not at the cone point, so every time slice remains a map of pointed triples. -/
private theorem relativeDiskBoundaryPointedHomotopicWithConstant_of_range_subset_base
    {q : ℕ+} (a : A) (f : relativeDiskBoundaryPointedMap q A a)
    (hRange : Set.range f.1 ⊆ A) :
    ContinuousMap.HomotopicWith f.1 (constantRelativeDiskBoundaryPointedMap (A := A) q a).1
      (IsRelativeDiskBoundaryPointedTripleMap q A a) := by
  let p : unitDisk ((q : ℕ) - 1) :=
    sphereBoundaryInclusion ((q : ℕ) - 1)
      (sphereBoundaryBasepoint ((q : ℕ) - 1))
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine
      { toFun := fun tx ↦
          f.1 ⟨(1 - (tx.1 : ℝ)) • tx.2.1 + (tx.1 : ℝ) • p.1, ?_⟩
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · -- The closed unit disk is convex, so the segment from `x` to the chosen boundary
      -- basepoint remains inside the disk.
      exact (convex_closedBall
        (0 : EuclideanSpace ℝ (Fin (((q : ℕ) - 1) + 1))) 1)
          tx.2.2 p.2 (sub_nonneg.mpr tx.1.2.2) tx.1.2.1 (by ring)
    · -- Compose `f` with the affine contraction to the chosen boundary basepoint.
      have hcont :
          Continuous fun tx : I × unitDisk ((q : ℕ) - 1) ↦
            ((1 - (tx.1 : ℝ)) • tx.2.1 + (tx.1 : ℝ) • p.1 :
              EuclideanSpace ℝ (Fin (((q : ℕ) - 1) + 1))) := by
        fun_prop
      exact f.1.continuous.comp <|
        Continuous.subtype_mk hcont fun tx ↦ by
          exact (convex_closedBall
            (0 : EuclideanSpace ℝ (Fin (((q : ℕ) - 1) + 1))) 1)
              tx.2.2 p.2 (sub_nonneg.mpr tx.1.2.2) tx.1.2.1 (by ring)
    · intro x
      -- At time `0`, the contraction is the identity on the disk.
      congr 1
      apply Subtype.ext
      simp
    · intro x
      -- At time `1`, the contraction lands at the chosen boundary basepoint.
      change f.1
          (⟨(1 - (1 : ℝ)) • x.1 + (1 : ℝ) • p.1, by
              simpa using p.2⟩ : unitDisk ((q : ℕ) - 1)) = a.1
      have hp :
          (⟨(1 - (1 : ℝ)) • x.1 + (1 : ℝ) • p.1, by
              simpa using p.2⟩ : unitDisk ((q : ℕ) - 1)) = p := by
        apply Subtype.ext
        simp
      rw [hp]
      exact relativeDiskBoundaryPointedMap_mapsTo_basepoint q A a f
  · intro t
    constructor
    · intro y
      -- Every time-slice still lands in `A` because the whole image of `f` lies in `A`.
      exact hRange ⟨_, rfl⟩
    · -- The chosen boundary basepoint stays fixed throughout the affine contraction.
      change f.1
          (⟨(1 - (t : ℝ)) • p.1 + (t : ℝ) • p.1, by
              simpa [← add_smul] using p.2⟩ : unitDisk ((q : ℕ) - 1)) = a.1
      have hp :
          (⟨(1 - (t : ℝ)) • p.1 + (t : ℝ) • p.1, by
              simpa [← add_smul] using p.2⟩ : unitDisk ((q : ℕ) - 1)) = p := by
        apply Subtype.ext
        simp [← add_smul]
      rw [hp]
      exact relativeDiskBoundaryPointedMap_mapsTo_basepoint q A a f

/-- Helper for Lemma 10.4.4: if a relative disk-boundary representative has image contained in
`A`, then its quotient class is the constant class. -/
private theorem relativeDiskBoundaryClass_eq_constant_of_range_subset_base
    {q : ℕ+} (a : A) (f : relativeDiskBoundaryPointedMap q A a)
    (hRange : Set.range f.1 ⊆ A) :
    (⟦f⟧ : relativeDiskBoundaryPointedHomotopyClass q A a) =
      ⟦constantRelativeDiskBoundaryPointedMap (A := A) q a⟧ := by
  -- Descend the explicit disk contraction through the quotient relation.
  exact Quotient.sound
    (relativeDiskBoundaryPointedHomotopicWithConstant_of_range_subset_base (A := A) a f hRange)

/-- Helper for Lemma 10.4.4: away from the base, every point in the image of a relative
disk-boundary map lies in some ambient open cell. -/
private theorem rangeDiffBase_subset_iUnion_openCell_of_relativeDiskBoundaryMap
    {q : ℕ+} {a : A} (f : relativeDiskBoundaryPointedMap q A a) :
    Set.range f.1 ∩ Aᶜ ⊆
      ⋃ s : Σ m, cell (Set.univ : Set X) m, openCell (C := (Set.univ : Set X)) s.1 s.2 := by
  intro x hx
  -- Rewrite membership in the whole complex as membership in the base or in an ambient open cell.
  have hxComplex :
      x ∈ A ∪ ⋃ (m : ℕ) (j : cell (Set.univ : Set X) m),
        openCell (C := (Set.univ : Set X)) m j := by
    simpa [union_iUnion_openCell_eq_complex (C := (Set.univ : Set X)) (D := A)] using
      (show x ∈ (Set.univ : Set X) from trivial)
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, exists_prop] at hx hxComplex
  rcases hx with ⟨_hxRange, hxNotBase⟩
  rcases hxComplex with hxBase | ⟨m, j, hxCell⟩
  · exact False.elim (hxNotBase hxBase)
  · exact Set.mem_iUnion.mpr ⟨⟨m, j⟩, hxCell⟩

/-- Helper for Lemma 10.4.4: every point in the image of a relative disk-boundary map lies either
in the base or in an ambient closed cell. -/
private theorem range_subset_base_union_iUnion_closedCell_of_relativeDiskBoundaryMap
    {q : ℕ+} {a : A} (f : relativeDiskBoundaryPointedMap q A a) :
    Set.range f.1 ⊆
      A ∪ ⋃ s : Σ m, cell (Set.univ : Set X) m, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  intro x hxRange
  by_cases hxBase : x ∈ A
  · exact Or.inl hxBase
  · have hxOpen :
        x ∈ ⋃ s : Σ m, cell (Set.univ : Set X) m, openCell (C := (Set.univ : Set X)) s.1 s.2 :=
      rangeDiffBase_subset_iUnion_openCell_of_relativeDiskBoundaryMap (A := A) f
        ⟨hxRange, hxBase⟩
    rcases Set.mem_iUnion.mp hxOpen with ⟨s, hs⟩
    exact Or.inr <| Set.mem_iUnion.mpr ⟨s, openCell_subset_closedCell _ _ hs⟩

/-- Helper for Lemma 10.4.4: the base of a relative CW pair is closed. -/
private theorem isClosed_base :
    IsClosed A := by
  -- The relative CW structure records the base as a closed subset of the ambient complex.
  simpa using (isClosedBase (Set.univ : Set X))

/-- Helper for Lemma 10.4.4: the image of a relative disk-boundary representative is compact. -/
private theorem isCompact_range_of_relativeDiskBoundaryMap
    {q : ℕ+} {a : A} (f : relativeDiskBoundaryPointedMap q A a) :
    IsCompact (Set.range f.1) := by
  -- Local instance justification: the standard disk is a compact subtype of Euclidean space.
  let _ : CompactSpace (unitDisk ((q : ℕ) - 1)) :=
    isCompact_iff_compactSpace.mp <|
      by simpa [unitDisk] using
        (isCompact_closedBall
          (0 : EuclideanSpace ℝ (Fin (((q : ℕ) - 1) + 1))) 1)
  -- The source disk is compact, so continuity of `f` makes its image compact.
  exact isCompact_range f.1.continuous

/-- Helper for Lemma 10.4.4: intersecting the compact image with the closed base remains compact.
-/
private theorem isCompact_range_inter_base_of_relativeDiskBoundaryMap
    {q : ℕ+} {a : A} (f : relativeDiskBoundaryPointedMap q A a) :
    IsCompact (Set.range f.1 ∩ A) := by
  -- The compact image stays compact after intersecting with the closed base.
  exact (isCompact_range_of_relativeDiskBoundaryMap (A := A) f).inter_right
    (isClosed_base (A := A))

/-- Helper for Lemma 10.4.4: every point of the ambient relative CW complex already lies in the
base or in one ambient closed cell. -/
private theorem mem_base_union_iUnion_closedCell (x : X) :
    x ∈ A ∪ ⋃ s : Σ m, cell (Set.univ : Set X) m,
      closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  -- Rewrite the ambient relative-CW union formula into the sigma-indexed closed-cell language.
  have hxUniv : x ∈ (Set.univ : Set X) := by
    trivial
  have hxCover :
      x ∈ A ∪ ⋃ (n : ℕ) (j : cell (Set.univ : Set X) n),
        closedCell (C := (Set.univ : Set X)) n j := by
    simpa [union (C := (Set.univ : Set X))] using hxUniv
  simpa [Set.mem_iUnion, exists_prop] using hxCover

/-- Helper for Lemma 10.4.4: any point lying in the base together with ambient closed cells is
already contained in one finite frontier-closed closed-cell carrier. -/
private theorem exists_frontierClosedFiniteClosedCellCarrier_of_mem_base_union_iUnion_closedCell
    {x : X}
    (hx :
      x ∈ A ∪ ⋃ s : Σ m, cell (Set.univ : Set X) m,
        closedCell (C := (Set.univ : Set X)) s.1 s.2) :
    ∃ T : Finset (Σ m, cell (Set.univ : Set X) m),
      x ∈ A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2 ∧
        ∀ s ∈ T,
          cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
            A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  classical
  -- Split into the base case and the single-cell case, then frontier-close the singleton support.
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hx
  rcases hx with hxA | ⟨s, hxs⟩
  · refine ⟨∅, ?_, ?_⟩
    · exact Or.inl hxA
    · intro t ht
      exact False.elim (Finset.notMem_empty _ ht)
  · let S : Finset (Σ m, cell (Set.univ : Set X) m) := {s}
    obtain ⟨T, hST, hFrontierT⟩ :=
      frontierClosedSigmaSupport_of_finiteClosedCellSigma (A := A) S
    refine ⟨T, ?_, hFrontierT⟩
    -- The singled-out closed cell survives inside its frontier-closed enlargement.
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
    exact Or.inr ⟨s, hST (by simp [S]), hxs⟩

/-- Helper for Lemma 10.4.4: every point of the ambient relative CW complex lies in one finite
frontier-closed closed-cell carrier. -/
private theorem exists_frontierClosedFiniteClosedCellCarrierContainingPoint
    (x : X) :
    ∃ T : Finset (Σ m, cell (Set.univ : Set X) m),
      x ∈ A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2 ∧
        ∀ s ∈ T,
          cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
            A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  -- First place the point in `A ∪ ⋃ closedCell`, then frontier-close the resulting singleton
  -- support.
  exact
    exists_frontierClosedFiniteClosedCellCarrier_of_mem_base_union_iUnion_closedCell
      (A := A) (x := x) (mem_base_union_iUnion_closedCell (A := A) x)

/-- Helper for Lemma 10.4.4: enlarging a finite sigma-family enlarges its closed-cell carrier. -/
private theorem base_union_finiteClosedCellSigma_mono
    {S T : Finset (Σ m, cell (Set.univ : Set X) m)}
    (hST : S ⊆ T) :
    A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2 ⊆
      A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  intro x hx
  -- Rewrite carrier membership through one chosen sigma-cell and move that cell along `hST`.
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hx ⊢
  rcases hx with hxA | ⟨s, hsS, hxs⟩
  · exact Or.inl hxA
  · exact Or.inr ⟨s, hST hsS, hxs⟩

/-- Helper for Lemma 10.4.4: a finite union of frontier-closed sigma-families is again
frontier-closed after collapsing the owners by `Finset.biUnion`. -/
private theorem frontierClosedFiniteClosedCellSigma_biUnion
    [DecidableEq (Σ m, cell (Set.univ : Set X) m)]
    (U : Finset
      {S : Finset (Σ m, cell (Set.univ : Set X) m) //
        ∀ s ∈ S,
          cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
            A ∪ ⋃ t ∈ S, closedCell (C := (Set.univ : Set X)) t.1 t.2}) :
    ∀ s ∈ U.biUnion fun u ↦ u.1,
      cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
        A ∪ ⋃ t ∈ U.biUnion fun u ↦ u.1,
          closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  intro s hs
  rcases Finset.mem_biUnion.mp hs with ⟨u, huU, hsU⟩
  -- First use the frontier-closed witness inside the chosen carrier, then enlarge that carrier to
  -- the `biUnion` carrier.
  exact (u.2 s hsU).trans <|
    base_union_finiteClosedCellSigma_mono (A := A) fun t ht ↦
      Finset.mem_biUnion.mpr ⟨u, huU, ht⟩

/-- Helper for Lemma 10.4.4: the union of two frontier-closed finite sigma-families is again
frontier-closed. -/
private theorem frontierClosedFiniteClosedCellSigma_union
    [DecidableEq (Σ m, cell (Set.univ : Set X) m)]
    {S T : Finset (Σ m, cell (Set.univ : Set X) m)}
    (hS :
      ∀ s ∈ S,
        cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
          A ∪ ⋃ t ∈ S, closedCell (C := (Set.univ : Set X)) t.1 t.2)
    (hT :
      ∀ s ∈ T,
        cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
          A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2) :
    ∀ s ∈ S ∪ T,
      cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
        A ∪ ⋃ t ∈ S ∪ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  intro s hs
  rcases Finset.mem_union.mp hs with hsS | hsT
  · -- First use the frontier-closed carrier for `S`, then enlarge it to `S ∪ T`.
    exact (hS s hsS).trans <|
      base_union_finiteClosedCellSigma_mono (A := A) fun t ht ↦
        Finset.mem_union.mpr (Or.inl ht)
  · -- Symmetrically, the carrier for `T` sits inside the union carrier.
    exact (hT s hsT).trans <|
      base_union_finiteClosedCellSigma_mono (A := A) fun t ht ↦
        Finset.mem_union.mpr (Or.inr ht)

/-- Helper for Lemma 10.4.4: frontier-closed finite sigma-carriers form a directed family under
union. -/
private theorem directed_frontierClosedFiniteClosedCellSigma
    [DecidableEq (Σ m, cell (Set.univ : Set X) m)] :
    Directed (· ⊆ ·) (fun U :
      {S : Finset (Σ m, cell (Set.univ : Set X) m) //
        ∀ s ∈ S,
          cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
            A ∪ ⋃ t ∈ S, closedCell (C := (Set.univ : Set X)) t.1 t.2} ↦
      A ∪ ⋃ s ∈ U.1, closedCell (C := (Set.univ : Set X)) s.1 s.2) := by
  intro U V
  refine ⟨⟨U.1 ∪ V.1, frontierClosedFiniteClosedCellSigma_union (A := A) U.2 V.2⟩, ?_, ?_⟩
  · -- Each original carrier embeds into the union carrier.
    exact base_union_finiteClosedCellSigma_mono (A := A) fun s hs ↦
      Finset.mem_union.mpr (Or.inl hs)
  · -- The same monotonicity handles the second summand.
    exact base_union_finiteClosedCellSigma_mono (A := A) fun s hs ↦
      Finset.mem_union.mpr (Or.inr hs)

/-- Helper for Lemma 10.4.4: in the Hausdorff case, the base together with finitely many ambient
closed cells is a closed subset of the ambient space. -/
private theorem isClosed_base_union_finiteClosedCellSigma
    [T2Space X]
    (S : Finset (Σ m, cell (Set.univ : Set X) m)) :
    IsClosed
      (A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · -- With no cells present, the carrier is just the closed base.
    simpa using isClosed_base (A := A)
  · intro s S hs hS
    have hsClosed :
        IsClosed (closedCell (C := (Set.univ : Set X)) s.1 s.2) :=
      RelCWComplex.isClosed_closedCell (C := (Set.univ : Set X)) (D := A)
    have hEq :
        A ∪ ⋃ t ∈ insert s S, closedCell (C := (Set.univ : Set X)) t.1 t.2 =
          (A ∪ ⋃ t ∈ S, closedCell (C := (Set.univ : Set X)) t.1 t.2) ∪
            closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
      ext x
      simp [or_assoc, or_left_comm, or_comm]
    -- Separate the distinguished cell from the old finite carrier and close the union.
    rw [hEq]
    exact hS.union hsClosed

/-- Helper for Lemma 10.4.4: a compact subset already lying in the base together with ambient
closed cells is contained in the base together with finitely many of those closed cells. -/
private theorem compactSubset_subset_base_union_finiteClosedCellSigma
    (K : Set X) (hKCompact : IsCompact K)
    (hK :
      K ⊆ A ∪ ⋃ s : Σ m, cell (Set.univ : Set X) m,
        closedCell (C := (Set.univ : Set X)) s.1 s.2) :
    ∃ S : Finset (Σ m, cell (Set.univ : Set X) m),
      K ⊆ A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  -- Route correction: `openCell` need not be open in the ambient CW topology (for example, an
  -- endpoint 0-cell of an interval is not open), so the former finite-open-subcover argument was
  -- invalid.  This is the standard closure-finite/weak-topology compact-subset theorem for relative
  -- CW complexes; keep it as the genuine missing geometric input instead of asserting false
  -- ambient openness.
  sorry

/-- Helper for Lemma 10.4.4: the compact image of a relative disk-boundary representative is
contained in the base together with finitely many ambient closed cells. -/
private theorem range_subset_base_union_finiteClosedCellSigma_of_relativeDiskBoundaryMap
    {q : ℕ+} {a : A} (f : relativeDiskBoundaryPointedMap q A a) :
    ∃ S : Finset (Σ m, cell (Set.univ : Set X) m),
      Set.range f.1 ⊆
        A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  have hRangeClosed :
      Set.range f.1 ⊆
        A ∪ ⋃ s : Σ m, cell (Set.univ : Set X) m,
          closedCell (C := (Set.univ : Set X)) s.1 s.2 :=
    range_subset_base_union_iUnion_closedCell_of_relativeDiskBoundaryMap (A := A) f
  have hCompactRange :
      IsCompact (Set.range f.1) :=
    isCompact_range_of_relativeDiskBoundaryMap (A := A) f
  -- Specialize the compact-support owner theorem to the image of the relative disk-boundary map.
  exact compactSubset_subset_base_union_finiteClosedCellSigma
    (A := A) (K := Set.range f.1) hCompactRange hRangeClosed

/-- Helper for Lemma 10.4.4: every cell surviving the low-degree pruning has dimension strictly
larger than the disk-boundary degree `q`. -/
private theorem lt_cellDim_of_mem_prunedFiniteClosedCellSigma
    {n : ℕ} {q : ℕ+}
    (hq : (q : ℕ) ≤ n)
    {S : Finset (Σ m, cell (Set.univ : Set X) m)}
    {s : Σ m, cell (Set.univ : Set X) m}
    (hs : s ∈ S.filter (fun s ↦ n < s.1)) :
    (q : ℕ) < s.1 := by
  -- Read the surviving dimension bound from the filter and compare it with `q ≤ n`.
  exact lt_of_le_of_lt hq (Finset.mem_filter.mp hs).2

/-- Helper for Lemma 10.4.4: pruning away the low-dimensional cells preserves the frontier cover
of every surviving cell. -/
private theorem cellFrontier_subset_base_union_prunedFiniteClosedCellSigma_of_noCellsLE
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n)
    {S : Finset (Σ m, cell (Set.univ : Set X) m)}
    {s : Σ m, cell (Set.univ : Set X) m}
    (hFrontierS :
      cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
        A ∪ ⋃ t ∈ S, closedCell (C := (Set.univ : Set X)) t.1 t.2) :
    cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
      A ∪ ⋃ t ∈ S.filter (fun t ↦ n < t.1),
        closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  -- Rewrite the pruned carrier back to the original finite carrier, then reuse the old frontier
  -- cover before the low-dimensional cells were removed.
  rw [show A ∪ ⋃ t ∈ S.filter (fun t ↦ n < t.1),
        closedCell (C := (Set.univ : Set X)) t.1 t.2 =
      A ∪ ⋃ t ∈ S, closedCell (C := (Set.univ : Set X)) t.1 t.2 by
        simpa using
          (base_union_finiteClosedCellSigma_pruneLowDegrees_of_noCellsLE
            (A := A) h_noCells S)]
  exact hFrontierS

/-- Helper for Lemma 10.4.4: a finite closed-cell cover of the image can be normalized to a
frontier-closed family in which every surviving cell has dimension strictly larger than `q`. -/
private theorem exists_frontierClosedPrunedFiniteClosedCellSigma_of_relativeDiskBoundaryMap
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n)
    {q : ℕ+} (hq : (q : ℕ) ≤ n) {a : A} (f : relativeDiskBoundaryPointedMap q A a)
    {S : Finset (Σ m, cell (Set.univ : Set X) m)}
    (hCover :
      Set.range f.1 ⊆
        A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2) :
    ∃ T : Finset (Σ m, cell (Set.univ : Set X) m),
      Set.range f.1 ⊆
          A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2 ∧
        (∀ s ∈ T, (q : ℕ) < s.1) ∧
        ∀ s ∈ T,
          cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
            A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
  classical
  obtain ⟨T, hST, hFrontierT⟩ :=
    frontierClosedSigmaSupport_of_finiteClosedCellSigma (A := A) S
  have hCoverT :
      Set.range f.1 ⊆
        A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
    intro x hx
    have hx' := hCover hx
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hx' ⊢
    rcases hx' with hxA | ⟨s, hsS, hxs⟩
    · exact Or.inl hxA
    · exact Or.inr ⟨s, hST hsS, hxs⟩
  let Tprune := T.filter (fun s ↦ n < s.1)
  have hCoverPrune :
      Set.range f.1 ⊆
        A ∪ ⋃ s ∈ Tprune, closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
    -- Prune away the forbidden low-dimensional cells once the support is frontier closed.
    rw [show A ∪ ⋃ s ∈ Tprune, closedCell (C := (Set.univ : Set X)) s.1 s.2 =
        A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2 by
          simpa [Tprune] using
            (base_union_finiteClosedCellSigma_pruneLowDegrees_of_noCellsLE
              (A := A) h_noCells T)]
    exact hCoverT
  have hPrunedDim : ∀ s ∈ Tprune, (q : ℕ) < s.1 := by
    intro s hs
    exact lt_cellDim_of_mem_prunedFiniteClosedCellSigma (A := A) (n := n) (q := q) hq hs
  have hFrontierPrune :
      ∀ s ∈ Tprune,
        cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
          A ∪ ⋃ t ∈ Tprune, closedCell (C := (Set.univ : Set X)) t.1 t.2 := by
    intro s hs
    -- Rewrite the pruned carrier back to the frontier-closed carrier and reuse that cover.
    exact
      cellFrontier_subset_base_union_prunedFiniteClosedCellSigma_of_noCellsLE
        (A := A) h_noCells (hFrontierT s (Finset.mem_filter.mp hs).1)
  exact ⟨Tprune, hCoverPrune, hPrunedDim, hFrontierPrune⟩

/-- Helper for Lemma 10.4.4: splitting a finite closed-cell carrier at one chosen cell rewrites
the carrier as the erased support together with that singled-out closed cell. -/
private theorem base_union_finiteClosedCellSigma_eq_erase_union
    [DecidableEq (Σ m, cell (Set.univ : Set X) m)]
    (T : Finset (Σ m, cell (Set.univ : Set X) m))
    {s : Σ m, cell (Set.univ : Set X) m} (hs : s ∈ T) :
    A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 =
      (A ∪ ⋃ t ∈ T.erase s, closedCell (C := (Set.univ : Set X)) t.1 t.2) ∪
        closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
  ext x
  constructor
  · intro hx
    -- Separate the distinguished cell `s` from the rest of the finite sigma-family.
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Finset.mem_erase] at hx ⊢
    rcases hx with hxA | ⟨t, htT, hxt⟩
    · exact Or.inl (Or.inl hxA)
    · by_cases hts : t = s
      · exact Or.inr (hts ▸ hxt)
      · exact Or.inl (Or.inr ⟨t, ⟨hts, htT⟩, hxt⟩)
  · intro hx
    -- Conversely, every point of the erased carrier or the singled-out closed cell lies in the
    -- original carrier.
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Finset.mem_erase] at hx ⊢
    rcases hx with (hxA | ⟨t, htErase, hxt⟩) | hxs
    · exact Or.inl hxA
    · exact Or.inr ⟨t, htErase.2, hxt⟩
    · exact Or.inr ⟨s, hs, hxs⟩

/-- Helper for Lemma 10.4.4: the connecting map `π_(q + 2)(X, x) → π_(q + 2)(X, A, x)` sends the
unit class to the unit class. -/
private theorem pairLoopToRelativeHomotopyGroupMap_one {Y : Type*} [TopologicalSpace Y]
    (B : Set Y) (b : B) (q : ℕ) :
    pairLoopToRelativeHomotopyGroupMap B b q 1 = 1 := by
  -- Unfold the transported definition and reduce to the standard homotopy-group map lemma.
  cases relativeHomotopyGroup_succ (q + 1) B b
  change homotopyGroupMap (pairLoopToRelativePathSpaceMap B b) (q + 1) (Path.refl b.1) 1 = 1
  exact homotopyGroupMap_one (pairLoopToRelativePathSpaceMap B b) q (Path.refl b.1)

/-- Helper for Lemma 10.4.4: the positive-degree pair boundary map is multiplicative. -/
private noncomputable def pairHomotopyBoundaryMulHom {Y : Type*} [TopologicalSpace Y]
    (B : Set Y) (b : B) (q : ℕ) :
    relativeHomotopyGroup (q + 1).succPNat B b →* π_ (q + 1) B b := by
  -- Rewrite the relative owner as the path-space homotopy group, then use the endpoint-induced
  -- multiplicative map.
  cases relativeHomotopyGroup_succ (q + 1) B b
  exact (pairRelativeEndpointMap B b).eStarMulHomOverEq q (pairRelativeEndpointMap_refl B b)

/-- Helper for Lemma 10.4.4: the bundled multiplicative boundary map has the same underlying
function as `pairHomotopyBoundaryMap`. -/
private theorem pairHomotopyBoundaryMulHom_apply {Y : Type*} [TopologicalSpace Y]
    (B : Set Y) (b : B) (q : ℕ)
    (u : relativeHomotopyGroup (q + 1).succPNat B b) :
    pairHomotopyBoundaryMulHom B b q u = pairHomotopyBoundaryMap B b q u := by
  -- Both owners are definitionally the same transported endpoint map after opening the relative
  -- homotopy-group spelling.
  cases relativeHomotopyGroup_succ (q + 1) B b
  rfl

/-- Helper for Lemma 10.4.4: a nonempty finite sigma-family of cells contains one of maximal
dimension. -/
private theorem exists_mem_maxCellDim
    {T : Finset (Σ m, cell (Set.univ : Set X) m)} (hT : T.Nonempty) :
    ∃ s ∈ T, ∀ t ∈ T, t.1 ≤ s.1 := by
  obtain ⟨s, hsT, hsSup⟩ := Finset.exists_mem_eq_sup T hT fun t ↦ t.1
  refine ⟨s, hsT, ?_⟩
  intro t htT
  -- Every other cell dimension is bounded by the chosen supremum-attaining cell.
  calc
    t.1 ≤ T.sup fun u ↦ u.1 := Finset.le_sup htT
    _ = s.1 := hsSup

/-- Helper for Lemma 10.4.4: once the image lands in a frontier-closed finite family of cells all
above degree `q`, the remaining proof is the maximal-cell induction. -/
private theorem relativeDiskBoundaryClass_eq_constant_of_frontierClosedPrunedSupport
    {q : ℕ+} {a : A} (f : relativeDiskBoundaryPointedMap q A a)
    (T : Finset (Σ m, cell (Set.univ : Set X) m))
    (hCover :
      Set.range f.1 ⊆
        A ∪ ⋃ s ∈ T, closedCell (C := (Set.univ : Set X)) s.1 s.2)
    (hDim : ∀ s ∈ T, (q : ℕ) < s.1)
    (hFrontier :
      ∀ s ∈ T,
        cellFrontier (C := (Set.univ : Set X)) s.1 s.2 ⊆
          A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2) :
    (⟦f⟧ : relativeDiskBoundaryPointedHomotopyClass q A a) =
      ⟦constantRelativeDiskBoundaryPointedMap (A := A) q a⟧ := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨s, hsT, hsMax⟩ := exists_mem_maxCellDim (A := A) hT
    let B : Set X :=
      A ∪ ⋃ t ∈ T.erase s, closedCell (C := (Set.univ : Set X)) t.1 t.2
    have hCoverSingle :
        Set.range f.1 ⊆ B ∪ closedCell (C := (Set.univ : Set X)) s.1 s.2 := by
      intro x hx
      have hx' : x ∈ A ∪ ⋃ t ∈ T, closedCell (C := (Set.univ : Set X)) t.1 t.2 := hCover hx
      rw [base_union_finiteClosedCellSigma_eq_erase_union (A := A) T hsT] at hx'
      simpa [B] using hx'
    -- Route correction: the proof is now reduced to the actual missing owner.
    -- TODO: prove the one-cell push-off step for the maximal cell `s` by comparing
    -- `collapseSubsetType (B ∪ closedCell s.1 s.2) B` with the boundary-collapsed disk quotient,
    -- transport the descended class to `𝕊 s.1`, and then combine that with the induction
    -- hypothesis on `T.erase s`.
    -- The current blocker is the quotient-normalized one-cell theorem; the maximal-cell setup is
    -- already isolated in `B`, `hCoverSingle`, and `hsMax`.
    sorry
  · have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    subst hT'
    have hRange : Set.range f.1 ⊆ A := by
      intro x hx
      have hx' : x ∈ A ∪ ⋃ s ∈ (∅ : Finset (Σ m, cell (Set.univ : Set X) m)),
          closedCell (C := (Set.univ : Set X)) s.1 s.2 := hCover hx
      simpa using hx'
    -- With no remaining cells in the support, the class is already constant inside the base.
    exact relativeDiskBoundaryClass_eq_constant_of_range_subset_base (A := A) a f hRange

/-- Helper for Lemma 10.4.4: normalize a finite closed-cell cover to a frontier-closed, pruned
support family before the remaining maximal-cell push-off step. -/
private theorem relativeDiskBoundaryClass_eq_constant_of_finiteClosedCellCover
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n)
    {q : ℕ+} (hq : (q : ℕ) ≤ n) {a : A} (f : relativeDiskBoundaryPointedMap q A a)
    (S : Finset (Σ m, cell (Set.univ : Set X) m))
    (hCover :
      Set.range f.1 ⊆
        A ∪ ⋃ s ∈ S, closedCell (C := (Set.univ : Set X)) s.1 s.2) :
    (⟦f⟧ : relativeDiskBoundaryPointedHomotopyClass q A a) =
      ⟦constantRelativeDiskBoundaryPointedMap (A := A) q a⟧ := by
  obtain ⟨T, hCoverT, hDimT, hFrontierT⟩ :=
    exists_frontierClosedPrunedFiniteClosedCellSigma_of_relativeDiskBoundaryMap
      (A := A) (n := n) h_noCells hq f hCover
  -- The support normalization is now isolated; the only remaining input is the finite-support
  -- maximal-cell induction on `T`.
  exact
    relativeDiskBoundaryClass_eq_constant_of_frontierClosedPrunedSupport
      (A := A) f T hCoverT hDimT hFrontierT

/-- Helper for Lemma 10.4.4: if there are no relative cells up through degree `n`, then every
relative disk-boundary representative in degree `q ≤ n` is homotopic to the constant one. -/
theorem relativeDiskBoundaryNullhomotopic_of_noCellsLE
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n)
    {q : ℕ+} (hq : (q : ℕ) ≤ n) (a : A) :
    ∀ f : relativeDiskBoundaryPointedMap q A a,
      (⟦f⟧ : relativeDiskBoundaryPointedHomotopyClass q A a) =
        ⟦constantRelativeDiskBoundaryPointedMap (A := A) q a⟧ := by
  intro f
  -- Route correction: isolate the genuine geometric input at the disk-boundary level instead of
  -- encoding it first as HELP data for the subtype inclusion.
  obtain ⟨S, hS⟩ :=
    range_subset_base_union_finiteClosedCellSigma_of_relativeDiskBoundaryMap (A := A) f
  -- The remaining geometric step is now isolated behind a frontier-closed finite support.
  exact
    relativeDiskBoundaryClass_eq_constant_of_finiteClosedCellCover
      (A := A) (n := n) h_noCells hq f S hS

/-- Helper for Lemma 10.4.4: the disk-boundary quotient is subsingleton in every degree `q ≤ n`
when the relative CW pair has no cells up through degree `n`. -/
theorem relativeDiskBoundaryPointedHomotopyClassSubsingleton_of_noCellsLE
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n) :
    ∀ {q : ℕ+}, (q : ℕ) ≤ n → ∀ a : A,
      Subsingleton (relativeDiskBoundaryPointedHomotopyClass q A a) := by
  intro q hq a
  refine ⟨?_⟩
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro f g
  -- Collapse both representatives to the constant disk-boundary class.
  calc
    (⟦f⟧ : relativeDiskBoundaryPointedHomotopyClass q A a) =
        ⟦constantRelativeDiskBoundaryPointedMap (A := A) q a⟧ := by
          exact relativeDiskBoundaryNullhomotopic_of_noCellsLE (A := A) h_noCells hq a f
    _ = ⟦g⟧ := by
          symm
          exact relativeDiskBoundaryNullhomotopic_of_noCellsLE (A := A) h_noCells hq a g

/-- Helper for Lemma 10.4.4: the positive-degree relative homotopy groups of `(X, A)` up through
degree `n` are trivial when there are no relative cells up through degree `n`. -/
theorem relativeHomotopyGroupSubsingleton_of_noCellsLE
    {n : ℕ} (h_noCells : NoCellsLE (Set.univ : Set X) A n) :
    ∀ {q : ℕ+}, (q : ℕ) ≤ n → ∀ a : A, Subsingleton (relativeHomotopyGroup q A a) := by
  intro q hq a
  let e :=
    relativeHomotopyGroupEquivRelativeDiskBoundaryPointedHomotopyClass (A := A) q a
  let hDisk :
      Subsingleton (relativeDiskBoundaryPointedHomotopyClass q A a) :=
    relativeDiskBoundaryPointedHomotopyClassSubsingleton_of_noCellsLE (A := A) h_noCells hq a
  refine ⟨?_⟩
  intro x y
  -- Transport the quotient-level triviality back along the Chapter 9 equivalence.
  exact e.injective (@Subsingleton.elim _ hDisk (e x) (e y))

/-- Helper for Lemma 10.4.4: surjectivity of `π₀(A) → π₀(X)` lifts to surjectivity of the
degree-`0` based homotopy-group map induced by `A ↪ X`. -/
theorem subtypeInclusionPiZeroSurjective_of_zerothHomotopySurjective
    (a : A) (h0 : Function.Surjective (zerothHomotopyInclusion A)) :
    Function.Surjective (((TopCat.subtypeInclusion A).hom).eStar 0 a) := by
  let eA : π_ 0 A a ≃ ZerothHomotopy A := HomotopyGroup.pi0EquivZerothHomotopy
  let eX : π_ 0 X a.1 ≃ ZerothHomotopy X := HomotopyGroup.pi0EquivZerothHomotopy
  have hEqMap :
      (((TopCat.subtypeInclusion A).hom).eStar 0 a) = pairSubspaceInclusionHomotopyGroupMap A a 0 := by
    -- The subtype inclusion is the pair-subspace inclusion from Chapter 9.
    simpa [pairSubspaceInclusion] using
      pairSubspaceInclusion_eStar_eq_pairSubspaceInclusionHomotopyGroupMap A a 0
  have hComm :
      eX.toFun ∘ (((TopCat.subtypeInclusion A).hom).eStar 0 a) =
        zerothHomotopyInclusion A ∘ eA.toFun := by
    -- Route correction: use the Chapter 9 pair-subspace comparison instead of the broken
    -- Observation 10.4.3 commutation lemma.
    calc
      eX.toFun ∘ (((TopCat.subtypeInclusion A).hom).eStar 0 a) =
          eX.toFun ∘ pairSubspaceInclusionHomotopyGroupMap A a 0 := by
            rw [hEqMap]
      _ = zerothHomotopyInclusion A ∘ eA.toFun := by
            simpa [eA, eX] using pairSubspaceInclusionPiZero_commutes A a
  intro v
  rcases h0 (eX v) with ⟨u, hu⟩
  refine ⟨eA.symm u, ?_⟩
  -- Transport the component-level surjectivity through the `π₀`/`ZerothHomotopy` bridge.
  apply eX.injective
  calc
    eX (((TopCat.subtypeInclusion A).hom).eStar 0 a (eA.symm u)) =
        zerothHomotopyInclusion A (eA (eA.symm u)) := by
          simpa using congrFun hComm (eA.symm u)
    _ = eX v := by simpa [eX] using hu

end Topology.RelCWComplex

/-- Lemma 10.4.4 (1): if the relative CW complex `(X, A)` has no relative `m`-cells for every
`m ≤ n`, then the pair `(X, A)` is `n`-connected. -/
theorem nConnectedPair_of_noCellsLE
    {X : Type u} [TopologicalSpace X] (A : Set X) [RelCWComplex (Set.univ : Set X) A]
    {n : ℕ} (h_noCells : RelCWComplex.NoCellsLE (Set.univ : Set X) A n) :
    NConnectedPair n A := by
  refine ⟨?_, ?_⟩
  · -- Degree `0` is handled by joining each open-cell point to a basepoint in `A`.
    exact RelCWComplex.zerothHomotopySurjective_of_noCellsLE (A := A)
      (h_noCells.mono (Nat.zero_le n))
  · intro q hq a
    -- Positive degrees reduce to the disk-boundary model isolated above.
    exact RelCWComplex.relativeHomotopyGroupSubsingleton_of_noCellsLE (A := A) h_noCells hq a

namespace Topology.RelCWComplex

variable {X : Type u} [TopologicalSpace X] (A : Set X)
variable [RelCWComplex (Set.univ : Set X) A]

end Topology.RelCWComplex

/-- Helper for Lemma 10.4.4: a cell of dimension `m ≤ n` already lies in the chosen
`n`-skeleton. -/
private theorem closedCell_subset_skeletonSet_of_le
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {m n : ℕ} (hmn : m ≤ n) (j : Topology.CWComplex.cell (Set.univ : Set X) m) :
    Topology.CWComplex.closedCell (C := (Set.univ : Set X)) m j ⊆ CWComplex.skeletonSet X n := by
  -- First place the cell in its own skeleton.
  refine Set.Subset.trans
    (RelCWComplex.closedCell_subset_skeleton (C := (Set.univ : Set X)) m j) ?_
  -- Then use monotonicity to reach the chosen degree `n`.
  simpa [Topology.CWComplex.skeletonSet] using
    (RelCWComplex.skeleton_mono (C := (Set.univ : Set X))
      (m := (m : ℕ∞)) (n := (n : ℕ∞))
      (show (m : ℕ∞) ≤ n from by exact_mod_cast hmn))

/-- Helper for Lemma 10.4.4: an open cell of dimension `m ≤ n` already lies in the chosen
`n`-skeleton. -/
private theorem openCell_subset_skeletonSet_of_le
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {m n : ℕ} (hmn : m ≤ n) (j : Topology.CWComplex.cell (Set.univ : Set X) m) :
    Topology.CWComplex.openCell (C := (Set.univ : Set X)) m j ⊆ CWComplex.skeletonSet X n := by
  -- Reduce to the closed-cell statement proved above.
  refine Set.Subset.trans
    (RelCWComplex.openCell_subset_closedCell (C := (Set.univ : Set X)) m j) ?_
  exact closedCell_subset_skeletonSet_of_le (X := X) hmn j

/-- Helper for Lemma 10.4.4: the chosen skeleton `X^n` is a closed subset of `X`. -/
private theorem skeletonSet_isClosed
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    IsClosed (CWComplex.skeletonSet X n) := by
  -- The classical skeleton is a subcomplex, hence closed by definition.
  simpa [Topology.CWComplex.skeletonSet] using
    (Topology.CWComplex.skeleton (Set.univ : Set X) n).closed

/-- Helper for Lemma 10.4.4: the retained cells `{j // n < m}` still have pairwise disjoint open
images. -/
private theorem skeletonRelativePairwiseDisjoint
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    Set.PairwiseDisjoint
      (Set.univ : Set (Σ m, {j : Topology.CWComplex.cell (Set.univ : Set X) m // n < m}))
      (fun mi ↦ Topology.CWComplex.map (C := (Set.univ : Set X)) mi.1 mi.2.1 '' Metric.ball 0 1) := by
  -- Reuse the ambient disjointness after forgetting the `n < m` witness.
  intro ⟨m, i⟩ _ ⟨l, j⟩ _ hne
  refine @RelCWComplex.pairwiseDisjoint' _ _ (Set.univ : Set X) (∅ : Set X) _
    ⟨m, i.1⟩ trivial ⟨l, j.1⟩ trivial ?_
  exact (Function.injective_id.sigma_map fun _ ↦ Subtype.val_injective).ne hne

/-- Helper for Lemma 10.4.4: every retained cell is disjoint from the base skeleton `X^n`. -/
private theorem skeletonRelativeDisjointBase
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n m : ℕ)
    (j : {i : Topology.CWComplex.cell (Set.univ : Set X) m // n < m}) :
    Disjoint (Topology.CWComplex.map (C := (Set.univ : Set X)) m j.1 '' Metric.ball 0 1)
      (CWComplex.skeletonSet X n) := by
  -- A cell of dimension `> n` is disjoint from the `n`-skeleton.
  simpa [RelCWComplex.openCell, Topology.CWComplex.skeletonSet] using
    (RelCWComplex.disjoint_skeleton_openCell (C := (Set.univ : Set X))
      (n := (n : ℕ∞)) (m := m) (j := j.1)
      (show (n : ℕ∞) < m from by exact_mod_cast j.2)).symm

/-- Helper for Lemma 10.4.4: the frontier of a retained cell lies in the base skeleton together
with finitely many retained lower-dimensional closed cells. -/
private theorem skeletonRelativeMapsTo
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n m : ℕ)
    (i : {j : Topology.CWComplex.cell (Set.univ : Set X) m // n < m}) :
    ∃ cells : Π l, Finset {j : Topology.CWComplex.cell (Set.univ : Set X) l // n < l},
      Set.MapsTo (Topology.CWComplex.map (C := (Set.univ : Set X)) m i.1) (Metric.sphere 0 1)
        (CWComplex.skeletonSet X n ∪
          ⋃ (l < m) (j ∈ cells l),
            Topology.CWComplex.map (C := (Set.univ : Set X)) l j.1 '' Metric.closedBall 0 1) := by
  classical
  obtain ⟨J, hJ⟩ := Topology.CWComplex.mapsTo (C := (Set.univ : Set X)) m i.1
  let cells : Π l, Finset {j : Topology.CWComplex.cell (Set.univ : Set X) l // n < l} := fun l ↦
    if hnl : n < l then
      (J l).attach.image fun j ↦
        (⟨j.1, hnl⟩ : {j : Topology.CWComplex.cell (Set.univ : Set X) l // n < l})
    else
      ∅
  refine ⟨cells, ?_⟩
  intro x hx
  specialize hJ hx
  simp only [Set.mem_union, Set.mem_iUnion, exists_prop] at hJ ⊢
  obtain ⟨l, hlm, j, hjJ, hxj⟩ := hJ
  by_cases hln : l ≤ n
  · -- Low-dimensional cells are absorbed into the base skeleton.
    exact Or.inl (closedCell_subset_skeletonSet_of_le (X := X) hln j hxj)
  · -- High-dimensional cells remain as relative cells of the filtered structure.
    refine Or.inr ⟨l, hlm, ⟨j, Nat.lt_of_not_ge hln⟩, ?_, hxj⟩
    simp [cells, Nat.lt_of_not_ge hln, hjJ]

/-- Helper for Lemma 10.4.4: the ambient weak-topology axiom yields the weak-topology axiom for
the filtered relative CW structure on `(X, X^n)`. -/
private theorem skeletonRelativeClosed
    {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) (A : Set X) (hA : A ⊆ (Set.univ : Set X)) :
    ((∀ m (j : {j : Topology.CWComplex.cell (Set.univ : Set X) m // n < m}),
        IsClosed
          (A ∩ Topology.CWComplex.map (C := (Set.univ : Set X)) m j.1 '' Metric.closedBall 0 1)) ∧
      IsClosed (A ∩ CWComplex.skeletonSet X n)) →
    IsClosed A := by
  intro hClosed
  -- Reduce the filtered weak-topology statement to the ambient CW weak-topology criterion.
  rw [CWComplex.closed (C := (Set.univ : Set X)) A hA]
  intro m j
  by_cases hmn : m ≤ n
  · -- Low-dimensional closed cells lie inside the base skeleton.
    have hsubset := closedCell_subset_skeletonSet_of_le (X := X) hmn j
    have hEq :
        A ∩ RelCWComplex.closedCell (C := (Set.univ : Set X)) m j =
          (A ∩ CWComplex.skeletonSet X n) ∩
            RelCWComplex.closedCell (C := (Set.univ : Set X)) m j := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨hx.1, hsubset hx.2⟩, hx.2⟩
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
    rw [hEq]
    exact hClosed.2.inter
      (RelCWComplex.isClosed_closedCell (C := (Set.univ : Set X)) (D := (∅ : Set X))
        (n := m) (i := j))
  · -- High-dimensional closed cells are exactly the retained relative cells.
    exact hClosed.1 m ⟨j, Nat.lt_of_not_ge hmn⟩

/-- Helper for Lemma 10.4.4: the base skeleton together with the retained closed cells still
covers the whole space. -/
private theorem skeletonRelativeUnion
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (n : ℕ) :
    CWComplex.skeletonSet X n ∪
      ⋃ (m : ℕ) (j : {j : Topology.CWComplex.cell (Set.univ : Set X) m // n < m}),
        Topology.CWComplex.map (C := (Set.univ : Set X)) m j.1 '' Metric.closedBall 0 1 =
      (Set.univ : Set X) := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hxSk : x ∈ CWComplex.skeletonSet X n
    · exact Or.inl hxSk
    · have hxOpen :
          x ∈ ⋃ (m : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) m),
            Topology.CWComplex.openCell (C := (Set.univ : Set X)) m j := by
        have hxUniv : x ∈ (Set.univ : Set X) := trivial
        rw [← Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))] at hxUniv
        exact hxUniv
      simp only [Set.mem_iUnion] at hxOpen
      rcases hxOpen with ⟨m, j, hxj⟩
      have hnm : n < m := by
        by_contra hnm
        exact hxSk (openCell_subset_skeletonSet_of_le (X := X) (Nat.le_of_not_gt hnm) j hxj)
      refine Or.inr <| Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨⟨j, hnm⟩, ?_⟩⟩
      exact RelCWComplex.openCell_subset_closedCell (C := (Set.univ : Set X)) m j hxj

/-- Helper for Lemma 10.4.4: the pair `(X, X^n)` carries the filtered relative CW structure
obtained by keeping precisely the cells of dimensions `> n`. -/
abbrev skeletonRelativeCW
    {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) :
    RelCWComplex (Set.univ : Set X) (CWComplex.skeletonSet X n) :=
  { cell := fun m ↦ {j : Topology.CWComplex.cell (Set.univ : Set X) m // n < m}
    map := fun m j ↦ Topology.CWComplex.map (C := (Set.univ : Set X)) m j.1
    source_eq := fun m j ↦ Topology.CWComplex.source_eq (C := (Set.univ : Set X)) m j.1
    continuousOn := fun m j ↦ Topology.CWComplex.continuousOn (C := (Set.univ : Set X)) m j.1
    continuousOn_symm := fun m j ↦
      Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set X)) m j.1
    pairwiseDisjoint' := skeletonRelativePairwiseDisjoint (X := X) n
    disjointBase' := skeletonRelativeDisjointBase (X := X) n
    mapsTo := skeletonRelativeMapsTo (X := X) n
    closed' := skeletonRelativeClosed (X := X) n
    isClosedBase := skeletonSet_isClosed (X := X) n
    union' := skeletonRelativeUnion (X := X) n }

/-- Helper for Lemma 10.4.4: in the filtered relative CW structure on `(X, X^n)`, there are no
relative cells of dimensions `m ≤ n`. -/
theorem noCellsLE_skeletonRelativeCW
    {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) :
    (skeletonRelativeCW (X := X) n).NoCellsLEOf n := by
  letI : RelCWComplex (Set.univ : Set X) (CWComplex.skeletonSet X n) :=
    skeletonRelativeCW (X := X) n
  -- The filtered relative cells are exactly the subtypes `{j // n < m}`, which are empty in
  -- degrees `m ≤ n`.
  intro m hm
  -- Unfold the retained cell type and observe that the inequality `n < m` is impossible.
  simpa [skeletonRelativeCW] using
    (show IsEmpty {j : Topology.CWComplex.cell (Set.univ : Set X) m // n < m} from
      ⟨fun j ↦ (Nat.not_lt_of_ge hm j.2).elim⟩)

/-- Lemma 10.4.4 (2): for a CW complex `X`, the pair `(X, X^n)` is `n`-connected, where `X^n`
is the canonical skeleton `CWComplex.skeleton (Set.univ : Set X) n`. -/
theorem nConnectedPair_skeleton
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) :
    NConnectedPair n (CWComplex.skeletonSet X n) := by
  let _ : T2Space X := instT2SpaceOfUnivCWComplex
  let hRel : RelCWComplex (Set.univ : Set X) (CWComplex.skeletonSet X n) :=
    skeletonRelativeCW (X := X) n
  letI : RelCWComplex (Set.univ : Set X) (CWComplex.skeletonSet X n) := hRel
  have hNo :
      RelCWComplex.NoCellsLE (Set.univ : Set X) (CWComplex.skeletonSet X n) n := by
    simpa [RelCWComplex.NoCellsLEOf] using noCellsLE_skeletonRelativeCW (X := X) n
  -- Reduce the skeleton corollary to the first part using the filtered relative CW structure.
  exact nConnectedPair_of_noCellsLE (A := CWComplex.skeletonSet X n)
    hNo
