import Mathlib.Topology.CWComplex.Classical.Subcomplex

open Topology
open scoped Set.Notation

universe u

namespace Topology.CWComplex

/-- Helper for Lemma 10.2.2: every point of an absolute CW complex lies in some closed cell. -/
theorem existsClosedCellContainingPoint
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x : X) :
    ∃ a : Σ n, cell (Set.univ : Set X) n,
      x ∈ closedCell (C := (Set.univ : Set X)) a.1 a.2 := by
  -- The closed cells cover the whole absolute CW complex.
  have hx :
      x ∈ ⋃ (n : ℕ) (j : cell (Set.univ : Set X) n),
        closedCell (C := (Set.univ : Set X)) n j := by
    rw [union (C := (Set.univ : Set X))]
    trivial
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨n, j, hxj⟩
  exact ⟨⟨n, j⟩, hxj⟩

/-- Helper for Lemma 10.2.2: a finite union of absolute-CW closed cells is compact. -/
theorem isCompact_iUnion_closedCell_finset
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (I : Finset (Σ n, cell (Set.univ : Set X) n)) :
    IsCompact (⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 : Set X) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      -- The empty finite family contributes the empty compact subset.
      simp
  | @insert a I ha hI =>
      -- Add one more compact closed cell to the previously compact finite carrier.
      have hUnion :
          (⋃ b ∈ insert a I, closedCell (C := (Set.univ : Set X)) b.1 b.2 : Set X) =
            closedCell (C := (Set.univ : Set X)) a.1 a.2 ∪
              ⋃ b ∈ I, closedCell (C := (Set.univ : Set X)) b.1 b.2 := by
        ext x
        simp
      rw [hUnion]
      exact (isCompact_closedCell (C := (Set.univ : Set X)) (n := a.1) (i := a.2)).union hI

/-- Helper for Lemma 10.2.2: any two points of an absolute CW complex lie in a compact finite
union of closed cells. -/
theorem existsCompactClosedCellCarrierContainingPair
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x y : X) :
    ∃ I : Finset (Σ n, cell (Set.univ : Set X) n),
      x ∈ ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 ∧
      y ∈ ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 ∧
      IsCompact (⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 : Set X) := by
  classical
  -- First choose one closed cell containing each point.
  obtain ⟨ax, hx⟩ := existsClosedCellContainingPoint x
  obtain ⟨ay, hy⟩ := existsClosedCellContainingPoint y
  let I : Finset (Σ n, cell (Set.univ : Set X) n) := {ax, ay}
  refine ⟨I, ?_, ?_, ?_⟩
  · -- The first chosen cell contains `x`.
    exact Set.mem_iUnion.2 ⟨ax, Set.mem_iUnion.2 ⟨by simp [I], hx⟩⟩
  · -- The second chosen cell contains `y`.
    exact Set.mem_iUnion.2 ⟨ay, Set.mem_iUnion.2 ⟨by simp [I], hy⟩⟩
  · -- Finite unions of closed-cell carriers are compact.
    simpa [I] using isCompact_iUnion_closedCell_finset I

/-- Helper for Lemma 10.2.2: every closed cell is contained in a finite family of cells that is
closed under the frontier recursion. -/
theorem existsFiniteClosureCarrierContainingCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (a : Σ n, cell (Set.univ : Set X) n) :
    ∃ I : Finset (Σ n, cell (Set.univ : Set X) n), a ∈ I ∧
      ∀ b ∈ I,
        cellFrontier (C := (Set.univ : Set X)) b.1 b.2 ⊆
          ⋃ c ∈ I, ⋃ (_ : c.1 < b.1), openCell (C := (Set.univ : Set X)) c.1 c.2 := by
  classical
  rcases a with ⟨n, j⟩
  induction n using Nat.case_strong_induction_on with
  | hz =>
      -- In dimension `0`, the singleton family `{j}` is already frontier-closed.
      refine ⟨{⟨0, j⟩}, by simp, ?_⟩
      intro b hb
      have hb' : b = ⟨0, j⟩ := by simpa using hb
      subst hb'
      simp [RelCWComplex.cellFrontier_zero_eq_empty]
  | hi n ih =>
      -- Close the chosen `(n + 1)`-cell under the finitely many lower-dimensional cells appearing
      -- in its frontier, and recurse on each of those lower cells.
      obtain ⟨J, hJ⟩ :=
        cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) (n + 1) j
      have hrec :
          ∀ l < n + 1, ∀ y : cell (Set.univ : Set X) l,
            ∃ I : Finset (Σ m, cell (Set.univ : Set X) m), ⟨l, y⟩ ∈ I ∧
              ∀ b ∈ I,
                cellFrontier (C := (Set.univ : Set X)) b.1 b.2 ⊆
                  ⋃ c ∈ I, ⋃ (_ : c.1 < b.1), openCell (C := (Set.univ : Set X)) c.1 c.2 := by
        intro l hl y
        exact ih l (Nat.le_of_lt_succ hl) y
      choose p hp_mem hp_frontier using hrec
      let I : Finset (Σ m, cell (Set.univ : Set X) m) :=
        {⟨n + 1, j⟩} ∪
          (Finset.range (n + 1)).attach.biUnion fun l =>
            (J l.1).biUnion fun y ↦ p l.1 (Finset.mem_range.mp l.2) y
      refine ⟨I, ?_, ?_⟩
      · -- The root cell is explicitly inserted in degree `n + 1`.
        simp [I]
      · intro b hb
        have hb_cases :
            b = ⟨n + 1, j⟩ ∨
              ∃ l, ∃ hl : l < n + 1, ∃ y : cell (Set.univ : Set X) l,
                y ∈ J l ∧ b ∈ p l hl y := by
          rcases Finset.mem_union.mp hb with hbroot | hbrec
          · exact Or.inl (by simpa using hbroot)
          · rcases Finset.mem_biUnion.mp hbrec with ⟨l, _, hbrec⟩
            rcases Finset.mem_biUnion.mp hbrec with ⟨y, hyJ, hby⟩
            exact Or.inr ⟨l.1, Finset.mem_range.mp l.2, y, hyJ, hby⟩
        rcases hb_cases with rfl | ⟨l, hl, y, hyJ, hby⟩
        · -- The root cell uses the original frontier cover, and the recursive families contain
          -- each frontier cell from `J`.
          intro x hx
          have hxJ := hJ hx
          simp only [Set.mem_iUnion, exists_prop] at hxJ ⊢
          obtain ⟨l, hln, y, hyJ', hxy⟩ := hxJ
          refine ⟨⟨l, y⟩, ?_, hln, hxy⟩
          have hyRoot : ⟨l, y⟩ ∈ p l hln y := hp_mem l hln y
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr
            ⟨⟨l, Finset.mem_range.mpr hln⟩, by simp, Finset.mem_biUnion.mpr ⟨y, hyJ', hyRoot⟩⟩
        · -- Any lower-dimensional selected cell comes from one recursive family, so its frontier
          -- closure follows from that family's frontier closure and the inclusion into `I`.
          have hbyFrontier := hp_frontier l hl y b hby
          intro x hx
          have hxrec := hbyFrontier hx
          simp only [Set.mem_iUnion, exists_prop] at hxrec ⊢
          obtain ⟨c, hcMem, hcb, hxc⟩ := hxrec
          refine ⟨c, ?_, hcb, hxc⟩
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_biUnion.mpr
            ⟨⟨l, Finset.mem_range.mpr hl⟩, by simp, Finset.mem_biUnion.mpr ⟨y, hyJ, hcMem⟩⟩

/-- Helper for Lemma 10.2.2: any two points of an absolute CW complex lie in one finite
frontier-closed family of closed cells. -/
theorem existsFiniteClosureCarrierContainingPair
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x y : X) :
    ∃ I : Finset (Σ n, cell (Set.univ : Set X) n),
      x ∈ ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 ∧
      y ∈ ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 ∧
      (∀ b ∈ I,
        cellFrontier (C := (Set.univ : Set X)) b.1 b.2 ⊆
          ⋃ c ∈ I, ⋃ (_ : c.1 < b.1), openCell (C := (Set.univ : Set X)) c.1 c.2) := by
  classical
  -- First choose one closed cell containing each point and close each choice under frontiers.
  obtain ⟨ax, hxax⟩ := existsClosedCellContainingPoint x
  obtain ⟨ay, hyay⟩ := existsClosedCellContainingPoint y
  obtain ⟨Ix, haxIx, hIx⟩ := existsFiniteClosureCarrierContainingCell ax
  obtain ⟨Iy, hayIy, hIy⟩ := existsFiniteClosureCarrierContainingCell ay
  let I := Ix ∪ Iy
  refine ⟨I, ?_, ?_, ?_⟩
  · -- The closed cell chosen for `x` remains in the union carrier.
    refine Set.mem_iUnion.2 ⟨ax, Set.mem_iUnion.2 ⟨?_, hxax⟩⟩
    exact Finset.mem_union.mpr <| Or.inl haxIx
  · -- The closed cell chosen for `y` remains in the union carrier.
    refine Set.mem_iUnion.2 ⟨ay, Set.mem_iUnion.2 ⟨?_, hyay⟩⟩
    exact Finset.mem_union.mpr <| Or.inr hayIy
  · -- Each selected cell comes from one of the two frontier-closed families.
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · intro z hz
      have hz' := hIx b hb hz
      simp only [Set.mem_iUnion, exists_prop] at hz' ⊢
      obtain ⟨c, hc, hcb, hzc⟩ := hz'
      exact ⟨c, Finset.mem_union.mpr <| Or.inl hc, hcb, hzc⟩
    · intro z hz
      have hz' := hIy b hb hz
      simp only [Set.mem_iUnion, exists_prop] at hz' ⊢
      obtain ⟨c, hc, hcb, hzc⟩ := hz'
      exact ⟨c, Finset.mem_union.mpr <| Or.inr hc, hcb, hzc⟩

/-- Helper for Lemma 10.2.2: the finite frontier-closed carrier built for a point-pair is also a
compact union of closed cells. -/
theorem existsFiniteCompactClosureCarrierContainingPair
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x y : X) :
    ∃ I : Finset (Σ n, cell (Set.univ : Set X) n),
      x ∈ ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 ∧
      y ∈ ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 ∧
      (∀ b ∈ I,
        cellFrontier (C := (Set.univ : Set X)) b.1 b.2 ⊆
          ⋃ c ∈ I, ⋃ (_ : c.1 < b.1), openCell (C := (Set.univ : Set X)) c.1 c.2) ∧
      IsCompact (⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2 : Set X) := by
  -- Package the already-built frontier-closed carrier together with the finite closed-cell
  -- compactness theorem so the remaining separation proof can work with one stabilized object.
  obtain ⟨I, hx, hy, hI⟩ := existsFiniteClosureCarrierContainingPair x y
  refine ⟨I, hx, hy, hI, ?_⟩
  exact isCompact_iUnion_closedCell_finset I

/-- Helper for Lemma 10.2.2: the sigma-indexed owners of absolute-CW closed cells. -/
private abbrev closedCellOwner
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :=
  Σ n, cell (Set.univ : Set X) n

/-- Helper for Lemma 10.2.2: the carrier of a finite family of absolute-CW closed cells. -/
private def closedCellCarrier
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (I : Finset (closedCellOwner X)) : Set X :=
  ⋃ a ∈ I, closedCell (C := (Set.univ : Set X)) a.1 a.2

/-- Helper for Lemma 10.2.2: a finite family is frontier-closed when every chosen frontier is
already contained in the closed-cell carrier. -/
private def frontierClosedCellFamily
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (I : Finset (closedCellOwner X)) : Prop :=
  ∀ a ∈ I,
    cellFrontier (C := (Set.univ : Set X)) a.1 a.2 ⊆ closedCellCarrier X I

/-- Helper for Lemma 10.2.2: a finite family is frontier-open-covered when every chosen frontier
is already contained in lower-dimensional selected open cells. -/
private def frontierOpenCellFamily
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (I : Finset (closedCellOwner X)) : Prop :=
  ∀ a ∈ I,
    cellFrontier (C := (Set.univ : Set X)) a.1 a.2 ⊆
      ⋃ c ∈ I, ⋃ (_ : c.1 < a.1), openCell (C := (Set.univ : Set X)) c.1 c.2

/-- Helper for Lemma 10.2.2: every chosen closed cell is contained in its finite carrier. -/
private theorem closedCell_subset_closedCellCarrier_of_mem
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {I : Finset (closedCellOwner X)} {a : closedCellOwner X} (ha : a ∈ I) :
    closedCell (C := (Set.univ : Set X)) a.1 a.2 ⊆ closedCellCarrier X I := by
  -- A selected owner contributes one summand of the sigma-indexed carrier union.
  intro x hx
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hx⟩⟩

/-- Helper for Lemma 10.2.2: the frontier-open-cell carrier returned by
`existsFiniteCompactClosureCarrierContainingPair` is automatically frontier-closed as a
closed-cell carrier. -/
private theorem frontierClosedCellFamily_of_frontierOpenCover
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {I : Finset (closedCellOwner X)}
    (hI :
      ∀ b ∈ I,
        cellFrontier (C := (Set.univ : Set X)) b.1 b.2 ⊆
          ⋃ c ∈ I, ⋃ (_ : c.1 < b.1), openCell (C := (Set.univ : Set X)) c.1 c.2) :
    frontierClosedCellFamily X I := by
  -- Route correction: convert the lower-dimensional open-cell frontier cover into the stronger
  -- closed-cell carrier language needed for the subtype transport step.
  intro a ha x hx
  have hxCover := hI a ha hx
  simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hxCover ⊢
  rcases hxCover with ⟨c, hc, _, hxc⟩
  exact ⟨c, hc, openCell_subset_closedCell _ _ hxc⟩

/-- Helper for Lemma 10.2.2: every carrier point already lies in one selected open cell of a
finite frontier-open-covered family. -/
private theorem pointMemSelectedOpenCellOfFrontierOpenCover
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {I : Finset (closedCellOwner X)} (hI : frontierOpenCellFamily X I)
    {x : X} (hxI : x ∈ closedCellCarrier X I) :
    ∃ a : closedCellOwner X, a ∈ I ∧ x ∈ openCell (C := (Set.univ : Set X)) a.1 a.2 := by
  -- Start from one selected closed-cell witness for `x`, then descend to a selected open cell if
  -- `x` happens to lie on that cell's frontier.
  simp only [closedCellCarrier, Set.mem_iUnion, exists_prop] at hxI
  rcases hxI with ⟨a, ha, hxaClosed⟩
  by_cases hxaOpen : x ∈ openCell (C := (Set.univ : Set X)) a.1 a.2
  · exact ⟨a, ha, hxaOpen⟩
  · have hxaFrontier : x ∈ cellFrontier (C := (Set.univ : Set X)) a.1 a.2 := by
      have hxaUnion :
          x ∈ cellFrontier (C := (Set.univ : Set X)) a.1 a.2 ∪
            openCell (C := (Set.univ : Set X)) a.1 a.2 := by
        simpa [RelCWComplex.cellFrontier_union_openCell_eq_closedCell
          (C := (Set.univ : Set X)) a.1 a.2] using hxaClosed
      rcases hxaUnion with hxaFrontier | hxaOpen'
      · exact hxaFrontier
      · exact False.elim (hxaOpen hxaOpen')
    have hxCover := hI a ha hxaFrontier
    simp only [Set.mem_iUnion, exists_prop] at hxCover
    rcases hxCover with ⟨b, hb, _, hxbOpen⟩
    exact ⟨b, hb, hxbOpen⟩

/-- Helper for Lemma 10.2.2: a finite frontier-open-covered carrier is exactly the union of its
selected open cells. -/
private theorem closedCellCarrier_eq_iUnion_openCell_of_frontierOpenCover
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {I : Finset (closedCellOwner X)} (hI : frontierOpenCellFamily X I) :
    closedCellCarrier X I = ⋃ a ∈ I, openCell (C := (Set.univ : Set X)) a.1 a.2 := by
  -- Every carrier point belongs to some selected open cell, while every selected open cell stays
  -- inside its chosen closed cell and hence inside the carrier.
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hxOpen⟩ :=
      pointMemSelectedOpenCellOfFrontierOpenCover (X := X) hI hx
    exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hxOpen⟩⟩
  · intro hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    rcases hx with ⟨a, ha, hxOpen⟩
    exact closedCell_subset_closedCellCarrier_of_mem X ha (openCell_subset_closedCell _ _ hxOpen)

/-- Helper for Lemma 10.2.2: any two points lie in one compact finite frontier-closed carrier of
closed cells. -/
private theorem existsFiniteFrontierClosedCompactCarrierContainingPair
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x y : X) :
    ∃ I : Finset (closedCellOwner X),
      frontierClosedCellFamily X I ∧
      x ∈ closedCellCarrier X I ∧
      y ∈ closedCellCarrier X I ∧
      IsCompact (closedCellCarrier X I) := by
  -- Package the previously constructed pair-carrier in the carrier language used by the subtype
  -- specialization pivot.
  obtain ⟨I, hx, hy, hI, hCompact⟩ := existsFiniteCompactClosureCarrierContainingPair x y
  refine ⟨I, frontierClosedCellFamily_of_frontierOpenCover X hI, hx, hy, ?_⟩
  simpa [closedCellCarrier] using hCompact

/-- Helper for Lemma 10.2.2: specialization transports to any closed-cell carrier containing both
points. -/
private theorem specializes_subtype_of_mem_closedCellCarrier
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {I : Finset (closedCellOwner X)} {x y : X}
    (hxI : x ∈ closedCellCarrier X I) (hyI : y ∈ closedCellCarrier X I) (hxy : x ⤳ y) :
    (⟨x, hxI⟩ : closedCellCarrier X I) ⤳ ⟨y, hyI⟩ := by
  -- The subtype embedding is inducing, so specialization is detected after forgetting to the
  -- ambient space.
  exact (subtype_specializes_iff _ _).2 hxy

/-- Helper for Lemma 10.2.2: an absolute-CW open cell is exactly the target of its
characteristic partial equivalence. -/
theorem openCell_eq_target
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) :
    openCell (C := (Set.univ : Set X)) n j =
      (map (C := (Set.univ : Set X)) n j).target := by
  -- Rewrite the open cell as the image of the chart source and then use the `PartialEquiv` API.
  rw [RelCWComplex.openCell, ← source_eq (C := (Set.univ : Set X)) n j]
  exact (map (C := (Set.univ : Set X)) n j).image_source_eq_target

/-- Helper for Lemma 10.2.2: on a fixed absolute-CW open cell, equality is detected by the
inverse chart. -/
theorem eq_of_symm_eq_of_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x y : X}
    (hx : x ∈ openCell (C := (Set.univ : Set X)) n j)
    (hy : y ∈ openCell (C := (Set.univ : Set X)) n j)
    (hxy : (map (C := (Set.univ : Set X)) n j).symm x =
      (map (C := (Set.univ : Set X)) n j).symm y) :
    x = y := by
  -- Convert open-cell membership into target membership so the `PartialEquiv.right_inv` API
  -- applies on both sides.
  have hxTarget : x ∈ (map (C := (Set.univ : Set X)) n j).target := by
    simpa [openCell_eq_target (X := X) j] using hx
  have hyTarget : y ∈ (map (C := (Set.univ : Set X)) n j).target := by
    simpa [openCell_eq_target (X := X) j] using hy
  calc
    x = map (C := (Set.univ : Set X)) n j ((map (C := (Set.univ : Set X)) n j).symm x) := by
      symm
      exact (map (C := (Set.univ : Set X)) n j).right_inv hxTarget
    _ = map (C := (Set.univ : Set X)) n j ((map (C := (Set.univ : Set X)) n j).symm y) := by
      rw [hxy]
    _ = y := (map (C := (Set.univ : Set X)) n j).right_inv hyTarget

/-- Helper for Lemma 10.2.2: inside a fixed absolute-CW open cell, the singleton of a point in
that cell is closed for the subspace topology on the open cell. -/
theorem isClosed_openCellSingleton
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hx : x ∈ openCell (C := (Set.univ : Set X)) n j) :
    IsClosed
      ((Subtype.val :
        openCell (C := (Set.univ : Set X)) n j → X) ⁻¹' ({x} : Set X)) := by
  -- Restrict the inverse chart to the open-cell subtype; continuity follows from the stored
  -- `continuousOn_symm` axiom.
  let chartInv : openCell (C := (Set.univ : Set X)) n j → Fin n → ℝ :=
    (openCell (C := (Set.univ : Set X)) n j).restrict ((map (C := (Set.univ : Set X)) n j).symm)
  have hcontChart :
      Continuous chartInv := by
    -- Convert the continuity-on-target statement into continuity on the open-cell subtype.
    have hcontOnSymm := continuousOn_symm (C := (Set.univ : Set X)) n j
    rw [continuousOn_iff_continuous_restrict] at hcontOnSymm
    have hopen : openCell (C := (Set.univ : Set X)) n j =
        (map (C := (Set.univ : Set X)) n j).target :=
      openCell_eq_target (X := X) j
    change Continuous
      ((openCell (C := (Set.univ : Set X)) n j).restrict
        ((map (C := (Set.univ : Set X)) n j).symm))
    rw [hopen]
    exact hcontOnSymm
  have hclosedFiber :
      IsClosed (chartInv ⁻¹' ({chartInv ⟨x, hx⟩} : Set (Fin n → ℝ))) := by
    -- Singletons are closed in Euclidean space, so their chart fibers are closed in the open
    -- cell subtype.
    simpa using (isClosed_singleton.preimage hcontChart)
  have hFiberEq :
      chartInv ⁻¹' ({chartInv ⟨x, hx⟩} : Set (Fin n → ℝ)) =
        (Subtype.val :
          openCell (C := (Set.univ : Set X)) n j → X) ⁻¹' ({x} : Set X) := by
    -- The previous inverse-chart uniqueness lemma turns equality of chart coordinates into
    -- equality of points inside the chosen open cell.
    ext z
    constructor
    · intro hz
      have hzEq : chartInv z = chartInv ⟨x, hx⟩ := by simpa using hz
      have hzx :
          z.1 = x := eq_of_symm_eq_of_mem_openCell (X := X) j z.2 hx hzEq
      simpa [hzx]
    · intro hz
      have hz' : z.1 = x := by simpa using hz
      simpa [chartInv, hz']
  rw [← hFiberEq]
  exact hclosedFiber

/-- Helper for Lemma 10.2.2: if a point misses the open part of a closed cell, then its singleton
meets that closed cell exactly along the frontier. -/
theorem singleton_inter_closedCell_eq_singleton_inter_cellFrontier_of_not_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hxOpen : x ∉ openCell (C := (Set.univ : Set X)) n j) :
    ({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) n j =
      ({x} : Set X) ∩ cellFrontier (C := (Set.univ : Set X)) n j := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyEq, hyClosed⟩
    subst hyEq
    -- A point of the closed cell is in the frontier unless it lies in the open cell.
    have hyFrontier : y ∈ cellFrontier (C := (Set.univ : Set X)) n j := by
      have hyUnion :
          y ∈ cellFrontier (C := (Set.univ : Set X)) n j ∪
            openCell (C := (Set.univ : Set X)) n j := by
        simpa [RelCWComplex.cellFrontier_union_openCell_eq_closedCell
          (C := (Set.univ : Set X)) n j] using hyClosed
      rcases hyUnion with hyFrontier | hyOpenCell
      · exact hyFrontier
      · exact False.elim (hxOpen hyOpenCell)
    exact ⟨rfl, hyFrontier⟩
  · intro hy
    rcases hy with ⟨hyEq, hyFrontier⟩
    subst hyEq
    have hyClosed : y ∈ closedCell (C := (Set.univ : Set X)) n j := by
      rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell (C := (Set.univ : Set X)) n j]
      exact Or.inl hyFrontier
    exact ⟨rfl, hyClosed⟩

/-- Helper for Lemma 10.2.2: a point of a positive-dimensional closed cell that misses the open
part already lies in some lower-dimensional closed cell. -/
theorem exists_lower_closedCell_of_mem_closedCell_and_not_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) (n + 1)) {x : X}
    (hxClosed : x ∈ closedCell (C := (Set.univ : Set X)) (n + 1) j)
    (hxOpen : x ∉ openCell (C := (Set.univ : Set X)) (n + 1) j) :
    ∃ m < n + 1, ∃ y : cell (Set.univ : Set X) m,
      x ∈ closedCell (C := (Set.univ : Set X)) m y := by
  -- First push the point from the closed cell into the frontier.
  have hxFrontier : x ∈ cellFrontier (C := (Set.univ : Set X)) (n + 1) j := by
    have hxInter :
        x ∈ ({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) (n + 1) j := ⟨rfl, hxClosed⟩
    have hxFrontierInter :
        x ∈ ({x} : Set X) ∩ cellFrontier (C := (Set.univ : Set X)) (n + 1) j := by
      rw [singleton_inter_closedCell_eq_singleton_inter_cellFrontier_of_not_mem_openCell
        (X := X) j hxOpen] at hxInter
      exact hxInter
    exact hxFrontierInter.2
  -- Then use the finite frontier cover to descend to a lower-dimensional open cell.
  obtain ⟨I, hI⟩ :=
    cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) (n + 1) j
  have hxCover :
      x ∈ ⋃ (m < n + 1) (y ∈ I m), openCell (C := (Set.univ : Set X)) m y :=
    hI hxFrontier
  simp only [Set.mem_iUnion, exists_prop] at hxCover
  rcases hxCover with ⟨m, hm, y, hyI, hxy⟩
  exact ⟨m, hm, y, openCell_subset_closedCell _ _ hxy⟩

/-- Helper for Lemma 10.2.2: once a point lies in a closed cell whose singleton-intersection is
closed, that closed-cell witness upgrades to ambient singleton-closedness. -/
theorem isClosed_singleton_of_isClosed_inter_closedCell_of_mem
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hClosed : IsClosed (({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) n j))
    (hxClosed : x ∈ closedCell (C := (Set.univ : Set X)) n j) :
    IsClosed ({x} : Set X) := by
  -- Intersecting `{x}` with a closed cell containing `x` does not change the singleton.
  have hEq :
      ({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) n j = ({x} : Set X) := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      rcases hy with rfl
      exact ⟨rfl, hxClosed⟩
  rwa [hEq] at hClosed

/-- Helper for Lemma 10.2.2: if a point of a positive-dimensional closed cell lies on the
frontier, the induction hypothesis on a lower-dimensional closed cell already closes the ambient
singleton. -/
theorem isClosed_singleton_inter_closedCell_succ_of_not_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} {n : ℕ} (j : cell (Set.univ : Set X) (n + 1))
    (hn :
      ∀ m ≤ n, ∀ y : cell (Set.univ : Set X) m,
        IsClosed (({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) m y))
    (hxClosed : x ∈ closedCell (C := (Set.univ : Set X)) (n + 1) j)
    (hxOpen : x ∉ openCell (C := (Set.univ : Set X)) (n + 1) j) :
    IsClosed (({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) (n + 1) j) := by
  -- Descend from the frontier point to a lower-dimensional closed cell.
  obtain ⟨m, hm, y, hxy⟩ :=
    exists_lower_closedCell_of_mem_closedCell_and_not_mem_openCell (X := X) j hxClosed hxOpen
  have hSingleton : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_isClosed_inter_closedCell_of_mem (X := X) y
      (hn m (Nat.le_of_lt_succ hm) y) hxy
  -- Once the ambient singleton is closed, intersecting with the original containing closed cell
  -- does not change the set because `x` already lies in that cell.
  have hEq :
      ({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) (n + 1) j = ({x} : Set X) := by
    ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      rcases hz with rfl
      exact ⟨rfl, hxClosed⟩
  rwa [hEq]

/-- Helper for Lemma 10.2.2: a cell frontier is disjoint from its own open cell. -/
theorem disjoint_cellFrontier_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) :
    Disjoint (cellFrontier (C := (Set.univ : Set X)) n j)
      (openCell (C := (Set.univ : Set X)) n j) := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
      -- In degree `0`, the frontier is empty.
      rw [RelCWComplex.cellFrontier_zero_eq_empty]
      exact Set.empty_disjoint _
  | hi n _ =>
      -- Every frontier point lies in a lower-dimensional open cell, which is disjoint from the
      -- chosen `(n + 1)`-cell.
      obtain ⟨I, hI⟩ :=
        cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) (n + 1) j
      refine Set.disjoint_left.2 ?_
      intro y hyFrontier hyOpen
      have hyCover :
          y ∈ ⋃ (m < n + 1) (i ∈ I m), openCell (C := (Set.univ : Set X)) m i :=
        hI hyFrontier
      simp only [Set.mem_iUnion, exists_prop] at hyCover
      obtain ⟨m, hm, i, _, hyLower⟩ := hyCover
      have hne :
          (⟨m, i⟩ : Σ l, cell (Set.univ : Set X) l) ≠ ⟨n + 1, j⟩ := by
        intro hEq
        cases hEq
        exact Nat.lt_irrefl _ hm
      exact Set.disjoint_left.mp
        (disjoint_openCell_of_ne (C := (Set.univ : Set X)) hne) hyLower hyOpen

/-- Helper for Lemma 10.2.2: a point in an open cell already exhausts its intersection with the
containing closed cell. -/
theorem singleton_inter_closedCell_eq_singleton_of_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) n j) :
    ({x} : Set X) ∩ closedCell (C := (Set.univ : Set X)) n j = ({x} : Set X) := by
  -- The containing closed cell already contains every point of the singleton.
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    rcases hy with rfl
    exact ⟨rfl, openCell_subset_closedCell _ _ hxOpen⟩

/-- Helper for Lemma 10.2.2: the frontier of a cell misses the singleton of any point of the
open part of that cell. -/
theorem disjoint_cellFrontier_singleton_of_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) n j) :
    Disjoint (cellFrontier (C := (Set.univ : Set X)) n j) ({x} : Set X) := by
  -- The previously proved frontier/open-cell disjointness excludes the chosen singleton point.
  refine Set.disjoint_left.2 ?_
  intro y hyFront hySingleton
  rcases hySingleton with rfl
  exact Set.disjoint_left.mp (disjoint_cellFrontier_openCell (X := X) j) hyFront hxOpen

/-- Helper for Lemma 10.2.2: inside a fixed open cell, the ambient closure of a singleton still
meets that open cell only at the original point. -/
theorem inter_openCell_closure_singleton_subset_singleton
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hx : x ∈ openCell (C := (Set.univ : Set X)) n j) :
    openCell (C := (Set.univ : Set X)) n j ∩ closure ({x} : Set X) ⊆ ({x} : Set X) := by
  -- Restrict the ambient singleton to the open-cell subtype and rewrite the resulting closure
  -- criterion back in the ambient space.
  have hclosedOpen :
      openCell (C := (Set.univ : Set X)) n j ∩
          closure (openCell (C := (Set.univ : Set X)) n j ∩ ({x} : Set X)) ⊆
        ({x} : Set X) := by
    have hclosedSubtype :
        IsClosed
          ((openCell (C := (Set.univ : Set X)) n j) ↓∩ ({x} : Set X)) := by
      simpa using isClosed_openCellSingleton (X := X) j hx
    exact (isClosed_preimage_val
      (s := openCell (C := (Set.univ : Set X)) n j) (t := ({x} : Set X))).1 hclosedSubtype
  have hSingletonEq :
      openCell (C := (Set.univ : Set X)) n j ∩ ({x} : Set X) = ({x} : Set X) := by
    ext y
    constructor
    · intro hy
      exact hy.2
    · intro hy
      rcases hy with rfl
      exact ⟨hx, rfl⟩
  simpa [hSingletonEq] using hclosedOpen

/-- Helper for Lemma 10.2.2: the closure of a singleton from an open cell can only meet the
containing closed cell at the singleton itself or along the cell frontier. -/
theorem inter_closedCell_closure_singleton_subset_singleton_union_frontier
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hx : x ∈ openCell (C := (Set.univ : Set X)) n j) :
    closedCell (C := (Set.univ : Set X)) n j ∩ closure ({x} : Set X) ⊆
      ({x} : Set X) ∪ cellFrontier (C := (Set.univ : Set X)) n j := by
  intro y hy
  rcases hy with ⟨hyClosed, hyClosure⟩
  have hyDecomp :
      y ∈ cellFrontier (C := (Set.univ : Set X)) n j ∪
        openCell (C := (Set.univ : Set X)) n j := by
    simpa [RelCWComplex.cellFrontier_union_openCell_eq_closedCell
      (C := (Set.univ : Set X)) n j] using hyClosed
  rcases hyDecomp with hyFrontier | hyOpen
  · exact Or.inr hyFrontier
  · have hySingleton :
        y ∈ ({x} : Set X) :=
      inter_openCell_closure_singleton_subset_singleton (X := X) j hx ⟨hyOpen, hyClosure⟩
    exact Or.inl hySingleton

/-- Helper for Lemma 10.2.2: once the frontier is known to miss the closure of the singleton,
the closed-cell part of that closure collapses to the singleton itself. -/
theorem inter_closedCell_closure_singleton_subset_singleton_of_disjoint_frontier_closure
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x : X}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) n j)
    (hFrontier :
      Disjoint (cellFrontier (C := (Set.univ : Set X)) n j) (closure ({x} : Set X))) :
    closedCell (C := (Set.univ : Set X)) n j ∩ closure ({x} : Set X) ⊆ ({x} : Set X) := by
  -- Split a closure point in the closed cell into the singleton branch and the frontier branch.
  intro y hy
  rcases
      inter_closedCell_closure_singleton_subset_singleton_union_frontier (X := X) j hxOpen hy with
    hySingleton | hyFrontier
  · exact hySingleton
  · exact False.elim <| Set.disjoint_left.mp hFrontier hyFrontier hy.2

/-- Helper for Lemma 10.2.2: a specialization target that remains in the same open cell is equal
to the original point. -/
theorem specializesEqOfMemSameOpenCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : cell (Set.univ : Set X) n) {x y : X}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) n j)
    (hxy : x ⤳ y)
    (hyOpen : y ∈ openCell (C := (Set.univ : Set X)) n j) :
    y = x := by
  -- Once both points lie in the same open cell, the earlier singleton-closure lemma forces
  -- equality.
  have hySingleton :
      y ∈ ({x} : Set X) :=
    inter_openCell_closure_singleton_subset_singleton (X := X) j hxOpen
      ⟨hyOpen, (specializes_iff_mem_closure.mp hxy)⟩
  simpa using hySingleton

/-- Helper for Lemma 10.2.2: a point cannot lie in two different absolute-CW open cells. -/
private theorem sigmaCell_eq_of_mem_twoOpenCells
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} {n m : ℕ} {j : cell (Set.univ : Set X) n}
    {i : cell (Set.univ : Set X) m}
    (hxj : x ∈ openCell (C := (Set.univ : Set X)) n j)
    (hxi : x ∈ openCell (C := (Set.univ : Set X)) m i) :
    (⟨n, j⟩ : closedCellOwner X) = ⟨m, i⟩ := by
  -- A common point witnesses non-disjointness, so open-cell disjointness forces the owners to
  -- agree.
  refine eq_of_not_disjoint_openCell (C := (Set.univ : Set X)) ?_
  exact Set.not_disjoint_iff.mpr ⟨x, hxj, hxi⟩

/-- Helper for Lemma 10.2.2: a point of a chosen `0`-open-cell cannot lie in any different
ambient open cell. -/
private theorem not_mem_openCell_of_mem_openCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} (j : cell (Set.univ : Set X) 0)
    (hxZero : x ∈ openCell (C := (Set.univ : Set X)) 0 j)
    {n : ℕ} (j' : cell (Set.univ : Set X) n)
    (hne : (⟨0, j⟩ : closedCellOwner X) ≠ ⟨n, j'⟩) :
    x ∉ openCell (C := (Set.univ : Set X)) n j' := by
  -- Any second open-cell witness would contradict open-cell disjointness.
  intro hxOther
  exact hne (sigmaCell_eq_of_mem_twoOpenCells (X := X) hxZero hxOther)

/-- Helper for Lemma 10.2.2: a point of a chosen `0`-open-cell cannot lie in a positive-dimensional
ambient open cell. -/
private theorem not_mem_openCell_succ_of_mem_openCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} (j : cell (Set.univ : Set X) 0)
    (hxZero : x ∈ openCell (C := (Set.univ : Set X)) 0 j)
    {n : ℕ} (j' : cell (Set.univ : Set X) (n + 1)) :
    x ∉ openCell (C := (Set.univ : Set X)) (n + 1) j' := by
  -- Positive-dimensional owners are automatically different from the chosen `0`-cell owner.
  exact not_mem_openCell_of_mem_openCell_zero (X := X) j hxZero j'
    (by
      intro hEq
      exact Nat.succ_ne_zero n (congrArg Sigma.fst hEq).symm)

/-- Helper for Lemma 10.2.2: specialization from a point in a `0`-open-cell cannot land in a
different ambient open cell. -/
private theorem not_specializes_of_mem_openCell_zero_of_mem_openCell_ne
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x y : X} {j : cell (Set.univ : Set X) 0}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) 0 j)
    {n : ℕ} {i : cell (Set.univ : Set X) n}
    (hneq : (⟨n, i⟩ : closedCellOwner X) ≠ ⟨0, j⟩)
    (hyOpen : y ∈ openCell (C := (Set.univ : Set X)) n i) :
    ¬ x ⤳ y := by
  -- Route correction: the old blocker asked for the whole target open cell to be a
  -- neighborhood inside a finite carrier. The right remaining lemma is only this direct ambient
  -- non-specialization statement for a `0`-cell source.
  -- TODO: prove this by transporting the specialization target into a top-dimensional skeleton
  -- neighborhood for `y`, then use `not_mem_openCell_of_mem_openCell_zero` to contradict that
  -- `x` would have to lie in the same ambient open cell.
  sorry

/-- Helper for Lemma 10.2.2: zero-cell source specialization inside one finite carrier collapses
to equality because a point of a `0`-open-cell already has ambiently closed singleton. -/
private theorem specializesEqValOfMemOpenCellZeroInCarrier
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {I : Finset (closedCellOwner X)} (hI : frontierOpenCellFamily X I)
    {x y : X} (hxI : x ∈ closedCellCarrier X I) (hyI : y ∈ closedCellCarrier X I)
    {j : cell (Set.univ : Set X) 0}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) 0 j)
    (hxy : (⟨x, hxI⟩ : closedCellCarrier X I) ⤳ ⟨y, hyI⟩) :
    y = x := by
  -- Pick the selected target cell, then rule out every owner except the source `0`-cell owner.
  obtain ⟨b, hb, hyOpen⟩ :=
    pointMemSelectedOpenCellOfFrontierOpenCover (X := X) hI hyI
  have hxyAmbient : x ⤳ y := (subtype_specializes_iff _ _).1 hxy
  by_cases hbEq : b = ⟨0, j⟩
  · cases hbEq
    exact specializesEqOfMemSameOpenCell (X := X) j hxOpen hxyAmbient hyOpen
  · exact False.elim
      ((not_specializes_of_mem_openCell_zero_of_mem_openCell_ne
          (X := X) hxOpen hbEq hyOpen) hxyAmbient)

/-- Helper for Lemma 10.2.2: a point of a zero-dimensional absolute-CW open cell has ambiently
closed singleton. -/
theorem isClosed_singleton_of_mem_openCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} {j : cell (Set.univ : Set X) 0}
    (hxOpen : x ∈ openCell (C := (Set.univ : Set X)) 0 j) :
    IsClosed ({x} : Set X) := by
  -- Route correction: package the zero-dimensional case directly instead of reviving the generic
  -- absolute-CW `T1` chain.
  have hClosureSingleton :
      closure ({x} : Set X) ⊆ ({x} : Set X) := by
    intro y hyClosure
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hyClosure
    obtain ⟨I, hxI, hyI, hIFrontier, _hICompact⟩ :=
      existsFiniteCompactClosureCarrierContainingPair x y
    have hxySubtype :
        (⟨x, hxI⟩ : closedCellCarrier X I) ⤳ ⟨y, hyI⟩ :=
      specializes_subtype_of_mem_closedCellCarrier (X := X) hxI hyI hxy
    have hEq : y = x :=
      specializesEqValOfMemOpenCellZeroInCarrier (X := X) hIFrontier hxI hyI hxOpen hxySubtype
    simpa [hEq]
  exact closure_subset_iff_isClosed.mp hClosureSingleton

end Topology.CWComplex
