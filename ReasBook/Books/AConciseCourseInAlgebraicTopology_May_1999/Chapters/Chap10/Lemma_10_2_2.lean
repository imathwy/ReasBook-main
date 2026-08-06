import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_2.Separation

open Topology

universe u v

-- Semantic recall via `lean_leansearch`: `Topology.CWComplex.Subcomplex` and
-- `Topology.RelCWComplex.Subcomplex` are the canonical owners for subcomplexes in the current
-- mathlib snapshot. No dedicated wedge-space owner surfaced, so the wedge is formalized by the
-- standard quotient of the disjoint union `Σ i, X i` that identifies all chosen basepoints.

/-- A chosen point of a CW complex is a vertex when it lies in some closed `0`-cell. -/
def IsCWVertex {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x : X) : Prop :=
  ∃ v : Topology.CWComplex.cell (Set.univ : Set X) 0,
    x ∈ (@Topology.RelCWComplex.closedCell X _ (Set.univ : Set X) (∅ : Set X) _ 0 v)

/-- The equivalence relation on `Σ i, X i` that identifies all specified basepoints and leaves all
other points unchanged. -/
private def basedWedgeSetoid {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) : Setoid (Sigma X) where
  r a b := a = b ∨ a.2 = x0 a.1 ∧ b.2 = x0 b.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | ⟨ha, hb⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with hab | ⟨ha, hb⟩
      · subst hab
        exact hbc
      · rcases hbc with hbc | ⟨hb', hc⟩
        · subst hbc
          exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

/-- The carrier of the wedge `⋁ i, X i`, presented as the quotient of `Σ i, X i` obtained by
identifying all chosen basepoints. -/
abbrev basedWedge {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) :=
  Quotient (basedWedgeSetoid X x0)

syntax:100 "⋁[" term "] " ident ", " term : term
macro_rules
  | `(⋁[$x0] $i, $X) => `(basedWedge (fun $i ↦ $X) $x0)

/-- The canonical map of the `i`th summand into the wedge quotient. -/
def basedWedgeInclusion {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) : X i → ⋁[x0] j, X j :=
  fun x ↦ Quotient.mk'' ⟨i, x⟩

/-- A representative-level retraction onto the `i`th wedge summand. It fixes the `i`th summand and
sends every other summand to the chosen basepoint `x0 i`. -/
private noncomputable def basedWedgeSummandRep
    {ι : Type u} (X : ι → Type v) (x0 : ∀ i, X i) (i : ι) :
    Sigma X → X i
  | ⟨i', x⟩ =>
      by
        classical
        by_cases h : i' = i
        · exact cast (by cases h; rfl) x
        · exact x0 i

@[simp] private theorem basedWedgeSummandRep_self
    {ι : Type u} (X : ι → Type v) (x0 : ∀ i, X i) (i : ι) (x : X i) :
    basedWedgeSummandRep X x0 i ⟨i, x⟩ = x := by
  classical
  simp [basedWedgeSummandRep]

private theorem basedWedgeSummandRep_basepoint
    {ι : Type u} (X : ι → Type v) (x0 : ∀ i, X i) (i j : ι) :
    basedWedgeSummandRep X x0 i ⟨j, x0 j⟩ = x0 i := by
  classical
  by_cases h : j = i
  · subst h
    simp [basedWedgeSummandRep]
  · simp [basedWedgeSummandRep, h]

private theorem basedWedgeSummandRep_rel
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) {a b : Sigma X}
    (h : (basedWedgeSetoid X x0).r a b) :
    basedWedgeSummandRep X x0 i a = basedWedgeSummandRep X x0 i b := by
  rcases a with ⟨j, x⟩
  rcases b with ⟨k, y⟩
  rcases h with h | ⟨hx, hy⟩
  · cases h
    rfl
  · have ha : basedWedgeSummandRep X x0 i ⟨j, x⟩ = x0 i := by
        have hrep :
            basedWedgeSummandRep X x0 i ⟨j, x⟩ =
              basedWedgeSummandRep X x0 i ⟨j, x0 j⟩ := by
          simpa using congrArg (fun z : X j ↦ basedWedgeSummandRep X x0 i ⟨j, z⟩) hx
        exact hrep.trans (basedWedgeSummandRep_basepoint X x0 i j)
    have hb : basedWedgeSummandRep X x0 i ⟨k, y⟩ = x0 i := by
        have hrep :
            basedWedgeSummandRep X x0 i ⟨k, y⟩ =
              basedWedgeSummandRep X x0 i ⟨k, x0 k⟩ := by
          simpa using congrArg (fun z : X k ↦ basedWedgeSummandRep X x0 i ⟨k, z⟩) hy
        exact hrep.trans (basedWedgeSummandRep_basepoint X x0 i k)
    exact ha.trans hb.symm

/-- The wedge quotient admits a canonical retraction onto each summand. -/
private noncomputable def basedWedgeSummandInverse
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) : (⋁[x0] j, X j) → X i :=
  Quotient.lift (basedWedgeSummandRep X x0 i) fun _ _ h ↦ basedWedgeSummandRep_rel X x0 i h

@[simp] private theorem basedWedgeSummandInverse_inclusion
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) (x : X i) :
    basedWedgeSummandInverse X x0 i (basedWedgeInclusion X x0 i x) = x := by
  exact basedWedgeSummandRep_self X x0 i x

/-- Helper for Lemma 10.2.2: retracting a point from a different summand returns the chosen
basepoint of the target summand. -/
@[simp] private theorem basedWedgeSummandInverse_other
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) {i j : ι} (hji : j ≠ i) (x : X j) :
    basedWedgeSummandInverse X x0 i (basedWedgeInclusion X x0 j x) = x0 i := by
  classical
  simp [basedWedgeSummandInverse, basedWedgeInclusion, basedWedgeSummandRep, hji]

/-- Chooses a `0`-cell of the `i`th summand whose closed cell contains the basepoint `x0 i`. -/
private noncomputable def basedWedgeBaseCell
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    Topology.CWComplex.cell (Set.univ : Set (X i)) 0 :=
  Classical.choose (hvertex i)

/-- Helper for Lemma 10.2.2: all chosen basepoints represent the same point of the wedge quotient. -/
private theorem basedWedgeInclusion_basepoint_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i j : ι) :
    basedWedgeInclusion X x0 i (x0 i) = basedWedgeInclusion X x0 j (x0 j) := by
  exact Quotient.sound (Or.inr ⟨rfl, rfl⟩)

/-- Helper for Lemma 10.2.2: the chosen basepoint lies in the chosen open `0`-cell of its
summand. -/
private theorem basedWedgeBasepoint_mem_openCell
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    x0 i ∈ Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) 0
      (basedWedgeBaseCell X x0 hvertex i) := by
  -- The chosen vertex hypothesis places `x0 i` in the chosen closed `0`-cell, and in dimension
  -- `0` the open and closed cells are the same singleton.
  have hxclosed :
      x0 i ∈ @Topology.RelCWComplex.closedCell (X i) _ (Set.univ : Set (X i)) (∅ : Set (X i)) _ 0
        (basedWedgeBaseCell X x0 hvertex i) :=
    Classical.choose_spec (hvertex i)
  rw [Topology.RelCWComplex.closedCell_zero_eq_singleton] at hxclosed
  rw [Topology.RelCWComplex.openCell_zero_eq_singleton]
  simpa using hxclosed

/-- Helper for Lemma 10.2.2: the characteristic map of the chosen base `0`-cell sends the unique
point of `Fin 0 → ℝ` to the chosen basepoint. -/
private theorem basedWedgeBaseCellMap_eq_basepoint
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    Topology.CWComplex.map (C := (Set.univ : Set (X i))) 0
        (basedWedgeBaseCell X x0 hvertex i) ![] = x0 i := by
  -- The chosen basepoint is the unique point of the chosen open `0`-cell.
  have hx0 := basedWedgeBasepoint_mem_openCell X x0 hvertex i
  rw [Topology.RelCWComplex.openCell_zero_eq_singleton] at hx0
  simpa using hx0.symm

/-- Helper for Lemma 10.2.2: no open cell other than the chosen base `0`-cell contains the chosen
basepoint. -/
private theorem basedWedgeBasepoint_not_mem_openCell
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) {n : ℕ}
    {j : Topology.CWComplex.cell (Set.univ : Set (X i)) n}
    (hne : (⟨n, j⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set (X i)) m) ≠
      ⟨0, basedWedgeBaseCell X x0 hvertex i⟩) :
    x0 i ∉ Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j := by
  -- Disjointness of distinct summand open cells rules out any second occurrence of the basepoint.
  intro hx
  have hx0 := basedWedgeBasepoint_mem_openCell X x0 hvertex i
  have hdisj :
      Disjoint (Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j)
        (Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) 0
          (basedWedgeBaseCell X x0 hvertex i)) :=
    Topology.CWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set (X i))) hne
  exact Set.disjoint_left.mp hdisj hx hx0

/-- The wedge inclusion of a fixed summand is injective. -/
theorem basedWedgeInclusion_injective
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) :
    Function.Injective (basedWedgeInclusion X x0 i) := by
  intro x y hxy
  have hxy' := congrArg (basedWedgeSummandInverse X x0 i) hxy
  simpa using hxy'

/-- The partial equivalence on the wedge obtained by restricting the quotient map to one summand. -/
private noncomputable def basedWedgeSummandPartialEquiv
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) (s : Set (X i)) :
    PartialEquiv (X i) (⋁[x0] j, X j) :=
  { toFun := basedWedgeInclusion X x0 i
    invFun := basedWedgeSummandInverse X x0 i
    source := s
    target := basedWedgeInclusion X x0 i '' s
    map_source' := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    map_target' := by
      rintro y ⟨x, hx, rfl⟩
      simpa using hx
    left_inv' := by
      intro x hx
      simp
    right_inv' := by
      rintro y ⟨x, hx, rfl⟩
      simp }

/-- Helper for Lemma 10.2.2: the quotient inclusion of a fixed wedge summand is continuous. -/
private theorem basedWedgeInclusion_continuous
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) :
    Continuous (basedWedgeInclusion X x0 i) := by
  -- The summand inclusion is the sigma injection followed by the quotient map.
  simpa [basedWedgeInclusion, Function.comp] using
    (continuous_quotient_mk'.comp (continuous_sigmaMk : Continuous (@Sigma.mk ι X i)))

/-- Helper for Lemma 10.2.2: the representative-level summand retraction is continuous on the
disjoint union `Σ i, X i`. -/
private theorem basedWedgeSummandRep_continuous
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) :
    Continuous (basedWedgeSummandRep X x0 i) := by
  classical
  rw [continuous_sigma_iff]
  intro i'
  by_cases h : i' = i
  · -- On the chosen summand the retraction is the identity.
    subst i'
    simpa [basedWedgeSummandRep] using (continuous_id : Continuous fun x : X i => x)
  · -- Every other summand collapses to the chosen basepoint.
    simpa [basedWedgeSummandRep, h] using (continuous_const : Continuous fun _ : X i' => x0 i)

/-- Helper for Lemma 10.2.2: the wedge quotient admits a continuous retraction onto each chosen
summand. -/
private theorem basedWedgeSummandInverse_continuous
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) :
    Continuous (basedWedgeSummandInverse X x0 i) := by
  -- The quotient-lifted retraction inherits continuity from its representative-level map.
  simpa [basedWedgeSummandInverse] using
    (Continuous.quotient_lift (f := basedWedgeSummandRep X x0 i)
      (basedWedgeSummandRep_continuous X x0 i)
      (fun _ _ h ↦ basedWedgeSummandRep_rel X x0 i h))

/-- Helper for Lemma 10.2.2: composing a summand cell map with the wedge inclusion carries images
exactly to the corresponding wedge-cell images. -/
private theorem basedWedgeCellMap_image_eq
    {ι : Type u} {α : Type*} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) (e : PartialEquiv α (X i)) (s : Set α) :
    (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)) '' s =
      basedWedgeInclusion X x0 i '' (e '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Helper for Lemma 10.2.2: composing a cell map with the wedge inclusion does not change its
source. -/
private theorem basedWedgeSummandTrans_source_eq
    {ι : Type u} {α : Type*} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) (e : PartialEquiv α (X i)) :
    (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).source = e.source := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, e.map_source hx⟩

/-- Helper for Lemma 10.2.2: the target of a transported summand cell map is the image of the
original target under the wedge inclusion. -/
private theorem basedWedgeSummandTrans_target_eq
    {ι : Type u} {α : Type*} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) (e : PartialEquiv α (X i)) :
    (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).target =
      basedWedgeInclusion X x0 i '' e.target := by
  -- Rewrite the target through the image of the unchanged source.
  calc
    (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).target =
        (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)) ''
          (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).source := by
          symm
          exact PartialEquiv.image_source_eq_target _
    _ = basedWedgeInclusion X x0 i '' (e '' e.source) := by
          rw [basedWedgeSummandTrans_source_eq, basedWedgeCellMap_image_eq]
    _ = basedWedgeInclusion X x0 i '' e.target := by
          rw [PartialEquiv.image_source_eq_target]

/-- The cell indices used for the wedge CW structure: one wedge-point `0`-cell when `ι` is
inhabited, the remaining `0`-cells of the summands, and all positive-dimensional summand cells. -/
private noncomputable def basedWedgeCell
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) :
    ℕ → Type (max u v)
  | 0 =>
      PLift (Nonempty ι) ⊕
        Σ i, {j : Topology.CWComplex.cell (Set.univ : Set (X i)) 0 //
          j ≠ basedWedgeBaseCell X x0 hvertex i}
  | n + 1 => Σ i, Topology.CWComplex.cell (Set.univ : Set (X i)) (n + 1)

/-- The characteristic maps for the explicit wedge CW structure. -/
private noncomputable def basedWedgeCellMap
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) :
    ∀ n, basedWedgeCell X x0 hvertex n → PartialEquiv (Fin n → ℝ) (⋁[x0] j, X j)
  | 0, Sum.inl h =>
      let i := Classical.choice h.down
      let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
        Topology.CWComplex.map 0 (basedWedgeBaseCell X x0 hvertex i)
      e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)
  | 0, Sum.inr ⟨i, j⟩ =>
      let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
        Topology.CWComplex.map 0 j.1
      e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)
  | n + 1, ⟨i, j⟩ =>
      let e : PartialEquiv (Fin (n + 1) → ℝ) (X i) :=
        Topology.CWComplex.map (n + 1) j
      e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)

/-- Helper for Lemma 10.2.2: package a cell of the `i`th summand as the corresponding wedge-cell
index, sending the chosen base `0`-cell to the distinguished wedge `0`-cell. -/
private noncomputable def basedWedgeSummandCellIndex
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    ∀ n, Topology.CWComplex.cell (Set.univ : Set (X i)) n → basedWedgeCell X x0 hvertex n
  | 0, j =>
      let _ : DecidableEq (Topology.CWComplex.cell (Set.univ : Set (X i)) 0) :=
        Classical.decEq _
      if h : j = basedWedgeBaseCell X x0 hvertex i then
        Sum.inl (PLift.up ⟨i⟩)
      else
        Sum.inr ⟨i, ⟨j, h⟩⟩
  | _ + 1, j => ⟨i, j⟩

/-- Helper for Lemma 10.2.2: every non-base open cell in a summand misses the common wedge point. -/
private theorem basedWedgeSummandOpenImage_avoidsWedgePoint
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) {n : ℕ}
    {j : Topology.CWComplex.cell (Set.univ : Set (X i)) n}
    (hne : (⟨n, j⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set (X i)) m) ≠
      ⟨0, basedWedgeBaseCell X x0 hvertex i⟩) :
    basedWedgeInclusion X x0 i (x0 i) ∉
      basedWedgeInclusion X x0 i '' Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j := by
  -- Pull the membership back along the injective summand inclusion and use the basepoint exclusion
  -- in the original summand.
  rintro ⟨x, hx, hxEq⟩
  have hx0 : x = x0 i := basedWedgeInclusion_injective X x0 i hxEq
  exact basedWedgeBasepoint_not_mem_openCell X x0 hvertex i hne (hx0 ▸ hx)

/-- Helper for Lemma 10.2.2: open-cell images from different wedge summands are disjoint once both
summand cells avoid their chosen base `0`-cells. -/
private theorem basedWedgeSummandOpenCellImage_disjoint_of_ne
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) {i j : ι} (hji : j ≠ i) {n m : ℕ}
    {a : Topology.CWComplex.cell (Set.univ : Set (X i)) n}
    {b : Topology.CWComplex.cell (Set.univ : Set (X j)) m}
    (ha : (⟨n, a⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
      ⟨0, basedWedgeBaseCell X x0 hvertex i⟩)
    (_hb : (⟨m, b⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X j)) l) ≠
      ⟨0, basedWedgeBaseCell X x0 hvertex j⟩) :
    Disjoint
      (basedWedgeInclusion X x0 i '' Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n a)
      (basedWedgeInclusion X x0 j '' Topology.CWComplex.openCell (C := (Set.univ : Set (X j))) m b) :=
  by
    -- Retract a hypothetical intersection point back to the `i`th summand.
    refine Set.disjoint_left.2 ?_
    intro y hy hz
    rcases hy with ⟨x, hx, rfl⟩
    rcases hz with ⟨z, hz, hEq⟩
    have hx0 : x = x0 i := by
      have hret := congrArg (basedWedgeSummandInverse X x0 i) hEq.symm
      calc
        x = basedWedgeSummandInverse X x0 i (basedWedgeInclusion X x0 j z) := by
          simpa using hret
        _ = x0 i := basedWedgeSummandInverse_other X x0 (i := i) (j := j) hji z
    -- The retraction shows that the intersection point is the common wedge point, which the
    -- chosen summand open cell avoids.
    have hwedge :
        basedWedgeInclusion X x0 i (x0 i) ∈
          basedWedgeInclusion X x0 i ''
            Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n a :=
      ⟨x0 i, hx0 ▸ hx, rfl⟩
    exact basedWedgeSummandOpenImage_avoidsWedgePoint X x0 hvertex i ha hwedge

/-- Helper for Lemma 10.2.2: the distinguished wedge open `0`-cell is the singleton common wedge
point. -/
private theorem basedWedgeDistinguishedOpenCell_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (h : PLift (Nonempty ι)) :
    basedWedgeCellMap X x0 hvertex 0 (Sum.inl h) '' Metric.ball (0 : Fin 0 → ℝ) 1 =
      {basedWedgeInclusion X x0 (Classical.choice h.down) (x0 (Classical.choice h.down))} := by
  let i := Classical.choice h.down
  let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
    Topology.CWComplex.map 0 (basedWedgeBaseCell X x0 hvertex i)
  have hx :
      Topology.CWComplex.map (C := (Set.univ : Set (X i))) 0
          (basedWedgeBaseCell X x0 hvertex i) ![] = x0 i := by
    -- The chosen basepoint is the unique point of the chosen open `0`-cell.
    have hx0 := basedWedgeBasepoint_mem_openCell X x0 hvertex i
    rw [Topology.RelCWComplex.openCell_zero_eq_singleton] at hx0
    simpa using hx0.symm
  -- Rewrite the distinguished cell as the image of the chosen base cell in a summand.
  change (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)) ''
      Metric.ball (0 : Fin 0 → ℝ) 1 = _
  rw [basedWedgeCellMap_image_eq]
  change basedWedgeInclusion X x0 i ''
      (Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) 0
        (basedWedgeBaseCell X x0 hvertex i)) = _
  rw [Topology.RelCWComplex.openCell_zero_eq_singleton]
  simpa [Set.image_singleton] using congrArg (basedWedgeInclusion X x0 i) hx

/-- Helper for Lemma 10.2.2: the distinguished wedge closed `0`-cell is the singleton common
wedge point. -/
private theorem basedWedgeDistinguishedClosedCell_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (h : PLift (Nonempty ι)) :
    basedWedgeCellMap X x0 hvertex 0 (Sum.inl h) '' Metric.closedBall (0 : Fin 0 → ℝ) 1 =
      {basedWedgeInclusion X x0 (Classical.choice h.down) (x0 (Classical.choice h.down))} := by
  let i := Classical.choice h.down
  let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
    Topology.CWComplex.map 0 (basedWedgeBaseCell X x0 hvertex i)
  have hx :
      Topology.CWComplex.map (C := (Set.univ : Set (X i))) 0
          (basedWedgeBaseCell X x0 hvertex i) ![] = x0 i := by
    -- The chosen basepoint is the unique point of the chosen closed `0`-cell.
    have hxclosed :
        x0 i ∈ @Topology.RelCWComplex.closedCell (X i) _ (Set.univ : Set (X i))
          (∅ : Set (X i)) _ 0 (basedWedgeBaseCell X x0 hvertex i) :=
      Classical.choose_spec (hvertex i)
    rw [Topology.RelCWComplex.closedCell_zero_eq_singleton] at hxclosed
    simpa using hxclosed.symm
  -- Rewrite the distinguished cell as the image of the chosen base cell in a summand.
  change (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)) ''
      Metric.closedBall (0 : Fin 0 → ℝ) 1 = _
  rw [basedWedgeCellMap_image_eq]
  change basedWedgeInclusion X x0 i ''
      (Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) 0
        (basedWedgeBaseCell X x0 hvertex i)) = _
  rw [Topology.RelCWComplex.closedCell_zero_eq_singleton]
  simpa [Set.image_singleton] using congrArg (basedWedgeInclusion X x0 i) hx

/-- Helper for Lemma 10.2.2: within a fixed summand, disjoint source open cells stay disjoint after
applying the wedge inclusion. -/
private theorem basedWedgeSummandOpenCellImage_disjoint
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i) (i : ι) {n m : ℕ}
    {j : Topology.CWComplex.cell (Set.univ : Set (X i)) n}
    {k : Topology.CWComplex.cell (Set.univ : Set (X i)) m}
    (hne : (⟨n, j⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠ ⟨m, k⟩) :
    Disjoint
      (basedWedgeInclusion X x0 i '' Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j)
      (basedWedgeInclusion X x0 i '' Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) m k) :=
    by
  -- Injectivity of the summand inclusion reduces disjointness back to the original summand cells.
  refine Set.disjoint_left.2 ?_
  intro y hyj hyk
  rcases hyj with ⟨x, hx, rfl⟩
  rcases hyk with ⟨z, hz, hzEq⟩
  have hxz : x = z := basedWedgeInclusion_injective X x0 i hzEq.symm
  have hdisj :
      Disjoint (Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j)
        (Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) m k) :=
    Topology.CWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set (X i))) hne
  exact Set.disjoint_left.mp hdisj hx (hxz ▸ hz)

/-- Helper for Lemma 10.2.2: every wedge open-cell image normalizes to either the distinguished
wedgepoint singleton or the image of a summand open cell. -/
private theorem basedWedgeCellOpenImage_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (n : ℕ) (j : basedWedgeCell X x0 hvertex n) :
    basedWedgeCellMap X x0 hvertex n j '' Metric.ball (0 : Fin n → ℝ) 1 =
      match n, j with
      | 0, Sum.inl h =>
          {basedWedgeInclusion X x0 (Classical.choice h.down) (x0 (Classical.choice h.down))}
      | 0, Sum.inr ⟨i, j⟩ =>
          basedWedgeInclusion X x0 i ''
            Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) 0 j.1
      | n + 1, ⟨i, j⟩ =>
          basedWedgeInclusion X x0 i ''
            Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) (n + 1) j := by
  -- Split the dependent wedge-cell index into the distinguished `0`-cell and the transported
  -- summand cells, then rewrite the image once and for all.
  cases n with
  | zero =>
      cases j with
      | inl h =>
          simpa using basedWedgeDistinguishedOpenCell_eq X x0 hvertex h
      | inr hij =>
          rcases hij with ⟨i, j⟩
          let e : PartialEquiv (Fin 0 → ℝ) (X i) := Topology.CWComplex.map 0 j.1
          simpa [basedWedgeCellMap, e, Topology.CWComplex.openCell] using
            (basedWedgeCellMap_image_eq X x0 i e (Metric.ball (0 : Fin 0 → ℝ) 1))
  | succ n =>
      rcases j with ⟨i, j⟩
      let e : PartialEquiv (Fin (n + 1) → ℝ) (X i) := Topology.CWComplex.map (n + 1) j
      -- In positive dimensions the wedge cell is exactly the summand cell transported by the
      -- summand inclusion.
      simpa [basedWedgeCellMap, e, Topology.CWComplex.openCell] using
        (basedWedgeCellMap_image_eq X x0 i e (Metric.ball (0 : Fin (n + 1) → ℝ) 1))

/-- Helper for Lemma 10.2.2: every wedge closed-cell image normalizes to either the distinguished
wedgepoint singleton or the image of a summand closed cell. -/
private theorem basedWedgeCellClosedImage_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (n : ℕ) (j : basedWedgeCell X x0 hvertex n) :
    basedWedgeCellMap X x0 hvertex n j '' Metric.closedBall (0 : Fin n → ℝ) 1 =
      match n, j with
      | 0, Sum.inl h =>
          {basedWedgeInclusion X x0 (Classical.choice h.down) (x0 (Classical.choice h.down))}
      | 0, Sum.inr ⟨i, j⟩ =>
          basedWedgeInclusion X x0 i ''
            Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) 0 j.1
      | n + 1, ⟨i, j⟩ =>
          basedWedgeInclusion X x0 i ''
            Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) (n + 1) j := by
  -- The same case split normalizes closed images and removes the dependent-index rewrite burden
  -- from later frontier and closedness arguments.
  cases n with
  | zero =>
      cases j with
      | inl h =>
          simpa using basedWedgeDistinguishedClosedCell_eq X x0 hvertex h
      | inr hij =>
          rcases hij with ⟨i, j⟩
          let e : PartialEquiv (Fin 0 → ℝ) (X i) := Topology.CWComplex.map 0 j.1
          simpa [basedWedgeCellMap, e, Topology.CWComplex.closedCell] using
            (basedWedgeCellMap_image_eq X x0 i e (Metric.closedBall (0 : Fin 0 → ℝ) 1))
  | succ n =>
      rcases j with ⟨i, j⟩
      let e : PartialEquiv (Fin (n + 1) → ℝ) (X i) := Topology.CWComplex.map (n + 1) j
      simpa [basedWedgeCellMap, e, Topology.CWComplex.closedCell] using
        (basedWedgeCellMap_image_eq X x0 i e (Metric.closedBall (0 : Fin (n + 1) → ℝ) 1))

/-- Helper for Lemma 10.2.2: packaging a summand cell and then taking its wedge open-cell image
recovers the image of the original summand open cell under the wedge inclusion. -/
private theorem basedWedgeSummandCellOpenImage_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n) :
    basedWedgeCellMap X x0 hvertex n (basedWedgeSummandCellIndex X x0 hvertex i n j) ''
        Metric.ball (0 : Fin n → ℝ) 1 =
      basedWedgeInclusion X x0 i '' Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j :=
  by
    -- Split off the `0`-cell case, where the chosen base cell is repackaged as the distinguished
    -- wedge-point cell.
    cases n with
    | zero =>
        by_cases h : j = basedWedgeBaseCell X x0 hvertex i
        · subst h
          simp [basedWedgeSummandCellIndex]
          change basedWedgeCellMap X x0 hvertex 0 (Sum.inl (PLift.up ⟨i⟩)) ''
              Metric.ball (0 : Fin 0 → ℝ) 1 = _
          rw [basedWedgeDistinguishedOpenCell_eq X x0 hvertex (PLift.up ⟨i⟩)]
          rw [Topology.RelCWComplex.openCell_zero_eq_singleton, Set.image_singleton,
            Set.singleton_eq_singleton_iff]
          have hbase :
              basedWedgeInclusion X x0 (Classical.choice (PLift.down (PLift.up ⟨i⟩)))
                  (x0 (Classical.choice (PLift.down (PLift.up ⟨i⟩)))) =
                basedWedgeInclusion X x0 i (x0 i) := by
            simpa using
              (basedWedgeInclusion_basepoint_eq X x0
                (Classical.choice (PLift.down (PLift.up ⟨i⟩))) i)
          exact hbase.trans
            (congrArg (basedWedgeInclusion X x0 i)
              (basedWedgeBaseCellMap_eq_basepoint X x0 hvertex i)).symm
        · rw [basedWedgeCellOpenImage_eq]
          simp [basedWedgeSummandCellIndex, h]
    | succ n =>
        -- In positive dimensions the packaged index is literally the transported summand cell.
        rw [basedWedgeCellOpenImage_eq]
        simp [basedWedgeSummandCellIndex]

/-- Helper for Lemma 10.2.2: packaging a summand cell and then taking its wedge closed-cell image
recovers the image of the original summand closed cell under the wedge inclusion. -/
private theorem basedWedgeSummandCellClosedImage_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n) :
    basedWedgeCellMap X x0 hvertex n (basedWedgeSummandCellIndex X x0 hvertex i n j) ''
        Metric.closedBall (0 : Fin n → ℝ) 1 =
      basedWedgeInclusion X x0 i '' Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) n j :=
  by
    -- The same normalization works for closed cells, with the base `0`-cell turning into the
    -- distinguished singleton wedge point.
    cases n with
    | zero =>
        by_cases h : j = basedWedgeBaseCell X x0 hvertex i
        · subst h
          simp [basedWedgeSummandCellIndex]
          change basedWedgeCellMap X x0 hvertex 0 (Sum.inl (PLift.up ⟨i⟩)) ''
              Metric.closedBall (0 : Fin 0 → ℝ) 1 = _
          rw [basedWedgeDistinguishedClosedCell_eq X x0 hvertex (PLift.up ⟨i⟩)]
          rw [Topology.RelCWComplex.closedCell_zero_eq_singleton, Set.image_singleton,
            Set.singleton_eq_singleton_iff]
          have hbase :
              basedWedgeInclusion X x0 (Classical.choice (PLift.down (PLift.up ⟨i⟩)))
                  (x0 (Classical.choice (PLift.down (PLift.up ⟨i⟩)))) =
                basedWedgeInclusion X x0 i (x0 i) := by
            simpa using
              (basedWedgeInclusion_basepoint_eq X x0
                (Classical.choice (PLift.down (PLift.up ⟨i⟩))) i)
          exact hbase.trans
            (congrArg (basedWedgeInclusion X x0 i)
              (basedWedgeBaseCellMap_eq_basepoint X x0 hvertex i)).symm
        · rw [basedWedgeCellClosedImage_eq]
          simp [basedWedgeSummandCellIndex, h]
    | succ n =>
        -- Positive-dimensional cells are transported without any additional case split.
        rw [basedWedgeCellClosedImage_eq]
        simp [basedWedgeSummandCellIndex]

/-- Each explicit wedge characteristic map has source `ball 0 1`. -/
private theorem basedWedgeCell_source_eq
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (n : ℕ) (j : basedWedgeCell X x0 hvertex n) :
    (basedWedgeCellMap X x0 hvertex n j).source = Metric.ball (0 : Fin n → ℝ) 1 := by
  -- Each wedge cell is a summand characteristic map followed by the wedge inclusion.
  cases n with
  | zero =>
      rcases j with h | hij
      · let i := Classical.choice h.down
        let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
          Topology.CWComplex.map 0 (basedWedgeBaseCell X x0 hvertex i)
        change (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).source =
          Metric.ball (0 : Fin 0 → ℝ) 1
        rw [basedWedgeSummandTrans_source_eq]
        simpa [e] using
          (Topology.CWComplex.source_eq (C := (Set.univ : Set (X i))) 0
            (basedWedgeBaseCell X x0 hvertex i))
      · rcases hij with ⟨i, j⟩
        let e : PartialEquiv (Fin 0 → ℝ) (X i) := Topology.CWComplex.map 0 j.1
        change (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).source =
          Metric.ball (0 : Fin 0 → ℝ) 1
        rw [basedWedgeSummandTrans_source_eq]
        simpa [e] using
          (Topology.CWComplex.source_eq (C := (Set.univ : Set (X i))) 0 j.1)
  | succ n =>
      rcases j with ⟨i, j⟩
      let e : PartialEquiv (Fin (n + 1) → ℝ) (X i) := Topology.CWComplex.map (n + 1) j
      change (e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).source =
        Metric.ball (0 : Fin (n + 1) → ℝ) 1
      rw [basedWedgeSummandTrans_source_eq]
      simpa [e] using
        (Topology.CWComplex.source_eq (C := (Set.univ : Set (X i))) (n + 1) j)

/-- The explicit wedge characteristic maps are continuous on the closed unit ball. -/
private theorem basedWedgeCell_continuousOn
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (n : ℕ) (j : basedWedgeCell X x0 hvertex n) :
    ContinuousOn (basedWedgeCellMap X x0 hvertex n j) (Metric.closedBall (0 : Fin n → ℝ) 1) :=
  by
    -- Each characteristic map is a summand characteristic map composed with the quotient inclusion.
    cases n with
    | zero =>
        rcases j with h | hij
        · let i := Classical.choice h.down
          let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
            Topology.CWComplex.map 0 (basedWedgeBaseCell X x0 hvertex i)
          simpa [basedWedgeCellMap, e, PartialEquiv.coe_trans, Function.comp] using
            (basedWedgeInclusion_continuous X x0 i).comp_continuousOn
              (Topology.CWComplex.continuousOn (C := (Set.univ : Set (X i))) 0
                (basedWedgeBaseCell X x0 hvertex i))
        · rcases hij with ⟨i, j⟩
          let e : PartialEquiv (Fin 0 → ℝ) (X i) := Topology.CWComplex.map 0 j.1
          simpa [basedWedgeCellMap, e, PartialEquiv.coe_trans, Function.comp] using
            (basedWedgeInclusion_continuous X x0 i).comp_continuousOn
              (Topology.CWComplex.continuousOn (C := (Set.univ : Set (X i))) 0 j.1)
    | succ n =>
        rcases j with ⟨i, j⟩
        let e : PartialEquiv (Fin (n + 1) → ℝ) (X i) := Topology.CWComplex.map (n + 1) j
        simpa [basedWedgeCellMap, e, PartialEquiv.coe_trans, Function.comp] using
          (basedWedgeInclusion_continuous X x0 i).comp_continuousOn
            (Topology.CWComplex.continuousOn (C := (Set.univ : Set (X i))) (n + 1) j)

/-- The inverses of the explicit wedge characteristic maps are continuous on their targets. -/
private theorem basedWedgeCell_continuousOn_symm
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (n : ℕ) (j : basedWedgeCell X x0 hvertex n) :
    ContinuousOn (basedWedgeCellMap X x0 hvertex n j).symm
      (basedWedgeCellMap X x0 hvertex n j).target := by
  -- The inverse factors through the continuous summand retraction.
  cases n with
  | zero =>
      rcases j with h | hij
      · let i := Classical.choice h.down
        let e : PartialEquiv (Fin 0 → ℝ) (X i) :=
          Topology.CWComplex.map 0 (basedWedgeBaseCell X x0 hvertex i)
        have hcomp :
            ContinuousOn (((e : PartialEquiv (Fin 0 → ℝ) (X i)).symm) ∘
              basedWedgeSummandInverse X x0 i)
              (basedWedgeInclusion X x0 i '' e.target) := by
          refine (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set (X i))) 0
            (basedWedgeBaseCell X x0 hvertex i)).comp
              (basedWedgeSummandInverse_continuous X x0 i).continuousOn ?_
          rintro _ ⟨x, hx, rfl⟩
          simpa using hx
        change ContinuousOn (((e : PartialEquiv (Fin 0 → ℝ) (X i)).symm) ∘
          basedWedgeSummandInverse X x0 i)
          ((e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).target)
        rw [basedWedgeSummandTrans_target_eq]
        exact hcomp
      · rcases hij with ⟨i, j⟩
        let e : PartialEquiv (Fin 0 → ℝ) (X i) := Topology.CWComplex.map 0 j.1
        have hcomp :
            ContinuousOn (((e : PartialEquiv (Fin 0 → ℝ) (X i)).symm) ∘
              basedWedgeSummandInverse X x0 i)
              (basedWedgeInclusion X x0 i '' e.target) := by
          refine (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set (X i))) 0 j.1).comp
            (basedWedgeSummandInverse_continuous X x0 i).continuousOn ?_
          rintro _ ⟨x, hx, rfl⟩
          simpa using hx
        change ContinuousOn (((e : PartialEquiv (Fin 0 → ℝ) (X i)).symm) ∘
          basedWedgeSummandInverse X x0 i)
          ((e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).target)
        rw [basedWedgeSummandTrans_target_eq]
        exact hcomp
  | succ n =>
      rcases j with ⟨i, j⟩
      let e : PartialEquiv (Fin (n + 1) → ℝ) (X i) := Topology.CWComplex.map (n + 1) j
      have hcomp :
          ContinuousOn (((e : PartialEquiv (Fin (n + 1) → ℝ) (X i)).symm) ∘
            basedWedgeSummandInverse X x0 i)
            (basedWedgeInclusion X x0 i '' e.target) := by
        refine (Topology.CWComplex.continuousOn_symm (C := (Set.univ : Set (X i))) (n + 1) j).comp
          (basedWedgeSummandInverse_continuous X x0 i).continuousOn ?_
        rintro _ ⟨x, hx, rfl⟩
        simpa using hx
      change ContinuousOn (((e : PartialEquiv (Fin (n + 1) → ℝ) (X i)).symm) ∘
        basedWedgeSummandInverse X x0 i)
        ((e.trans (basedWedgeSummandPartialEquiv X x0 i e.target)).target)
      rw [basedWedgeSummandTrans_target_eq]
      exact hcomp

/-- The open cells of the explicit wedge CW structure are pairwise disjoint. -/
private theorem basedWedgeCell_pairwiseDisjoint
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) :
    (Set.univ : Set (Σ n, basedWedgeCell X x0 hvertex n)).PairwiseDisjoint
      (fun ni ↦ basedWedgeCellMap X x0 hvertex ni.1 ni.2 '' Metric.ball 0 1) := by
  classical
  intro ni _ nj _ hne
  rcases ni with ⟨n, j⟩
  rcases nj with ⟨m, k⟩
  -- Route correction: normalize each wedge open-cell image once, then dispatch the resulting
  -- distinguished-vs-transported and same-summand-vs-cross-summand cases to the dedicated
  -- disjointness lemmas already established above.
  change Disjoint
      (basedWedgeCellMap X x0 hvertex n j '' Metric.ball (0 : Fin n → ℝ) 1)
      (basedWedgeCellMap X x0 hvertex m k '' Metric.ball (0 : Fin m → ℝ) 1)
  cases n with
  | zero =>
      cases j with
      | inl h =>
          cases m with
          | zero =>
              cases k with
              | inl h' =>
                  have hh : h = h' := Subsingleton.elim _ _
                  exact (hne <| by cases hh; rfl).elim
              | inr hik =>
                  rcases hik with ⟨i, k⟩
                  rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inl h)]
                  rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i, k⟩)]
                  refine Set.disjoint_left.2 ?_
                  intro y hy1 hy2
                  simp only [Set.mem_singleton_iff] at hy1
                  subst y
                  have hkne :
                      (⟨0, k.1⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                        ⟨0, basedWedgeBaseCell X x0 hvertex i⟩ := by
                    intro hσ
                    apply k.2
                    simpa using hσ
                  have hy2' :
                      basedWedgeInclusion X x0 i (x0 i) ∈
                        basedWedgeInclusion X x0 i ''
                          Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) 0 k.1 := by
                    simpa [basedWedgeInclusion_basepoint_eq X x0 i (Classical.choice h.down)] using hy2
                  exact basedWedgeSummandOpenImage_avoidsWedgePoint X x0 hvertex i hkne hy2'
          | succ m =>
              rcases k with ⟨i, k⟩
              rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inl h)]
              rw [basedWedgeCellOpenImage_eq X x0 hvertex (m + 1) ⟨i, k⟩]
              refine Set.disjoint_left.2 ?_
              intro y hy1 hy2
              simp only [Set.mem_singleton_iff] at hy1
              subst y
              have hkne :
                  (⟨m + 1, k⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                    ⟨0, basedWedgeBaseCell X x0 hvertex i⟩ := by
                intro hσ
                cases hσ
              have hy2' :
                  basedWedgeInclusion X x0 i (x0 i) ∈
                    basedWedgeInclusion X x0 i ''
                      Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) (m + 1) k := by
                simpa [basedWedgeInclusion_basepoint_eq X x0 i (Classical.choice h.down)] using hy2
              exact basedWedgeSummandOpenImage_avoidsWedgePoint X x0 hvertex i hkne hy2'
      | inr hij =>
          rcases hij with ⟨i, j⟩
          cases m with
          | zero =>
              cases k with
              | inl h =>
                  rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i, j⟩)]
                  rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inl h)]
                  refine Set.disjoint_left.2 ?_
                  intro y hy1 hy2
                  simp only [Set.mem_singleton_iff] at hy2
                  subst y
                  have hjne :
                      (⟨0, j.1⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                        ⟨0, basedWedgeBaseCell X x0 hvertex i⟩ := by
                    intro hσ
                    apply j.2
                    simpa using hσ
                  have hy1' :
                      basedWedgeInclusion X x0 i (x0 i) ∈
                        basedWedgeInclusion X x0 i ''
                          Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) 0 j.1 := by
                    simpa [basedWedgeInclusion_basepoint_eq X x0 i (Classical.choice h.down)] using hy1
                  exact basedWedgeSummandOpenImage_avoidsWedgePoint X x0 hvertex i hjne hy1'
              | inr hik =>
                  rcases hik with ⟨i', k⟩
                  rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i, j⟩)]
                  rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i', k⟩)]
                  by_cases hii : i' = i
                  · subst i'
                    have hjk :
                        (⟨0, j.1⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                          ⟨0, k.1⟩ := by
                      intro hσ
                      have hjk' : j = k := by
                        apply Subtype.ext
                        simpa using hσ
                      apply hne
                      cases hjk'
                      rfl
                    exact basedWedgeSummandOpenCellImage_disjoint X x0 i hjk
                  · exact basedWedgeSummandOpenCellImage_disjoint_of_ne X x0 hvertex hii
                      (by
                        intro hσ
                        apply j.2
                        simpa using hσ)
                      (by
                        intro hσ
                        apply k.2
                        simpa using hσ)
          | succ m =>
              rcases k with ⟨i', k⟩
              rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i, j⟩)]
              rw [basedWedgeCellOpenImage_eq X x0 hvertex (m + 1) ⟨i', k⟩]
              by_cases hii : i' = i
              · subst i'
                have hjk :
                    (⟨0, j.1⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                      ⟨m + 1, k⟩ := by
                  intro hσ
                  cases hσ
                exact basedWedgeSummandOpenCellImage_disjoint X x0 i hjk
              · exact basedWedgeSummandOpenCellImage_disjoint_of_ne X x0 hvertex hii
                  (by
                    intro hσ
                    apply j.2
                    simpa using hσ)
                  (by
                    intro hσ
                    cases hσ)
  | succ n =>
      rcases j with ⟨i, j⟩
      cases m with
      | zero =>
          cases k with
          | inl h =>
              rw [basedWedgeCellOpenImage_eq X x0 hvertex (n + 1) ⟨i, j⟩]
              rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inl h)]
              refine Set.disjoint_left.2 ?_
              intro y hy1 hy2
              simp only [Set.mem_singleton_iff] at hy2
              subst y
              have hjne :
                  (⟨n + 1, j⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                    ⟨0, basedWedgeBaseCell X x0 hvertex i⟩ := by
                intro hσ
                cases hσ
              have hy1' :
                  basedWedgeInclusion X x0 i (x0 i) ∈
                    basedWedgeInclusion X x0 i ''
                      Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) (n + 1) j := by
                simpa [basedWedgeInclusion_basepoint_eq X x0 i (Classical.choice h.down)] using hy1
              exact basedWedgeSummandOpenImage_avoidsWedgePoint X x0 hvertex i hjne hy1'
          | inr hik =>
              rcases hik with ⟨i', k⟩
              rw [basedWedgeCellOpenImage_eq X x0 hvertex (n + 1) ⟨i, j⟩]
              rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i', k⟩)]
              by_cases hji : i' = i
              · subst i'
                have hjk :
                    (⟨n + 1, j⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                      ⟨0, k.1⟩ := by
                  intro hσ
                  cases hσ
                exact basedWedgeSummandOpenCellImage_disjoint X x0 i hjk
              · exact basedWedgeSummandOpenCellImage_disjoint_of_ne X x0 hvertex hji
                  (by
                    intro hσ
                    cases hσ)
                  (by
                    intro hσ
                    apply k.2
                    simpa using hσ)
      | succ m =>
          rcases k with ⟨i', k⟩
          rw [basedWedgeCellOpenImage_eq X x0 hvertex (n + 1) ⟨i, j⟩]
          rw [basedWedgeCellOpenImage_eq X x0 hvertex (m + 1) ⟨i', k⟩]
          by_cases hji : i' = i
          · subst i'
            have hjk :
                (⟨n + 1, j⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set (X i)) l) ≠
                  ⟨m + 1, k⟩ := by
              intro hσ
              cases hσ
              exact hne rfl
            exact basedWedgeSummandOpenCellImage_disjoint X x0 i hjk
          · exact basedWedgeSummandOpenCellImage_disjoint_of_ne X x0 hvertex hji
              (by
                intro hσ
                cases hσ)
              (by
                intro hσ
                cases hσ)

/-- The frontier of each wedge cell lies in finitely many lower-dimensional wedge closed cells. -/
private theorem basedWedgeCell_mapsTo
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (n : ℕ) (j : basedWedgeCell X x0 hvertex n) :
    ∃ I : Π m, Finset (basedWedgeCell X x0 hvertex m),
      Set.MapsTo (basedWedgeCellMap X x0 hvertex n j) (Metric.sphere (0 : Fin n → ℝ) 1)
        (⋃ (m < n) (k ∈ I m), basedWedgeCellMap X x0 hvertex m k '' Metric.closedBall 0 1) :=
  by
    classical
    cases n with
    | zero =>
        -- The `0`-sphere is empty, so the frontier condition is vacuous.
        refine ⟨fun _ ↦ ∅, ?_⟩
        rw [Set.mapsTo_iff_image_subset]
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxFalse : False := by
          have hzero : x = 0 := by
            ext i
            exact Fin.elim0 i
          have : (0 : ℝ) = 1 := by
            simpa [Metric.sphere, hzero] using hx
          norm_num at this
        exact hxFalse.elim
    | succ n =>
        rcases j with ⟨i, j⟩
        -- Pull a finite frontier witness family from the chosen summand and package each witness
        -- cell back into the wedge index type.
        obtain ⟨I, hI⟩ :=
          Topology.CWComplex.cellFrontier_subset_finite_closedCell
            (C := (Set.univ : Set (X i))) (n + 1) j
        let J : Π m, Finset (basedWedgeCell X x0 hvertex m) := fun m =>
          (I m).image (basedWedgeSummandCellIndex X x0 hvertex i m)
        refine ⟨J, ?_⟩
        rw [Set.mapsTo_iff_image_subset]
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxFrontier :
            Topology.CWComplex.map (C := (Set.univ : Set (X i))) (n + 1) j x ∈
              Topology.CWComplex.cellFrontier (C := (Set.univ : Set (X i))) (n + 1) j := by
          exact ⟨x, hx, rfl⟩
        have hcover := hI hxFrontier
        simp only [Topology.CWComplex.closedCell, Set.mem_iUnion, exists_prop] at hcover
        rcases hcover with ⟨m, hm, k, hk, hxk⟩
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨m, hm, basedWedgeSummandCellIndex X x0 hvertex i m k, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
        · -- Rewrite the packaged wedge closed cell back to the summand closed cell witness.
          rw [basedWedgeSummandCellClosedImage_eq X x0 hvertex i m k]
          refine ⟨Topology.CWComplex.map (C := (Set.univ : Set (X i))) (n + 1) j x, hxk, ?_⟩
          rfl

/-- Closedness for the explicit wedge CW structure. -/
private theorem basedWedgeClosed
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (A : Set (⋁[x0] j, X j))
    (hA : A ⊆ (Set.univ : Set (⋁[x0] j, X j))) :
    (∀ n j, IsClosed (A ∩ basedWedgeCellMap X x0 hvertex n j '' Metric.closedBall 0 1)) →
      IsClosed A := by
  intro hClosedCell
  let q : Sigma X → ⋁[x0] j, X j := Quotient.mk''
  -- Pull `A` back to each sigma fiber, use the summand CW weak-topology axiom there, and then
  -- descend the resulting closedness along the quotient map.
  have hPreimageClosed : IsClosed (q ⁻¹' A) := by
    rw [isClosed_sigma_iff]
    intro i
    let Ai : Set (X i) := (basedWedgeInclusion X x0 i) ⁻¹' A
    have hAiClosedCell :
        ∀ n j, IsClosed (Ai ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) n j) := by
      intro n j
      have hWedgeCellClosed :=
        hClosedCell n (basedWedgeSummandCellIndex X x0 hvertex i n j)
      have hPreimage :
          IsClosed
            ((basedWedgeInclusion X x0 i) ⁻¹'
              (A ∩ basedWedgeCellMap X x0 hvertex n
                (basedWedgeSummandCellIndex X x0 hvertex i n j) ''
                  Metric.closedBall (0 : Fin n → ℝ) 1)) :=
        hWedgeCellClosed.preimage (basedWedgeInclusion_continuous X x0 i)
      have hEq :
          (basedWedgeInclusion X x0 i) ⁻¹'
              (A ∩ basedWedgeCellMap X x0 hvertex n
                (basedWedgeSummandCellIndex X x0 hvertex i n j) ''
                  Metric.closedBall (0 : Fin n → ℝ) 1) =
            Ai ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) n j := by
        rw [basedWedgeSummandCellClosedImage_eq X x0 hvertex i n j]
        ext x
        constructor
        · intro hx
          rcases hx with ⟨hxA, hxCell⟩
          rcases hxCell with ⟨y, hy, hxy⟩
          have hxy' : x = y := basedWedgeInclusion_injective X x0 i hxy.symm
          exact ⟨hxA, hxy' ▸ hy⟩
        · intro hx
          rcases hx with ⟨hxA, hxCell⟩
          exact ⟨hxA, ⟨x, hxCell, rfl⟩⟩
      rw [hEq] at hPreimage
      exact hPreimage
    have hAiClosed : IsClosed Ai :=
      Topology.CWComplex.closed' (C := (Set.univ : Set (X i))) Ai
        (by intro x hx; trivial) hAiClosedCell
    simpa [Ai, q, basedWedgeInclusion] using hAiClosed
  exact (isQuotientMap_quotient_mk'.isClosed_preimage).mp hPreimageClosed

/-- The explicit wedge closed cells cover the whole wedge. -/
private theorem basedWedgeCell_union
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) :
    ⋃ (n : ℕ) (j : basedWedgeCell X x0 hvertex n),
      basedWedgeCellMap X x0 hvertex n j '' Metric.closedBall 0 1 =
        (Set.univ : Set (⋁[x0] j, X j)) := by
  ext y
  constructor
  · intro hy
    trivial
  · refine Quotient.inductionOn y ?_
    rintro ⟨i, x⟩
    intro _hy
    -- Cover the chosen representative by a summand closed cell and then package that cell into the
    -- wedge index family.
    have hx :
        x ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n),
          Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) n j := by
      let hCover :
          (⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n),
            Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) n j) =
            (Set.univ : Set (X i)) :=
        Topology.CWComplex.union (C := (Set.univ : Set (X i)))
      exact hCover.symm ▸ (show x ∈ (Set.univ : Set (X i)) from trivial)
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨n, j, hxj⟩
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨n, basedWedgeSummandCellIndex X x0 hvertex i n j, ?_⟩
    rw [basedWedgeSummandCellClosedImage_eq X x0 hvertex i n j]
    exact ⟨x, hxj, rfl⟩

/-- Lemma 10.2.2 (1). For CW complexes `X i` with chosen basepoints `x0 i` that are vertices, the
wedge `⋁[x0] i, X i`, owned by `basedWedge X x0`, admits a CW structure. -/
@[implicit_reducible]
noncomputable def basedWedgeCWComplex
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) :
    CWComplex (Set.univ : Set (⋁[x0] j, X j)) where
  cell := basedWedgeCell X x0 hvertex
  map := basedWedgeCellMap X x0 hvertex
  source_eq := basedWedgeCell_source_eq X x0 hvertex
  continuousOn := basedWedgeCell_continuousOn X x0 hvertex
  continuousOn_symm := basedWedgeCell_continuousOn_symm X x0 hvertex
  pairwiseDisjoint' := basedWedgeCell_pairwiseDisjoint X x0 hvertex
  mapsTo' := basedWedgeCell_mapsTo X x0 hvertex
  closed' := basedWedgeClosed X x0 hvertex
  union' := basedWedgeCell_union X x0 hvertex

/-- Extracts the vertex hypotheses needed for `basedWedgeCWComplex` from ambient `Fact`s. -/
private theorem isCWVertex_of_fact
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    [∀ i, Fact (IsCWVertex (x0 i))] :
    ∀ i, IsCWVertex (x0 i) :=
  fun i ↦ show IsCWVertex (x0 i) from Fact.out

/-- The wedge `⋁[x0] i, X i` carries the CW-complex structure of `basedWedgeCWComplex` once
the vertex hypotheses are available as `Fact`s. -/
noncomputable instance instCWComplexBasedWedge
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    [∀ i, Fact (IsCWVertex (x0 i))] :
    CWComplex (Set.univ : Set (⋁[x0] j, X j)) :=
  basedWedgeCWComplex X x0 (isCWVertex_of_fact X x0)

/-- The subcomplex type for the explicit wedge CW structure on `⋁[x0] i, X i`. -/
abbrev BasedWedgeSubcomplex
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) :=
  letI : CWComplex (Set.univ : Set (⋁[x0] j, X j)) := basedWedgeCWComplex X x0 hvertex
  CWComplex.Subcomplex (Set.univ : Set (⋁[x0] j, X j))

/-- The ambient wedge cells carried by the image of the `i`th summand inclusion. -/
private def basedWedgeSummandCells
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    Π n, Set (basedWedgeCell X x0 hvertex n)
  | 0 =>
      {j | match j with
        | Sum.inl _ => True
        | Sum.inr ⟨i', _⟩ => i' = i}
  | _ + 1 => {j | j.1 = i}

/-- Helper for Lemma 10.2.2: the packaged wedge cell from the `i`th summand is selected by the
canonical summand subcomplex cell family. -/
private theorem basedWedgeSummandCellIndex_mem
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) (n : ℕ)
    (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n) :
    basedWedgeSummandCellIndex X x0 hvertex i n j ∈ basedWedgeSummandCells X x0 hvertex i n := by
  -- The packaging keeps the cell in the `i`th summand and only replaces the base `0`-cell by the
  -- distinguished wedge-point cell.
  cases n with
  | zero =>
      by_cases h : j = basedWedgeBaseCell X x0 hvertex i
      · simp [basedWedgeSummandCellIndex, basedWedgeSummandCells, h]
      · simp [basedWedgeSummandCellIndex, basedWedgeSummandCells, h]
  | succ n =>
      simp [basedWedgeSummandCellIndex, basedWedgeSummandCells]

/-- Helper for Lemma 10.2.2: on the chosen sigma fiber, the quotient preimage of the same summand
range is the whole fiber. -/
private theorem basedWedgeSummandRangeFiber_eq_self
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)] (x0 : ∀ i, X i)
    (i : ι) :
    Sigma.mk i ⁻¹' ((Quotient.mk'' : Sigma X → ⋁[x0] k, X k) ⁻¹'
      Set.range (basedWedgeInclusion X x0 i)) =
      Set.univ := by
  ext x
  -- Every point of the `i`th fiber is literally in the range of the `i`th inclusion.
  simp [basedWedgeInclusion]

/-- Helper for Lemma 10.2.2: the open cells selected for the `i`th wedge summand cover exactly the
range of the `i`th wedge inclusion. -/
private theorem basedWedgeSummandRange_openCellUnion
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    ⋃ (n : ℕ) (j ∈ basedWedgeSummandCells X x0 hvertex i n),
      basedWedgeCellMap X x0 hvertex n j '' Metric.ball 0 1 =
        Set.range (basedWedgeInclusion X x0 i) := by
  ext y
  constructor
  · intro hy
    -- Any selected wedge cell is either the distinguished wedge point or a transported cell from
    -- the chosen summand, so its image lands in the summand range.
    simp only [Set.mem_iUnion] at hy
    rcases hy with ⟨n, j, hj, hyj⟩
    simp only [Set.mem_range]
    cases n with
    | zero =>
        cases j with
        | inl h =>
            rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inl h)] at hyj
            simp only [Set.mem_singleton_iff] at hyj
            refine ⟨x0 i, ?_⟩
            calc
              basedWedgeInclusion X x0 i (x0 i) =
                  basedWedgeInclusion X x0 (Classical.choice h.down)
                    (x0 (Classical.choice h.down)) :=
                basedWedgeInclusion_basepoint_eq X x0 i (Classical.choice h.down)
              _ = y := hyj.symm
        | inr hij =>
            rcases hij with ⟨i', j'⟩
            have hi : i' = i := hj
            rw [basedWedgeCellOpenImage_eq X x0 hvertex 0 (Sum.inr ⟨i', j'⟩)] at hyj
            rcases hyj with ⟨x, hx, rfl⟩
            subst hi
            exact ⟨x, rfl⟩
    | succ n =>
        rcases j with ⟨i', j'⟩
        have hi : i' = i := hj
        rw [basedWedgeCellOpenImage_eq X x0 hvertex (n + 1) ⟨i', j'⟩] at hyj
        rcases hyj with ⟨x, hx, rfl⟩
        subst hi
        exact ⟨x, rfl⟩
  · intro hy
    rcases hy with ⟨x, rfl⟩
    -- Cover `x` by a summand open cell, then package that cell into the wedge index set.
    have hx : x ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n),
        Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j := by
      let hcover :
          (⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n),
            Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j) =
            (Set.univ : Set (X i)) :=
        Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set (X i)))
      exact hcover.symm ▸ (show x ∈ (Set.univ : Set (X i)) from trivial)
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨n, j, hxj⟩
    simp only [Set.mem_iUnion]
    refine ⟨n, basedWedgeSummandCellIndex X x0 hvertex i n j,
      basedWedgeSummandCellIndex_mem X x0 hvertex i n j, ?_⟩
    rw [basedWedgeSummandCellOpenImage_eq X x0 hvertex i n j]
    exact ⟨x, hxj, rfl⟩

/-- Helper for Lemma 10.2.2: the subtype-indexed open-cell union required by
`CWComplex.Subcomplex` for the `i`th wedge summand is exactly the summand range. -/
private theorem basedWedgeSummandSubcomplex_union
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    ∅ ∪ ⋃ (n : ℕ) (j : {j // j ∈ basedWedgeSummandCells X x0 hvertex i n}),
      basedWedgeCellMap X x0 hvertex n j.1 '' Metric.ball 0 1 =
        Set.range (basedWedgeInclusion X x0 i) := by
  -- Rewrite the subtype-indexed union back to the packaged-index formulation from the previous
  -- lemma.
  rw [Set.empty_union]
  simp_rw [Set.iUnion_subtype]
  simpa using basedWedgeSummandRange_openCellUnion X x0 hvertex i

/-- Helper for Lemma 10.2.2: every wedge closed cell selected by the `i`th summand cell family
lies inside the range of the `i`th wedge inclusion. -/
private theorem basedWedgeSummandClosedCell_subset_range
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) (n : ℕ)
    {j : basedWedgeCell X x0 hvertex n}
    (hj : j ∈ basedWedgeSummandCells X x0 hvertex i n) :
    basedWedgeCellMap X x0 hvertex n j '' Metric.closedBall (0 : Fin n → ℝ) 1 ⊆
      Set.range (basedWedgeInclusion X x0 i) := by
  intro y hy
  -- Normalize the selected wedge closed cell and read off that every branch lands in the chosen
  -- summand range.
  cases n with
  | zero =>
      cases j with
      | inl h =>
          rw [basedWedgeCellClosedImage_eq X x0 hvertex 0 (Sum.inl h)] at hy
          simp only [Set.mem_singleton_iff] at hy
          refine ⟨x0 i, ?_⟩
          calc
            basedWedgeInclusion X x0 i (x0 i) =
                basedWedgeInclusion X x0 (Classical.choice h.down)
                  (x0 (Classical.choice h.down)) :=
              basedWedgeInclusion_basepoint_eq X x0 i (Classical.choice h.down)
            _ = y := hy.symm
      | inr hij =>
          rcases hij with ⟨i', j'⟩
          have hi : i' = i := hj
          rw [basedWedgeCellClosedImage_eq X x0 hvertex 0 (Sum.inr ⟨i', j'⟩)] at hy
          rcases hy with ⟨x, hx, rfl⟩
          subst hi
          exact ⟨x, rfl⟩
  | succ n =>
      rcases j with ⟨i', j'⟩
      have hi : i' = i := hj
      rw [basedWedgeCellClosedImage_eq X x0 hvertex (n + 1) ⟨i', j'⟩] at hy
      rcases hy with ⟨x, hx, rfl⟩
      subst hi
      exact ⟨x, rfl⟩

/-- Helper for Lemma 10.2.2: on a different sigma fiber, the quotient preimage of the `i`th
summand range is exactly the chosen basepoint `{x0 j}`. -/
private theorem basedWedgeSummandRangeFiber_eq_other
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)] (x0 : ∀ i, X i)
    {i j : ι} (hji : j ≠ i) :
    Sigma.mk j ⁻¹' ((Quotient.mk'' : Sigma X → ⋁[x0] k, X k) ⁻¹'
      Set.range (basedWedgeInclusion X x0 i)) =
      {x0 j} := by
  ext x
  have hij : i ≠ j := fun hij ↦ hji hij.symm
  -- Equality in the quotient forces the point to be the chosen basepoint because the summand
  -- retraction collapses every other summand to that basepoint.
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_range, basedWedgeInclusion] at hx
    rcases hx with ⟨y, hy⟩
    have hy' := congrArg (basedWedgeSummandInverse X x0 j) hy
    have hxj :
        basedWedgeSummandInverse X x0 j (Quotient.mk'' (Sigma.mk j x)) = x := by
      change basedWedgeSummandRep X x0 j (Sigma.mk j x) = x
      exact basedWedgeSummandRep_self X x0 j x
    have hiy :
        basedWedgeSummandInverse X x0 j (Quotient.mk'' (Sigma.mk i y)) = x0 j := by
      simpa [basedWedgeInclusion] using
        (basedWedgeSummandInverse_other X x0 (i := j) (j := i) hij y)
    exact hxj.symm.trans (hy'.symm.trans hiy)
  · intro hx
    subst x
    -- The chosen basepoints of different summands are identified by the quotient relation.
    simp only [Set.mem_preimage, Set.mem_range, basedWedgeInclusion]
    refine ⟨x0 i, Quotient.sound ?_⟩
    exact show (basedWedgeSetoid X x0).r (Sigma.mk i (x0 i)) (Sigma.mk j (x0 j)) from
      Or.inr ⟨rfl, rfl⟩

/-- Helper for Lemma 10.2.2: every non-basepoint of a summand lies in an open cell that misses the
distinguished basepoint. -/
private theorem existsOpenCellNeighborhoodDisjointBasepoint
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) {y : X i} (hy : y ≠ x0 i) :
    ∃ n : ℕ, ∃ j : Topology.CWComplex.cell (Set.univ : Set (X i)) n,
      y ∈ Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j ∧
        x0 i ∉ Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j := by
  -- Cover `y` by some summand open cell using the global cell decomposition of `X i`.
  have hyCover :
      y ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n),
        Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j := by
    let hcover :
        (⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set (X i)) n),
          Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) n j) =
          (Set.univ : Set (X i)) :=
      Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set (X i)))
    exact hcover.symm ▸ (show y ∈ (Set.univ : Set (X i)) from trivial)
  simp only [Set.mem_iUnion] at hyCover
  rcases hyCover with ⟨n, j, hyj⟩
  -- The containing cell cannot be the distinguished base `0`-cell, or else `y = x0 i`.
  have hneCell :
      (⟨n, j⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set (X i)) m) ≠
        ⟨0, basedWedgeBaseCell X x0 hvertex i⟩ := by
    intro hEq
    cases hEq
    rw [Topology.RelCWComplex.openCell_zero_eq_singleton] at hyj
    have hyEq :
        y =
          Topology.CWComplex.map (C := (Set.univ : Set (X i))) 0
            (basedWedgeBaseCell X x0 hvertex i) ![] := by
      simpa using hyj
    have hyBase : y = x0 i :=
      hyEq.trans (basedWedgeBaseCellMap_eq_basepoint X x0 hvertex i)
    exact hy hyBase
  refine ⟨n, j, hyj, ?_⟩
  -- Distinct open cells are disjoint from the distinguished basepoint cell.
  exact basedWedgeBasepoint_not_mem_openCell X x0 hvertex i hneCell

/-- Helper for Lemma 10.2.2: if a point misses the open part of a closed cell, then its singleton
meets that closed cell exactly along the frontier. -/
private theorem singleton_inter_closedCell_eq_singleton_inter_cellFrontier_of_not_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set X) n) {x : X}
    (hxOpen : x ∉ Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j) :
    ({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j =
      ({x} : Set X) ∩ Topology.CWComplex.cellFrontier (C := (Set.univ : Set X)) n j := by
  -- A singleton point in the closed cell must lie on the frontier unless it lies in the open cell.
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyEq, hyClosed⟩
    subst hyEq
    have hyFrontier :
        y ∈ Topology.CWComplex.cellFrontier (C := (Set.univ : Set X)) n j := by
      have hyUnion :
          y ∈ Topology.CWComplex.cellFrontier (C := (Set.univ : Set X)) n j ∪
            Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j := by
        simpa [Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell
          (C := (Set.univ : Set X)) n j] using hyClosed
      rcases hyUnion with hyFrontier | hyOpenCell
      · exact hyFrontier
      · exact False.elim (hxOpen hyOpenCell)
    exact ⟨rfl, hyFrontier⟩
  · intro hy
    rcases hy with ⟨hyEq, hyFrontier⟩
    subst hyEq
    have hyClosed :
        y ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j := by
      rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell
        (C := (Set.univ : Set X)) n j]
      exact Or.inl hyFrontier
    exact ⟨rfl, hyClosed⟩

/-- Helper for Lemma 10.2.2: a point of a positive-dimensional closed cell that misses the open
part already lies in some lower-dimensional closed cell. -/
private theorem exists_lower_closedCell_of_mem_closedCell_and_not_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set X) (n + 1)) {x : X}
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) (n + 1) j)
    (hxOpen : x ∉ Topology.CWComplex.openCell (C := (Set.univ : Set X)) (n + 1) j) :
    ∃ m < n + 1, ∃ y : Topology.CWComplex.cell (Set.univ : Set X) m,
      x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) m y := by
  -- Rewrite the missed open-cell branch as frontier membership.
  have hxFrontier :
      x ∈ Topology.CWComplex.cellFrontier (C := (Set.univ : Set X)) (n + 1) j := by
    have hxInter :
        x ∈ ({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) (n + 1) j :=
      ⟨rfl, hxClosed⟩
    have hxFrontierInter :
        x ∈ ({x} : Set X) ∩
          Topology.CWComplex.cellFrontier (C := (Set.univ : Set X)) (n + 1) j := by
      rw [singleton_inter_closedCell_eq_singleton_inter_cellFrontier_of_not_mem_openCell
        (X := X) j hxOpen] at hxInter
      exact hxInter
    exact hxFrontierInter.2
  -- The frontier is covered by finitely many lower-dimensional open cells.
  obtain ⟨I, hI⟩ :=
    Topology.CWComplex.cellFrontier_subset_finite_openCell
      (C := (Set.univ : Set X)) (n + 1) j
  have hxCover :
      x ∈ ⋃ (m < n + 1) (y ∈ I m),
        Topology.CWComplex.openCell (C := (Set.univ : Set X)) m y :=
    hI hxFrontier
  simp only [Set.mem_iUnion, exists_prop] at hxCover
  rcases hxCover with ⟨m, hm, y, _, hxy⟩
  exact ⟨m, hm, y, Topology.CWComplex.openCell_subset_closedCell _ _ hxy⟩

/-- Helper for Lemma 10.2.2: once a singleton/closed-cell intersection is closed and the point
lies in that closed cell, the ambient singleton is already closed. -/
private theorem isClosed_singleton_of_isClosed_inter_closedCell_of_mem
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set X) n) {x : X}
    (hClosed :
      IsClosed (({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j))
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j) :
    IsClosed ({x} : Set X) := by
  -- The containing closed cell does not change the singleton once it already contains the point.
  have hEq :
      ({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j =
        ({x} : Set X) := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      rcases hy with rfl
      exact ⟨rfl, hxClosed⟩
  rwa [hEq] at hClosed

/-- Helper for Lemma 10.2.2: if a point of a positive-dimensional closed cell lies on the
frontier, the lower-dimensional closed-cell induction hypothesis already closes the original
singleton/closed-cell intersection. -/
private theorem isClosed_singleton_inter_closedCell_succ_of_not_mem_openCell
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} {n : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (hn :
      ∀ m ≤ n, ∀ y : Topology.CWComplex.cell (Set.univ : Set X) m,
        IsClosed (({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) m y))
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) (n + 1) j)
    (hxOpen : x ∉ Topology.CWComplex.openCell (C := (Set.univ : Set X)) (n + 1) j) :
    IsClosed (({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) (n + 1) j) := by
  -- Descend from the frontier to a lower-dimensional closed cell, then bootstrap back up.
  obtain ⟨m, hm, y, hxy⟩ :=
    exists_lower_closedCell_of_mem_closedCell_and_not_mem_openCell (X := X) j hxClosed hxOpen
  have hSingleton : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_isClosed_inter_closedCell_of_mem (X := X) y
      (hn m (Nat.le_of_lt_succ hm) y) hxy
  have hEq :
      ({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) (n + 1) j =
        ({x} : Set X) := by
    ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      rcases hz with rfl
      exact ⟨rfl, hxClosed⟩
  rwa [hEq]

/-- Helper for Lemma 10.2.2: every point of an absolute CW complex lies in some open cell. -/
private theorem existsOpenCellContainingPoint
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)] (x : X) :
    ∃ a : Σ n, Topology.CWComplex.cell (Set.univ : Set X) n,
      x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) a.1 a.2 := by
  -- Rewrite the ambient point into the canonical union of open cells and read off one witness.
  have hx :
      x ∈ ⋃ (n : ℕ) (j : Topology.CWComplex.cell (Set.univ : Set X) n),
        Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j := by
    have hcover := Topology.CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))
    exact hcover.symm ▸ (show x ∈ (Set.univ : Set X) from trivial)
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨n, j, hxj⟩
  exact ⟨⟨n, j⟩, hxj⟩

/-- Helper for Lemma 10.2.2: a point cannot lie in two different absolute-CW open cells. -/
private theorem sigmaCell_eq_of_mem_twoOpenCells
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} {n m : ℕ} {j : Topology.CWComplex.cell (Set.univ : Set X) n}
    {i : Topology.CWComplex.cell (Set.univ : Set X) m}
    (hxj : x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j)
    (hxi : x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) m i) :
    (⟨n, j⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set X) l) = ⟨m, i⟩ := by
  -- A common point witnesses non-disjointness, so open-cell disjointness forces the owners to agree.
  refine Topology.CWComplex.eq_of_not_disjoint_openCell (C := (Set.univ : Set X)) ?_
  exact Set.not_disjoint_iff.mpr ⟨x, hxj, hxi⟩

/-- Helper for Lemma 10.2.2: a point in an absolute-CW `0`-open-cell cannot lie in any
positive-dimensional open cell. -/
private theorem not_mem_openCell_of_mem_openCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} (j : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (hxZero : x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) 0 j)
    {n : ℕ} (j' : Topology.CWComplex.cell (Set.univ : Set X) n)
    (hne :
      (⟨0, j⟩ : Σ l, Topology.CWComplex.cell (Set.univ : Set X) l) ≠ ⟨n, j'⟩) :
    x ∉ Topology.CWComplex.openCell (C := (Set.univ : Set X)) n j' := by
  -- A point of the selected `0`-cell cannot witness non-disjointness with any different owner.
  intro hxOther
  exact hne (sigmaCell_eq_of_mem_twoOpenCells (X := X) hxZero hxOther)

/-- Helper for Lemma 10.2.2: a point in an absolute-CW `0`-open-cell cannot lie in any
positive-dimensional open cell. -/
private theorem not_mem_openCell_succ_of_mem_openCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} (j : Topology.CWComplex.cell (Set.univ : Set X) 0)
    (hxZero : x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) 0 j)
    {n : ℕ} (j' : Topology.CWComplex.cell (Set.univ : Set X) (n + 1)) :
    x ∉ Topology.CWComplex.openCell (C := (Set.univ : Set X)) (n + 1) j' := by
  -- Route correction: use the owner-uniqueness helper instead of redoing the sigma-cell
  -- contradiction in each positive-dimensional branch.
  exact not_mem_openCell_of_mem_openCell_zero (X := X) j hxZero j'
    (by
      intro hEq
      exact Nat.succ_ne_zero n (congrArg Sigma.fst hEq).symm)

/-- Helper for Lemma 10.2.2: membership in a closed `0`-cell upgrades to the corresponding open
`0`-cell because both zero-dimensional cells are the same singleton. -/
private theorem mem_openCell_zero_of_mem_closedCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) {x : X}
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j) :
    x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) 0 j := by
  -- Normalize both zero-dimensional cells to the same singleton.
  rw [Topology.RelCWComplex.closedCell_zero_eq_singleton] at hxClosed
  rw [Topology.RelCWComplex.openCell_zero_eq_singleton]
  simpa using hxClosed

/-- Helper for Lemma 10.2.2: a closed `0`-cell containing `x` is exactly the singleton `{x}`. -/
private theorem closedCell_zero_eq_singleton_of_mem
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) {x : X}
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j) :
    Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j = ({x} : Set X) := by
  -- Normalize the chosen `0`-cell to the canonical singleton supplied by the closed-cell API.
  have hxEq : Topology.CWComplex.map (C := (Set.univ : Set X)) 0 j ![] = x := by
    rw [Topology.RelCWComplex.closedCell_zero_eq_singleton] at hxClosed
    simpa using hxClosed.symm
  rw [Topology.RelCWComplex.closedCell_zero_eq_singleton, Set.singleton_eq_singleton_iff]
  exact hxEq

/-- Helper for Lemma 10.2.2: if a point misses a closed cell, then its singleton has empty
intersection with that cell. -/
private theorem singleton_inter_closedCell_eq_empty_of_not_mem
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {n : ℕ} (j : Topology.CWComplex.cell (Set.univ : Set X) n) {x : X}
    (hxClosed : x ∉ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j) :
    ({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n j = ∅ := by
  -- If `x` is not in the cell, the singleton contributes no point to the intersection.
  ext y
  constructor
  · intro hy
    have hyx : y = x := by simpa using hy.1
    subst hyx
    exact False.elim (hxClosed hy.2)
  · intro hy
    exact False.elim hy

/-- Helper for Lemma 10.2.2: a point carried by an absolute-CW `0`-open-cell has ambiently
closed singleton. -/
private theorem isClosed_singleton_of_mem_openCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {x : X} {j : Topology.CWComplex.cell (Set.univ : Set X) 0}
    (hxOpen : x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) 0 j) :
    IsClosed ({x} : Set X) := by
  -- Route correction: use the item-owned support theorem as the canonical owner of the remaining
  -- absolute-CW separation argument, so the blocker only lives in one file.
  exact Topology.CWComplex.isClosed_singleton_of_mem_openCell_zero (X := X) hxOpen

/-- Helper for Lemma 10.2.2: a point carried by an absolute-CW `0`-cell has ambiently closed
singleton. -/
private theorem isClosed_singleton_of_mem_closedCell_zero
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) {x : X}
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j) :
    IsClosed ({x} : Set X) := by
  -- Route correction: use the item-owned zero-cell support theorem rather than keeping the
  -- carrier-local specialization argument inline in the wedge file.
  have hxOpen :
      x ∈ Topology.CWComplex.openCell (C := (Set.univ : Set X)) 0 j :=
    mem_openCell_zero_of_mem_closedCell_zero (X := X) j hxClosed
  exact isClosed_singleton_of_mem_openCell_zero (X := X) hxOpen

/-- Helper for Lemma 10.2.2: the remaining absolute-CW separation frontier is the ambient
closedness of a singleton carried by a `0`-cell. -/
private theorem isClosed_singleton_inter_closedCell_zero_of_mem
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (j : Topology.CWComplex.cell (Set.univ : Set X) 0) {x : X}
    (hxClosed : x ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j) :
    IsClosed (({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j) := by
  -- Route correction: close the `0`-dimensional branch directly from singleton closedness, rather
  -- than routing through a global separation instance.
  have hClosedSingleton : IsClosed ({x} : Set X) :=
    isClosed_singleton_of_mem_closedCell_zero (X := X) j hxClosed
  have hEq :
      ({x} : Set X) ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) 0 j =
        ({x} : Set X) := by
    -- The containing `0`-cell is already the singleton `{x}` by the zero-dimensional API.
    rw [closedCell_zero_eq_singleton_of_mem (X := X) j hxClosed, Set.inter_self]
  rwa [hEq]

/-- Helper for Lemma 10.2.2: each chosen basepoint singleton is closed in its summand because the
CW weak-topology axiom reduces the check to intersections with closed cells. -/
private theorem basedWedgeBasepointSingleton_closed
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    IsClosed ({x0 i} : Set (X i)) := by
  -- Route correction: avoid the generic absolute-CW `T1` detour from the support file.
  -- Instead, use the weak-topology criterion and show each closed-cell intersection with `{x0 i}`
  -- is closed by dimension induction.
  refine Topology.CWComplex.closed' (C := (Set.univ : Set (X i))) ({x0 i} : Set (X i))
    (by intro x hx; trivial) ?_
  intro n
  change ∀ j : Topology.CWComplex.cell (Set.univ : Set (X i)) n,
    IsClosed (({x0 i} : Set (X i)) ∩
      Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) n j)
  induction n using Nat.case_strong_induction_on with
  | hz =>
      intro j
      by_cases hxClosed :
          x0 i ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) 0 j
      · -- A `0`-cell containing the basepoint is exactly the singleton `{x0 i}`.
        exact isClosed_singleton_inter_closedCell_zero_of_mem (X := X i) j hxClosed
      · -- Missing the closed `0`-cell forces the singleton intersection to be empty.
        rw [singleton_inter_closedCell_eq_empty_of_not_mem (X := X i) j hxClosed]
        exact isClosed_empty
  | hi n ih =>
      intro j
      by_cases hxClosed :
          x0 i ∈ Topology.CWComplex.closedCell (C := (Set.univ : Set (X i))) (n + 1) j
      · -- Positive-dimensional cells cannot contain the basepoint in their open part.
        have hxOpen :
            x0 i ∉ Topology.CWComplex.openCell (C := (Set.univ : Set (X i))) (n + 1) j := by
          refine basedWedgeBasepoint_not_mem_openCell X x0 hvertex i ?_
          intro hEq
          exact Nat.succ_ne_zero n (congrArg Sigma.fst hEq)
        exact isClosed_singleton_inter_closedCell_succ_of_not_mem_openCell (X := X i) j
          (fun m hm y ↦ ih m hm y) hxClosed hxOpen
      · -- If the basepoint misses the closed cell, the intersection is empty.
        rw [singleton_inter_closedCell_eq_empty_of_not_mem (X := X i) j hxClosed]
        exact isClosed_empty

/-- Helper for Lemma 10.2.2: if every chosen basepoint singleton is closed in its own summand,
then the image of each summand inclusion is closed in the wedge quotient. -/
private theorem basedWedgeSummandSubcomplex_closed_of_singletonClosed
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hsingleton : ∀ j : ι, IsClosed ({x0 j} : Set (X j))) (i : ι) :
    IsClosed (Set.range (basedWedgeInclusion X x0 i) : Set (⋁[x0] j, X j)) := by
  -- Pull back the summand image along the quotient map and test closedness fiberwise on `Sigma X`.
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  -- The quotient preimage is closed once every sigma-fiber preimage is closed.
  rw [isClosed_sigma_iff]
  intro j
  by_cases hji : j = i
  · subst hji
    -- On the chosen fiber, every point already lies in the summand range.
    change IsClosed
      (Sigma.mk j ⁻¹' ((Quotient.mk'' : Sigma X → ⋁[x0] k, X k) ⁻¹'
        Set.range (basedWedgeInclusion X x0 j)))
    have hfiber :
        Sigma.mk j ⁻¹' ((Quotient.mk'' : Sigma X → ⋁[x0] k, X k) ⁻¹'
          Set.range (basedWedgeInclusion X x0 j)) =
          (Set.univ : Set (X j)) := by
      ext x
      simp [basedWedgeInclusion]
    rw [hfiber]
    exact isClosed_univ
  · -- On every other fiber, only the chosen basepoint survives in the quotient preimage.
    change IsClosed
      (Sigma.mk j ⁻¹' ((Quotient.mk'' : Sigma X → ⋁[x0] k, X k) ⁻¹'
        Set.range (basedWedgeInclusion X x0 i)))
    rw [basedWedgeSummandRangeFiber_eq_other X x0 hji]
    -- The off-diagonal fiber is exactly the closed singleton `{x0 j}`.
    exact hsingleton j

/-- The image of a summand inclusion is closed in the explicit wedge CW structure. -/
private theorem basedWedgeSummandSubcomplex_closed
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    IsClosed (Set.range (basedWedgeInclusion X x0 i) : Set (⋁[x0] j, X j)) := by
  -- Route correction: isolate the quotient-fiber argument from the remaining singleton-closed
  -- obligation so the only open frontier is the absolute-CW separation bridge above.
  exact basedWedgeSummandSubcomplex_closed_of_singletonClosed X x0
    (fun j ↦ basedWedgeBasepointSingleton_closed X x0 hvertex j) i

/-- The canonical subcomplex of the wedge carried by the image of the `i`th summand. -/
noncomputable def basedWedgeSummandSubcomplex
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    BasedWedgeSubcomplex X x0 hvertex :=
  letI : CWComplex (Set.univ : Set (⋁[x0] j, X j)) := basedWedgeCWComplex X x0 hvertex
  { carrier := Set.range (basedWedgeInclusion X x0 i)
    I := basedWedgeSummandCells X x0 hvertex i
    closed' := basedWedgeSummandSubcomplex_closed X x0 hvertex i
    -- The selected wedge cells are exactly the packaged open cells coming from the chosen
    -- summand.
    union' := basedWedgeSummandSubcomplex_union X x0 hvertex i }

/-- The carrier of the canonical subcomplex determined by the `i`th wedge summand is exactly the
image of the `i`th wedge inclusion. -/
@[simp] theorem basedWedgeSummandSubcomplex_coe
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    (basedWedgeSummandSubcomplex X x0 hvertex i : Set (⋁[x0] j, X j)) =
      Set.range (basedWedgeInclusion X x0 i) :=
  rfl

/-- The canonical map of the `i`th summand into the wedge is an embedding at the quotient-topology
level, independently of any CW structure on the summands. -/
theorem basedWedgeInclusion_isEmbedding
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x0 : ∀ i, X i) (i : ι) :
    IsEmbedding (basedWedgeInclusion X x0 i) := by
  -- The quotient inclusion has the continuous summand retraction as a left inverse.
  have hleft : Function.LeftInverse (basedWedgeSummandInverse X x0 i)
      (basedWedgeInclusion X x0 i) := by
    intro x
    exact basedWedgeSummandInverse_inclusion X x0 i x
  exact hleft.isEmbedding
    (basedWedgeSummandInverse_continuous X x0 i)
    (basedWedgeInclusion_continuous X x0 i)

/-- Lemma 10.2.2 (2). For each summand of the wedge of CW complexes with vertex basepoints, the
canonical map `basedWedgeInclusion X x0 i : X i → ⋁[x0] j, X j` is an embedding, and its image is
the carrier of the named subcomplex `basedWedgeSummandSubcomplex X x0 hvertex i` of the wedge CW
structure. -/
theorem basedWedgeSummandSubcomplex_spec
    {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    [∀ i, CWComplex (Set.univ : Set (X i))] (x0 : ∀ i, X i)
    (hvertex : ∀ i, IsCWVertex (x0 i)) (i : ι) :
    IsEmbedding (basedWedgeInclusion X x0 i) ∧
      (basedWedgeSummandSubcomplex X x0 hvertex i : Set (⋁[x0] j, X j)) =
        Set.range (basedWedgeInclusion X x0 i) := by
  exact ⟨basedWedgeInclusion_isEmbedding X x0 i,
    basedWedgeSummandSubcomplex_coe X x0 hvertex i⟩
