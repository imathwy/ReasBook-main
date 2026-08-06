import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_2

open scoped unitInterval
open Set Filter Topology

universe u v

variable {X₀ : Type u} {J : Type v}

local instance sourceTopology : TopologicalSpace (X₀ ⊕ (J × I)) :=
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  inferInstance

local instance graphTopology (boundary : J ↪ Fin 2 → X₀) :
    TopologicalSpace (graphRealization boundary) :=
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := sourceTopology
  show TopologicalSpace (Quotient (graphRealizationSetoid boundary)) from inferInstance

-- Semantic recall: `LocallyCompactSpace` is the canonical topological target property here, and
-- `FiniteGraph` in Definition 4.1.4 is the local chapter precedent for a graph property class.

/-- The edges of `graphRealization boundary` incident to the vertex `x`. -/
def incidentEdges (boundary : J ↪ Fin 2 → X₀) (x : X₀) : Set J :=
  {j | boundary j 0 = x ∨ boundary j 1 = x}

@[simp] theorem mem_incidentEdges_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀) (j : J) :
    j ∈ incidentEdges boundary x ↔ boundary j 0 = x ∨ boundary j 1 = x :=
  Iff.rfl

/-- For Definition 4.1.5, a graph realization is locally finite when each vertex is the boundary
point
of only finitely many edges, i.e. for every vertex `x : X₀` there are only finitely many edge
indices `j : J` such that `boundary j 0 = x` or `boundary j 1 = x`. -/
class LocallyFiniteGraph (boundary : J ↪ Fin 2 → X₀) : Prop where
  finiteIncidentEdges (x : X₀) : (incidentEdges boundary x).Finite

instance LocallyFiniteGraph.finiteIncidentEdgesFinite {boundary : J ↪ Fin 2 → X₀} (x : X₀)
    [h : LocallyFiniteGraph boundary] : Finite (incidentEdges boundary x) :=
  (h.finiteIncidentEdges x).to_subtype

/-- In a locally finite graph realization, each vertex is incident to only finitely many edges. -/
theorem LocallyFiniteGraph.finiteIncidentEdges' {boundary : J ↪ Fin 2 → X₀} (x : X₀)
    [LocallyFiniteGraph boundary] :
    Finite (incidentEdges boundary x) :=
  inferInstance

/-- Helper for Definition 4.1.5: the closed initial half-branch of the edge `j` up to `a`. -/
def leftClosedBranchSource (j : J) (a : I) : Set (X₀ ⊕ (J × I)) :=
  Sum.inr '' (Prod.mk j '' Set.Icc 0 a)

/-- Helper for Definition 4.1.5: the closed terminal half-branch of the edge `j` from `a`. -/
def rightClosedBranchSource (j : J) (a : I) : Set (X₀ ⊕ (J × I)) :=
  Sum.inr '' (Prod.mk j '' Set.Icc a 1)

/-- Helper for Definition 4.1.5: the source-side closed branch data contributed by the edge `j`
at the vertex `x`. -/
def initialIncidentClosedBranchSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left : J → I) (_right : J → I) (j : J) : Set (X₀ ⊕ (J × I)) :=
  {z | ∃ t : I, boundary j 0 = x ∧ z = Sum.inr (j, t) ∧ t ∈ Set.Icc 0 (left j)}

/-- Helper for Definition 4.1.5: the source-side closed terminal branch data contributed by the
edge `j` at the vertex `x`. -/
def terminalIncidentClosedBranchSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (_left : J → I) (right : J → I) (j : J) : Set (X₀ ⊕ (J × I)) :=
  {z | ∃ t : I, boundary j 1 = x ∧ z = Sum.inr (j, t) ∧ t ∈ Set.Icc (right j) 1}

/-- Helper for Definition 4.1.5: the source-side closed branch data contributed by the edge `j`
at the vertex `x`. -/
def incidentClosedBranchSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (j : J) : Set (X₀ ⊕ (J × I)) :=
  initialIncidentClosedBranchSource boundary x left right j ∪
    terminalIncidentClosedBranchSource boundary x left right j

/-- Helper for Definition 4.1.5: the source-side closed star around the vertex `x`. -/
def vertexClosedStarSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) : Set (X₀ ⊕ (J × I)) :=
  ({Sum.inl x} : Set (X₀ ⊕ (J × I))) ∪
    ⋃ j ∈ incidentEdges boundary x, incidentClosedBranchSource boundary x left right j

/-- Helper for Definition 4.1.5: the quotient image of the closed source star around `x`. -/
def vertexClosedStar (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) : Set (graphRealization boundary) :=
  (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ''
    vertexClosedStarSource boundary x left right

/-- Helper for Definition 4.1.5: the vertex summand of the closed star contains only the center
vertex. -/
@[simp] theorem mem_vertexClosedStarSource_inl (boundary : J ↪ Fin 2 → X₀) (x y : X₀)
    (left right : J → I) :
    Sum.inl y ∈ vertexClosedStarSource boundary x left right ↔ y = x := by
  constructor
  · intro hy
    rcases hy with h | h
    · simpa using h
    · rcases mem_iUnion.1 h with ⟨j, h⟩
      rcases mem_iUnion.1 h with ⟨_, h⟩
      rcases h with h | h <;> rcases h with ⟨t, _, ht, _⟩ <;> cases ht
  · intro hy
    left
    simp [hy]

/-- Helper for Definition 4.1.5: the edge summand of the closed star records exactly the initial
and terminal closed branches incident to `x`. -/
@[simp] theorem mem_vertexClosedStarSource_inr (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (j : J) (t : I) :
    Sum.inr (j, t) ∈ vertexClosedStarSource boundary x left right ↔
      ((boundary j 0 = x ∧ t ≤ left j) ∨ (boundary j 1 = x ∧ right j ≤ t)) := by
  constructor
  · intro hz
    rcases hz with h | h
    · cases h
    · rcases mem_iUnion.1 h with ⟨j', h⟩
      rcases mem_iUnion.1 h with ⟨_, h⟩
      rcases h with h | h
      · rcases h with ⟨u, hu0, huEq, huIcc⟩
        cases huEq
        exact Or.inl ⟨hu0, huIcc.2⟩
      · rcases h with ⟨u, hu1, huEq, huIcc⟩
        cases huEq
        exact Or.inr ⟨hu1, huIcc.1⟩
  · intro hz
    right
    refine mem_iUnion.2 ⟨j, mem_iUnion.2 ?_⟩
    rcases hz with hz | hz
    · refine ⟨by simpa [mem_incidentEdges_iff] using Or.inl hz.1, ?_⟩
      left
      exact ⟨t, hz.1, rfl, ⟨unitInterval.nonneg', hz.2⟩⟩
    · refine ⟨by simpa [mem_incidentEdges_iff] using Or.inr hz.1, ?_⟩
      right
      exact ⟨t, hz.1, rfl, ⟨hz.2, unitInterval.le_one'⟩⟩

/-- Helper for Definition 4.1.5: each closed initial half-branch is compact in the source. -/
lemma isCompact_leftClosedBranchSource (j : J) (a : I) :
    IsCompact (leftClosedBranchSource (X₀ := X₀) j a) := by
  -- Identify the branch with the image of the compact interval `Set.Icc 0 a`.
  have hset :
      leftClosedBranchSource (X₀ := X₀) j a =
        (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) '' Set.Icc 0 a := by
    ext z
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
  rw [hset]
  -- The source inclusion is continuous because the vertex and edge-index coordinates are discrete.
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hcont : Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
    simpa using (continuous_inr.comp (continuous_const.prodMk continuous_id))
  have hIcc : IsCompact (Set.Icc (0 : I) a) := by
    -- Compare the subtype interval with the real closed interval `[0, a]`.
    rw [Subtype.isCompact_iff]
    have himage : ((↑) '' (Set.Icc (0 : I) a) : Set ℝ) = Set.Icc (0 : ℝ) (a : ℝ) := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        refine ⟨⟨r, ⟨hr.1, le_trans hr.2 a.2.2⟩⟩, hr, rfl⟩
    rw [himage]
    have hbounded : Bornology.IsBounded (Set.Icc (0 : ℝ) (a : ℝ)) := by
      refine (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (0 : ℝ) 1)).subset ?_
      intro r hr
      have hle : r ≤ (1 : ℝ) := le_trans hr.2 a.2.2
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hr.1] using hle
    exact (Metric.isCompact_iff_isClosed_bounded.2 ⟨isClosed_Icc, hbounded⟩)
  simpa using hIcc.image hcont

/-- Helper for Definition 4.1.5: each closed terminal half-branch is compact in the source. -/
lemma isCompact_rightClosedBranchSource (j : J) (a : I) :
    IsCompact (rightClosedBranchSource (X₀ := X₀) j a) := by
  -- Identify the branch with the image of the compact interval `Set.Icc a 1`.
  have hset :
      rightClosedBranchSource (X₀ := X₀) j a =
        (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) '' Set.Icc a 1 := by
    ext z
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
  rw [hset]
  -- The same source inclusion pushes compactness of the interval to the branch.
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hcont : Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
    simpa using (continuous_inr.comp (continuous_const.prodMk continuous_id))
  have hIcc : IsCompact (Set.Icc a (1 : I)) := by
    -- Compare the subtype interval with the real closed interval `[a, 1]`.
    rw [Subtype.isCompact_iff]
    have himage : ((↑) '' (Set.Icc a (1 : I)) : Set ℝ) = Set.Icc (a : ℝ) (1 : ℝ) := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        refine ⟨⟨r, ⟨le_trans a.2.1 hr.1, hr.2⟩⟩, hr, rfl⟩
    rw [himage]
    have hbounded : Bornology.IsBounded (Set.Icc (a : ℝ) (1 : ℝ)) := by
      refine (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (0 : ℝ) 1)).subset ?_
      intro r hr
      have hnonneg : 0 ≤ r := le_trans a.2.1 hr.1
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hnonneg] using hr.2
    exact (Metric.isCompact_iff_isClosed_bounded.2 ⟨isClosed_Icc, hbounded⟩)
  simpa using hIcc.image hcont

/-- Helper for Definition 4.1.5: the initial source-side contribution of `j` is compact. -/
lemma isCompact_initialIncidentClosedBranchSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (j : J) :
    IsCompact (initialIncidentClosedBranchSource boundary x left right j) := by
  classical
  -- The branch is either empty or exactly the corresponding closed half-branch.
  by_cases h0 : boundary j 0 = x
  · have hset :
        initialIncidentClosedBranchSource boundary x left right j =
          leftClosedBranchSource (X₀ := X₀) j (left j) := by
      ext z
      constructor
      · rintro ⟨t, -, rfl, ht⟩
        exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨t, ht, rfl⟩
        exact ⟨t, h0, rfl, ht⟩
    rw [hset]
    exact isCompact_leftClosedBranchSource j (left j)
  · have hset :
        initialIncidentClosedBranchSource boundary x left right j = ∅ := by
      ext z
      simp [initialIncidentClosedBranchSource, h0]
    rw [hset]
    exact isCompact_empty

/-- Helper for Definition 4.1.5: the terminal source-side contribution of `j` is compact. -/
lemma isCompact_terminalIncidentClosedBranchSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (j : J) :
    IsCompact (terminalIncidentClosedBranchSource boundary x left right j) := by
  classical
  -- The branch is either empty or exactly the corresponding closed half-branch.
  by_cases h1 : boundary j 1 = x
  · have hset :
        terminalIncidentClosedBranchSource boundary x left right j =
          rightClosedBranchSource (X₀ := X₀) j (right j) := by
      ext z
      constructor
      · rintro ⟨t, -, rfl, ht⟩
        exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨t, ht, rfl⟩
        exact ⟨t, h1, rfl, ht⟩
    rw [hset]
    exact isCompact_rightClosedBranchSource j (right j)
  · have hset :
        terminalIncidentClosedBranchSource boundary x left right j = ∅ := by
      ext z
      simp [terminalIncidentClosedBranchSource, h1]
    rw [hset]
    exact isCompact_empty

/-- Helper for Definition 4.1.5: the closed branch contribution of a single incident edge is
compact. -/
lemma isCompact_incidentClosedBranchSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (j : J) :
    IsCompact (incidentClosedBranchSource boundary x left right j) := by
  -- Each edge contributes two compact branch pieces, one for each possible endpoint.
  rw [incidentClosedBranchSource]
  exact (isCompact_initialIncidentClosedBranchSource boundary x left right j).union
    (isCompact_terminalIncidentClosedBranchSource boundary x left right j)

/-- Helper for Definition 4.1.5: a closed source star is compact whenever only finitely many
incident edges occur. -/
lemma vertexClosedStarSourceCompact (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (hfinite : (incidentEdges boundary x).Finite) :
    IsCompact (vertexClosedStarSource boundary x left right) := by
  classical
  -- The source star is a finite union of compact branch pieces together with the central vertex.
  rw [vertexClosedStarSource]
  refine isCompact_singleton.union ?_
  refine hfinite.isCompact_biUnion ?_
  intro j hj
  exact isCompact_incidentClosedBranchSource boundary x left right j

/-- Helper for Definition 4.1.5: the quotient closed star around a locally finite vertex is
compact. -/
lemma vertexClosedStarCompact (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (hfinite : (incidentEdges boundary x).Finite) :
    IsCompact (vertexClosedStar boundary x left right) := by
  -- Push the compact source star through the quotient projection.
  let q : (X₀ ⊕ (J × I)) → graphRealization boundary :=
    @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hq : Continuous q := by
    simpa [q, graphRealization] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)))
  simpa [vertexClosedStar, q] using
    (vertexClosedStarSourceCompact boundary x left right hfinite).image hq

/-- Helper for Definition 4.1.5: a single generating endpoint identification cannot move an
interior point of an edge. -/
lemma graphRealizationRel_edgeInterior_eq_iff (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationRel boundary a b) :
    a = Sum.inr (j, t) ↔ b = Sum.inr (j, t) := by
  constructor
  · intro ha
    subst ha
    cases b with
    | inl x =>
        rcases hab with (⟨hzero, _⟩ | ⟨hone, _⟩)
        · exact (ht₀ hzero).elim
        · exact (ht₁ hone).elim
    | inr jt =>
        cases hab
  · intro hb
    subst hb
    cases a with
    | inl x =>
        rcases hab with (⟨_, hzero⟩ | ⟨_, hone⟩)
        · exact (ht₀ hzero).elim
        · exact (ht₁ hone).elim
    | inr jt =>
        cases hab

/-- Helper for Definition 4.1.5: the full realization setoid fixes any interior edge point. -/
lemma graphRealizationSetoid_edgeInterior_eq_iff (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationSetoid boundary a b) :
    a = Sum.inr (j, t) ↔ b = Sum.inr (j, t) := by
  -- Extend the endpoint check along the equivalence closure generated by the quotient relation.
  induction hab with
  | rel _ _ hrel =>
      exact graphRealizationRel_edgeInterior_eq_iff boundary j t ht₀ ht₁ hrel
  | refl a =>
      simp
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Definition 4.1.5: an interior edge representative is fixed by the realization
quotient relation. -/
lemma graphRealizationSetoid_edgeInterior_fixed (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {z : X₀ ⊕ (J × I)}
    (hz : graphRealizationSetoid boundary (Sum.inr (j, t)) z) :
    z = Sum.inr (j, t) :=
  (graphRealizationSetoid_edgeInterior_eq_iff boundary j t ht₀ ht₁ hz).1 rfl

/-- Helper for Definition 4.1.5: quotient points coming from edge interiors remember both their
edge index and parameter. -/
lemma graphEdgePointInterior_eq_iff (boundary : J ↪ Fin 2 → X₀) {j j' : J} {s t : I}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    graphEdgePoint boundary j s = graphEdgePoint boundary j' t ↔ j = j' ∧ s = t := by
  constructor
  · intro hEq
    -- Move back to the source setoid and use the interior-point rigidity lemma there.
    have hsetoid :
        graphRealizationSetoid boundary (Sum.inr (j, s)) (Sum.inr (j', t)) := by
      change
        @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary) (Sum.inr (j, s)) =
          @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary) (Sum.inr (j', t)) at hEq
      exact Quotient.eq'.1 hEq
    have hsource :
        Sum.inr (j', t) = (Sum.inr (j, s) : X₀ ⊕ (J × I)) :=
      graphRealizationSetoid_edgeInterior_fixed boundary j s hs₀ hs₁ hsetoid
    cases hsource
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Helper for Definition 4.1.5: the source-side open star around the vertex `x`. -/
def vertexOpenStarSource (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) : Set (X₀ ⊕ (J × I)) :=
  {z | z = Sum.inl x ∨ ∃ j t, z = Sum.inr (j, t) ∧
      ((boundary j 0 = x ∧ t < left j) ∨ (boundary j 1 = x ∧ right j < t))}

/-- Helper for Definition 4.1.5: the quotient image of the open source star around `x`. -/
def vertexOpenStar (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) : Set (graphRealization boundary) :=
  (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ''
    vertexOpenStarSource boundary x left right

/-- Helper for Definition 4.1.5: the vertex summand of the open star contains only the center
vertex. -/
@[simp] theorem mem_vertexOpenStarSource_inl (boundary : J ↪ Fin 2 → X₀) (x y : X₀)
    (left right : J → I) :
    Sum.inl y ∈ vertexOpenStarSource boundary x left right ↔ y = x := by
  constructor
  · intro hy
    rcases hy with h | ⟨j, t, hz, _⟩
    · simpa using h
    · cases hz
  · intro hy
    left
    simp [hy]

/-- Helper for Definition 4.1.5: the edge summand of the open star is described by the chosen
incident initial and terminal open segments. -/
@[simp] theorem mem_vertexOpenStarSource_inr (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) (j : J) (t : I) :
    Sum.inr (j, t) ∈ vertexOpenStarSource boundary x left right ↔
      ((boundary j 0 = x ∧ t < left j) ∨ (boundary j 1 = x ∧ right j < t)) := by
  constructor
  · intro hz
    rcases hz with h | ⟨j', t', hz, hmem⟩
    · cases h
    · cases hz
      simpa using hmem
  · intro hz
    right
    exact ⟨j, t, rfl, hz⟩

/-- Helper for Definition 4.1.5: the open source star is open in the source disjoint union. -/
lemma vertexOpenStarSource_isOpen (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    IsOpen (vertexOpenStarSource boundary x left right) := by
  classical
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := ⟨rfl⟩
  let _ : DiscreteTopology J := ⟨rfl⟩
  rw [isOpen_sum_iff]
  constructor
  · -- The vertex summand is discrete, so the center singleton is open.
    have hpre : Sum.inl ⁻¹' vertexOpenStarSource boundary x left right = ({x} : Set X₀) := by
      ext y
      simp [mem_vertexOpenStarSource_inl]
    rw [hpre]
    change @TopologicalSpace.IsOpen X₀ ⊥ ({x} : Set X₀)
    simpa using isOpen_discrete ({x} : Set X₀)
  · -- The edge summand is a union of open rectangles indexed by the incident edges.
    have hEq :
        Sum.inr ⁻¹' vertexOpenStarSource boundary x left right =
          (⋃ j, (if boundary j 0 = x then ({j} : Set J) ×ˢ Set.Iio (left j) else ∅)) ∪
            ⋃ j, (if boundary j 1 = x then ({j} : Set J) ×ˢ Set.Ioi (right j) else ∅) := by
      ext p
      rcases p with ⟨j, t⟩
      by_cases h0 : boundary j 0 = x
      · by_cases h1 : boundary j 1 = x
        · simp [mem_vertexOpenStarSource_inr, h0, h1]
        · simp [mem_vertexOpenStarSource_inr, h0, h1]
      · by_cases h1 : boundary j 1 = x
        · simp [mem_vertexOpenStarSource_inr, h0, h1]
        · simp [mem_vertexOpenStarSource_inr, h0, h1]
    rw [hEq]
    refine IsOpen.union ?_ ?_
    · refine isOpen_iUnion fun j ↦ ?_
      by_cases h0 : boundary j 0 = x
      · have hsingle : IsOpen ({j} : Set J) := by
          change @TopologicalSpace.IsOpen J ⊥ ({j} : Set J)
          simpa using isOpen_discrete ({j} : Set J)
        simpa [h0] using hsingle.prod isOpen_Iio
      · simp [h0]
    · refine isOpen_iUnion fun j ↦ ?_
      by_cases h1 : boundary j 1 = x
      · have hsingle : IsOpen ({j} : Set J) := by
          change @TopologicalSpace.IsOpen J ⊥ ({j} : Set J)
          simpa using isOpen_discrete ({j} : Set J)
        simpa [h1] using hsingle.prod isOpen_Ioi
      · simp [h1]

/-- Helper for Definition 4.1.5: the open source star is invariant under a single generating
endpoint identification once the chosen radii really reach the corresponding vertex. -/
lemma vertexOpenStarSource_rel_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → (0 : I) < left j)
    (hright : ∀ j, boundary j 1 = x → right j < (1 : I))
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationRel boundary a b) :
    a ∈ vertexOpenStarSource boundary x left right ↔
      b ∈ vertexOpenStarSource boundary x left right := by
  cases a with
  | inl xa =>
      cases b with
      | inl xb =>
          cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with (⟨hxa, ht⟩ | ⟨hxa, ht⟩)
          · subst hxa
            subst ht
            constructor
            · intro hmem
              simp only [mem_vertexOpenStarSource_inl, mem_vertexOpenStarSource_inr] at hmem ⊢
              exact Or.inl ⟨hmem, hleft j hmem⟩
            · intro hmem
              simp only [mem_vertexOpenStarSource_inl, mem_vertexOpenStarSource_inr] at hmem ⊢
              rcases hmem with hmem | hmem
              · exact hmem.1
              · exact (not_lt_of_ge unitInterval.nonneg' hmem.2).elim
          · subst hxa
            subst ht
            constructor
            · intro hmem
              simp only [mem_vertexOpenStarSource_inl, mem_vertexOpenStarSource_inr] at hmem ⊢
              exact Or.inr ⟨hmem, hright j hmem⟩
            · intro hmem
              simp only [mem_vertexOpenStarSource_inl, mem_vertexOpenStarSource_inr] at hmem ⊢
              rcases hmem with hmem | hmem
              · exact (not_lt_of_ge unitInterval.le_one' hmem.2).elim
              · exact hmem.1
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl xb =>
          rcases hab with (⟨ht, hxb⟩ | ⟨ht, hxb⟩)
          · subst ht
            subst hxb
            constructor
            · intro hmem
              simp only [mem_vertexOpenStarSource_inr, mem_vertexOpenStarSource_inl] at hmem ⊢
              rcases hmem with hmem | hmem
              · exact hmem.1
              · exact (not_lt_of_ge unitInterval.nonneg' hmem.2).elim
            · intro hmem
              simp only [mem_vertexOpenStarSource_inr, mem_vertexOpenStarSource_inl] at hmem ⊢
              exact Or.inl ⟨hmem, hleft j hmem⟩
          · subst ht
            subst hxb
            constructor
            · intro hmem
              simp only [mem_vertexOpenStarSource_inr, mem_vertexOpenStarSource_inl] at hmem ⊢
              rcases hmem with hmem | hmem
              · exact (not_lt_of_ge unitInterval.le_one' hmem.2).elim
              · exact hmem.1
            · intro hmem
              simp only [mem_vertexOpenStarSource_inr, mem_vertexOpenStarSource_inl] at hmem ⊢
              exact Or.inr ⟨hmem, hright j hmem⟩
      | inr jt' =>
          cases hab

/-- Helper for Definition 4.1.5: the open source star is saturated for the generated realization
setoid. -/
lemma vertexOpenStarSource_setoid_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → (0 : I) < left j)
    (hright : ∀ j, boundary j 1 = x → right j < (1 : I))
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationSetoid boundary a b) :
    a ∈ vertexOpenStarSource boundary x left right ↔
      b ∈ vertexOpenStarSource boundary x left right := by
  induction hab with
  | rel _ _ hrel =>
      exact vertexOpenStarSource_rel_iff boundary x left right hleft hright hrel
  | refl _ =>
      simp
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Definition 4.1.5: the quotient preimage of the open star is exactly its saturated
source model. -/
lemma vertexOpenStar_preimage (boundary : J ↪ Fin 2 → X₀) (x : X₀) (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → (0 : I) < left j)
    (hright : ∀ j, boundary j 1 = x → right j < (1 : I)) :
    (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹'
        vertexOpenStar boundary x left right =
      vertexOpenStarSource boundary x left right := by
  ext z
  constructor
  · rintro ⟨y, hy, hEq⟩
    have hsetoid : graphRealizationSetoid boundary y z := Quotient.eq'.1 hEq
    exact (vertexOpenStarSource_setoid_iff boundary x left right hleft hright hsetoid).1 hy
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Helper for Definition 4.1.5: the quotient open star is open whenever the source star reaches
the corresponding endpoints. -/
lemma vertexOpenStar_isOpen (boundary : J ↪ Fin 2 → X₀) (x : X₀) (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → (0 : I) < left j)
    (hright : ∀ j, boundary j 1 = x → right j < (1 : I)) :
    IsOpen (vertexOpenStar boundary x left right) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology J := ⟨rfl⟩
  exact (isQuotientMap_quotient_mk'.isOpen_preimage
    (s := vertexOpenStar boundary x left right)).1 <| by
      simpa using
        (vertexOpenStar_preimage boundary x left right hleft hright).symm ▸
          vertexOpenStarSource_isOpen boundary x left right

/-- Helper for Definition 4.1.5: the center vertex belongs to the quotient open star. -/
lemma graphVertex_mem_vertexOpenStar (boundary : J ↪ Fin 2 → X₀) (x : X₀) (left right : J → I) :
    graphVertex boundary x ∈ vertexOpenStar boundary x left right := by
  -- The quotient star always contains the source vertex representative.
  refine ⟨Sum.inl x, ?_, rfl⟩
  left
  rfl

/-- Helper for Definition 4.1.5: the quotient open star sits inside the corresponding closed
star once the closed star uses larger branch pieces. -/
lemma vertexOpenStar_subset_vertexClosedStar (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (leftOpen leftClosed rightClosed rightOpen : J → I)
    (hleft : ∀ j, boundary j 0 = x → leftOpen j < leftClosed j)
    (hright : ∀ j, boundary j 1 = x → rightClosed j < rightOpen j) :
    vertexOpenStar boundary x leftOpen rightOpen ⊆
      vertexClosedStar boundary x leftClosed rightClosed := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  rcases hz with rfl | ⟨j, t, rfl, hz⟩
  · left
    rfl
  · right
    rcases hz with hz | hz
    · refine mem_iUnion.2
        ⟨j, mem_iUnion.2 ⟨by simpa [mem_incidentEdges_iff] using Or.inl hz.1, ?_⟩⟩
      left
      exact ⟨t, hz.1, rfl, ⟨unitInterval.nonneg', le_of_lt (lt_trans hz.2 (hleft j hz.1))⟩⟩
    · refine mem_iUnion.2
        ⟨j, mem_iUnion.2 ⟨by simpa [mem_incidentEdges_iff] using Or.inr hz.1, ?_⟩⟩
      right
      exact ⟨t, hz.1, rfl, ⟨le_of_lt (lt_trans (hright j hz.1) hz.2), unitInterval.le_one'⟩⟩

/-- Helper for Definition 4.1.5: source-side containment descends to the quotient open star. -/
lemma vertexOpenStar_subset_of_sourceSubset (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) {U : Set (graphRealization boundary)}
    (hsub : vertexOpenStarSource boundary x left right ⊆
      (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹' U) :
    vertexOpenStar boundary x left right ⊆ U := by
  rintro _ ⟨z, hz, rfl⟩
  exact hsub hz

/-- Helper for Definition 4.1.5: source-side containment descends to the quotient closed star. -/
lemma vertexClosedStar_subset_of_sourceSubset (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) {U : Set (graphRealization boundary)}
    (hsub : vertexClosedStarSource boundary x left right ⊆
      (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹' U) :
    vertexClosedStar boundary x left right ⊆ U := by
  rintro _ ⟨z, hz, rfl⟩
  exact hsub hz

/-- Helper for Definition 4.1.5: the closed source star is closed in the disjoint source space. -/
lemma vertexClosedStarSource_isClosed (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    IsClosed (vertexClosedStarSource boundary x left right) := by
  classical
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := ⟨rfl⟩
  let _ : DiscreteTopology J := ⟨rfl⟩
  -- Work on the complement: each fiber is a union of basic open intervals in the unit interval.
  rw [← isOpen_compl_iff, isOpen_sum_iff]
  constructor
  · have hpre :
        Sum.inl ⁻¹' (vertexClosedStarSource boundary x left right)ᶜ = ({x} : Set X₀)ᶜ := by
      ext y
      simp [mem_vertexClosedStarSource_inl]
    rw [hpre]
    change @TopologicalSpace.IsOpen X₀ ⊥ ({x} : Set X₀)ᶜ
    simpa using isOpen_discrete (({x} : Set X₀)ᶜ)
  · change IsOpen {p : J × I | Sum.inr p ∈ (vertexClosedStarSource boundary x left right)ᶜ}
    rw [isOpen_iff_mem_nhds]
    rintro ⟨j, t⟩ ht
    have hnot : Sum.inr (j, t) ∉ vertexClosedStarSource boundary x left right := by
      simpa [mem_compl_iff] using ht
    have hsingle : IsOpen ({j} : Set J) := by
      change @TopologicalSpace.IsOpen J ⊥ ({j} : Set J)
      simpa using isOpen_discrete ({j} : Set J)
    by_cases h0 : boundary j 0 = x
    · by_cases h1 : boundary j 1 = x
      · have hlt : left j < t := by
          refine lt_of_not_ge ?_
          intro hle
          exact hnot <| (mem_vertexClosedStarSource_inr boundary x left right j t).2
            (Or.inl ⟨h0, hle⟩)
        have htr : t < right j := by
          refine lt_of_not_ge ?_
          intro hle
          exact hnot <| (mem_vertexClosedStarSource_inr boundary x left right j t).2
            (Or.inr ⟨h1, hle⟩)
        let V : Set (J × I) := ({j} : Set J) ×ˢ Set.Ioo (left j) (right j)
        have hVopen : IsOpen V := by
          simpa [V] using hsingle.prod isOpen_Ioo
        have hVmem : (j, t) ∈ V := by
          simp [V, hlt, htr]
        refine Filter.mem_of_superset (hVopen.mem_nhds hVmem) ?_
        · rintro ⟨j', t'⟩ hp
          rcases hp with ⟨hpj, hpt⟩
          have hj' : j' = j := by simpa using hpj
          cases hj'
          have hpnot : Sum.inr (j, t') ∉ vertexClosedStarSource boundary x left right := by
            intro hmem
            rcases (mem_vertexClosedStarSource_inr boundary x left right j t').1 hmem with
              hmem | hmem
            · exact (not_lt_of_ge hmem.2 hpt.1).elim
            · exact (not_lt_of_ge hmem.2 hpt.2).elim
          simpa [mem_compl_iff] using hpnot
      · have hlt : left j < t := by
          refine lt_of_not_ge ?_
          intro hle
          exact hnot <| (mem_vertexClosedStarSource_inr boundary x left right j t).2
            (Or.inl ⟨h0, hle⟩)
        let V : Set (J × I) := ({j} : Set J) ×ˢ Set.Ioi (left j)
        have hVopen : IsOpen V := by
          simpa [V] using hsingle.prod isOpen_Ioi
        have hVmem : (j, t) ∈ V := by
          simp [V, hlt]
        refine Filter.mem_of_superset (hVopen.mem_nhds hVmem) ?_
        · rintro ⟨j', t'⟩ hp
          rcases hp with ⟨hpj, hpt⟩
          have hj' : j' = j := by simpa using hpj
          cases hj'
          have hpnot : Sum.inr (j, t') ∉ vertexClosedStarSource boundary x left right := by
            intro hmem
            rcases (mem_vertexClosedStarSource_inr boundary x left right j t').1 hmem with
              hmem | hmem
            · exact (not_lt_of_ge hmem.2 hpt).elim
            · exact (h1 hmem.1).elim
          simpa [mem_compl_iff] using hpnot
    · by_cases h1 : boundary j 1 = x
      · have htr : t < right j := by
          refine lt_of_not_ge ?_
          intro hle
          exact hnot <| (mem_vertexClosedStarSource_inr boundary x left right j t).2
            (Or.inr ⟨h1, hle⟩)
        let V : Set (J × I) := ({j} : Set J) ×ˢ Set.Iio (right j)
        have hVopen : IsOpen V := by
          simpa [V] using hsingle.prod isOpen_Iio
        have hVmem : (j, t) ∈ V := by
          simp [V, htr]
        refine Filter.mem_of_superset (hVopen.mem_nhds hVmem) ?_
        · rintro ⟨j', t'⟩ hp
          rcases hp with ⟨hpj, hpt⟩
          have hj' : j' = j := by simpa using hpj
          cases hj'
          have hpnot : Sum.inr (j, t') ∉ vertexClosedStarSource boundary x left right := by
            intro hmem
            rcases (mem_vertexClosedStarSource_inr boundary x left right j t').1 hmem with
              hmem | hmem
            · exact (h0 hmem.1).elim
            · exact (not_lt_of_ge hmem.2 hpt).elim
          simpa [mem_compl_iff] using hpnot
      · let V : Set (J × I) := ({j} : Set J) ×ˢ (Set.univ : Set I)
        have hVopen : IsOpen V := by
          simpa [V] using hsingle.prod isOpen_univ
        have hVmem : (j, t) ∈ V := by
          simp [V]
        refine Filter.mem_of_superset (hVopen.mem_nhds hVmem) ?_
        · rintro ⟨j', t'⟩ hp
          rcases hp with ⟨hpj, _⟩
          have hj' : j' = j := by simpa using hpj
          cases hj'
          have hpnot : Sum.inr (j, t') ∉ vertexClosedStarSource boundary x left right := by
            intro hmem
            rcases (mem_vertexClosedStarSource_inr boundary x left right j t').1 hmem with
              hmem | hmem
            · exact (h0 hmem.1).elim
            · exact (h1 hmem.1).elim
          simpa [mem_compl_iff] using hpnot

/-- Helper for Definition 4.1.5: the closed source star is invariant under a single generating
endpoint identification once its branch parameters stop before the opposite vertex. -/
lemma vertexClosedStarSource_rel_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → left j < (1 : I))
    (hright : ∀ j, boundary j 1 = x → (0 : I) < right j)
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationRel boundary a b) :
    a ∈ vertexClosedStarSource boundary x left right ↔
      b ∈ vertexClosedStarSource boundary x left right := by
  cases a with
  | inl xa =>
      cases b with
      | inl xb =>
          cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with (⟨hxa, ht⟩ | ⟨hxa, ht⟩)
          · subst hxa
            subst ht
            constructor
            · intro hmem
              rw [mem_vertexClosedStarSource_inl] at hmem
              rw [mem_vertexClosedStarSource_inr]
              exact Or.inl ⟨hmem, unitInterval.nonneg'⟩
            · intro hmem
              rw [mem_vertexClosedStarSource_inl]
              rw [mem_vertexClosedStarSource_inr] at hmem
              rcases hmem with hmem | hmem
              · exact hmem.1
              · exact (not_le_of_gt (hright j hmem.1) hmem.2).elim
          · subst hxa
            subst ht
            constructor
            · intro hmem
              rw [mem_vertexClosedStarSource_inl] at hmem
              rw [mem_vertexClosedStarSource_inr]
              exact Or.inr ⟨hmem, unitInterval.le_one'⟩
            · intro hmem
              rw [mem_vertexClosedStarSource_inl]
              rw [mem_vertexClosedStarSource_inr] at hmem
              rcases hmem with hmem | hmem
              · exact (not_le_of_gt (hleft j hmem.1) hmem.2).elim
              · exact hmem.1
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl xb =>
          rcases hab with (⟨ht, hxb⟩ | ⟨ht, hxb⟩)
          · subst ht
            subst hxb
            constructor
            · intro hmem
              rw [mem_vertexClosedStarSource_inr] at hmem
              rw [mem_vertexClosedStarSource_inl]
              rcases hmem with hmem | hmem
              · exact hmem.1
              · exact (not_le_of_gt (hright j hmem.1) hmem.2).elim
            · intro hmem
              rw [mem_vertexClosedStarSource_inr]
              rw [mem_vertexClosedStarSource_inl] at hmem
              exact Or.inl ⟨hmem, unitInterval.nonneg'⟩
          · subst ht
            subst hxb
            constructor
            · intro hmem
              rw [mem_vertexClosedStarSource_inr] at hmem
              rw [mem_vertexClosedStarSource_inl]
              rcases hmem with hmem | hmem
              · exact (not_le_of_gt (hleft j hmem.1) hmem.2).elim
              · exact hmem.1
            · intro hmem
              rw [mem_vertexClosedStarSource_inr]
              rw [mem_vertexClosedStarSource_inl] at hmem
              exact Or.inr ⟨hmem, unitInterval.le_one'⟩
      | inr jt' =>
          cases hab

/-- Helper for Definition 4.1.5: the closed source star is saturated for the realization setoid
when its branches stop before the opposite endpoints. -/
lemma vertexClosedStarSource_setoid_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → left j < (1 : I))
    (hright : ∀ j, boundary j 1 = x → (0 : I) < right j)
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationSetoid boundary a b) :
    a ∈ vertexClosedStarSource boundary x left right ↔
      b ∈ vertexClosedStarSource boundary x left right := by
  induction hab with
  | rel _ _ hrel =>
      exact vertexClosedStarSource_rel_iff boundary x left right hleft hright hrel
  | refl _ =>
      simp
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Definition 4.1.5: the quotient preimage of the closed star is exactly its saturated
source model once the branches stop before the opposite endpoints. -/
lemma vertexClosedStar_preimage (boundary : J ↪ Fin 2 → X₀) (x : X₀) (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → left j < (1 : I))
    (hright : ∀ j, boundary j 1 = x → (0 : I) < right j) :
    (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹'
        vertexClosedStar boundary x left right =
      vertexClosedStarSource boundary x left right := by
  ext z
  constructor
  · rintro ⟨y, hy, hEq⟩
    have hsetoid : graphRealizationSetoid boundary y z := Quotient.eq'.1 hEq
    exact (vertexClosedStarSource_setoid_iff boundary x left right hleft hright hsetoid).1 hy
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Helper for Definition 4.1.5: the quotient closed star is closed once the source branches stop
before the opposite endpoints. -/
lemma vertexClosedStar_isClosed (boundary : J ↪ Fin 2 → X₀) (x : X₀) (left right : J → I)
    (hleft : ∀ j, boundary j 0 = x → left j < (1 : I))
    (hright : ∀ j, boundary j 1 = x → (0 : I) < right j) :
    IsClosed (vertexClosedStar boundary x left right) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  exact (isQuotientMap_quotient_mk'.isClosed_preimage
    (s := vertexClosedStar boundary x left right)).1 <| by
      simpa using
        (vertexClosedStar_preimage boundary x left right hleft hright).symm ▸
          vertexClosedStarSource_isClosed boundary x left right

/-- Helper for Definition 4.1.5: the source-side closed edge segment over `j` from `a` to `b`. -/
def edgeClosedSegmentSource (j : J) (a b : I) : Set (X₀ ⊕ (J × I)) :=
  Sum.inr '' (Prod.mk j '' Set.Icc a b)

/-- Helper for Definition 4.1.5: the quotient image of the closed edge segment over `j` from `a`
to `b`. -/
def edgeClosedSegment (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I) :
    Set (graphRealization boundary) :=
  (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ''
    edgeClosedSegmentSource (X₀ := X₀) j a b

/-- Helper for Definition 4.1.5: the source-side open edge segment over `j` from `a` to `b`. -/
def edgeOpenSegmentSource (j : J) (a b : I) : Set (X₀ ⊕ (J × I)) :=
  Sum.inr '' (Prod.mk j '' Set.Ioo a b)

/-- Helper for Definition 4.1.5: the quotient image of the open edge segment over `j` from `a`
to `b`. -/
def edgeOpenSegment (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I) :
    Set (graphRealization boundary) :=
  (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ''
    edgeOpenSegmentSource (X₀ := X₀) j a b

/-- Helper for Definition 4.1.5: closed source edge segments are compact. -/
lemma isCompact_edgeClosedSegmentSource (j : J) (a b : I) :
    IsCompact (edgeClosedSegmentSource (X₀ := X₀) j a b) := by
  -- Identify the source segment with the continuous image of the closed interval `Set.Icc a b`.
  have hset :
      edgeClosedSegmentSource (X₀ := X₀) j a b =
        (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) '' Set.Icc a b := by
    ext z
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
  rw [hset]
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hcont : Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
    simpa using (continuous_inr.comp (continuous_const.prodMk continuous_id))
  have hIcc : IsCompact (Set.Icc a b) := by
    -- The unit interval is a compact linear order, and closed intervals remain compact.
    exact isCompact_Icc
  simpa using hIcc.image hcont

/-- Helper for Definition 4.1.5: quotient closed edge segments are compact. -/
lemma edgeClosedSegmentCompact (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I) :
    IsCompact (edgeClosedSegment boundary j a b) := by
  let q : (X₀ ⊕ (J × I)) → graphRealization boundary :=
    @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hq : Continuous q := by
    simpa [q, graphRealization] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)))
  simpa [edgeClosedSegment, q] using
    (isCompact_edgeClosedSegmentSource (X₀ := X₀) j a b).image hq

/-- Helper for Definition 4.1.5: source-side open edge segments are open. -/
lemma edgeOpenSegmentSource_isOpen (j : J) (a b : I) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    IsOpen (edgeOpenSegmentSource (X₀ := X₀) j a b) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology J := ⟨rfl⟩
  have hEq :
      edgeOpenSegmentSource (X₀ := X₀) j a b =
        Sum.inr '' (({j} : Set J) ×ˢ Set.Ioo a b) := by
    ext z
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨(j, t), ⟨by simp, ht⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases y with ⟨j', t'⟩
      rcases hy with ⟨hyj, hyt⟩
      have hyj' : j' = j := by
        simpa using hyj
      cases hyj'
      exact ⟨(j, t'), ⟨t', hyt, rfl⟩, rfl⟩
  rw [hEq]
  have hsingle : IsOpen ({j} : Set J) := by
    change @TopologicalSpace.IsOpen J ⊥ ({j} : Set J)
    simpa using isOpen_discrete ({j} : Set J)
  exact isOpenMap_inr _ (hsingle.prod isOpen_Ioo)

/-- Helper for Definition 4.1.5: interior open edge segments are saturated for the realization
setoid. -/
lemma edgeOpenSegmentSource_setoid_iff (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I)
    (ha : (0 : I) < a) (hb : b < (1 : I))
    {z z' : X₀ ⊕ (J × I)} (hzz' : graphRealizationSetoid boundary z z') :
    z ∈ edgeOpenSegmentSource (X₀ := X₀) j a b ↔
      z' ∈ edgeOpenSegmentSource (X₀ := X₀) j a b := by
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    have ht₀ : t ≠ 0 := by
      exact (unitInterval.pos_iff_ne_zero).1 (lt_of_lt_of_le ha (le_of_lt ht.1))
    have ht₁ : t ≠ 1 := by
      exact (unitInterval.lt_one_iff_ne_one).1 (lt_of_le_of_lt (le_of_lt ht.2) hb)
    have hz' : z' = Sum.inr (j, t) :=
      graphRealizationSetoid_edgeInterior_fixed boundary j t ht₀ ht₁ hzz'
    subst hz'
    exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
  · intro hz'
    rcases hz' with ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    have ht₀ : t ≠ 0 := by
      exact (unitInterval.pos_iff_ne_zero).1 (lt_of_lt_of_le ha (le_of_lt ht.1))
    have ht₁ : t ≠ 1 := by
      exact (unitInterval.lt_one_iff_ne_one).1 (lt_of_le_of_lt (le_of_lt ht.2) hb)
    have hz : z = Sum.inr (j, t) :=
      graphRealizationSetoid_edgeInterior_fixed boundary j t ht₀ ht₁ hzz'.symm
    subst hz
    exact ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩

/-- Helper for Definition 4.1.5: the quotient preimage of an interior open edge segment is its
source model. -/
lemma edgeOpenSegment_preimage (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I)
    (ha : (0 : I) < a) (hb : b < (1 : I)) :
    (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹'
        edgeOpenSegment boundary j a b =
      edgeOpenSegmentSource (X₀ := X₀) j a b := by
  ext z
  constructor
  · rintro ⟨y, hy, hEq⟩
    have hsetoid : graphRealizationSetoid boundary y z := Quotient.eq'.1 hEq
    exact (edgeOpenSegmentSource_setoid_iff boundary j a b ha hb hsetoid).1 hy
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Helper for Definition 4.1.5: quotient interior edge segments are open. -/
lemma edgeOpenSegment_isOpen (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I)
    (ha : (0 : I) < a) (hb : b < (1 : I)) :
    IsOpen (edgeOpenSegment boundary j a b) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  exact (isQuotientMap_quotient_mk'.isOpen_preimage
    (s := edgeOpenSegment boundary j a b)).1 <| by
      simpa using
        (edgeOpenSegment_preimage boundary j a b ha hb).symm ▸
          edgeOpenSegmentSource_isOpen (X₀ := X₀) j a b

/-- Helper for Definition 4.1.5: interior edge points belong to the corresponding quotient open
segment. -/
lemma graphEdgePoint_mem_edgeOpenSegment (boundary : J ↪ Fin 2 → X₀) (j : J) {a t b : I}
    (hat : a < t) (htb : t < b) :
    graphEdgePoint boundary j t ∈ edgeOpenSegment boundary j a b := by
  refine ⟨(Sum.inr (j, t) : X₀ ⊕ (J × I)), ?_, rfl⟩
  exact ⟨(j, t), ⟨t, ⟨hat, htb⟩, rfl⟩, rfl⟩

/-- Helper for Definition 4.1.5: a realization point coming from `graphEdgePoint boundary j t`
lies in an open segment only on the same edge and with parameter in that interval. -/
lemma graphEdgePoint_mem_edgeOpenSegment_iff (boundary : J ↪ Fin 2 → X₀) {j j' : J} {t a b : I}
    (ha : (0 : I) < a) (hb : b < (1 : I)) :
    graphEdgePoint boundary j t ∈ edgeOpenSegment boundary j' a b ↔
      j = j' ∧ a < t ∧ t < b := by
  constructor
  · intro hmem
    have hpre :
        (Sum.inr (j, t) : X₀ ⊕ (J × I)) ∈
          (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹'
            edgeOpenSegment boundary j' a b := by
      simpa [graphEdgePoint, graphRealizationPoint] using hmem
    rw [edgeOpenSegment_preimage boundary j' a b ha hb] at hpre
    rcases hpre with ⟨y, hy, hEq⟩
    rcases hy with ⟨u, hu, hyEq⟩
    cases hEq
    cases hyEq
    exact ⟨rfl, hu.1, hu.2⟩
  · rintro ⟨rfl, hat, htb⟩
    exact graphEdgePoint_mem_edgeOpenSegment boundary j hat htb

/-- Helper for Definition 4.1.5: quotient open edge segments sit inside the corresponding closed
edge segments. -/
lemma edgeOpenSegment_subset_edgeClosedSegment (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I) :
    edgeOpenSegment boundary j a b ⊆ edgeClosedSegment boundary j a b := by
  rintro _ ⟨z, hz, rfl⟩
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨t, ht, rfl⟩
  exact ⟨(Sum.inr (j, t) : X₀ ⊕ (J × I)),
    ⟨(j, t), ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩, rfl⟩, rfl⟩

/-- Helper for Definition 4.1.5: source-side containment descends to quotient edge segments. -/
lemma edgeClosedSegment_subset_of_sourceSubset (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I)
    {U : Set (graphRealization boundary)}
    (hsub : edgeClosedSegmentSource (X₀ := X₀) j a b ⊆
      (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹' U) :
    edgeClosedSegment boundary j a b ⊆ U := by
  rintro _ ⟨z, hz, rfl⟩
  exact hsub hz

/-- Helper for Definition 4.1.5: a neighborhood of the initial endpoint of `j` contains both a
small open initial segment and a slightly larger closed initial segment. -/
lemma exists_initialBranchScalesWithin (j : J) {S : Set (X₀ ⊕ (J × I))}
    (hS : S ∈ 𝓝 (Sum.inr (j, (0 : I)))) :
    ∃ openRadius closedRadius : I,
      0 < openRadius ∧ openRadius < closedRadius ∧ closedRadius < 1 ∧
        ∀ {t : I}, t ≤ closedRadius → Sum.inr (j, t) ∈ S := by
  let e : I → X₀ ⊕ (J × I) := fun t ↦ Sum.inr (j, t)
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hpre : e ⁻¹' S ∈ 𝓝 (0 : I) := by
    simpa [e] using (continuous_inr.comp (continuous_const.prodMk continuous_id)).continuousAt hS
  obtain ⟨u, hu, huS⟩ := exists_Ico_subset_of_mem_nhds hpre ⟨(1 : I), zero_lt_one⟩
  obtain ⟨openRadius, hopen, hopenu⟩ := exists_between hu
  obtain ⟨closedRadius, hclosed, hclosedu⟩ := exists_between hopenu
  refine ⟨openRadius, closedRadius, hopen, hclosed,
    lt_of_lt_of_le hclosedu unitInterval.le_one', ?_⟩
  intro t ht
  exact huS ⟨unitInterval.nonneg', lt_of_le_of_lt ht hclosedu⟩

/-- Helper for Definition 4.1.5: a neighborhood of the terminal endpoint of `j` contains both a
small open terminal segment and a slightly larger closed terminal segment. -/
lemma exists_terminalBranchScalesWithin (j : J) {S : Set (X₀ ⊕ (J × I))}
    (hS : S ∈ 𝓝 (Sum.inr (j, (1 : I)))) :
    ∃ closedRadius openRadius : I,
      0 < closedRadius ∧ closedRadius < openRadius ∧ openRadius < 1 ∧
        ∀ {t : I}, closedRadius ≤ t → Sum.inr (j, t) ∈ S := by
  let e : I → X₀ ⊕ (J × I) := fun t ↦ Sum.inr (j, t)
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hpre : e ⁻¹' S ∈ 𝓝 (1 : I) := by
    simpa [e] using (continuous_inr.comp (continuous_const.prodMk continuous_id)).continuousAt hS
  obtain ⟨l, hl, hlS⟩ := exists_Ioc_subset_of_mem_nhds hpre ⟨(0 : I), zero_lt_one⟩
  obtain ⟨closedRadius, hlc, hcl⟩ := exists_between hl
  obtain ⟨openRadius, hco, hop⟩ := exists_between hcl
  refine ⟨closedRadius, openRadius, lt_of_le_of_lt unitInterval.nonneg' hlc, hco, hop, ?_⟩
  intro t ht
  exact hlS ⟨lt_of_lt_of_le hlc ht, unitInterval.le_one'⟩

/-- Helper for Definition 4.1.5: a neighborhood of an interior edge point contains a closed edge
segment around that point. -/
lemma exists_edgeClosedSegmentWithin (j : J) (t : I) {S : Set (X₀ ⊕ (J × I))}
    (hS : S ∈ 𝓝 (Sum.inr (j, t))) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    ∃ a b : I, 0 < a ∧ a < t ∧ t < b ∧ b < 1 ∧
      edgeClosedSegmentSource (X₀ := X₀) j a b ⊆ S := by
  let e : I → X₀ ⊕ (J × I) := fun u ↦ Sum.inr (j, u)
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hpre : e ⁻¹' S ∈ 𝓝 t := by
    simpa [e] using (continuous_inr.comp (continuous_const.prodMk continuous_id)).continuousAt hS
  obtain ⟨a₀, b₀, htmem, habS⟩ := (mem_nhds_iff_exists_Ioo_subset'
    ⟨(0 : I), (unitInterval.pos_iff_ne_zero).2 ht₀⟩
    ⟨(1 : I), (unitInterval.lt_one_iff_ne_one).2 ht₁⟩).1 hpre
  obtain ⟨a, ha₀a, hat⟩ := exists_between htmem.1
  obtain ⟨b, htb, hbb₀⟩ := exists_between htmem.2
  refine ⟨a, b, lt_of_le_of_lt unitInterval.nonneg' ha₀a, hat, htb,
    lt_of_lt_of_le hbb₀ unitInterval.le_one', ?_⟩
  rintro _ ⟨y, ⟨u, hu, rfl⟩, rfl⟩
  exact habS ⟨lt_of_lt_of_le ha₀a hu.1, lt_of_le_of_lt hu.2 hbb₀⟩

/-- Helper for Definition 4.1.5: a locally finite vertex has a compact closed-star neighborhood
inside every neighborhood of its realization point. -/
lemma vertexCompactNeighborhoodWithin (boundary : J ↪ Fin 2 → X₀) [LocallyFiniteGraph boundary]
    (x : X₀) {n : Set (graphRealization boundary)} (hn : n ∈ 𝓝 (graphVertex boundary x)) :
    ∃ K ∈ 𝓝 (graphVertex boundary x), K ⊆ n ∧ IsCompact K := by
  classical
  let q : (X₀ ⊕ (J × I)) → graphRealization boundary :=
    @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)
  -- First replace the ambient neighborhood by an open one so source-side transport is stable.
  rcases (nhds_basis_opens _).mem_iff.1 hn with ⟨W, ⟨hxW, hWopen⟩, hWsub⟩
  have hWnhds : W ∈ 𝓝 (graphVertex boundary x) := hWopen.mem_nhds hxW
  have hpreVertex : q ⁻¹' W ∈ 𝓝 (Sum.inl x) := by
    simpa [q, graphVertex, graphRealizationPoint] using
      (continuous_quotient_mk' : Continuous q).continuousAt hWnhds
  have hleftChoice :
      ∀ j, ∃ openRadius closedRadius : I,
        boundary j 0 = x →
          0 < openRadius ∧ openRadius < closedRadius ∧ closedRadius < 1 ∧
            ∀ {t : I}, t ≤ closedRadius → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j
    by_cases h0 : boundary j 0 = x
    · -- Endpoint neighborhoods at `0` produce the initial branch radii.
      have hEq0 : graphVertex boundary x = graphEdgePoint boundary j 0 := by
        simpa [h0] using graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j
      have hWedge : W ∈ 𝓝 (graphEdgePoint boundary j 0) := by
        simpa [hEq0] using hWnhds
      have hpreEdge : q ⁻¹' W ∈ 𝓝 (Sum.inr (j, (0 : I))) := by
        simpa [q, graphEdgePoint, graphRealizationPoint] using
          (continuous_quotient_mk' : Continuous q).continuousAt hWedge
      obtain ⟨openRadius, closedRadius, hopen, hlt, hclosed, hmem⟩ :=
        exists_initialBranchScalesWithin (X₀ := X₀) j hpreEdge
      exact ⟨openRadius, closedRadius, fun _ ↦ ⟨hopen, hlt, hclosed, fun ht ↦ hmem ht⟩⟩
    · exact ⟨0, 0, fun hEq ↦ (h0 hEq).elim⟩
  choose leftOpen leftClosed hleftWitness using hleftChoice
  have hrightChoice :
      ∀ j, ∃ closedRadius openRadius : I,
        boundary j 1 = x →
          0 < closedRadius ∧ closedRadius < openRadius ∧ openRadius < 1 ∧
            ∀ {t : I}, closedRadius ≤ t → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j
    by_cases h1 : boundary j 1 = x
    · -- Endpoint neighborhoods at `1` produce the terminal branch radii.
      have hEq1 : graphVertex boundary x = graphEdgePoint boundary j 1 := by
        simpa [h1] using graphVertex_boundary_one_eq_graphEdgePoint_one boundary j
      have hWedge : W ∈ 𝓝 (graphEdgePoint boundary j 1) := by
        simpa [hEq1] using hWnhds
      have hpreEdge : q ⁻¹' W ∈ 𝓝 (Sum.inr (j, (1 : I))) := by
        simpa [q, graphEdgePoint, graphRealizationPoint] using
          (continuous_quotient_mk' : Continuous q).continuousAt hWedge
      obtain ⟨closedRadius, openRadius, hclosedPos, hlt, hopen, hmem⟩ :=
        exists_terminalBranchScalesWithin (X₀ := X₀) j hpreEdge
      exact ⟨closedRadius, openRadius,
        fun _ ↦ ⟨hclosedPos, hlt, hopen, fun ht ↦ hmem ht⟩⟩
    · exact ⟨1, 1, fun hEq ↦ (h1 hEq).elim⟩
  choose rightClosed rightOpen hrightWitness using hrightChoice
  have hleftOpen :
      ∀ j, boundary j 0 = x → (0 : I) < leftOpen j := by
    intro j h0
    exact (hleftWitness j h0).1
  have hleftLt :
      ∀ j, boundary j 0 = x → leftOpen j < leftClosed j := by
    intro j h0
    exact (hleftWitness j h0).2.1
  have hleftMem :
      ∀ j, boundary j 0 = x → ∀ {t : I}, t ≤ leftClosed j → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j h0 t ht
    exact (hleftWitness j h0).2.2.2 ht
  have hrightLt :
      ∀ j, boundary j 1 = x → rightClosed j < rightOpen j := by
    intro j h1
    exact (hrightWitness j h1).2.1
  have hrightOpen :
      ∀ j, boundary j 1 = x → rightOpen j < (1 : I) := by
    intro j h1
    exact (hrightWitness j h1).2.2.1
  have hrightMem :
      ∀ j, boundary j 1 = x → ∀ {t : I}, rightClosed j ≤ t → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j h1 t ht
    exact (hrightWitness j h1).2.2.2 ht
  have hopenStar :
      IsOpen (vertexOpenStar boundary x leftOpen rightOpen) :=
    vertexOpenStar_isOpen boundary x leftOpen rightOpen hleftOpen hrightOpen
  have hmemOpenStar :
      graphVertex boundary x ∈ vertexOpenStar boundary x leftOpen rightOpen :=
    graphVertex_mem_vertexOpenStar boundary x leftOpen rightOpen
  have hopenStarNhds :
      vertexOpenStar boundary x leftOpen rightOpen ∈ 𝓝 (graphVertex boundary x) :=
    hopenStar.mem_nhds hmemOpenStar
  have hopenSubClosed :
      vertexOpenStar boundary x leftOpen rightOpen ⊆
        vertexClosedStar boundary x leftClosed rightClosed :=
    vertexOpenStar_subset_vertexClosedStar boundary x leftOpen leftClosed rightClosed rightOpen
      hleftLt hrightLt
  have hclosedSourceSub :
      vertexClosedStarSource boundary x leftClosed rightClosed ⊆ q ⁻¹' W := by
    intro z hz
    rcases hz with rfl | hz
    · simpa [q, graphVertex, graphRealizationPoint] using hxW
    · rcases mem_iUnion.1 hz with ⟨j, hz⟩
      rcases mem_iUnion.1 hz with ⟨hj, hz⟩
      rcases hz with hz | hz
      · rcases hz with ⟨t, h0, rfl, ht⟩
        exact hleftMem j h0 ht.2
      · rcases hz with ⟨t, h1, rfl, ht⟩
        exact hrightMem j h1 ht.1
  have hclosedSubW :
      vertexClosedStar boundary x leftClosed rightClosed ⊆ W :=
    vertexClosedStar_subset_of_sourceSubset boundary x leftClosed rightClosed hclosedSourceSub
  -- The closed star is compact and still a neighborhood because it contains the open star.
  refine ⟨vertexClosedStar boundary x leftClosed rightClosed,
    Filter.mem_of_superset hopenStarNhds hopenSubClosed, hclosedSubW.trans hWsub,
    vertexClosedStarCompact boundary x leftClosed rightClosed
      (LocallyFiniteGraph.finiteIncidentEdges (boundary := boundary) x)⟩

/-- Helper for Definition 4.1.5: an interior edge point has a compact closed-segment neighborhood
inside every neighborhood of its realization point. -/
lemma edgeInteriorCompactNeighborhoodWithin (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {n : Set (graphRealization boundary)}
    (hn : n ∈ 𝓝 (graphEdgePoint boundary j t)) :
    ∃ K ∈ 𝓝 (graphEdgePoint boundary j t), K ⊆ n ∧ IsCompact K := by
  let q : (X₀ ⊕ (J × I)) → graphRealization boundary :=
    @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)
  -- Replace the ambient neighborhood by an open one before transporting it to the source.
  rcases (nhds_basis_opens _).mem_iff.1 hn with ⟨W, ⟨htW, hWopen⟩, hWsub⟩
  have hWnhds : W ∈ 𝓝 (graphEdgePoint boundary j t) := hWopen.mem_nhds htW
  have hpre : q ⁻¹' W ∈ 𝓝 (Sum.inr (j, t)) := by
    simpa [q, graphEdgePoint, graphRealizationPoint] using
      (continuous_quotient_mk' : Continuous q).continuousAt hWnhds
  obtain ⟨a, b, ha, hat, htb, hb, hsegmentSub⟩ :=
    exists_edgeClosedSegmentWithin (X₀ := X₀) j t hpre ht₀ ht₁
  have hopenSegment : IsOpen (edgeOpenSegment boundary j a b) :=
    edgeOpenSegment_isOpen boundary j a b ha hb
  have hmemSegment : graphEdgePoint boundary j t ∈ edgeOpenSegment boundary j a b :=
    graphEdgePoint_mem_edgeOpenSegment boundary j hat htb
  have hopenNhds : edgeOpenSegment boundary j a b ∈ 𝓝 (graphEdgePoint boundary j t) :=
    hopenSegment.mem_nhds hmemSegment
  have hsegmentSubClosed :
      edgeOpenSegment boundary j a b ⊆ edgeClosedSegment boundary j a b :=
    edgeOpenSegment_subset_edgeClosedSegment boundary j a b
  have hclosedSubW : edgeClosedSegment boundary j a b ⊆ W :=
    edgeClosedSegment_subset_of_sourceSubset boundary j a b hsegmentSub
  -- The open segment gives the neighborhood filter, while the larger closed segment is compact.
  refine ⟨edgeClosedSegment boundary j a b,
    Filter.mem_of_superset hopenNhds hsegmentSubClosed, hclosedSubW.trans hWsub,
    edgeClosedSegmentCompact boundary j a b⟩

/-- Helper for Definition 4.1.5: a compact neighborhood of `graphVertex boundary x` contains a
compact closed star with an open star still centered at `x`. -/
lemma compactVertexClosedStarWithin (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {K : Set (graphRealization boundary)} (hKc : IsCompact K)
    (hKnhds : K ∈ 𝓝 (graphVertex boundary x)) :
    ∃ leftOpen leftClosed rightClosed rightOpen : J → I,
      (∀ j, boundary j 0 = x → (0 : I) < leftOpen j) ∧
      (∀ j, boundary j 0 = x → leftOpen j < leftClosed j) ∧
      (∀ j, boundary j 0 = x → leftClosed j < (1 : I)) ∧
      (∀ j, boundary j 1 = x → (0 : I) < rightClosed j) ∧
      (∀ j, boundary j 1 = x → rightClosed j < rightOpen j) ∧
      (∀ j, boundary j 1 = x → rightOpen j < (1 : I)) ∧
      (∀ j, boundary j 0 = x → boundary j 1 = x → leftOpen j < rightOpen j) ∧
      let U := vertexOpenStar boundary x leftOpen rightOpen
      let C := vertexClosedStar boundary x leftClosed rightClosed
      U ∈ 𝓝 (graphVertex boundary x) ∧ U ⊆ C ∧ C ⊆ K ∧ IsCompact C := by
  classical
  let q : (X₀ ⊕ (J × I)) → graphRealization boundary :=
    @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)
  -- Replace the compact neighborhood by an open neighborhood contained in it.
  rcases (nhds_basis_opens _).mem_iff.1 hKnhds with ⟨W, ⟨hxW, hWopen⟩, hWsub⟩
  have hWnhds : W ∈ 𝓝 (graphVertex boundary x) := hWopen.mem_nhds hxW
  have hleftChoice :
      ∀ j, ∃ openRadius closedRadius : I,
        boundary j 0 = x →
          0 < openRadius ∧ openRadius < closedRadius ∧ closedRadius < 1 ∧
            ∀ {t : I}, t ≤ closedRadius → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j
    by_cases h0 : boundary j 0 = x
    · -- Pull the vertex neighborhood back to the initial endpoint of the edge.
      have hEq0 : graphVertex boundary x = graphEdgePoint boundary j 0 := by
        simpa [h0] using graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j
      have hWedge : W ∈ 𝓝 (graphEdgePoint boundary j 0) := by
        simpa [hEq0] using hWnhds
      have hpreEdge : q ⁻¹' W ∈ 𝓝 (Sum.inr (j, (0 : I))) := by
        simpa [q, graphEdgePoint, graphRealizationPoint] using
          (continuous_quotient_mk' : Continuous q).continuousAt hWedge
      obtain ⟨openRadius, closedRadius, hopen, hlt, hclosed, hmem⟩ :=
        exists_initialBranchScalesWithin (X₀ := X₀) j hpreEdge
      exact ⟨openRadius, closedRadius, fun _ ↦ ⟨hopen, hlt, hclosed, fun ht ↦ hmem ht⟩⟩
    · exact ⟨0, 0, fun hEq ↦ (h0 hEq).elim⟩
  choose rawLeftOpen rawLeftClosed hleftWitness using hleftChoice
  have hrightChoice :
      ∀ j, ∃ closedRadius openRadius : I,
        boundary j 1 = x →
          0 < closedRadius ∧ closedRadius < openRadius ∧ openRadius < 1 ∧
            ∀ {t : I}, closedRadius ≤ t → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j
    by_cases h1 : boundary j 1 = x
    · -- Pull the same neighborhood back to the terminal endpoint of the edge.
      have hEq1 : graphVertex boundary x = graphEdgePoint boundary j 1 := by
        simpa [h1] using graphVertex_boundary_one_eq_graphEdgePoint_one boundary j
      have hWedge : W ∈ 𝓝 (graphEdgePoint boundary j 1) := by
        simpa [hEq1] using hWnhds
      have hpreEdge : q ⁻¹' W ∈ 𝓝 (Sum.inr (j, (1 : I))) := by
        simpa [q, graphEdgePoint, graphRealizationPoint] using
          (continuous_quotient_mk' : Continuous q).continuousAt hWedge
      obtain ⟨closedRadius, openRadius, hclosedPos, hlt, hopen, hmem⟩ :=
        exists_terminalBranchScalesWithin (X₀ := X₀) j hpreEdge
      exact ⟨closedRadius, openRadius,
        fun _ ↦ ⟨hclosedPos, hlt, hopen, fun ht ↦ hmem ht⟩⟩
    · exact ⟨1, 1, fun hEq ↦ (h1 hEq).elim⟩
  choose rightClosed rightOpen hrightWitness using hrightChoice
  have leftOpenChoice :
      ∀ j, ∃ openRadius : I,
        boundary j 0 = x →
          0 < openRadius ∧ openRadius < rawLeftClosed j ∧
            (boundary j 1 = x → openRadius < rightOpen j) := by
    intro j
    by_cases h0 : boundary j 0 = x
    · by_cases h1 : boundary j 1 = x
      · have hrawLeftPos : (0 : I) < rawLeftClosed j := by
          exact lt_trans (hleftWitness j h0).1 (hleftWitness j h0).2.1
        have hrightOpenPos : (0 : I) < rightOpen j := by
          exact lt_trans (hrightWitness j h1).1 (hrightWitness j h1).2.1
        by_cases hcmp : rawLeftClosed j < rightOpen j
        · obtain ⟨openRadius, hopen, hlt⟩ := exists_between hrawLeftPos
          exact ⟨openRadius, fun _ ↦ ⟨hopen, hlt, fun _ ↦ lt_trans hlt hcmp⟩⟩
        · have hle : rightOpen j ≤ rawLeftClosed j := le_of_not_gt hcmp
          obtain ⟨openRadius, hopen, hlt⟩ := exists_between hrightOpenPos
          exact ⟨openRadius, fun _ ↦ ⟨hopen, lt_of_lt_of_le hlt hle, fun _ ↦ hlt⟩⟩
      · exact ⟨rawLeftOpen j, fun _ ↦ ⟨(hleftWitness j h0).1, (hleftWitness j h0).2.1,
          fun hEq ↦ (h1 hEq).elim⟩⟩
    · exact ⟨0, fun hEq ↦ (h0 hEq).elim⟩
  choose leftOpen hleftOpenWitness using leftOpenChoice
  let leftClosed := rawLeftClosed
  have hleftOpen :
      ∀ j, boundary j 0 = x → (0 : I) < leftOpen j := by
    intro j h0
    exact (hleftOpenWitness j h0).1
  have hleftLt :
      ∀ j, boundary j 0 = x → leftOpen j < leftClosed j := by
    intro j h0
    exact (hleftOpenWitness j h0).2.1
  have hleftClosed :
      ∀ j, boundary j 0 = x → leftClosed j < (1 : I) := by
    intro j h0
    exact (hleftWitness j h0).2.2.1
  have hleftMem :
      ∀ j, boundary j 0 = x → ∀ {t : I}, t ≤ leftClosed j → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j h0 t ht
    exact (hleftWitness j h0).2.2.2 ht
  have hrightClosed :
      ∀ j, boundary j 1 = x → (0 : I) < rightClosed j := by
    intro j h1
    exact (hrightWitness j h1).1
  have hrightLt :
      ∀ j, boundary j 1 = x → rightClosed j < rightOpen j := by
    intro j h1
    exact (hrightWitness j h1).2.1
  have hrightOpen :
      ∀ j, boundary j 1 = x → rightOpen j < (1 : I) := by
    intro j h1
    exact (hrightWitness j h1).2.2.1
  have hrightMem :
      ∀ j, boundary j 1 = x → ∀ {t : I}, rightClosed j ≤ t → Sum.inr (j, t) ∈ q ⁻¹' W := by
    intro j h1 t ht
    exact (hrightWitness j h1).2.2.2 ht
  have hloopLt :
      ∀ j, boundary j 0 = x → boundary j 1 = x → leftOpen j < rightOpen j := by
    intro j h0 h1
    exact (hleftOpenWitness j h0).2.2 h1
  let U := vertexOpenStar boundary x leftOpen rightOpen
  let C := vertexClosedStar boundary x leftClosed rightClosed
  -- The open star still gives a neighborhood of the vertex.
  have hUopen : IsOpen U := by
    simpa [U] using vertexOpenStar_isOpen boundary x leftOpen rightOpen hleftOpen hrightOpen
  have hUmem : graphVertex boundary x ∈ U := by
    simpa [U] using graphVertex_mem_vertexOpenStar boundary x leftOpen rightOpen
  have hUnhds : U ∈ 𝓝 (graphVertex boundary x) := hUopen.mem_nhds hUmem
  have hUSubC : U ⊆ C := by
    simpa [U, C] using
      vertexOpenStar_subset_vertexClosedStar boundary x leftOpen leftClosed rightClosed rightOpen
        hleftLt hrightLt
  have hCSourceSub :
      vertexClosedStarSource boundary x leftClosed rightClosed ⊆ q ⁻¹' W := by
    intro z hz
    rcases hz with rfl | hz
    · simpa [q, graphVertex, graphRealizationPoint] using hxW
    · rcases mem_iUnion.1 hz with ⟨j, hz⟩
      rcases mem_iUnion.1 hz with ⟨_, hz⟩
      rcases hz with hz | hz
      · rcases hz with ⟨t, h0, rfl, ht⟩
        exact hleftMem j h0 ht.2
      · rcases hz with ⟨t, h1, rfl, ht⟩
        exact hrightMem j h1 ht.1
  have hCSubK : C ⊆ K := by
    have hCSubW : C ⊆ W := by
      simpa [C] using
        vertexClosedStar_subset_of_sourceSubset boundary x leftClosed rightClosed hCSourceSub
    exact hCSubW.trans hWsub
  have hCc : IsCompact C := by
    -- Closedness comes from the saturated source model, then compactness is inherited from `K`.
    refine IsCompact.of_isClosed_subset hKc ?_ hCSubK
    simpa [C] using
      vertexClosedStar_isClosed boundary x leftClosed rightClosed hleftClosed hrightClosed
  refine ⟨leftOpen, leftClosed, rightClosed, rightOpen, hleftOpen, hleftLt, hleftClosed,
    hrightClosed, hrightLt, hrightOpen, hloopLt, ?_⟩
  exact ⟨hUnhds, hUSubC, hCSubK, hCc⟩

/-- A locally finite graph realization is locally compact. -/
instance locallyFiniteGraph_locallyCompactSpace (boundary : J ↪ Fin 2 → X₀)
    [h : LocallyFiniteGraph boundary] : LocallyCompactSpace (graphRealization boundary) := by
  refine ⟨?_⟩
  intro y n hn
  obtain ⟨z, rfl⟩ := Quotient.exists_rep y
  cases z with
  | inl x =>
      -- Vertex representatives use the closed-star witness built from endpoint neighborhoods.
      simpa [graphVertex, graphRealizationPoint] using
        vertexCompactNeighborhoodWithin (boundary := boundary) x hn
  | inr jt =>
      rcases jt with ⟨j, t⟩
      rcases eq_or_ne t 0 with rfl | ht₀
      · -- Route correction: the endpoint case should reuse the vertex witness, not unfold a new
        -- interval argument at `t = 0`.
        have hvertex : n ∈ 𝓝 (graphVertex boundary (boundary j 0)) := by
          simpa [graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j] using hn
        simpa [graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j] using
          vertexCompactNeighborhoodWithin (boundary := boundary) (boundary j 0) hvertex
      · rcases eq_or_ne t 1 with rfl | ht₁
        · -- The terminal endpoint reduces to the corresponding vertex in the same way.
          have hvertex : n ∈ 𝓝 (graphVertex boundary (boundary j 1)) := by
            simpa [graphVertex_boundary_one_eq_graphEdgePoint_one boundary j] using hn
          simpa [graphVertex_boundary_one_eq_graphEdgePoint_one boundary j] using
            vertexCompactNeighborhoodWithin (boundary := boundary) (boundary j 1) hvertex
        · -- Genuine edge interiors use the compact closed-segment witness.
          simpa [graphEdgePoint, graphRealizationPoint] using
            edgeInteriorCompactNeighborhoodWithin boundary j t ht₀ ht₁ hn

/-- Definition 4.1.5. A compact neighborhood of `graphVertex boundary x` forces only finitely
many incident edges at `x`. -/
lemma finiteIncidentEdges_of_compactVertexNeighborhood (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {K : Set (graphRealization boundary)} (hKc : IsCompact K)
    (hKnhds : K ∈ 𝓝 (graphVertex boundary x)) :
    (incidentEdges boundary x).Finite := by
  classical
  obtain ⟨leftOpen, leftClosed, rightClosed, rightOpen, hleftOpen, hleftLt, hleftClosed,
    hrightClosed, hrightLt, hrightOpen, hloopLt, hstar⟩ :=
      compactVertexClosedStarWithin boundary x hKc hKnhds
  let U := vertexOpenStar boundary x leftOpen rightOpen
  let C := vertexClosedStar boundary x leftClosed rightClosed
  have hstar' : U ∈ 𝓝 (graphVertex boundary x) ∧ U ⊆ C ∧ C ⊆ K ∧ IsCompact C := by
    simpa [U, C] using hstar
  rcases hstar' with ⟨hUnhds, hUSubC, hCSubK, hCc⟩
  -- Choose one slightly larger open shell around each initial and terminal closed branch.
  have hInitialChoice :
      ∀ j, ∃ a b : I,
        boundary j 0 = x →
          (0 : I) < a ∧ a < leftOpen j ∧ leftClosed j < b ∧ b < (1 : I) := by
    intro j
    by_cases h0 : boundary j 0 = x
    · obtain ⟨a, ha0, haleft⟩ := exists_between (hleftOpen j h0)
      obtain ⟨b, hclosedb, hb1⟩ := exists_between (hleftClosed j h0)
      exact ⟨a, b, fun _ ↦ ⟨ha0, haleft, hclosedb, hb1⟩⟩
    · exact ⟨0, 1, fun hEq ↦ (h0 hEq).elim⟩
  choose initialLower initialUpper hInitialShell using hInitialChoice
  have hTerminalChoice :
      ∀ j, ∃ a b : I,
        boundary j 1 = x →
          (0 : I) < a ∧ a < rightClosed j ∧ rightOpen j < b ∧ b < (1 : I) := by
    intro j
    by_cases h1 : boundary j 1 = x
    · obtain ⟨a, ha0, haright⟩ := exists_between (hrightClosed j h1)
      obtain ⟨b, hopenb, hb1⟩ := exists_between (hrightOpen j h1)
      exact ⟨a, b, fun _ ↦ ⟨ha0, haright, hopenb, hb1⟩⟩
    · exact ⟨0, 1, fun hEq ↦ (h1 hEq).elim⟩
  choose terminalLower terminalUpper hTerminalShell using hTerminalChoice
  let shellIndex : Set (Fin 2 × J) :=
    {ij | (ij.1 = 0 ∧ boundary ij.2 0 = x) ∨ (ij.1 = 1 ∧ boundary ij.2 1 = x)}
  let shellSet : Fin 2 × J → Set (graphRealization boundary)
    | (0, j) => edgeOpenSegment boundary j (initialLower j) (initialUpper j)
    | (1, j) => edgeOpenSegment boundary j (terminalLower j) (terminalUpper j)
  have hUopen : IsOpen U := by
    simpa [U] using vertexOpenStar_isOpen boundary x leftOpen rightOpen hleftOpen hrightOpen
  have hcompactDiff : IsCompact (C \ U) := hCc.diff hUopen
  have hshellOpen : ∀ i ∈ shellIndex, IsOpen (shellSet i) := by
    intro i hi
    rcases i with ⟨k, j⟩
    rcases hi with hi | hi
    · rcases hi with ⟨hk, h0⟩
      subst hk
      simpa [shellSet] using
        edgeOpenSegment_isOpen boundary j (initialLower j) (initialUpper j)
          (hInitialShell j h0).1 (hInitialShell j h0).2.2.2
    · rcases hi with ⟨hk, h1⟩
      subst hk
      simpa [shellSet] using
        edgeOpenSegment_isOpen boundary j (terminalLower j) (terminalUpper j)
          (hTerminalShell j h1).1 (hTerminalShell j h1).2.2.2
  have hcover : C \ U ⊆ ⋃ i ∈ shellIndex, shellSet i := by
    intro y hy
    rcases hy with ⟨hyC, hyU⟩
    rcases hyC with ⟨z, hzC, rfl⟩
    have hzNotU : z ∉ vertexOpenStarSource boundary x leftOpen rightOpen := by
      intro hzU
      exact hyU ⟨z, hzU, rfl⟩
    rcases z with z | ⟨j, t⟩
    · have hzEq : z = x := by
        exact (mem_vertexClosedStarSource_inl boundary x z leftClosed rightClosed).1 hzC
      subst hzEq
      exact (hzNotU (by left; rfl)).elim
    · rcases (mem_vertexClosedStarSource_inr boundary x leftClosed rightClosed j t).1 hzC with
        hz0 | hz1
      · have htLeft : leftOpen j ≤ t := by
          refine le_of_not_gt ?_
          intro ht
          exact hzNotU <|
            (mem_vertexOpenStarSource_inr boundary x leftOpen rightOpen j t).2
              (Or.inl ⟨hz0.1, ht⟩)
        refine mem_iUnion.2 ⟨(0, j), mem_iUnion.2 ?_⟩
        refine ⟨Or.inl ⟨rfl, hz0.1⟩, ?_⟩
        have hlt : initialLower j < t := lt_of_lt_of_le (hInitialShell j hz0.1).2.1 htLeft
        have hgt : t < initialUpper j := lt_of_le_of_lt hz0.2 (hInitialShell j hz0.1).2.2.1
        simpa [shellSet] using graphEdgePoint_mem_edgeOpenSegment boundary j hlt hgt
      · have htRight : t ≤ rightOpen j := by
          refine le_of_not_gt ?_
          intro ht
          exact hzNotU <|
            (mem_vertexOpenStarSource_inr boundary x leftOpen rightOpen j t).2
              (Or.inr ⟨hz1.1, ht⟩)
        refine mem_iUnion.2 ⟨(1, j), mem_iUnion.2 ?_⟩
        refine ⟨Or.inr ⟨rfl, hz1.1⟩, ?_⟩
        have hlt : terminalLower j < t := lt_of_lt_of_le (hTerminalShell j hz1.1).2.1 hz1.2
        have hgt : t < terminalUpper j := lt_of_le_of_lt htRight (hTerminalShell j hz1.1).2.2.1
        simpa [shellSet] using graphEdgePoint_mem_edgeOpenSegment boundary j hlt hgt
  obtain ⟨coverIndex, hcoverIndexSub, hcoverIndexFinite, hfiniteCover⟩ :=
    hcompactDiff.elim_finite_subcover_image (b := shellIndex) (c := shellSet) hshellOpen hcover
  have mem_openStar_edgePoint_iff (j : J) (t : I) :
      graphEdgePoint boundary j t ∈ U ↔
        ((boundary j 0 = x ∧ t < leftOpen j) ∨ (boundary j 1 = x ∧ rightOpen j < t)) := by
    constructor
    · intro hmem
      have hpre :
          (Sum.inr (j, t) : X₀ ⊕ (J × I)) ∈
            (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹' U := by
        simpa [U, graphEdgePoint, graphRealizationPoint] using hmem
      rw [vertexOpenStar_preimage boundary x leftOpen rightOpen hleftOpen hrightOpen] at hpre
      simpa [mem_vertexOpenStarSource_inr] using hpre
    · intro hmem
      have hpre :
          (Sum.inr (j, t) : X₀ ⊕ (J × I)) ∈
            (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹' U := by
        rw [vertexOpenStar_preimage boundary x leftOpen rightOpen hleftOpen hrightOpen]
        simpa [mem_vertexOpenStarSource_inr] using hmem
      simpa [U, graphEdgePoint, graphRealizationPoint] using hpre
  have witness_mem_coverIndex {j : J} {t : I}
      (hwitness : graphEdgePoint boundary j t ∈ C \ U) :
      j ∈ Prod.snd '' coverIndex := by
    have hwitnessCover := hfiniteCover hwitness
    rcases mem_iUnion.1 hwitnessCover with ⟨i, hwitnessCover⟩
    rcases mem_iUnion.1 hwitnessCover with ⟨hi, hiMem⟩
    rcases i with ⟨k, j'⟩
    have hiShell : (k, j') ∈ shellIndex := hcoverIndexSub hi
    have hjEq : j = j' := by
      rcases hiShell with hiShell | hiShell
      · rcases hiShell with ⟨hk, h0'⟩
        subst hk
        exact (graphEdgePoint_mem_edgeOpenSegment_iff boundary
          (hInitialShell j' h0').1 (hInitialShell j' h0').2.2.2).1 hiMem |>.1
      · rcases hiShell with ⟨hk, h1'⟩
        subst hk
        exact (graphEdgePoint_mem_edgeOpenSegment_iff boundary
          (hTerminalShell j' h1').1 (hTerminalShell j' h1').2.2.2).1 hiMem |>.1
    exact ⟨(k, j'), hi, by simp [hjEq]⟩
  -- Each incident edge contributes a witness in `C \ U`, so the finite shell cover projects to
  -- a finite set of incident edge indices.
  have hincidentSubset : incidentEdges boundary x ⊆ Prod.snd '' coverIndex := by
    intro j hj
    by_cases h0 : boundary j 0 = x
    · by_cases h1 : boundary j 1 = x
      · obtain ⟨t, hleftt, htmin⟩ :=
          exists_between (lt_min (hleftLt j h0) (hloopLt j h0 h1))
        have htClosed : t < leftClosed j := lt_of_lt_of_le htmin (min_le_left _ _)
        have htOpen : t < rightOpen j := lt_of_lt_of_le htmin (min_le_right _ _)
        have hwitness : graphEdgePoint boundary j t ∈ C \ U := by
          refine ⟨?_, ?_⟩
          · refine ⟨Sum.inr (j, t), ?_, rfl⟩
            rw [mem_vertexClosedStarSource_inr]
            exact Or.inl ⟨h0, le_of_lt htClosed⟩
          · intro hmem
            rcases (mem_openStar_edgePoint_iff j t).1 hmem with hmem | hmem
            · exact (not_lt_of_ge (le_of_lt hleftt) hmem.2).elim
            · exact (not_lt_of_ge (le_of_lt htOpen) hmem.2).elim
        exact witness_mem_coverIndex hwitness
      · obtain ⟨t, hleftt, htClosed⟩ := exists_between (hleftLt j h0)
        have hwitness : graphEdgePoint boundary j t ∈ C \ U := by
          refine ⟨?_, ?_⟩
          · refine ⟨Sum.inr (j, t), ?_, rfl⟩
            rw [mem_vertexClosedStarSource_inr]
            exact Or.inl ⟨h0, le_of_lt htClosed⟩
          · intro hmem
            rcases (mem_openStar_edgePoint_iff j t).1 hmem with hmem | hmem
            · exact (not_lt_of_ge (le_of_lt hleftt) hmem.2).elim
            · exact (h1 hmem.1).elim
        exact witness_mem_coverIndex hwitness
    · have h1 : boundary j 1 = x := by
        rcases (mem_incidentEdges_iff boundary x j).1 hj with h0' | h1
        · exact (h0 h0').elim
        · exact h1
      obtain ⟨t, hrightt, htOpen⟩ := exists_between (hrightLt j h1)
      have hwitness : graphEdgePoint boundary j t ∈ C \ U := by
        refine ⟨?_, ?_⟩
        · refine ⟨Sum.inr (j, t), ?_, rfl⟩
          rw [mem_vertexClosedStarSource_inr]
          exact Or.inr ⟨h1, le_of_lt hrightt⟩
        · intro hmem
          rcases (mem_openStar_edgePoint_iff j t).1 hmem with hmem | hmem
          · exact (h0 hmem.1).elim
          · exact (not_lt_of_ge (le_of_lt htOpen) hmem.2).elim
      exact witness_mem_coverIndex hwitness
  exact (hcoverIndexFinite.image Prod.snd).subset hincidentSubset

/-- Conversely, local compactness of the graph realization recovers local finiteness of the
underlying graph. -/
instance locallyCompactSpace_locallyFiniteGraph (boundary : J ↪ Fin 2 → X₀)
    [LocallyCompactSpace (graphRealization boundary)] : LocallyFiniteGraph boundary := by
  refine ⟨?_⟩
  intro x
  -- Pull local compactness back to a compact vertex neighborhood and then apply the shell-cover
  -- finiteness criterion.
  obtain ⟨K, hKc, hKnhds⟩ : ∃ K : Set (graphRealization boundary), IsCompact K ∧
      K ∈ 𝓝 (graphVertex boundary x) := exists_compact_mem_nhds (graphVertex boundary x)
  exact finiteIncidentEdges_of_compactVertexNeighborhood boundary x hKc hKnhds

/-- Local finiteness of a graph realization is equivalent to local compactness. -/
theorem locallyFiniteGraph_iff_locallyCompactSpace (boundary : J ↪ Fin 2 → X₀) :
    LocallyFiniteGraph boundary ↔ LocallyCompactSpace (graphRealization boundary) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
