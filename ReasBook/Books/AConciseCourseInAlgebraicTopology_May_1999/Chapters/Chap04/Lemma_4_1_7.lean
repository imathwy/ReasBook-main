import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Analysis.Convex.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4.FiniteGraph

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval
open Set Filter Topology

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall: `StronglyLocallyContractibleSpace` is the canonical owner here, and
-- `StronglyLocallyContractibleSpace.locallyContractible` is the source-facing bridge.

/-- Helper for Lemma 4.1.7: the source disjoint union carries the chapter's intended discrete
topologies on `X₀` and `J` together with the usual topology on `I`. -/
abbrev graphRealizationSourceFaithfulSourceTopologicalSpace :
    TopologicalSpace (X₀ ⊕ (J × I)) :=
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  inferInstance

/-- Helper for Lemma 4.1.7: within this item, the canonical topology on
`graphRealization boundary` is the source-faithful quotient topology coming from discrete
vertices and edges together with the usual topology on `I`. -/
-- `Definition_4_1_2` still exports the legacy quotient topology induced from indiscrete `X₀`
-- and `J`.
-- Local instance justification (noncanonical choice): this item uses the source-faithful model.
local instance graphRealization_sourceFaithfulTopologicalSpace
    (boundary : J ↪ Fin 2 → X₀) : TopologicalSpace (graphRealization boundary) :=
  graphRealizationSourceFaithfulTopologicalSpace boundary

/-- Helper for Lemma 4.1.7: the source star around a vertex consists of that vertex together
with the chosen initial and terminal edge segments incident to it. -/
def graphVertexStarSource (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I) :
    Set (X₀ ⊕ (J × I)) :=
  {z | z = Sum.inl x ∨ ∃ j t, z = Sum.inr (j, t) ∧
      ((boundary j 0 = x ∧ t < ρ₀ j) ∨ (boundary j 1 = x ∧ ρ₁ j < t))}

/-- Helper for Lemma 4.1.7: the source star contains exactly the distinguished vertex on the
vertex summand. -/
@[simp]
theorem mem_graphVertexStarSource_inl (boundary : J ↪ Fin 2 → X₀) (x y : X₀) (ρ₀ ρ₁ : J → I) :
    Sum.inl y ∈ graphVertexStarSource boundary x ρ₀ ρ₁ ↔ y = x := by
  constructor
  · intro hy
    rcases hy with h | ⟨j, t, hz, _⟩
    · simpa using h
    · cases hz
  · intro hy
    left
    simp [hy]

/-- Helper for Lemma 4.1.7: on the edge summand, the source star is exactly the union of the
chosen one-sided incident edge segments. -/
@[simp]
theorem mem_graphVertexStarSource_inr (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (j : J) (t : I) :
    Sum.inr (j, t) ∈ graphVertexStarSource boundary x ρ₀ ρ₁ ↔
      ((boundary j 0 = x ∧ t < ρ₀ j) ∨ (boundary j 1 = x ∧ ρ₁ j < t)) := by
  constructor
  · intro hz
    rcases hz with h | ⟨j', t', hz, hmem⟩
    · cases h
    · cases hz
      simpa using hmem
  · intro hz
    right
    exact ⟨j, t, rfl, hz⟩

/-- Helper for Lemma 4.1.7: sufficiently short incident edge segments give an open star in the
source disjoint union. -/
theorem graphVertexStarSource_isOpen (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    IsOpen (graphVertexStarSource boundary x ρ₀ ρ₁) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  rw [isOpen_sum_iff]
  constructor
  · -- On the vertex summand, the star is the singleton `{x}`.
    change IsOpen {y : X₀ | y = x}
    simpa using (@isOpen_discrete X₀ ⊥ (discreteTopology_bot X₀) ({x} : Set X₀))
  · -- On the edge summand, the star is a union of open product rectangles over the incident edges.
    change IsOpen {p : J × I | Sum.inr p ∈ graphVertexStarSource boundary x ρ₀ ρ₁}
    let leftBranches : Set (J × I) :=
      ⋃ j ∈ {j : J | boundary j 0 = x}, ({j} : Set J) ×ˢ Set.Iio (ρ₀ j)
    let rightBranches : Set (J × I) :=
      ⋃ j ∈ {j : J | boundary j 1 = x}, ({j} : Set J) ×ˢ Set.Ioi (ρ₁ j)
    have hleftOpen : IsOpen leftBranches := by
      refine isOpen_biUnion fun j _ ↦ ?_
      exact (@isOpen_discrete J ⊥ (discreteTopology_bot J) ({j} : Set J)).prod isOpen_Iio
    have hrightOpen : IsOpen rightBranches := by
      refine isOpen_biUnion fun j _ ↦ ?_
      exact (@isOpen_discrete J ⊥ (discreteTopology_bot J) ({j} : Set J)).prod isOpen_Ioi
    have hleftEq :
        {p : J × I | boundary p.1 0 = x ∧ p.2 < ρ₀ p.1} = leftBranches := by
      ext p
      simp [leftBranches]
    have hrightEq :
        {p : J × I | boundary p.1 1 = x ∧ ρ₁ p.1 < p.2} = rightBranches := by
      ext p
      simp [rightBranches]
    have hdecomp :
        {p : J × I | Sum.inr p ∈ graphVertexStarSource boundary x ρ₀ ρ₁} =
          {p : J × I | boundary p.1 0 = x ∧ p.2 < ρ₀ p.1} ∪
            {p : J × I | boundary p.1 1 = x ∧ ρ₁ p.1 < p.2} := by
      ext p
      simpa [Prod.mk.eta] using
        (mem_graphVertexStarSource_inr boundary x ρ₀ ρ₁ p.1 p.2)
    rw [hdecomp, hleftEq, hrightEq]
    exact hleftOpen.union hrightOpen

/-- Helper for Lemma 4.1.7: the source star is invariant under a single generating endpoint
identification. -/
theorem graphVertexStarSource_rel_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I))
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationRel boundary a b) :
    a ∈ graphVertexStarSource boundary x ρ₀ ρ₁ ↔
      b ∈ graphVertexStarSource boundary x ρ₀ ρ₁ := by
  cases a with
  | inl xa =>
      cases b with
      | inl xb =>
          cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with (⟨hxa, ht⟩ | ⟨hxa, ht⟩)
          · subst xa
            subst t
            constructor
            · -- The initial endpoint enters the edge segment because `ρ₀ j` is positive.
              intro ha
              rw [mem_graphVertexStarSource_inl] at ha
              rw [mem_graphVertexStarSource_inr]
              exact Or.inl ⟨ha, hρ₀ j ha⟩
            · -- Membership at the endpoint forces the corresponding incident-vertex case.
              intro hb
              rw [mem_graphVertexStarSource_inl]
              rw [mem_graphVertexStarSource_inr] at hb
              rcases hb with h0 | h1
              · exact h0.1
              · exact False.elim ((not_lt_of_ge (ρ₁ j).2.1) h1.2)
          · subst xa
            subst t
            constructor
            · -- The terminal endpoint enters the edge segment because `ρ₁ j` lies below `1`.
              intro ha
              rw [mem_graphVertexStarSource_inl] at ha
              rw [mem_graphVertexStarSource_inr]
              exact Or.inr ⟨ha, hρ₁ j ha⟩
            · -- At `t = 1`, only the terminal-incident branch can occur.
              intro hb
              rw [mem_graphVertexStarSource_inl]
              rw [mem_graphVertexStarSource_inr] at hb
              rcases hb with h0 | h1
              · exact False.elim ((not_lt_of_ge (ρ₀ j).2.2) h0.2)
              · exact h1.1
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl xb =>
          rcases hab with (⟨ht, hxb⟩ | ⟨ht, hxb⟩)
          · subst t
            subst xb
            constructor
            · -- At `t = 0`, only the initial-incident branch can occur.
              intro ha
              rw [mem_graphVertexStarSource_inr] at ha
              rw [mem_graphVertexStarSource_inl]
              rcases ha with h0 | h1
              · exact h0.1
              · exact False.elim ((not_lt_of_ge (ρ₁ j).2.1) h1.2)
            · -- The vertex representative maps back to the endpoint using positivity of `ρ₀ j`.
              intro hb
              rw [mem_graphVertexStarSource_inl] at hb
              rw [mem_graphVertexStarSource_inr]
              exact Or.inl ⟨hb, hρ₀ j hb⟩
          · subst t
            subst xb
            constructor
            · -- At `t = 1`, only the terminal-incident branch can occur.
              intro ha
              rw [mem_graphVertexStarSource_inr] at ha
              rw [mem_graphVertexStarSource_inl]
              rcases ha with h0 | h1
              · exact False.elim ((not_lt_of_ge (ρ₀ j).2.2) h0.2)
              · exact h1.1
            · -- The vertex representative maps back to the endpoint using `ρ₁ j < 1`.
              intro hb
              rw [mem_graphVertexStarSource_inl] at hb
              rw [mem_graphVertexStarSource_inr]
              exact Or.inr ⟨hb, hρ₁ j hb⟩
      | inr jt' =>
          cases hab

/-- Helper for Lemma 4.1.7: the source star is saturated for the quotient relation generated by
the endpoint identifications. -/
theorem graphVertexStarSource_setoid_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I))
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationSetoid boundary a b) :
    a ∈ graphVertexStarSource boundary x ρ₀ ρ₁ ↔
      b ∈ graphVertexStarSource boundary x ρ₀ ρ₁ := by
  -- Extend the endpoint-invariance check from generators to the full equivalence closure.
  induction hab with
  | rel _ _ hrel =>
      exact graphVertexStarSource_rel_iff boundary x ρ₀ ρ₁ hρ₀ hρ₁ hrel
  | refl a =>
      simp
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Lemma 4.1.7: the quotient image of the source star is the corresponding vertex
star neighborhood in the realization. -/
def graphVertexStar (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I) :
    Set (graphRealization boundary) :=
  graphRealizationPoint boundary '' graphVertexStarSource boundary x ρ₀ ρ₁

/-- Helper for Lemma 4.1.7: the vertex star viewed inside the graph realization equipped with the
source-faithful quotient topology. -/
abbrev graphVertexStarSet (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I) :
    Set (graphRealization boundary) :=
  graphVertexStar boundary x ρ₀ ρ₁

/-- Helper for Lemma 4.1.7: the quotient preimage of the vertex star is the saturated source
star used to define it. -/
theorem graphVertexStar_preimage (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) :
    graphRealizationPoint boundary ⁻¹' graphVertexStar boundary x ρ₀ ρ₁ =
      graphVertexStarSource boundary x ρ₀ ρ₁ := by
  ext z
  constructor
  · -- Any representative of a quotient point in the star is related to a source-star point.
    intro hz
    rw [graphVertexStar] at hz
    rcases hz with ⟨w, hw, hEq⟩
    have hwz : graphRealizationSetoid boundary w z := by
      exact Quotient.exact (by simpa [graphRealizationPoint] using hEq)
    exact
      (graphVertexStarSource_setoid_iff boundary x ρ₀ ρ₁ hρ₀ hρ₁ hwz).1 hw
  · -- A source-star representative maps into the quotient image by construction.
    intro hz
    rw [graphVertexStar]
    exact ⟨z, hz, rfl⟩

/-- Helper for Lemma 4.1.7: if the source star is chosen inside the pullback of a neighborhood,
its quotient image is an open neighborhood of `graphVertex boundary x` contained in that target
neighborhood. -/
theorem graphVertexStar_isOpenNeighborhood (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I))
    {U : Set (graphRealization boundary)}
    (hsub : graphVertexStarSource boundary x ρ₀ ρ₁ ⊆ graphRealizationPoint boundary ⁻¹' U) :
    IsOpen (graphVertexStarSet boundary x ρ₀ ρ₁) ∧
      graphVertex boundary x ∈ graphVertexStarSet boundary x ρ₀ ρ₁ ∧
      graphVertexStarSet boundary x ρ₀ ρ₁ ⊆ U := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  -- With the corrected quotient topology fixed above, the textbook vertex-star neighborhood
  -- package is the intended proof route here.
  constructor
  · -- The saturated source star has open quotient image because the quotient map detects openness
    -- from the preimage.
    have hq : IsQuotientMap (graphRealizationPoint boundary) := by
      simpa [graphRealizationPoint] using
        (isQuotientMap_quotient_mk' :
          IsQuotientMap
            (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)))
    have hpreimageOpen :
        IsOpen (graphRealizationPoint boundary ⁻¹' graphVertexStar boundary x ρ₀ ρ₁) := by
      rw [graphVertexStar_preimage boundary x ρ₀ ρ₁ hρ₀ hρ₁]
      exact graphVertexStarSource_isOpen boundary x ρ₀ ρ₁
    exact (hq.isOpen_preimage).1 hpreimageOpen
  constructor
  · -- The center vertex belongs to the quotient star via its distinguished source representative.
    refine ⟨Sum.inl x, ?_, rfl⟩
    exact (mem_graphVertexStarSource_inl boundary x x ρ₀ ρ₁).2 rfl
  · -- Source-side containment descends directly to the quotient image.
    rintro _ ⟨z, hz, rfl⟩
    exact hsub hz

/-- Helper for Lemma 4.1.7: an interior point of an edge is fixed by the generated quotient
relation because the endpoint identifications never touch it. -/
theorem graphRealizationSetoid_edgeInterior_eq (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {z : X₀ ⊕ (J × I)}
    (hz : graphRealizationSetoid boundary (Sum.inr (j, t)) z) :
    z = Sum.inr (j, t) := by
  -- Apply the setoid-invariance lemma to the distinguished interior representative.
  exact (graphRealizationSetoid_edgeInterior_eq_iff boundary j t ht₀ ht₁ hz).1 rfl

/-- Helper for Lemma 4.1.7: the realized open edge segment viewed inside the graph realization
equipped with the source-faithful quotient topology. -/
abbrev edgeOpenSegmentSet (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I) :
    Set (graphRealization boundary) :=
  edgeOpenSegment boundary j a b

/- Helper for Lemma 4.1.7: the edge parameterization is continuous for the source-faithful
quotient topology on the realization. -/
theorem continuous_graphEdgePoint (boundary : J ↪ Fin 2 → X₀) (j : J) :
    Continuous (graphEdgePoint boundary j) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  -- The edge map is the quotient map applied to the right summand parameterization.
  simpa [graphEdgePoint, graphRealizationPoint] using
    (continuous_quotient_mk'.comp (continuous_inr.comp (continuous_const.prodMk continuous_id)))

/-- Helper for Lemma 4.1.7: an arbitrary open source slice of a fixed edge stays open in the
source disjoint union. -/
theorem isOpen_graphEdgeSourceImage (j : J) {s : Set I} (hs : IsOpen s) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    IsOpen (Sum.inr '' (Prod.mk j '' s) : Set (X₀ ⊕ (J × I))) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  have hprod : IsOpen (((fun t : I ↦ (j, t)) '' s) : Set (J × I)) := by
    have himage : ((fun t : I ↦ (j, t)) '' s : Set (J × I)) = ({j} : Set J) ×ˢ s := by
      ext p
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨by simp, ht⟩
      · rintro ⟨hj, hp⟩
        exact ⟨p.2, hp, by cases hj; rfl⟩
    rw [himage]
    exact (@isOpen_discrete J ⊥ (discreteTopology_bot J) ({j} : Set J)).prod hs
  exact isOpenMap_inr _ hprod

/-- Helper for Lemma 4.1.7: away from the endpoints, the quotient identifies no new source
representatives on a fixed edge slice. -/
theorem graphEdgePoint_preimage_image_of_interior (boundary : J ↪ Fin 2 → X₀) (j : J) {s : Set I}
    (hs₀ : ∀ ⦃t : I⦄, t ∈ s → t ≠ 0) (hs₁ : ∀ ⦃t : I⦄, t ∈ s → t ≠ 1) :
    graphRealizationPoint boundary ⁻¹' (graphEdgePoint boundary j '' s) =
      Sum.inr '' (Prod.mk j '' s) := by
  ext z
  constructor
  · -- Equality in the quotient keeps an interior edge point fixed.
    intro hz
    rcases hz with ⟨t, ht, hEq⟩
    have hzsetoid : graphRealizationSetoid boundary (Sum.inr (j, t)) z := by
      exact Quotient.exact (by simpa [graphEdgePoint, graphRealizationPoint] using hEq)
    exact
      (graphRealizationSetoid_edgeInterior_eq boundary j t (hs₀ ht) (hs₁ ht) hzsetoid) ▸
        ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩
  · -- Any source point on the fixed interior slice maps into the quotient image immediately.
    rintro ⟨⟨j', t⟩, hp, rfl⟩
    rcases hp with ⟨u, hu, hp⟩
    cases hp
    exact ⟨t, hu, rfl⟩

/-- Helper for Lemma 4.1.7: an open interior slice of a fixed edge has open image in the
realization. -/
theorem isOpen_graphEdgePoint_image_of_interior (boundary : J ↪ Fin 2 → X₀) (j : J) {s : Set I}
    (hs : IsOpen s) (hs₀ : ∀ ⦃t : I⦄, t ∈ s → t ≠ 0) (hs₁ : ∀ ⦃t : I⦄, t ∈ s → t ≠ 1) :
    IsOpen (graphEdgePoint boundary j '' s) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  have hq : IsQuotientMap (graphRealizationPoint boundary) := by
    simpa [graphRealizationPoint] using
      (isQuotientMap_quotient_mk' :
        IsQuotientMap
          (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)))
  have hpreimageOpen :
      IsOpen (graphRealizationPoint boundary ⁻¹' (graphEdgePoint boundary j '' s)) := by
    rw [graphEdgePoint_preimage_image_of_interior boundary j hs₀ hs₁]
    exact isOpen_graphEdgeSourceImage j hs
  exact (hq.isOpen_preimage).1 hpreimageOpen

/-- Helper for Lemma 4.1.7: an open interval inside `I` is homeomorphic to the corresponding open
interval in `ℝ`. -/
noncomputable def unitIntervalIooHomeomorph (a b : I) :
    Set.Ioo a b ≃ₜ Set.Ioo (a : ℝ) (b : ℝ) where
  toFun := fun t ↦ by
    rcases t with ⟨x, hx⟩
    exact
      ⟨(x : ℝ), by
        simpa [Set.mem_Ioo] using hx⟩
  invFun := fun t ↦ by
    rcases t with ⟨x, hx⟩
    let y : I := ⟨x, ⟨le_trans a.2.1 hx.1.le, le_trans hx.2.le b.2.2⟩⟩
    exact
      ⟨y, by
        simpa [y, Set.mem_Ioo] using hx⟩
  left_inv := by
    intro t
    ext
    rfl
  right_inv := by
    intro t
    ext
    rfl
  continuous_toFun := by
    -- This map just forgets the ambient `I` proof and keeps the same real coordinate.
    exact continuous_subtype_val.subtype_val.subtype_mk _
  continuous_invFun := by
    -- The inverse is the obvious coercion back into `I`, followed by the interval proof.
    exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Helper for Lemma 4.1.7: every strict interior edge segment is contractible because it is
homeomorphic to a real open interval. -/
theorem edgeOpenSegment_contractible (boundary : J ↪ Fin 2 → X₀) (j : J) (a b : I)
    (ha : (0 : I) < a) (hab : a < b) (hb : b < (1 : I)) :
    ContractibleSpace (edgeOpenSegmentSet boundary j a b) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hrealContractible : ContractibleSpace (Set.Ioo (a : ℝ) (b : ℝ)) := by
    have hnonempty : (Set.Ioo (a : ℝ) (b : ℝ)).Nonempty := by
      have habReal : (a : ℝ) < b := hab
      refine ⟨(a + b) / 2, ?_⟩
      constructor
      · have : (a : ℝ) < (a + b) / 2 := by nlinarith
        exact this
      · have : (a + b) / 2 < (b : ℝ) := by nlinarith
        exact this
    exact Convex.contractibleSpace (convex_Ioo (a : ℝ) b) hnonempty
  have hdomainContractible : ContractibleSpace (Set.Ioo a b) := by
    let _ : ContractibleSpace (Set.Ioo (a : ℝ) (b : ℝ)) := hrealContractible
    exact (unitIntervalIooHomeomorph a b).contractibleSpace
  let edgeParam : Set.Ioo a b → graphRealization boundary := fun t ↦ graphEdgePoint boundary j t
  have hedge_injective : Function.Injective edgeParam := by
    intro s t hst
    have hs₀ : (s : I) ≠ 0 := ne_of_gt (lt_trans ha s.2.1)
    have hs₁ : (s : I) ≠ 1 := ne_of_lt (lt_trans s.2.2 hb)
    have hsetoid : graphRealizationSetoid boundary (Sum.inr (j, (s : I))) (Sum.inr (j, (t : I))) := by
      exact Quotient.exact (by simpa [edgeParam, graphEdgePoint, graphRealizationPoint] using hst)
    have hEq : Sum.inr (j, (t : I)) = Sum.inr (j, (s : I)) :=
      graphRealizationSetoid_edgeInterior_eq boundary j (s : I) hs₀ hs₁ hsetoid
    apply Subtype.ext
    simpa using (congrArg Prod.snd (Sum.inr.inj hEq)).symm
  have hedge_openMap : IsOpenMap edgeParam := by
    intro s hs
    -- Open subsets of the interval model stay open after applying the edge parameterization.
    have hsIoo : IsOpen ((Subtype.val : Set.Ioo a b → I) '' s) :=
      isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap _ hs
    have hs₀ :
        ∀ ⦃t : I⦄, t ∈ ((Subtype.val : Set.Ioo a b → I) '' s) → t ≠ 0 := by
      rintro t ⟨u, hu, rfl⟩
      exact ne_of_gt (lt_trans ha u.2.1)
    have hs₁ :
        ∀ ⦃t : I⦄, t ∈ ((Subtype.val : Set.Ioo a b → I) '' s) → t ≠ 1 := by
      rintro t ⟨u, hu, rfl⟩
      exact ne_of_lt (lt_trans u.2.2 hb)
    have hopenAmbient :
        IsOpen (graphEdgePoint boundary j '' ((Subtype.val : Set.Ioo a b → I) '' s)) :=
      isOpen_graphEdgePoint_image_of_interior boundary j hsIoo hs₀ hs₁
    have himage :
        edgeParam '' s = graphEdgePoint boundary j '' ((Subtype.val : Set.Ioo a b → I) '' s) := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨v, hv, hvEq⟩, huEq⟩
        subst hvEq
        exact ⟨v, hv, huEq⟩
    rw [himage]
    exact hopenAmbient
  have hedge_cont : Continuous edgeParam :=
    (continuous_graphEdgePoint boundary j).comp continuous_subtype_val
  have hedge_embedding : IsEmbedding edgeParam :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap
      hedge_cont hedge_injective hedge_openMap).toIsEmbedding
  have hhomeo : Set.Ioo a b ≃ₜ Set.range edgeParam :=
    hedge_embedding.toHomeomorph
  have hImageEq :
      Set.range edgeParam = edgeOpenSegmentSet boundary j a b := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Sum.inr (j, t), ⟨(j, t), ⟨t, t.2, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with ⟨⟨j', t⟩, ⟨u, hu, huEq⟩, hwEq⟩
      cases huEq
      cases hwEq
      exact ⟨⟨t, hu⟩, rfl⟩
  let _ : ContractibleSpace (Set.Ioo a b) := hdomainContractible
  let hsegment : Set.Ioo a b ≃ₜ edgeOpenSegmentSet boundary j a b :=
    hhomeo.trans (Homeomorph.setCongr hImageEq)
  exact hsegment.symm.contractibleSpace

/-- Helper for Lemma 4.1.7: a neighborhood of a genuine interior edge point contains a realized
open edge segment that is already contractible. -/
theorem edgeInteriorContractibleNeighborhoodWithin (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    ∀ {U : Set (graphRealization boundary)},
      U ∈ 𝓝 (graphEdgePoint boundary j t : graphRealization boundary) →
      ∃ V ∈ 𝓝 (graphEdgePoint boundary j t : graphRealization boundary),
        V ⊆ U ∧ ContractibleSpace V := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  intro U hU
  have htLeft : (0 : I) < t := lt_of_le_of_ne t.2.1 ht₀.symm
  have htRight : t < (1 : I) := lt_of_le_of_ne t.2.2 ht₁
  obtain ⟨l, hl0, hlt⟩ := exists_between htLeft
  obtain ⟨u, htu, hu1⟩ := exists_between htRight
  have hpreimage :
      (graphEdgePoint boundary j) ⁻¹' U ∈ 𝓝 t := by
    exact (continuous_graphEdgePoint boundary j).continuousAt.preimage_mem_nhds hU
  have hinterval :
      Set.Ioo l u ∈ 𝓝 t := by
    exact isOpen_Ioo.mem_nhds ⟨hlt, htu⟩
  have hrefined :
      (graphEdgePoint boundary j) ⁻¹' U ∩ Set.Ioo l u ∈ 𝓝 t := by
    exact inter_mem hpreimage hinterval
  rcases
      (mem_nhds_iff_exists_Ioo_subset'
        (show ∃ l' : I, l' < t from ⟨l, hlt⟩)
        (show ∃ u' : I, t < u' from ⟨u, htu⟩)).1 hrefined with
    ⟨a, b, htMem, hsub⟩
  have hab : a < b := htMem.1.trans htMem.2
  have hbounds : l ≤ a ∧ b ≤ u := by
    apply (Set.Ioo_subset_Ioo_iff hab).1
    intro y hy
    exact (hsub hy).2
  have ha : (0 : I) < a := lt_of_lt_of_le hl0 hbounds.1
  have hb : b < (1 : I) := lt_of_le_of_lt hbounds.2 hu1
  refine
    ⟨edgeOpenSegmentSet boundary j a b,
      IsOpen.mem_nhds (edgeOpenSegment_isOpen boundary j a b ha hb) ?_, ?_, ?_⟩
  · -- The chosen interior interval still contains the original edge point.
    exact ⟨Sum.inr (j, t), ⟨(j, t), ⟨t, htMem, rfl⟩, rfl⟩, rfl⟩
  · -- The entire realized edge segment lies inside the prescribed neighborhood.
    rintro _ ⟨w, hw, rfl⟩
    rcases hw with ⟨⟨j', u⟩, ⟨v, hv, hvEq⟩, hwEq⟩
    cases hvEq
    cases hwEq
    exact (hsub hv).1
  · -- Contractibility comes from the interval model proved above.
    exact edgeOpenSegment_contractible boundary j a b ha hab hb

/-- Helper for Lemma 4.1.7: the branchwise source deformation contracts the chosen source star
toward the distinguished vertex by scaling each initial branch and terminal branch separately. -/
noncomputable def vertexStarSourceDeform (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (ρ₀ ρ₁ : J → I) (s : I) :
    (X₀ ⊕ (J × I)) → (X₀ ⊕ (J × I)) :=
  let _ : DecidableEq X₀ := Classical.decEq X₀
  fun
    | Sum.inl y => Sum.inl y
    | Sum.inr (j, t) =>
        if h₀ : boundary j 0 = x ∧ t < ρ₀ j then
          Sum.inr (j, s * t)
        else if h₁ : boundary j 1 = x ∧ ρ₁ j < t then
          Sum.inr (j, σ (s * σ t))
        else
          Sum.inr (j, t)

/-- Helper for Lemma 4.1.7: the source deformation keeps every initial edge endpoint fixed. -/
theorem vertexStarSourceDeform_edge_zero (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (ρ₀ ρ₁ : J → I) (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) (s : I) (j : J) :
    vertexStarSourceDeform boundary x ρ₀ ρ₁ s (Sum.inr (j, 0)) = Sum.inr (j, 0) := by
  -- At `t = 0`, the deformation either uses the initial-branch formula or leaves the endpoint in
  -- place, and both outcomes are the original endpoint.
  have hnotTerminal : ¬(boundary j 1 = x ∧ ρ₁ j < (0 : I)) := by
    rintro ⟨_, hlt⟩
    exact (not_lt_of_ge (ρ₁ j).2.1) hlt
  by_cases hInitial : boundary j 0 = x
  · have hpos : (0 : I) < ρ₀ j := hρ₀ j hInitial
    simp [vertexStarSourceDeform, hInitial, hpos, hnotTerminal]
  · simp [vertexStarSourceDeform, hInitial, hnotTerminal]

/-- Helper for Lemma 4.1.7: the source deformation keeps every terminal edge endpoint fixed. -/
theorem vertexStarSourceDeform_edge_one (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (ρ₀ ρ₁ : J → I) (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) (s : I) (j : J) :
    vertexStarSourceDeform boundary x ρ₀ ρ₁ s (Sum.inr (j, 1)) = Sum.inr (j, 1) := by
  -- At `t = 1`, the deformation either uses the terminal-branch formula or leaves the endpoint in
  -- place, and both outcomes are the original endpoint.
  have hnotInitial : ¬(boundary j 0 = x ∧ (1 : I) < ρ₀ j) := by
    rintro ⟨_, hlt⟩
    exact (not_lt_of_ge (ρ₀ j).2.2) hlt
  by_cases hTerminal : boundary j 1 = x
  · have hlt : ρ₁ j < (1 : I) := hρ₁ j hTerminal
    simp [vertexStarSourceDeform, hnotInitial, hTerminal, hlt]
  · simp [vertexStarSourceDeform, hnotInitial, hTerminal]

/-- Helper for Lemma 4.1.7: under separated radii, the branchwise source deformation preserves
membership in the source star. -/
theorem vertexStarSourceDeform_mem (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (ρ₀ ρ₁ : J → I) (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I))
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j) (s : I)
    {z : X₀ ⊕ (J × I)} (hz : z ∈ graphVertexStarSource boundary x ρ₀ ρ₁) :
    vertexStarSourceDeform boundary x ρ₀ ρ₁ s z ∈ graphVertexStarSource boundary x ρ₀ ρ₁ := by
  cases z with
  | inl y =>
      -- The deformation fixes the vertex representative, so the center stays in the source star.
      rw [mem_graphVertexStarSource_inl] at hz
      simpa [vertexStarSourceDeform, mem_graphVertexStarSource_inl, hz]
  | inr jt =>
      rcases jt with ⟨j, t⟩
      rw [mem_graphVertexStarSource_inr] at hz
      rcases hz with hInitial | hTerminal
      · -- On an initial branch, the scaled parameter stays below the chosen initial radius.
        have hnotTerminal : ¬(boundary j 1 = x ∧ ρ₁ j < t) := by
          rintro ⟨hBoundary, hlt⟩
          have : ρ₀ j < ρ₀ j :=
            lt_trans (hsep j hInitial.1 hBoundary) (lt_trans hlt hInitial.2)
          exact (lt_irrefl _ this).elim
        have hmul : s * t ≤ t := unitInterval.mul_le_right
        have hdeform :
            vertexStarSourceDeform boundary x ρ₀ ρ₁ s (Sum.inr (j, t)) = Sum.inr (j, s * t) := by
          simp [vertexStarSourceDeform, hInitial, hnotTerminal]
        rw [hdeform]
        rw [mem_graphVertexStarSource_inr]
        left
        refine ⟨hInitial.1, ?_⟩
        exact lt_of_le_of_lt hmul hInitial.2
      · -- On a terminal branch, the deformed parameter moves monotonically toward `1`.
        have hnotInitial : ¬(boundary j 0 = x ∧ t < ρ₀ j) := by
          rintro ⟨hBoundary, hlt⟩
          have : ρ₀ j < ρ₀ j :=
            lt_trans (hsep j hBoundary hTerminal.1) (lt_trans hTerminal.2 hlt)
          exact (lt_irrefl _ this).elim
        have hdeform :
            vertexStarSourceDeform boundary x ρ₀ ρ₁ s (Sum.inr (j, t)) =
              Sum.inr (j, σ (s * σ t)) := by
          simp [vertexStarSourceDeform, hnotInitial, hTerminal]
        rw [hdeform]
        rw [mem_graphVertexStarSource_inr]
        right
        refine ⟨hTerminal.1, ?_⟩
        have hmono : t ≤ σ (s * σ t) := by
          rw [unitInterval.le_symm_comm]
          exact unitInterval.mul_le_right
        exact lt_of_lt_of_le hTerminal.2 hmono

/-- Helper for Lemma 4.1.7: every time slice of the source deformation respects the graph
realization setoid, so it descends to quotient representatives. -/
theorem vertexStarSourceDeform_setoid (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (ρ₀ ρ₁ : J → I) (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) (s : I)
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationSetoid boundary a b) :
    graphRealizationSetoid boundary
      (vertexStarSourceDeform boundary x ρ₀ ρ₁ s a)
      (vertexStarSourceDeform boundary x ρ₀ ρ₁ s b) := by
  -- The generating relations only identify edge endpoints with their corresponding vertices, and
  -- the endpoint formulas above show the deformation preserves those generators.
  induction hab with
  | rel a b hrel =>
      cases a with
      | inl xa =>
          cases b with
          | inl xb =>
              cases hrel
          | inr jt =>
              rcases jt with ⟨j, t⟩
              rcases hrel with (⟨hxa, ht⟩ | ⟨hxa, ht⟩)
              · subst xa
                subst t
                refine Relation.EqvGen.rel _ _ ?_
                rw [vertexStarSourceDeform_edge_zero boundary x ρ₀ ρ₁ hρ₀ hρ₁ s j]
                exact Or.inl ⟨rfl, rfl⟩
              · subst xa
                subst t
                refine Relation.EqvGen.rel _ _ ?_
                rw [vertexStarSourceDeform_edge_one boundary x ρ₀ ρ₁ hρ₀ hρ₁ s j]
                exact Or.inr ⟨rfl, rfl⟩
      | inr jt =>
          rcases jt with ⟨j, t⟩
          cases b with
          | inl xb =>
              rcases hrel with (⟨ht, hxb⟩ | ⟨ht, hxb⟩)
              · subst t
                subst xb
                refine Relation.EqvGen.rel _ _ ?_
                rw [vertexStarSourceDeform_edge_zero boundary x ρ₀ ρ₁ hρ₀ hρ₁ s j]
                exact Or.inl ⟨rfl, rfl⟩
              · subst t
                subst xb
                refine Relation.EqvGen.rel _ _ ?_
                rw [vertexStarSourceDeform_edge_one boundary x ρ₀ ρ₁ hρ₀ hρ₁ s j]
                exact Or.inr ⟨rfl, rfl⟩
          | inr jt' =>
              cases hrel
  | refl a =>
      exact Relation.EqvGen.refl _
  | symm a b hab ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Helper for Lemma 4.1.7: every neighborhood of a realized vertex contains a source star with
loop-safe separated radii. -/
theorem existsSeparatedVertexStarRadiiWithin (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {U : Set (graphRealization boundary)}
    (hU : U ∈ 𝓝 (graphVertex boundary x : graphRealization boundary)) :
    ∃ ρ₀ ρ₁ : J → I,
      (∀ j, boundary j 0 = x → (0 : I) < ρ₀ j) ∧
      (∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) ∧
      (∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j) ∧
      graphVertexStarSource boundary x ρ₀ ρ₁ ⊆ graphRealizationPoint boundary ⁻¹' U := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  classical
  let mid : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hxU : graphVertex boundary x ∈ U := mem_of_mem_nhds hU
  have hleftChoice :
      ∀ j, boundary j 0 = x →
        ∃ a : I, (0 : I) < a ∧ Set.Iio a ⊆ (graphEdgePoint boundary j) ⁻¹' U := by
    intro j hj
    have hUj : U ∈ 𝓝 (graphEdgePoint boundary j 0 : graphRealization boundary) := by
      have hEq : graphVertex boundary x = graphEdgePoint boundary j 0 := by
        simpa [hj] using graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j
      exact hEq ▸ hU
    have hPreimage :
        (graphEdgePoint boundary j) ⁻¹' U ∈ 𝓝 (0 : I) :=
      (continuous_graphEdgePoint boundary j).continuousAt.preimage_mem_nhds hUj
    rcases (nhds_bot_basis.mem_iff.1 hPreimage) with ⟨a, ha, hsub⟩
    exact ⟨a, ha, hsub⟩
  have hrightChoice :
      ∀ j, boundary j 1 = x →
        ∃ b : I, b < (1 : I) ∧ Set.Ioi b ⊆ (graphEdgePoint boundary j) ⁻¹' U := by
    intro j hj
    have hUj : U ∈ 𝓝 (graphEdgePoint boundary j 1 : graphRealization boundary) := by
      have hEq : graphVertex boundary x = graphEdgePoint boundary j 1 := by
        simpa [hj] using graphVertex_boundary_one_eq_graphEdgePoint_one boundary j
      exact hEq ▸ hU
    have hPreimage :
        (graphEdgePoint boundary j) ⁻¹' U ∈ 𝓝 (1 : I) :=
      (continuous_graphEdgePoint boundary j).continuousAt.preimage_mem_nhds hUj
    rcases (nhds_top_basis.mem_iff.1 hPreimage) with ⟨b, hb, hsub⟩
    exact ⟨b, hb, hsub⟩
  let α : J → I := fun j ↦
    if hj : boundary j 0 = x then Classical.choose (hleftChoice j hj) else mid
  let β : J → I := fun j ↦
    if hj : boundary j 1 = x then Classical.choose (hrightChoice j hj) else mid
  have hαpos : ∀ j, boundary j 0 = x → (0 : I) < α j := by
    intro j hj
    dsimp [α]
    simpa [hj] using (Classical.choose_spec (hleftChoice j hj)).1
  have hαsub : ∀ j, boundary j 0 = x →
      Set.Iio (α j) ⊆ (graphEdgePoint boundary j) ⁻¹' U := by
    intro j hj
    dsimp [α]
    simpa [hj] using (Classical.choose_spec (hleftChoice j hj)).2
  have hβlt : ∀ j, boundary j 1 = x → β j < (1 : I) := by
    intro j hj
    dsimp [β]
    simpa [hj] using (Classical.choose_spec (hrightChoice j hj)).1
  have hβsub : ∀ j, boundary j 1 = x →
      Set.Ioi (β j) ⊆ (graphEdgePoint boundary j) ⁻¹' U := by
    intro j hj
    dsimp [β]
    simpa [hj] using (Classical.choose_spec (hrightChoice j hj)).2
  let ρ₀ : J → I := fun j ↦
    ⟨((α j : ℝ) / 4 : ℝ), by
      constructor
      · nlinarith [show (0 : ℝ) ≤ α j from (α j).2.1]
      · nlinarith [show (α j : ℝ) ≤ 1 from (α j).2.2]⟩
  let ρ₁ : J → I := fun j ↦
    ⟨(((β j : ℝ) + 3) / 4 : ℝ), by
      constructor
      · nlinarith [show (0 : ℝ) ≤ β j from (β j).2.1]
      · nlinarith [show (β j : ℝ) ≤ 1 from (β j).2.2]⟩
  refine ⟨ρ₀, ρ₁, ?_, ?_, ?_, ?_⟩
  · intro j hj
    -- Shrinking the left radius preserves the one-sided containment and enforces positivity.
    dsimp [ρ₀]
    change (0 : ℝ) < (α j : ℝ) / 4
    nlinarith [show (0 : ℝ) < α j from hαpos j hj]
  · intro j hj
    -- Enlarging the right threshold preserves containment while keeping it below `1`.
    dsimp [ρ₁]
    change ((β j : ℝ) + 3) / 4 < (1 : ℝ)
    nlinarith [show (β j : ℝ) < 1 from hβlt j hj]
  · intro j hj0 hj1
    -- The separated formulas force every loop edge to keep a gap between its two chosen branches.
    dsimp [ρ₀, ρ₁]
    change (α j : ℝ) / 4 < ((β j : ℝ) + 3) / 4
    nlinarith [show (α j : ℝ) ≤ 1 from (α j).2.2,
      show (0 : ℝ) ≤ β j from (β j).2.1]
  · intro z hz
    cases z with
    | inl y =>
        -- The center vertex itself already lies in the target neighborhood.
        rw [mem_graphVertexStarSource_inl] at hz
        simpa [graphVertex, hz] using hxU
    | inr jt =>
        rcases jt with ⟨j, t⟩
        rw [mem_graphVertexStarSource_inr] at hz
        rcases hz with h0 | h1
        · -- Any chosen initial branch still sits inside the pulled-back neighborhood.
          have htα : t < α j := by
            have hle : ((ρ₀ j : I) : ℝ) ≤ α j := by
              dsimp [ρ₀]
              nlinarith [show (0 : ℝ) ≤ α j from (α j).2.1]
            exact lt_of_lt_of_le h0.2 hle
          exact hαsub j h0.1 htα
        · -- Any chosen terminal branch stays in the pulled-back neighborhood as well.
          have hβt : β j < t := by
            have hlt : (β j : ℝ) < ρ₁ j := by
              dsimp [ρ₁]
              nlinarith [show (β j : ℝ) < 1 from hβlt j h1.1]
            exact lt_trans hlt h1.2
          exact hβsub j h1.1 hβt

/-- Helper for Lemma 4.1.7: the realized star is the codomain of the ambient quotient map
restricted to the open source-star preimage. -/
theorem graphVertexStarSet_restrictPreimage_isQuotientMap (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    IsQuotientMap ((graphVertexStarSet boundary x ρ₀ ρ₁).restrictPreimage
      (graphRealizationPoint boundary)) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hq : IsQuotientMap (graphRealizationPoint boundary) := by
    simpa [graphRealizationPoint] using
      (isQuotientMap_quotient_mk' :
        IsQuotientMap
          (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)))
  have hOpenStar : IsOpen (graphVertexStarSet boundary x ρ₀ ρ₁) := by
    -- Route correction: use the restricted quotient map on the already-open star set instead of
    -- reopening raw quotient-image equalities at every later transport step.
    let U : Set (graphRealization boundary) := Set.univ
    have hsub :
        graphVertexStarSource boundary x ρ₀ ρ₁ ⊆ graphRealizationPoint boundary ⁻¹' U := by
      simp [U]
    exact
      (graphVertexStar_isOpenNeighborhood boundary x ρ₀ ρ₁ hρ₀ hρ₁ hsub).1
  exact hq.restrictPreimage_isOpen hOpenStar

/-- Helper for Lemma 4.1.7: transport the restricted quotient map to the exact source-star subtype
used by the deformation lemmas. -/
theorem graphVertexStarSourceSubtype_isQuotientMap (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I)) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    IsQuotientMap fun z : graphVertexStarSource boundary x ρ₀ ρ₁ ↦
      (⟨graphRealizationPoint boundary z.1, by
          change z.1 ∈ graphRealizationPoint boundary ⁻¹' graphVertexStarSet boundary x ρ₀ ρ₁
          rw [graphVertexStar_preimage boundary x ρ₀ ρ₁ hρ₀ hρ₁]
          exact z.2⟩ :
        graphVertexStarSet boundary x ρ₀ ρ₁) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let hpre := graphVertexStar_preimage boundary x ρ₀ ρ₁ hρ₀ hρ₁
  let e :
      (graphRealizationPoint boundary ⁻¹' graphVertexStarSet boundary x ρ₀ ρ₁) ≃ₜ
        graphVertexStarSource boundary x ρ₀ ρ₁ :=
    Homeomorph.setCongr hpre
  have hRestrict :
      IsQuotientMap ((graphVertexStarSet boundary x ρ₀ ρ₁).restrictPreimage
        (graphRealizationPoint boundary)) :=
    graphVertexStarSet_restrictPreimage_isQuotientMap boundary x ρ₀ ρ₁ hρ₀ hρ₁
  -- Route correction: normalize the quotient interface to the source-star subtype once, then keep
  -- every later transport step in the source-star spelling used by the deformation lemmas.
  convert hRestrict.comp e.symm.isQuotientMap using 1

/-- Helper for Lemma 4.1.7: the source deformation specializes to the identity map at time `1`. -/
theorem vertexStarSourceDeform_one (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    (ρ₀ ρ₁ : J → I) {z : X₀ ⊕ (J × I)} :
    vertexStarSourceDeform boundary x ρ₀ ρ₁ 1 z = z := by
  -- At time `1`, both branch formulas reduce to the original edge parameter.
  cases z with
  | inl y =>
      simp [vertexStarSourceDeform]
  | inr jt =>
      rcases jt with ⟨j, t⟩
      by_cases hInitial : boundary j 0 = x ∧ t < ρ₀ j
      · simp [vertexStarSourceDeform, hInitial]
      · by_cases hTerminal : boundary j 1 = x ∧ ρ₁ j < t
        · simp [vertexStarSourceDeform, hInitial, hTerminal]
        · simp [vertexStarSourceDeform, hInitial, hTerminal]

/-- Helper for Lemma 4.1.7: the source deformation collapses every source-star point to the center
vertex in the realization at time `0`. -/
theorem graphVertexStarSourceDeform_zero_eq_vertex (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I) {z : X₀ ⊕ (J × I)}
    (hz : z ∈ graphVertexStarSource boundary x ρ₀ ρ₁) :
    graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ 0 z) =
      graphVertex boundary x := by
  -- At time `0`, the deformation reaches the appropriate endpoint representative of the center.
  cases z with
  | inl y =>
      have hy : y = x :=
        (mem_graphVertexStarSource_inl boundary x y ρ₀ ρ₁).1 hz
      subst hy
      simp [vertexStarSourceDeform, graphVertex]
  | inr jt =>
      rcases jt with ⟨j, t⟩
      by_cases hInitial : boundary j 0 = x ∧ t < ρ₀ j
      · -- On an initial branch, time `0` reaches the initial endpoint.
        simpa [vertexStarSourceDeform, hInitial, hInitial.1] using
          (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm
      · have hTerminal : boundary j 1 = x ∧ ρ₁ j < t := by
          rw [mem_graphVertexStarSource_inr] at hz
          rcases hz with h0 | h1
          · exact False.elim (hInitial h0)
          · exact h1
        -- If the initial branch is absent, time `0` reaches the terminal endpoint instead.
        simpa [vertexStarSourceDeform, hInitial, hTerminal, hTerminal.1] using
          (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm

/-- Helper for Lemma 4.1.7: multiplication on the unit interval is continuous. -/
theorem continuous_unitIntervalMul : Continuous fun p : I × I ↦ p.1 * p.2 := by
  -- View multiplication in `I` through the ambient real-valued multiplication and repackage it.
  change Continuous (fun p : I × I ↦
    (⟨((p.1 : I) : ℝ) * ((p.2 : I) : ℝ), by
      constructor
      · exact mul_nonneg p.1.2.1 p.2.2.1
      · nlinarith [p.1.2.2, p.2.2.2, p.1.2.1, p.2.2.1]⟩ : I))
  refine
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk ?_

/-- Helper for Lemma 4.1.7: the source parameter remembers the interval coordinate on the edge
summand and sends the vertex summand to `0`. -/
def graphRealizationSourceParameter : X₀ ⊕ (J × I) → I
  | Sum.inl _ => 0
  | Sum.inr (_, t) => t

/-- Helper for Lemma 4.1.7: the source-parameter coordinate is continuous for the source-faithful
sum topology. -/
theorem continuous_graphRealizationSourceParameter :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    Continuous (graphRealizationSourceParameter (X₀ := X₀) (J := J)) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  -- The vertex branch is constant and the edge branch is the second product projection.
  let f : X₀ ⊕ (J × I) → I := Sum.elim (fun _ : X₀ ↦ (0 : I)) fun p : J × I ↦ p.2
  have hf : Continuous f := continuous_sum_dom.2 ⟨continuous_const, continuous_snd⟩
  convert hf using 1
  ext z
  cases z <;> rfl

/-- Helper for Lemma 4.1.7: on an initial incident branch, the source deformation is the scaled
edge parameterization. -/
theorem graphVertexStarSourceDeformation_initial_eq (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j)
    {s t : I} {j : J} (hj : boundary j 0 = x) (ht : t < ρ₀ j) :
    graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ s (Sum.inr (j, t))) =
      graphEdgePoint boundary j (s * t) := by
  have hInitial : boundary j 0 = x ∧ t < ρ₀ j := ⟨hj, ht⟩
  have hnotTerminal : ¬(boundary j 1 = x ∧ ρ₁ j < t) := by
    rintro ⟨hj₁, hρ₁t⟩
    have : ρ₀ j < ρ₀ j := lt_trans (hsep j hj hj₁) (lt_trans hρ₁t ht)
    exact (lt_irrefl _ this).elim
  -- Route correction: normalize the initial branch directly in the raw realization codomain.
  simp [graphEdgePoint, vertexStarSourceDeform, hInitial, hnotTerminal]

/-- Helper for Lemma 4.1.7: on a terminal incident branch, the source deformation is the
reflected scaled edge parameterization. -/
theorem graphVertexStarSourceDeformation_terminal_eq (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j)
    {s t : I} {j : J} (hj : boundary j 1 = x) (ht : ρ₁ j < t) :
    graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ s (Sum.inr (j, t))) =
      graphEdgePoint boundary j (σ (s * σ t)) := by
  have hTerminal : boundary j 1 = x ∧ ρ₁ j < t := ⟨hj, ht⟩
  have hnotInitial : ¬(boundary j 0 = x ∧ t < ρ₀ j) := by
    rintro ⟨hj₀, htρ₀⟩
    have : ρ₁ j < ρ₁ j := lt_trans ht (lt_trans htρ₀ (hsep j hj₀ hj))
    exact (lt_irrefl _ this).elim
  -- Route correction: normalize the terminal branch directly in the raw realization codomain.
  simp [graphEdgePoint, vertexStarSourceDeform, hnotInitial, hTerminal]

/-- Helper for Lemma 4.1.7: pulling the source star back along `Prod.snd` gives the ambient slab
decomposition used by the continuity proof. -/
theorem snd_preimage_graphVertexStarSource_eq (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I) :
    (Prod.snd : I × (X₀ ⊕ (J × I)) → X₀ ⊕ (J × I)) ⁻¹'
        graphVertexStarSource boundary x ρ₀ ρ₁ =
      ((((Set.univ : Set I) ×ˢ ({Sum.inl x} : Set (X₀ ⊕ (J × I)))) ∪
            ⋃ j : {j : J // boundary j 0 = x},
              (Set.univ : Set I) ×ˢ
                (Sum.inr '' (Prod.mk j.1 '' Set.Iio (ρ₀ j.1)) : Set (X₀ ⊕ (J × I)))) ∪
          ⋃ j : {j : J // boundary j 1 = x},
            (Set.univ : Set I) ×ˢ
              (Sum.inr '' (Prod.mk j.1 '' Set.Ioi (ρ₁ j.1)) : Set (X₀ ⊕ (J × I)))) := by
  -- Expand source-star membership once, then keep the ambient slab spelling for gluing.
  ext p
  rcases p with ⟨s, z⟩
  cases z with
  | inl y =>
      simp [mem_graphVertexStarSource_inl]
  | inr jt =>
      rcases jt with ⟨j, t⟩
      have hInitial :
          (s, Sum.inr (j, t)) ∈
              ⋃ j : {j : J // boundary j 0 = x},
                (Set.univ : Set I) ×ˢ
                  (Sum.inr '' (Prod.mk j.1 '' Set.Iio (ρ₀ j.1)) : Set (X₀ ⊕ (J × I))) ↔
            boundary j 0 = x ∧ t < ρ₀ j := by
        constructor
        · intro hz
          rcases mem_iUnion.mp hz with ⟨⟨j', hj'⟩, hz⟩
          rcases hz with ⟨_, hz⟩
          rcases hz with ⟨_, ⟨u, hu, hEq⟩, hzEq⟩
          cases hEq
          cases hzEq
          exact ⟨hj', hu⟩
        · rintro ⟨hj, ht⟩
          refine mem_iUnion.mpr ?_
          refine ⟨⟨j, hj⟩, ?_⟩
          exact ⟨by simp, ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩⟩
      have hTerminal :
          (s, Sum.inr (j, t)) ∈
              ⋃ j : {j : J // boundary j 1 = x},
                (Set.univ : Set I) ×ˢ
                  (Sum.inr '' (Prod.mk j.1 '' Set.Ioi (ρ₁ j.1)) : Set (X₀ ⊕ (J × I))) ↔
            boundary j 1 = x ∧ ρ₁ j < t := by
        constructor
        · intro hz
          rcases mem_iUnion.mp hz with ⟨⟨j', hj'⟩, hz⟩
          rcases hz with ⟨_, hz⟩
          rcases hz with ⟨_, ⟨u, hu, hEq⟩, hzEq⟩
          cases hEq
          cases hzEq
          exact ⟨hj', hu⟩
        · rintro ⟨hj, ht⟩
          refine mem_iUnion.mpr ?_
          refine ⟨⟨j, hj⟩, ?_⟩
          exact ⟨by simp, ⟨(j, t), ⟨t, ht, rfl⟩, rfl⟩⟩
      simpa [mem_graphVertexStarSource_inr, hInitial, hTerminal]

/-- Helper for Lemma 4.1.7: on an initial incident slice, the ambient deformation is continuous
because it agrees with the scaled edge parameterization. -/
theorem continuousOn_graphVertexStarSourceDeformation_initialSlice
    (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j)
    (j : J) (hj : boundary j 0 = x) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    ContinuousOn
      (fun p : I × (X₀ ⊕ (J × I)) =>
        graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2))
      ((Set.univ : Set I) ×ˢ (Sum.inr '' (Prod.mk j '' Set.Iio (ρ₀ j)))) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hParam :
      Continuous fun p : I × (X₀ ⊕ (J × I)) => graphRealizationSourceParameter p.2 := by
    exact continuous_graphRealizationSourceParameter.comp continuous_snd
  have hModel :
      Continuous fun p : I × (X₀ ⊕ (J × I)) =>
        graphEdgePoint boundary j (p.1 * graphRealizationSourceParameter p.2) := by
    exact
      (continuous_graphEdgePoint boundary j).comp
        (continuous_unitIntervalMul.comp (continuous_fst.prodMk hParam))
  refine hModel.continuousOn.congr ?_
  rintro ⟨s, z⟩ hz
  rcases hz with ⟨_, hz⟩
  rcases hz with ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  -- On this slice, the branch formula already matches the continuous edge model.
  simp [graphRealizationSourceParameter,
    graphVertexStarSourceDeformation_initial_eq boundary x ρ₀ ρ₁ hsep hj ht]

/-- Helper for Lemma 4.1.7: on a terminal incident slice, the ambient deformation is continuous
because it agrees with the reflected scaled edge parameterization. -/
theorem continuousOn_graphVertexStarSourceDeformation_terminalSlice
    (boundary : J ↪ Fin 2 → X₀) (x : X₀) (ρ₀ ρ₁ : J → I)
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j)
    (j : J) (hj : boundary j 1 = x) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    ContinuousOn
      (fun p : I × (X₀ ⊕ (J × I)) =>
        graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2))
      ((Set.univ : Set I) ×ˢ (Sum.inr '' (Prod.mk j '' Set.Ioi (ρ₁ j)))) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  have hParam :
      Continuous fun p : I × (X₀ ⊕ (J × I)) => graphRealizationSourceParameter p.2 := by
    exact continuous_graphRealizationSourceParameter.comp continuous_snd
  have hSymmParam :
      Continuous fun p : I × (X₀ ⊕ (J × I)) => σ (graphRealizationSourceParameter p.2) := by
    exact unitInterval.continuous_symm.comp hParam
  have hMul :
      Continuous fun p : I × (X₀ ⊕ (J × I)) => p.1 * σ (graphRealizationSourceParameter p.2) := by
    exact continuous_unitIntervalMul.comp (continuous_fst.prodMk hSymmParam)
  have hModel :
      Continuous fun p : I × (X₀ ⊕ (J × I)) =>
        graphEdgePoint boundary j (σ (p.1 * σ (graphRealizationSourceParameter p.2))) := by
    exact (continuous_graphEdgePoint boundary j).comp (unitInterval.continuous_symm.comp hMul)
  refine hModel.continuousOn.congr ?_
  rintro ⟨s, z⟩ hz
  rcases hz with ⟨_, hz⟩
  rcases hz with ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  -- On this slice, the branch formula already matches the reflected continuous edge model.
  simp [graphRealizationSourceParameter,
    graphVertexStarSourceDeformation_terminal_eq boundary x ρ₀ ρ₁ hsep hj ht]

/-- Helper for Lemma 4.1.7: on the source-star subtype, the branchwise deformation gives a
continuous family of points in the graph realization. -/
theorem continuous_graphVertexStarSourceDeformation (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    Continuous fun p : I × graphVertexStarSource boundary x ρ₀ ρ₁ =>
      graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2.1) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let F : I × (X₀ ⊕ (J × I)) → graphRealization boundary := fun p =>
    graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2)
  let initialPiece : {j : J // boundary j 0 = x} → Set (I × (X₀ ⊕ (J × I))) := fun j =>
    (Set.univ : Set I) ×ˢ
      (Sum.inr '' (Prod.mk j.1 '' Set.Iio (ρ₀ j.1)) : Set (X₀ ⊕ (J × I)))
  let terminalPiece : {j : J // boundary j 1 = x} → Set (I × (X₀ ⊕ (J × I))) := fun j =>
    (Set.univ : Set I) ×ˢ
      (Sum.inr '' (Prod.mk j.1 '' Set.Ioi (ρ₁ j.1)) : Set (X₀ ⊕ (J × I)))
  have hCenter :
      ContinuousOn F ((Set.univ : Set I) ×ˢ ({Sum.inl x} : Set (X₀ ⊕ (J × I)))) := by
    have hConst : Continuous fun _ : I × (X₀ ⊕ (J × I)) => graphVertex boundary x := continuous_const
    refine hConst.continuousOn.congr ?_
    rintro ⟨s, z⟩ hz
    rcases hz with ⟨_, hz⟩
    have hz' : z = Sum.inl x := by simpa using hz
    subst hz'
    -- On the center slice, the deformation is literally constant at the center vertex.
    simp [F, graphVertex, vertexStarSourceDeform]
  have hInitial :
      ∀ j, ContinuousOn F (initialPiece j) := by
    intro j
    simpa [F, initialPiece] using
      continuousOn_graphVertexStarSourceDeformation_initialSlice
        boundary x ρ₀ ρ₁ hsep j.1 j.2
  have hTerminal :
      ∀ j, ContinuousOn F (terminalPiece j) := by
    intro j
    simpa [F, terminalPiece] using
      continuousOn_graphVertexStarSourceDeformation_terminalSlice
        boundary x ρ₀ ρ₁ hsep j.1 j.2
  have hCenterSourceOpen :
      IsOpen ({Sum.inl x} : Set (X₀ ⊕ (J × I))) := by
    let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
    have hSingle : IsOpen ({x} : Set X₀) := by
      change @TopologicalSpace.IsOpen X₀ ⊥ ({x} : Set X₀)
      simpa using isOpen_discrete ({x} : Set X₀)
    have hImage :
        IsOpen (((Sum.inl : X₀ → X₀ ⊕ (J × I)) '' ({x} : Set X₀))) :=
      isOpenMap_inl (({x} : Set X₀)) hSingle
    rw [show ({Sum.inl x} : Set (X₀ ⊕ (J × I))) =
        ((Sum.inl : X₀ → X₀ ⊕ (J × I)) '' ({x} : Set X₀)) by
          ext z
          constructor
          · intro hz
            have hz' : z = Sum.inl x := by simpa using hz
            subst hz'
            exact ⟨x, by simp, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            simpa using hy]
    exact hImage
  have hCenterOpen :
      IsOpen ((Set.univ : Set I) ×ˢ ({Sum.inl x} : Set (X₀ ⊕ (J × I)))) := by
    exact isOpen_univ.prod hCenterSourceOpen
  have hInitialOpen : ∀ j, IsOpen (initialPiece j) := by
    intro j
    change IsOpen
      ((Set.univ : Set I) ×ˢ
        ((Sum.inr '' (Prod.mk j.1 '' Set.Iio (ρ₀ j.1)) : Set (X₀ ⊕ (J × I)))))
    exact isOpen_univ.prod (isOpen_graphEdgeSourceImage (j := j.1) isOpen_Iio)
  have hTerminalOpen : ∀ j, IsOpen (terminalPiece j) := by
    intro j
    change IsOpen
      ((Set.univ : Set I) ×ˢ
        ((Sum.inr '' (Prod.mk j.1 '' Set.Ioi (ρ₁ j.1)) : Set (X₀ ⊕ (J × I)))))
    exact isOpen_univ.prod (isOpen_graphEdgeSourceImage (j := j.1) isOpen_Ioi)
  have hInitialUnion : ContinuousOn F (⋃ j, initialPiece j) := by
    rw [continuousOn_iUnion_iff_of_isOpen hInitialOpen]
    exact hInitial
  have hTerminalUnion : ContinuousOn F (⋃ j, terminalPiece j) := by
    rw [continuousOn_iUnion_iff_of_isOpen hTerminalOpen]
    exact hTerminal
  have hInitialUnionOpen : IsOpen (⋃ j, initialPiece j) := isOpen_iUnion hInitialOpen
  have hTerminalUnionOpen : IsOpen (⋃ j, terminalPiece j) := isOpen_iUnion hTerminalOpen
  have hAmbient :
      ContinuousOn F
        ((Prod.snd : I × (X₀ ⊕ (J × I)) → X₀ ⊕ (J × I)) ⁻¹'
          graphVertexStarSource boundary x ρ₀ ρ₁) := by
    rw [snd_preimage_graphVertexStarSource_eq boundary x ρ₀ ρ₁]
    have hCenterInitial :
        ContinuousOn F
          (((Set.univ : Set I) ×ˢ ({Sum.inl x} : Set (X₀ ⊕ (J × I)))) ∪
            ⋃ j, initialPiece j) := by
      exact hCenter.union_of_isOpen hInitialUnion hCenterOpen hInitialUnionOpen
    exact hCenterInitial.union_of_isOpen hTerminalUnion
      (hCenterOpen.union hInitialUnionOpen) hTerminalUnionOpen
  let G : I × graphVertexStarSource boundary x ρ₀ ρ₁ → I × (X₀ ⊕ (J × I)) := fun p =>
    (p.1, p.2.1)
  have hG : Continuous G := by
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hGMaps :
      ∀ p : I × graphVertexStarSource boundary x ρ₀ ρ₁,
        G p ∈ (Prod.snd : I × (X₀ ⊕ (J × I)) → X₀ ⊕ (J × I)) ⁻¹'
          graphVertexStarSource boundary x ρ₀ ρ₁ := by
    intro p
    exact p.2.2
  -- Restrict the ambient glued family along the open source-star subtype only after gluing.
  change Continuous (F ∘ G)
  exact hAmbient.comp_continuous hG hGMaps

/-- Helper for Lemma 4.1.7: once the source-star homotopy is descended through the normalized
quotient interface, the realized star identity map is nullhomotopic. -/
theorem graphVertexStar_idNullhomotopicOfSeparatedRadii (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I))
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j) :
    (ContinuousMap.id (graphVertexStarSet boundary x ρ₀ ρ₁)).Nullhomotopic := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceFaithfulSourceTopologicalSpace
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  classical
  have hCenterMem : graphVertex boundary x ∈ graphVertexStarSet boundary x ρ₀ ρ₁ := by
    refine ⟨Sum.inl x, ?_, rfl⟩
    exact (mem_graphVertexStarSource_inl boundary x x ρ₀ ρ₁).2 rfl
  let center : graphVertexStarSet boundary x ρ₀ ρ₁ := ⟨graphVertex boundary x, hCenterMem⟩
  let rawFamilyVal :
      I × graphVertexStarSource boundary x ρ₀ ρ₁ → graphRealization boundary := fun p =>
    graphRealizationPoint boundary (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2.1)
  have hRawMem :
      ∀ p : I × graphVertexStarSource boundary x ρ₀ ρ₁,
        rawFamilyVal p ∈ graphVertexStarSet boundary x ρ₀ ρ₁ := by
    intro p
    change vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2.1 ∈
      graphRealizationPoint boundary ⁻¹' graphVertexStarSet boundary x ρ₀ ρ₁
    rw [graphVertexStar_preimage boundary x ρ₀ ρ₁ hρ₀ hρ₁]
    exact vertexStarSourceDeform_mem boundary x ρ₀ ρ₁ hρ₀ hρ₁ hsep p.1 p.2.2
  let rawFamily :
      I × graphVertexStarSource boundary x ρ₀ ρ₁ →
        graphVertexStarSet boundary x ρ₀ ρ₁ := fun p =>
    ⟨rawFamilyVal p, hRawMem p⟩
  have hRawVal :
      Continuous rawFamilyVal :=
    continuous_graphVertexStarSourceDeformation boundary x ρ₀ ρ₁ hsep
  have hRaw : Continuous rawFamily := hRawVal.subtype_mk hRawMem
  have hqMem :
      ∀ z : graphVertexStarSource boundary x ρ₀ ρ₁,
        graphRealizationPoint boundary z.1 ∈ graphVertexStarSet boundary x ρ₀ ρ₁ := by
    intro z
    change z.1 ∈ graphRealizationPoint boundary ⁻¹' graphVertexStarSet boundary x ρ₀ ρ₁
    rw [graphVertexStar_preimage boundary x ρ₀ ρ₁ hρ₀ hρ₁]
    exact z.2
  let q :
      graphVertexStarSource boundary x ρ₀ ρ₁ →
        graphVertexStarSet boundary x ρ₀ ρ₁ := fun z =>
    ⟨graphRealizationPoint boundary z.1, hqMem z⟩
  have hq : IsQuotientMap q := by
    simpa [q] using
      (graphVertexStarSourceSubtype_isQuotientMap boundary x ρ₀ ρ₁ hρ₀ hρ₁)
  let rep :
      graphVertexStarSet boundary x ρ₀ ρ₁ →
        graphVertexStarSource boundary x ρ₀ ρ₁ := Function.surjInv hq.surjective
  let descended :
      I × graphVertexStarSet boundary x ρ₀ ρ₁ →
        graphVertexStarSet boundary x ρ₀ ρ₁ := fun p =>
    rawFamily (p.1, rep p.2)
  have hDescendedComp :
      ∀ p : I × graphVertexStarSource boundary x ρ₀ ρ₁,
        descended (p.1, q p.2) = rawFamily p := by
    intro p
    have hrep :
        q (rep (q p.2)) = q p.2 :=
      Function.rightInverse_surjInv hq.surjective (q p.2)
    have hsetoid :
        graphRealizationSetoid boundary (rep (q p.2)).1 p.2.1 := by
      exact Quotient.exact (by simpa [q, graphRealizationPoint] using congrArg Subtype.val hrep)
    have hdeformSetoid :
        graphRealizationSetoid boundary
          (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 (rep (q p.2)).1)
          (vertexStarSourceDeform boundary x ρ₀ ρ₁ p.1 p.2.1) :=
      vertexStarSourceDeform_setoid boundary x ρ₀ ρ₁ hρ₀ hρ₁ p.1 hsetoid
    -- The descended family is defined using a chosen representative, so fiber-constancy closes
    -- the comparison with the raw source-star family.
    apply Subtype.ext
    simpa [descended, rawFamily, rawFamilyVal] using
      (Quotient.sound hdeformSetoid :
        rawFamilyVal (p.1, rep (q p.2)) = rawFamilyVal p)
  have hDescendedCompContinuous :
      Continuous fun p : I × graphVertexStarSource boundary x ρ₀ ρ₁ =>
        descended (p.1, q p.2) := by
    rw [show
        (fun p : I × graphVertexStarSource boundary x ρ₀ ρ₁ => descended (p.1, q p.2)) =
          rawFamily by
        funext p
        exact hDescendedComp p]
    exact hRaw
  let _ : WeaklyLocallyCompactSpace I := by
    change WeaklyLocallyCompactSpace ↥(Set.Icc (0 : ℝ) 1)
    exact
      { exists_compact_mem_nhds := fun _ ↦
          ⟨Set.univ, isCompact_univ, univ_mem⟩ }
  let _ : TopologicalSpace.PseudoMetrizableSpace ℝ := UniformSpace.pseudoMetrizableSpace
  let _ : TopologicalSpace.MetrizableSpace ℝ :=
    TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace
  let _ : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
  let _ : R1Space ℝ := T2Space.r1Space
  let _ : R1Space I := by
    change R1Space ↥(Set.Icc (0 : ℝ) 1)
    exact instR1SpaceSubtype (p := Set.Icc (0 : ℝ) 1)
  let _ : LocallyCompactSpace I := WeaklyLocallyCompactSpace.locallyCompactSpace
  have hDescended : Continuous descended := by
    exact hq.continuous_lift_prod_right hDescendedCompContinuous
  have hZero :
      ∀ y : graphVertexStarSet boundary x ρ₀ ρ₁, descended (0, y) = center := by
    intro y
    apply Subtype.ext
    -- Time `0` sends every source-star representative to the center vertex in the realization.
    simpa [descended, rawFamily, rawFamilyVal, center] using
      (graphVertexStarSourceDeform_zero_eq_vertex boundary x ρ₀ ρ₁ (rep y).2)
  have hOne :
      ∀ y : graphVertexStarSet boundary x ρ₀ ρ₁, descended (1, y) = y := by
    intro y
    have hrep :
        q (rep y) = y :=
      Function.rightInverse_surjInv hq.surjective y
    have hOneVal : rawFamilyVal (1, rep y) = y.1 := by
      calc
        rawFamilyVal (1, rep y)
            = graphRealizationPoint boundary (rep y).1 := by
                simp [rawFamilyVal, vertexStarSourceDeform_one boundary x ρ₀ ρ₁]
        _ = y.1 := congrArg Subtype.val hrep
    apply Subtype.ext
    -- Time `1` recovers the chosen quotient representative, hence the original star point.
    simpa [descended, rawFamily] using hOneVal
  let homotopyToId :
      ContinuousMap.Homotopy
        (ContinuousMap.const (graphVertexStarSet boundary x ρ₀ ρ₁) center)
        (ContinuousMap.id (graphVertexStarSet boundary x ρ₀ ρ₁)) :=
    { toContinuousMap := ⟨descended, hDescended⟩
      map_zero_left := hZero
      map_one_left := hOne }
  -- Route correction: descend the family once through the normalized quotient map, then reverse
  -- the resulting constant-to-identity homotopy to obtain a nullhomotopy of the identity.
  refine ⟨center, ?_⟩
  exact ⟨homotopyToId.symm⟩

/-- Helper for Lemma 4.1.7: separated branch radii make the realized vertex star contractible. -/
theorem graphVertexStar_contractibleOfSeparatedRadii (boundary : J ↪ Fin 2 → X₀)
    (x : X₀) (ρ₀ ρ₁ : J → I)
    (hρ₀ : ∀ j, boundary j 0 = x → (0 : I) < ρ₀ j)
    (hρ₁ : ∀ j, boundary j 1 = x → ρ₁ j < (1 : I))
    (hsep : ∀ j, boundary j 0 = x → boundary j 1 = x → ρ₀ j < ρ₁ j) :
    ContractibleSpace (graphVertexStarSet boundary x ρ₀ ρ₁) := by
  -- The remaining work is precisely the nullhomotopy of the realized star identity map.
  rw [contractible_iff_id_nullhomotopic]
  exact graphVertexStar_idNullhomotopicOfSeparatedRadii boundary x ρ₀ ρ₁ hρ₀ hρ₁ hsep

/-- Helper for Lemma 4.1.7: every neighborhood of a realized vertex contains a smaller realized
vertex star whose separated branches make it contractible. -/
theorem vertexContractibleNeighborhoodWithin (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    :
    ∀ {U : Set (graphRealization boundary)},
      U ∈ 𝓝 (graphVertex boundary x : graphRealization boundary) →
      ∃ V ∈ 𝓝 (graphVertex boundary x : graphRealization boundary),
        V ⊆ U ∧ ContractibleSpace V := by
  intro U hU
  rcases existsSeparatedVertexStarRadiiWithin boundary x hU with
    ⟨ρ₀, ρ₁, hρ₀, hρ₁, hsep, hsub⟩
  let V := graphVertexStarSet boundary x ρ₀ ρ₁
  have hVdata := graphVertexStar_isOpenNeighborhood boundary x ρ₀ ρ₁ hρ₀ hρ₁ hsub
  refine
    ⟨V, ?_, hVdata.2.2,
      graphVertexStar_contractibleOfSeparatedRadii boundary x ρ₀ ρ₁ hρ₀ hρ₁ hsep⟩
  -- The separated source star is already an open neighborhood of the center vertex.
  exact hVdata.1.mem_nhds hVdata.2.1

/-- Graph realizations admit a basis of contractible neighborhoods for the chapter's
source-faithful quotient topology on `graphRealization boundary`. -/
instance graphRealization_stronglyLocallyContractibleSpace
    (boundary : J ↪ Fin 2 → X₀) :
    @StronglyLocallyContractibleSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  refine ⟨fun y ↦ by
    rw [hasBasis_self]
    refine Quotient.inductionOn y ?_
    intro z U hU
    cases z with
    | inl x =>
        -- Vertex representatives use the star-neighborhood theorem.
        rcases vertexContractibleNeighborhoodWithin boundary x hU with ⟨V, hV, hVU, hVc⟩
        exact ⟨V, hV, hVc, hVU⟩
    | inr jt =>
        rcases jt with ⟨j, t⟩
        by_cases ht0 : t = 0
        · subst ht0
          -- The initial endpoint is the corresponding realized vertex.
          change U ∈ 𝓝 (graphEdgePoint boundary j 0 : graphRealization boundary) at hU
          have hEq : graphVertex boundary (boundary j 0) = graphEdgePoint boundary j 0 := by
            exact graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j
          have hU0 : U ∈ 𝓝 (graphVertex boundary (boundary j 0) : graphRealization boundary) := by
            have hU0' := hU
            rwa [← hEq] at hU0'
          rcases vertexContractibleNeighborhoodWithin boundary (boundary j 0) hU0 with
            ⟨V, hV, hVU, hVc⟩
          refine ⟨V, ?_, hVc, hVU⟩
          change V ∈ 𝓝 (graphEdgePoint boundary j 0 : graphRealization boundary)
          have hV0 := hV
          rwa [hEq] at hV0
        · by_cases ht1 : t = 1
          · subst ht1
            -- The terminal endpoint is the other realized vertex of the edge.
            change U ∈ 𝓝 (graphEdgePoint boundary j 1 : graphRealization boundary) at hU
            have hEq : graphVertex boundary (boundary j 1) = graphEdgePoint boundary j 1 := by
              exact graphVertex_boundary_one_eq_graphEdgePoint_one boundary j
            have hU1 :
                U ∈ 𝓝 (graphVertex boundary (boundary j 1) : graphRealization boundary) := by
              have hU1' := hU
              rwa [← hEq] at hU1'
            rcases vertexContractibleNeighborhoodWithin boundary (boundary j 1) hU1 with
              ⟨V, hV, hVU, hVc⟩
            refine ⟨V, ?_, hVc, hVU⟩
            change V ∈ 𝓝 (graphEdgePoint boundary j 1 : graphRealization boundary)
            have hV1 := hV
            rwa [hEq] at hV1
          · -- Genuine interior representatives are handled by open edge segments.
            rcases edgeInteriorContractibleNeighborhoodWithin boundary j t ht0 ht1 hU with
              ⟨V, hV, hVU, hVc⟩
            exact ⟨V, hV, hVc, hVU⟩
    ⟩

/-- Graph realizations are locally contractible via the canonical strong local-contractibility
instance. -/
instance graphRealization_locallyContractibleSpace
    (boundary : J ↪ Fin 2 → X₀) :
    @LocallyContractibleSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) := by
  let _ : @StronglyLocallyContractibleSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) :=
    graphRealization_stronglyLocallyContractibleSpace boundary
  exact StronglyLocallyContractibleSpace.locallyContractible

/-- Lemma 4.1.7: every graph is locally contractible. -/
theorem graphRealization_locallyContractible (boundary : J ↪ Fin 2 → X₀) :
    @LocallyContractibleSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) :=
  graphRealization_locallyContractibleSpace boundary
