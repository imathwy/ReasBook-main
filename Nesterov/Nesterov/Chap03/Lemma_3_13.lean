import Nesterov.Chap03.Lemma_3_1_14
import Nesterov.Chap03.Proposition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped Topology WithTopConvexAnalysis

universe u v

variable {ι : Type u}

/- Lemma 3.13 lies in the finite-family specialization of Chapter 3's pointwise-supremum and
active-subdifferential calculus for `WithTop ℝ`-valued convex functions.

Relevant owner-style declarations sampled before refinement:
- `pointwiseSupremumOn` in `PointwiseSupremumOn`
- `activePointwiseSupremumOnIndices` in `Lemma_3_1_14`
- `ClosedConvexOn.pointwise_sSup` in `Theorem_3_1_8`
- `subdifferential` in `Definition_3_1_5`

Best owner abstraction:
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`,
  `ClosedConvexOn.pointwise_sSup`, `dom`, `ClosedConvexFunction`, `subdifferential`

Primitive data:
- a finite index type `ι`
- a family `φ : X → ι → WithTop ℝ`

Derived API in this file:
- the finite-specialization bridge `pointwiseSupremumOn_univ_eq_sup'`
- the finite inequality and active-set bridges
- the closed-convex, interior-domain, and unconstrained active-subdifferential conclusions for
  the specialization `pointwiseSupremumOn (Set.univ : Set ι) φ`

Source/core/bridge triage:
- source-facing: Lemma 3.13 as the finite-family specialization of the chapter supremum calculus
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`,
  `ClosedConvexOn.pointwise_sSup`, `dom`, `ClosedConvexFunction`, `subdifferential`
- bridge/view: `pointwiseSupremumOn_univ_eq_sup'`, `pointwiseSupremumOn_univ_le_zero_iff`,
  `mem_activePointwiseSupremumOnIndices_univ_iff`

This file therefore does not introduce a second finite-maximum owner. It keeps only the finite
`Set.univ` specialization layer above the existing chapter owner `pointwiseSupremumOn`, and it
states the genuinely finite-specific domain/interior and unconstrained active-subdifferential
results directly on that owner surface.
-/

/-- Evaluating the Chapter 3 supremum owner on the finite set `Set.univ` reproduces the usual
nonempty finite supremum. -/
theorem pointwiseSupremumOn_univ_eq_sup'
    [Fintype ι] [Nonempty ι] {X : Type v} {φ : X → ι → WithTop ℝ} {x : X} :
    pointwiseSupremumOn (Set.univ : Set ι) φ x =
      Finset.univ.sup' Finset.univ_nonempty (φ x) := by
  simpa [pointwiseSupremumOn_apply, Set.image_univ] using
    (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty (φ x)).symm

/-- The `Set.univ` specialization of `pointwiseSupremumOn` is nonpositive at `x` exactly when
every slice is nonpositive there. -/
theorem pointwiseSupremumOn_univ_le_zero_iff
    {X : Type v} {φ : X → ι → WithTop ℝ} {x : X} :
    pointwiseSupremumOn (Set.univ : Set ι) φ x ≤ 0 ↔ ∀ i : ι, φ x i ≤ 0 := by
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    simpa [pointwiseSupremumOn_apply, Set.image_univ, iSup] using
      (ciSup_le_iff
        (show BddAbove (Set.range (φ x)) from ⟨⊤, fun _ _ ↦ le_top⟩))
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    rw [pointwiseSupremumOn_apply, Set.image_univ, Set.range_eq_empty]
    simp [sSup]

/-- For the finite specialization `Δ = Set.univ`, an index is active exactly when its slice
attains the pointwise supremum value. -/
@[simp] theorem mem_activePointwiseSupremumOnIndices_univ_iff
    {X : Type v} {φ : X → ι → WithTop ℝ} {x : X} {i : ι} :
    i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ↔
      φ x i = pointwiseSupremumOn (Set.univ : Set ι) φ x := by
  simpa using
    (mem_activePointwiseSupremumOnIndices_iff :
      i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ↔
        i ∈ (Set.univ : Set ι) ∧
          φ x i = pointwiseSupremumOn (Set.univ : Set ι) φ x)

section ClosedConvex

variable {X : Type v} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Helper for Lemma 3.13: if the index type is empty, the `Set.univ` pointwise supremum is the
constant zero function. -/
lemma pointwiseSupremumOn_univ_eq_zero_of_isEmpty
    [IsEmpty ι] {φ : X → ι → WithTop ℝ} :
    pointwiseSupremumOn (Set.univ : Set ι) φ = fun _ ↦ (0 : WithTop ℝ) := by
  funext x
  -- With no active indices, the supremum is over the empty image set.
  rw [pointwiseSupremumOn_apply, Set.image_univ, Set.range_eq_empty]
  simp [sSup]

/-- Lemma 3.13 (1): the finite specialization of the pointwise supremum of closed convex
extended-real-valued functions is again a closed convex function. -/
-- Proof sketch: specialize the finite-family pointwise supremum to the chapter owner
-- `pointwiseSupremumOn (Set.univ : Set ι) φ`, then apply the usual epigraph-intersection argument
-- for finitely many closed convex slices.
theorem closedConvexFunction_pointwiseSupremumOn_univ
    {φ : X → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun x ↦ φ x i)) :
    ClosedConvexFunction (pointwiseSupremumOn (Set.univ : Set ι) φ) := by
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    let f : X → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
    have hEpigraph :
        constrainedEpigraph (dom f) f =
          ⋂ i : ι, constrainedEpigraph (dom (fun x ↦ φ x i)) (fun x ↦ φ x i) := by
      ext p
      constructor
      · intro hp
        rw [Set.mem_iInter]
        intro i
        rcases mem_constrainedEpigraph_iff.mp hp with ⟨hpDom, hpLe⟩
        refine mem_constrainedEpigraph_iff.mpr ?_
        constructor
        · change φ p.1 i < ⊤
          have hle : φ p.1 i ≤ f p.1 := by
            rw [show f p.1 = pointwiseSupremumOn (Set.univ : Set ι) φ p.1 by rfl,
              pointwiseSupremumOn_apply]
            exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
          exact lt_of_le_of_lt hle hpDom
        · have hle : φ p.1 i ≤ f p.1 := by
            rw [show f p.1 = pointwiseSupremumOn (Set.univ : Set ι) φ p.1 by rfl,
              pointwiseSupremumOn_apply]
            exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
          exact hle.trans hpLe
      · intro hp
        rcases hι with ⟨i₀⟩
        rw [Set.mem_iInter] at hp
        have hsSup_le : f p.1 ≤ p.2 := by
          rw [show f p.1 = pointwiseSupremumOn (Set.univ : Set ι) φ p.1 by rfl,
            pointwiseSupremumOn_apply]
          have himage_nonempty :
              ((fun y ↦ φ p.1 y) '' (Set.univ : Set ι)).Nonempty := by
            exact ⟨φ p.1 i₀, ⟨i₀, by simp, rfl⟩⟩
          exact csSup_le himage_nonempty fun _ hs ↦ by
            rcases hs with ⟨i, -, rfl⟩
            exact (mem_constrainedEpigraph_iff.mp (hp i)).2
        refine mem_constrainedEpigraph_iff.mpr ?_
        constructor
        · exact lt_of_le_of_lt hsSup_le (by simp)
        · exact hsSup_le
    -- In the nonempty branch, the effective epigraph is the intersection of the slice epigraphs.
    refine ⟨subset_rfl, ?_, ?_⟩
    · rw [hEpigraph]
      exact isClosed_iInter fun i ↦ (hφ i).isClosed_constrainedEpigraph
    · rw [hEpigraph]
      exact convex_iInter fun i ↦ (hφ i).convex_constrainedEpigraph
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    -- In the empty branch, the supremum is the constant zero function.
    rw [pointwiseSupremumOn_univ_eq_zero_of_isEmpty (φ := φ)]
    simpa using
      (closedConvexFunction_coe_of_convexOn_continuous
        (f := fun _ : X ↦ (0 : ℝ))
        (convexOn_const (0 : ℝ) convex_univ) continuous_const)

end ClosedConvex

/-- Lemma 3.13 (2): the interior of the effective domain of the finite specialization of the
pointwise supremum is the intersection of the interiors of the component effective domains. -/
-- Proof sketch: in the nonempty case, rewrite the effective domain using
-- `pointwiseSupremumOn_univ_eq_sup'` and `Finset.sup'_lt_iff`; in the empty case, use
-- `pointwiseSupremumOn_univ_le_zero_iff` to see the supremum is everywhere finite. Then apply the
-- canonical finite-intersection identity `interior_iInter_of_finite`.
theorem interior_dom_pointwiseSupremumOn_univ
    [Finite ι] {X : Type v} [TopologicalSpace X] {φ : X → ι → WithTop ℝ} :
    interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ)) =
      ⋂ i : ι, interior (dom (fun x ↦ φ x i)) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hdom :
      dom (pointwiseSupremumOn (Set.univ : Set ι) φ) = ⋂ i : ι, dom (fun x ↦ φ x i) := by
    ext x
    classical
    by_cases hι : Nonempty ι
    · let _ : Nonempty ι := hι
      constructor
      · intro hx
        change pointwiseSupremumOn (Set.univ : Set ι) φ x < (⊤ : WithTop ℝ) at hx
        rw [pointwiseSupremumOn_univ_eq_sup'] at hx
        rw [Set.mem_iInter]
        have hlt :
            Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
              ∀ i ∈ Finset.univ, φ x i < ⊤ := by
          simpa using
            (Finset.sup'_lt_iff :
              Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
                ∀ i ∈ Finset.univ, φ x i < ⊤)
        intro i
        change φ x i < (⊤ : WithTop ℝ)
        exact hlt.mp hx i (by simp)
      · intro hx
        rw [Set.mem_iInter] at hx
        change pointwiseSupremumOn (Set.univ : Set ι) φ x < (⊤ : WithTop ℝ)
        rw [pointwiseSupremumOn_univ_eq_sup']
        have hlt :
            Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
              ∀ i ∈ Finset.univ, φ x i < ⊤ := by
          simpa using
            (Finset.sup'_lt_iff :
              Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
                ∀ i ∈ Finset.univ, φ x i < ⊤)
        exact hlt.mpr fun i hi ↦ hx i
    · let _ : IsEmpty ι := not_nonempty_iff.mp hι
      constructor
      · intro _
        simp
      · intro _
        change pointwiseSupremumOn (Set.univ : Set ι) φ x < (⊤ : WithTop ℝ)
        have hle : pointwiseSupremumOn (Set.univ : Set ι) φ x ≤ 0 := by
          rw [pointwiseSupremumOn_univ_le_zero_iff]
          intro i
          exact isEmptyElim i
        exact lt_of_le_of_lt hle (by simp)
  simpa [hdom] using
    (interior_iInter_of_finite (fun i : ι ↦ dom (fun x ↦ φ x i)))

section Subdifferential

variable {V : Type v} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Helper for Lemma 3.13: constraining the subgradient inequality to `dom f` does not change the
subdifferential. -/
lemma constrainedSubdifferential_dom_eq_subdifferential
    {f : V → WithTop ℝ} {x : V} :
    ∂[dom f] f(x) = ∂ f(x) := by
  ext g
  -- Both owners record the same affine minorant condition on the effective domain of `f`.
  rw [mem_constrainedSubdifferential_iff, mem_subdifferential_iff, IsSubgradientAt]
  constructor
  · rintro ⟨hx, -, hminorant⟩
    exact ⟨hx, hminorant⟩
  · rintro ⟨hx, hminorant⟩
    exact ⟨hx, hx, hminorant⟩

/-- Helper for Lemma 3.13: a whole-space subgradient restricts to any smaller feasible set inside
the effective domain. -/
lemma mem_constrainedSubdifferential_of_mem_subdifferential
    {Q : Set V} {f : V → WithTop ℝ} {x g : V}
    (hg : g ∈ ∂ f(x)) (hxQ : x ∈ Q) (hQ : Q ⊆ dom f) :
    g ∈ ∂[Q] f(x) := by
  -- Restrict the global affine minorant to the smaller feasible set `Q`.
  rcases (mem_subdifferential_iff.mp hg) with ⟨hxDom, hminorant⟩
  exact mem_constrainedSubdifferential_iff.mpr
    ⟨hxQ, hQ hxQ, fun y hyQ ↦ hminorant (hQ hyQ)⟩

/-- Helper for Lemma 3.13: the convex hull of the active slice subdifferentials is contained in
the subdifferential of the finite `Set.univ` pointwise supremum. -/
lemma active_hull_subset_subdifferential_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ}
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    convexHull ℝ
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)} ⊆
      ∂ (pointwiseSupremumOn (Set.univ : Set ι) φ)(x) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let f : V → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
  have hxDom : x ∈ dom f := interior_subset hx
  have hxEff : x ∈ pointwiseSupremumOnEffectiveDomain (dom f) (Set.univ : Set ι) φ := by
    -- The owner effective domain over `dom f` is exactly `dom f` at the base point.
    exact ⟨hxDom, hxDom⟩
  have hpre :
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)} ⊆
        ⋃ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
          ∂[dom f] (fun y ↦ φ y i)(x) := by
    intro g hg
    rcases hg with ⟨i, hi, hgi⟩
    have hdom_subset : dom f ⊆ dom (fun y ↦ φ y i) := by
      intro y hy
      change φ y i < ⊤
      have hle : φ y i ≤ f y := by
        rw [show f y = pointwiseSupremumOn (Set.univ : Set ι) φ y by rfl, pointwiseSupremumOn_apply]
        exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
      exact lt_of_le_of_lt hle hy
    have hgi' : g ∈ ∂[dom f] (fun y ↦ φ y i)(x) := by
      -- Each whole-space slice subgradient is valid on the smaller common domain.
      exact mem_constrainedSubdifferential_of_mem_subdifferential hgi hxDom hdom_subset
    change g ∈ ⋃ j ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
        ∂[dom f] (fun y ↦ φ y j)(x)
    refine Set.mem_iUnion.2 ?_
    exact ⟨i, Set.mem_iUnion.2 ⟨hi, hgi'⟩⟩
  have howner :
      convexHull ℝ
          (⋃ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
            ∂[dom f] (fun y ↦ φ y i)(x)) ⊆
        ∂ f(x) := by
    -- This is exactly the owner inclusion on the common feasible set `dom f`.
    simpa [f, pointwiseSupremumOnEffectiveDomain, constrainedSubdifferential_dom_eq_subdifferential]
      using
        (convexHull_activePointwiseSupremumOnSubdifferentials_subset
          (Q := dom f) (Δ := (Set.univ : Set ι)) (φ := φ) (x := x) hxEff)
  exact Set.Subset.trans (convexHull_mono hpre) howner

/-- Lemma 3.13 (3): at an interior point of the effective domain of the nonempty finite
specialization of the pointwise supremum, the unconstrained subdifferential is the convex hull of
the union of the subdifferentials of the active slices. -/
-- Proof sketch: rewrite `hx` using `interior_dom_pointwiseSupremumOn_univ`, reduce activity to
-- `activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x`, and combine the standard active-slice
-- argument with the support-function identification for the convex hull of active
-- subdifferentials.
theorem subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun x ↦ φ x i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    ∂ (pointwiseSupremumOn (Set.univ : Set ι) φ)(x) =
      convexHull ℝ
        {g | ∃ i : ι,
            i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
              g ∈ ∂ (fun y ↦ φ y i)(x)} :=
  by
    apply Set.Subset.antisymm
    · -- Route correction: the easy inclusion is finished below, so the remaining blocker is the
      -- source-faithful reverse inclusion `∂ f(x) ⊆ convexHull(active slice subdifferentials)`.
      -- TODO: compare support pairings or directional derivatives without importing later Chapter 3
      -- results that add `[FiniteDimensional ℝ V]` or `[CompleteSpace V]` to the theorem header.
      sorry
    · -- The forward inclusion is the owner active-slice inclusion specialized to the common domain.
      exact active_hull_subset_subdifferential_pointwiseSupremumOn_univ (φ := φ) hx

end Subdifferential

end
