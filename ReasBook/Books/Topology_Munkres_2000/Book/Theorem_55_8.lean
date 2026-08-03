module

public import Topology_Munkres_2000.Book.Lemma_27_5
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Proposition_55_1

public section

open scoped CoveringDimension

/-- Helper for Theorem 55.8: the standard triangle is a bounded subset of the Euclidean
plane. -/
private lemma isBounded_standardTriangle : Bornology.IsBounded standardTriangle := by
  -- The coordinate inequalities place the triangle in a fixed Euclidean ball.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2, ?_⟩
  intro point hpoint
  rw [mem_standardTriangle] at hpoint
  rw [EuclideanSpace.norm_eq]
  have hcoord0 : point 0 ≤ 1 := by
    linarith [hpoint.2.2, hpoint.2.1]
  have hcoord1 : point 1 ≤ 1 := by
    linarith [hpoint.2.2, hpoint.1]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [abs_of_nonneg hpoint.1, abs_of_nonneg hpoint.2.1]
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [sq_nonneg (point 0), sq_nonneg (point 1)]

/-- Helper for Theorem 55.8: the standard triangle is compact. -/
private lemma isCompact_standardTriangle : IsCompact standardTriangle := by
  -- Each defining half-space is closed, and the preceding bound gives compactness.
  have hcoord0 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 0) := by
    fun_prop
  have hcoord1 : Continuous (fun point : EuclideanSpace ℝ (Fin 2) ↦ point 1) := by
    fun_prop
  have hclosed : IsClosed standardTriangle := by
    have htriangle : standardTriangle =
        {point | 0 ≤ point 0 ∧ 0 ≤ point 1 ∧ point 0 + point 1 ≤ 1} := by
      ext point
      exact mem_standardTriangle point
    rw [htriangle]
    exact (isClosed_le continuous_const hcoord0).inter
      ((isClosed_le continuous_const hcoord1).inter
        (isClosed_le (hcoord0.add hcoord1) continuous_const))
  exact Metric.isCompact_of_isClosed_isBounded hclosed isBounded_standardTriangle

/-- Helper for Theorem 55.8: failure of a covering-dimension bound is witnessed by an
open cover having no covering open refinement of the prescribed order. -/
private lemma existsOpenCoverWithoutOrderBound {X : Type*} [TopologicalSpace X] {n : ℕ}
    (hbound : ¬ HasCoveringDimensionLE X n) :
    ∃ 𝒸 : Set (Set X),
      (∀ U ∈ 𝒸, IsOpen U) ∧ ⋃₀ 𝒸 = Set.univ ∧
        ∀ 𝒝 : Set (Set X), IsOpenRefinement 𝒝 𝒸 → ⋃₀ 𝒝 = Set.univ →
          ¬ 𝒝.HasOrderLE (n + 1) := by
  classical
  -- Negating the open-cover characterization exposes the obstructing cover.
  rw [hasCoveringDimensionLE_iff] at hbound
  push Not at hbound
  exact hbound

/-- Helper for Theorem 55.8: deleting the empty member from a sufficiently small open
family produces an open refinement of a cover admitting that Lebesgue number. -/
private lemma nonemptyMembers_isOpenRefinement_of_diam_lt
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {𝒸 𝒞 : Set (Set X)} {δ : ℝ} (hδ : IsLebesgueNumber 𝒞 δ)
    (hopen : ∀ U ∈ 𝒸, IsOpen U) (hdiam : ∀ U ∈ 𝒸, Metric.diam U < δ) :
    IsOpenRefinement (𝒸 \ {∅}) 𝒞 := by
  -- Nonempty members satisfy every hypothesis in the Lebesgue-number interface.
  rw [isOpenRefinement_iff]
  constructor
  · rw [isRefinement_iff]
    intro U hU
    have hU_nonempty : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hU.2
    exact hδ.exists_superset hU_nonempty Metric.isBounded_of_compactSpace (hdiam U hU.1)
  · intro U hU
    exact hopen U hU.1

/-- Helper for Theorem 55.8: a subfamily of a family of order at most `n` also has order
at most `n`. -/
private lemma hasOrderLE_of_subset {X : Type*} {𝒸 𝒝 : Set (Set X)} {n : ℕ}
    (hsubset : 𝒝 ⊆ 𝒸) (horder : 𝒸.HasOrderLE n) : 𝒝.HasOrderLE n := by
  -- At each point, membership in the subfamily injects into membership in the family.
  rw [Set.hasOrderLE_iff] at horder ⊢
  intro point
  apply (Set.encard_le_encard ?_).trans (horder point)
  intro U hU
  exact ⟨hsubset hU.1, hU.2⟩

/-- Helper for Theorem 55.8: the standard triangle has no covering-dimension bound of
one. -/
private lemma standardTriangleNotHasCoveringDimensionLEOne :
    ¬ HasCoveringDimensionLE standardTriangle 1 := by
  -- Route correction: the canonical earlier proposition now exports the required lower bound.
  intro hbound
  have hupper : dim standardTriangle ≤ (1 : WithBot ℕ∞) :=
    (coveringDimension_le_iff standardTriangle 1).mpr hbound
  -- Composing the bounds would force the false numeral inequality `2 ≤ 1`.
  have himpossible : (2 : WithBot ℕ∞) ≤ 1 :=
    standardTriangle_two_le_coveringDimension.trans hupper
  norm_num at himpossible

/-- Theorem 55.8. There is an `ε > 0` such that every relative-open cover of
`standardTriangle` by sets of diameter less than `ε` contains a point belonging to at least
three distinct cover members. -/
theorem standardTriangle_openCover_threefold :
    ∃ ε > 0, ∀ 𝒜 : Set (Set standardTriangle),
      (∀ U ∈ 𝒜, IsOpen U) →
      ⋃₀ 𝒜 = Set.univ →
      (∀ U ∈ 𝒜, Metric.diam U < ε) →
      ∃ point : standardTriangle, 3 ≤ Set.encard {U ∈ 𝒜 | point ∈ U} := by
  classical
  -- Compactness and the dimension obstruction produce a cover with a positive Lebesgue number.
  letI : CompactSpace standardTriangle :=
    isCompact_iff_compactSpace.mp isCompact_standardTriangle
  obtain ⟨obstruction, hobstructionOpen, hobstructionCover, hobstructs⟩ :=
    existsOpenCoverWithoutOrderBound standardTriangleNotHasCoveringDimensionLEOne
  obtain ⟨ε, hε⟩ :=
    lebesgueNumberLemma obstruction hobstructionOpen hobstructionCover
  refine ⟨ε, hε.pos, ?_⟩
  intro family hopen hcover hdiam
  -- Absence of a threefold point makes the cover order two.
  by_contra hthreefold
  push Not at hthreefold
  have horder : family.HasOrderLE 2 := by
    rw [Set.hasOrderLE_iff]
    intro point
    have hpoint := hthreefold point
    have hthree : (3 : ℕ∞) = 2 + 1 := by
      norm_num
    rw [hthree] at hpoint
    exact (Order.lt_add_one_iff_of_not_isMax
      (not_isMax_iff_ne_top.mpr (ENat.coe_ne_top 2))).mp hpoint
  -- Removing the empty member preserves covering and order, while enabling refinement.
  have hrefines : IsOpenRefinement (family \ {∅}) obstruction :=
    nonemptyMembers_isOpenRefinement_of_diam_lt hε hopen hdiam
  have hnormalizedCover : ⋃₀ (family \ {∅}) = Set.univ := by
    rw [Set.sUnion_sdiff_singleton_empty, hcover]
  have hnormalizedOrder : (family \ {∅}).HasOrderLE 2 :=
    hasOrderLE_of_subset Set.sdiff_subset horder
  exact hobstructs (family \ {∅}) hrefines hnormalizedCover hnormalizedOrder

/-- Equivalently, sufficiently fine open covers of `standardTriangle` do not have order at most
two. -/
theorem standardTriangle_openCover_not_hasOrderLE_two :
    ∃ ε > 0, ∀ 𝒜 : Set (Set standardTriangle),
      (∀ U ∈ 𝒜, IsOpen U) →
      ⋃₀ 𝒜 = Set.univ →
      (∀ U ∈ 𝒜, Metric.diam U < ε) →
      ¬𝒜.HasOrderLE 2 := by
  obtain ⟨ε, hε, h_threefold⟩ := standardTriangle_openCover_threefold
  refine ⟨ε, hε, ?_⟩
  intro 𝒜 h_open h_cover h_diam h_order
  obtain ⟨point, h_point⟩ := h_threefold 𝒜 h_open h_cover h_diam
  have h_le := Set.hasOrderLE_iff.mp h_order point
  exact (not_lt_of_ge h_le) (lt_of_lt_of_le (by norm_num) h_point)

end
