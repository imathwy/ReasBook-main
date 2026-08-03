module

public import Topology_Munkres_2000.Book.Exercise_16_9
public import Mathlib.Topology.Metrizable.Basic

public section

open Filter Prod.Lex

/-- Helper for Exercise 20.2: a same-fiber lexicographic interval is exactly a vertical open
interval. -/
lemma realProdLex_Ioo_same_fst (x a b : ℝ) :
    Set.Ioo (toLex (x, a)) (toLex (x, b)) =
      {q : ℝ ×ₗ ℝ | (ofLex q).1 = x ∧ (ofLex q).2 ∈ Set.Ioo a b} := by
  -- Expand both lexicographic inequalities and eliminate impossible first-coordinate cases.
  ext q
  simp only [Set.mem_Ioo, Prod.Lex.lt_iff, Set.mem_setOf_eq, ofLex_toLex]
  constructor
  · rintro ⟨ha | ⟨hx, ha⟩, hb | ⟨hx', hb⟩⟩
    · exact (lt_asymm ha hb).elim
    · subst hx'
      exact (lt_irrefl _ ha).elim
    · subst hx
      exact (lt_irrefl _ hb).elim
    · subst hx
      exact ⟨rfl, ha, hb⟩
  · rintro ⟨hx, ha, hb⟩
    subst hx
    exact ⟨Or.inr ⟨rfl, ha⟩, Or.inr ⟨rfl, hb⟩⟩

/-- Helper for Exercise 20.2: the preimage of a vertical interval under the canonical coordinate
map has the expected same-fiber description. -/
lemma realProdLex_preimage_verticalInterval (p : ℝ ×ₗ ℝ) (a b : ℝ) :
    (fun q : ℝ ×ₗ ℝ ↦
      (WithTopology.toTopology (⊥ : TopologicalSpace ℝ) (ofLex q).1, (ofLex q).2)) ⁻¹'
        ({WithTopology.toTopology (⊥ : TopologicalSpace ℝ) (ofLex p).1} ×ˢ Set.Ioo a b) =
      {q : ℝ ×ₗ ℝ | (ofLex q).1 = (ofLex p).1 ∧ (ofLex q).2 ∈ Set.Ioo a b} := by
  -- Membership in the singleton first coordinate reduces to equality before wrapping.
  ext q
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Ioo,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨congrArg WithTopology.ofTopology hfirst, hsecond⟩
  · rintro ⟨hfirst, hsecond⟩
    exact ⟨congrArg (WithTopology.toTopology (⊥ : TopologicalSpace ℝ)) hfirst, hsecond⟩

/-- Helper for Exercise 20.2: vertical intervals form a neighborhood basis in the
lexicographic real plane. -/
lemma realProdLex_nhds_basis_verticalIntervals (p : ℝ ×ₗ ℝ) :
    (nhds p).HasBasis
      (fun ab : ℝ × ℝ ↦ ab.1 < (ofLex p).2 ∧ (ofLex p).2 < ab.2)
      (fun ab ↦ {q : ℝ ×ₗ ℝ |
        (ofLex q).1 = (ofLex p).1 ∧ (ofLex q).2 ∈ Set.Ioo ab.1 ab.2}) := by
  -- Refine the order-topology interval basis to endpoints in the fiber of `p`.
  letI : OrderTopology (ℝ ×ₗ ℝ) := ⟨rfl⟩
  refine (nhds_basis_Ioo p).to_hasBasis ?_ ?_
  · rintro ⟨lower, upper⟩ ⟨hlower, hupper⟩
    obtain ⟨a, b, ha, hb, hlower', hupper'⟩ :=
      RealPlaneTopology.exists_sameFiber_Ioo_subset hlower hupper
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    rw [← realProdLex_Ioo_same_fst (ofLex p).1 a b]
    exact Set.Ioo_subset_Ioo hlower'.le hupper'.le
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨(toLex ((ofLex p).1, a), toLex ((ofLex p).1, b)), ?_, ?_⟩
    · exact ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, ha⟩),
        Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hb⟩)⟩
    · rw [realProdLex_Ioo_same_fst]

/-- Helper for Exercise 20.2: vertical intervals form a neighborhood basis in the product of
a discrete real line with the standard real line. -/
lemma discreteRealProd_nhds_basis_verticalIntervals (p : WithDiscreteTopology ℝ × ℝ) :
    (nhds p).HasBasis
      (fun ab : ℝ × ℝ ↦ ab.1 < p.2 ∧ p.2 < ab.2)
      (fun ab ↦ {p.1} ×ˢ Set.Ioo ab.1 ab.2) := by
  -- The first-coordinate neighborhood filter is pure, while the second has interval basis.
  rw [nhds_prod_eq, nhds_discrete]
  refine ((Filter.hasBasis_pure p.1).prod (nhds_basis_Ioo p.2)).to_hasBasis ?_ ?_
  · rintro ⟨u, ⟨a, b⟩⟩ ⟨-, ha, hb⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Set.Subset.rfl⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨((), (a, b)), ⟨trivial, ha, hb⟩, Set.Subset.rfl⟩

/-- Helper for Exercise 20.2: the lexicographic real plane embeds in the product of a discrete
real line with the standard real line. -/
lemma realProdLex_isEmbedding_discreteProduct :
    Topology.IsEmbedding
      (fun p : ℝ ×ₗ ℝ ↦
        (WithTopology.toTopology (⊥ : TopologicalSpace ℝ) (ofLex p).1, (ofLex p).2)) := by
  -- The neighborhood bases show that the coordinate map is inducing.
  refine Topology.IsEmbedding.mk (Topology.isInducing_iff_nhds.mpr ?_) ?_
  · intro p
    refine (realProdLex_nhds_basis_verticalIntervals p).eq_of_same_basis ?_
    simpa only [realProdLex_preimage_verticalInterval] using
      ((discreteRealProd_nhds_basis_verticalIntervals
        (WithTopology.toTopology (⊥ : TopologicalSpace ℝ) (ofLex p).1, (ofLex p).2)).comap
          (fun q : ℝ ×ₗ ℝ ↦
            (WithTopology.toTopology (⊥ : TopologicalSpace ℝ) (ofLex q).1, (ofLex q).2)))
  · -- Equality of image coordinates recovers the original lexicographic pair.
    intro p q hpq
    apply ofLex.injective
    apply Prod.ext
    · exact congrArg WithTopology.ofTopology (congrArg (fun z ↦ z.1) hpq)
    · exact congrArg (fun z ↦ z.2) hpq

/-- Exercise 20.2: The real plane with the dictionary order topology is metrizable. -/
instance realProdLexMetrizableSpace : TopologicalSpace.MetrizableSpace (ℝ ×ₗ ℝ) := by
  -- Pull back the standard product metrizable structure along the canonical embedding.
  exact realProdLex_isEmbedding_discreteProduct.metrizableSpace
