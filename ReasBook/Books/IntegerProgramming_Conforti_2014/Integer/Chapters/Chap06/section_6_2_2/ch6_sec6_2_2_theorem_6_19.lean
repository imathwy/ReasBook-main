import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

section Theorem619

variable {p : ℕ}

/-- Theorem 6.19. Any full-dimensional maximal lattice-free convex set `K ⊆ ℝ^p` has at most
`2^p` facets. -/
theorem maximal_lattice_free_facets_encard_le_two_pow
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.encard ≤ (2 ^ p : ℕ∞) := sorry

/-- A full-dimensional maximal lattice-free convex set has only finitely many facets. -/
theorem maximal_lattice_free_facets_finite
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.Finite :=
  Set.finite_of_encard_le_coe (maximal_lattice_free_facets_encard_le_two_pow hfull hK)

/-- Theorem 6.19 in finite-cardinality form: a full-dimensional maximal lattice-free convex set
has at most `2^p` facets. -/
theorem maximal_lattice_free_facets_ncard_le_two_pow
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    {F : Set (Fin p → ℝ) | IsFacetOf K F}.ncard ≤ 2 ^ p :=
  (Set.encard_le_coe_iff_finite_ncard_le.mp
    (maximal_lattice_free_facets_encard_le_two_pow hfull hK)).2

end Theorem619
