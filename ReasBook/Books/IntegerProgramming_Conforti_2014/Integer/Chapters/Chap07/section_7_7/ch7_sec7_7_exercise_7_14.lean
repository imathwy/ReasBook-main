import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9_part2

open scoped BigOperators

section Exercise714

/-- Exercise 7.14. Assume `λ` is the flow-cover excess determined by `∑_{j ∈ C} a_j = b + λ`
with `0 < λ`. If the zero-lifted flow-cover inequality `(7.14)` defines a facet of `conv(T)`,
then the necessary condition `λ < max_{j ∈ C} a_j` holds. The ambient single-node flow set and
the canonical flow-cover owners `flow_cover_value` and `flow_cover_face` are reused from
Theorem 7.9, with the explicit `λ` presentation recovered in Part 2 by
`flow_cover_value_eq_zero_lifted_value`. -/
theorem flow_cover_excess_lt_cover_max_of_facet_defining
    {n : ℕ} (b : ℝ) (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (hC : C.Nonempty)
    (hcover : Finset.sum C a = b + lam)
    (hlampos : 0 < lam)
    (hfacet : flow_cover_inequality_facet_defining a b C) :
    lam < C.sup' hC a := sorry

end Exercise714
