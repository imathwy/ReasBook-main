import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 21.9 is the Debrunner--Flor extension theorem with the literal domain
  bound `Atilde.dom ⊆ convexHull ℝ A.dom`.
- `core/canonical`: the extension owner remains `Maximal IsMonotone Atilde`, as in
  `exists_isMaximallyMonotone_extension`.
- `bridge/view`: the closure/nonempty variant supported by the current Chapter 21 development is
  recorded below as an explicit auxiliary fallback, not as the labeled source theorem. -/
/-- Theorem 21.9: if `A : H → 2^H` is monotone, then there exists a maximally monotone extension
`Atilde` of `A` such that `Atilde.dom ⊆ convexHull ℝ A.dom`, written with the canonical extension
relation `A ≤ Atilde`. -/
theorem exists_isMaximallyMonotone_extension_dom_subset_convexHull_dom
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) :
    ∃ Atilde ≥ A, Maximal IsMonotone Atilde ∧
      Atilde.dom ⊆ convexHull ℝ A.dom := sorry

/-- Auxiliary closure-level fallback for Theorem 21.9: if `A` is monotone with nonempty graph,
then there exists a maximally monotone extension `Atilde` of `A` such that
`Atilde.dom ⊆ closure (convexHull ℝ A.dom)`. -/
theorem exists_isMaximallyMonotone_extension_dom_subset_closure_convexHull_dom_of_graph_nonempty
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) :
    ∃ Atilde ≥ A, Maximal IsMonotone Atilde ∧
      Atilde.dom ⊆ closure (convexHull ℝ A.dom) := sorry

/-- Pointwise form of the auxiliary closure-level fallback: if `A` is monotone with nonempty
graph, then the chosen maximally monotone extension can be taken so that every point of
`Atilde.dom` lies in `closure (convexHull ℝ A.dom)`. -/
theorem exists_isMaximallyMonotone_extension_mem_closure_convexHull_dom_of_mem_dom_of_graph_nonempty
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) (hA_graph : (gra A).Nonempty) :
    ∃ Atilde ≥ A, Maximal IsMonotone Atilde ∧
      ∀ ⦃x : H⦄, x ∈ Atilde.dom → x ∈ closure (convexHull ℝ A.dom) := sorry

end SetValuedOperator
