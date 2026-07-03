import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_20_21 (from Chap20) -/
universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.21 asserts existence of a maximally monotone extension of a given
  monotone set-valued operator.
- `core/canonical`: the owner abstraction is `Maximal IsMonotone Amax`, introduced in
  Definition 20.20.
- `bridge/view`: graph containment `gra A ⊆ gra Amax` is equivalent to the pointwise extension
  relation `A ≤ Amax`, so the public statement should stay on the order-theoretic owner layer. -/

-- Proof sketch: apply Zorn's lemma to the poset of monotone set-valued operators extending `A`,
-- ordered by the canonical pointwise relation `≤`. The hypothesis `hA` supplies a base point,
-- unions of chains remain monotone upper bounds, and Definition 20.20 identifies the resulting
-- maximal element as a maximally monotone extension of `A`.
/-- Theorem 20.21: every monotone set-valued operator on a real Hilbert space admits an extension
`Amax` with `A ≤ Amax` and `Maximal IsMonotone Amax`; equivalently, `gra A ⊆ gra Amax` and `Amax`
is maximally monotone. -/
theorem exists_isMaximallyMonotone_extension
    (A : SetValuedOperator H H) (hA : A.IsMonotone) :
    ∃ Amax ≥ A, Maximal IsMonotone Amax := sorry

end SetValuedOperator
