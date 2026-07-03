import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_34
import ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Ω : Type v}
variable {E : Type u} [MeasurableSpace E]

/-
Remark 12.9 is a `bridge/view` item. Its owner abstractions are the Chapter 2 tail
`σ`-algebra `tailRandomVariableMeasurableSpace` and the Chapter 12 exchangeable
`σ`-algebra `exchangeableSigmaAlgebra`. The main public bridge theorem is the generic
process-level inclusion, and the coordinate-sequence-space statement is kept as its canonical
specialization.
-/
-- Proof sketch: a tail event for `X` depends only on coordinates from some index onward, hence is
-- unchanged by every finite permutation of coordinates. Therefore each tail stage belongs to the
-- corresponding finite-exchangeable stage, and intersecting over all stages gives the owner-level
-- inclusion into the exchangeable `σ`-algebra of the sample-sequence map.
/-- Remark 12.9 (1): for any sequence of random variables `X`, the tail `σ`-algebra of `X` is
contained in the exchangeable `σ`-algebra of its sample-sequence map. -/
theorem tailRandomVariableMeasurableSpace_le_exchangeableSigmaAlgebra
    (X : ℕ → Ω → E) :
    tailRandomVariableMeasurableSpace X ≤ exchangeableSigmaAlgebra (Function.swap X) := sorry

-- Proof sketch: for each `n`, every event depending only on coordinates `n, n + 1, ...` is
-- unchanged by permutations of the first `n` coordinates, so the `n`th tail stage lies in the
-- `n`th symmetric stage from Definition 12.6; intersect over `n`.
/-- Remark 12.9 (1): on sequence space, the tail `σ`-algebra is contained in the exchangeable
`σ`-algebra. -/
theorem coordinateTailMeasurableSpace_le_exchangeableSequenceSigmaAlgebra :
    tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E) ≤
      exchangeableSequenceSigmaAlgebra := by
  simpa [exchangeableSigmaAlgebra, Function.swap] using
    tailRandomVariableMeasurableSpace_le_exchangeableSigmaAlgebra
      (Function.eval : ℕ → (ℕ → E) → E)

-- Proof sketch: on `Bool`-valued sequence space, the event that there is exactly one `true`
-- coordinate is measurable and invariant under every finite permutation, so it belongs to the
-- exchangeable `σ`-algebra; it is not tail-measurable because changing finitely many coordinates
-- can create or destroy that property while leaving the tail fixed.
/-- Remark 12.9 (2): for `Bool`-valued sequences, the inclusion of the tail `σ`-algebra into the
exchangeable `σ`-algebra can be strict. -/
theorem coordinateTailMeasurableSpace_lt_exchangeableSequenceSigmaAlgebra_bool :
    tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → Bool) → Bool) <
      exchangeableSequenceSigmaAlgebra := sorry
