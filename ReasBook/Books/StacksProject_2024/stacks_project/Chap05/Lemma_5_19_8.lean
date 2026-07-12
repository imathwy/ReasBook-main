import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling for Lemma 5.19.8:
- primary domain: quotient maps and specialization/generalization lifting in topology
- owner declarations inspected: `IsOpenQuotientMap`, `GeneralizingMap`, `Setoid.ker`, and
  `Topology.IsQuotientMap.homeomorph`
- best owner abstraction: the quotient relation is canonically owned by `Setoid.ker π`, and the
  quotient space itself is canonically owned by `Quotient (Setoid.ker π)` together with
  `Topology.IsQuotientMap.homeomorph`
- primitive data: finite `s`-fibres, the two generalizing-map hypotheses, and the source relation
  identified directly with `Setoid.ker π`
- derived API: first the `T₀` conclusion on the canonical kernel quotient, then the source-facing
  `T₀` conclusion on `X`

Layer triage:
- `source-facing`: the finite-fibre relation criterion implying `T0Space X`
- `core/canonical`: `GeneralizingMap`, `Setoid.ker`, `Quotient (Setoid.ker π)`,
  `Topology.IsQuotientMap.homeomorph`
- `bridge/view`: the explicit source relation `∃ r, t r = u ∧ s r = v`, kept only inline as the
  source-facing description of the canonical kernel relation

Refinement choice:
- keep the kernel quotient as the core owner theorem and derive the original `X`-statement from the
  quotient-map homeomorphism, instead of treating `X` as the primitive owner
- keep the textbook relation directly in the hypothesis that bridges it to `Setoid.ker π`
-/

section QuotientKer

variable {R : Type u} {U : Type v} {X : Type w}
variable [TopologicalSpace R] [TopologicalSpace U] [T0Space U] [QuasiSober U]
variable (s t : R → U) (π : U → X)

-- Proof sketch: identify the source-facing relation `(u, v) ↦ ∃ r, t r = u ∧ s r = v` with the
-- canonical kernel relation `Setoid.ker π`. This gives the owner-level `T₀` theorem for the
-- canonical quotient `Quotient (Setoid.ker π)`, and the original statement on `X` is then its
-- quotient-map homeomorphism bridge.
/-- Canonical quotient-owner form of Lemma 5.19.8: under the finite-fibre relation criterion, the
kernel quotient `Quotient (Setoid.ker π)` is Kolmogorov. -/
theorem t0Space_quotient_ker_of_quasiSober_of_finiteFibers
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hs_gen : GeneralizingMap s) (ht_gen : GeneralizingMap t)
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v) :
    T0Space (Quotient (Setoid.ker π)) := sorry

end QuotientKer

section

variable {R : Type u} {U : Type v} {X : Type w}
variable [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X]
variable [T0Space U] [QuasiSober U]
variable (s t : R → U) (π : U → X)

/-- Lemma 5.19.8, source-facing bridge: let `π : U → X` be an open quotient map with `U`
quasi-sober and `T₀`. Assume the source-facing relation `(u, v) ↦ ∃ r, t r = u ∧ s r = v`
agrees with `Setoid.ker π`, the fibres of `s` are finite, and generalizations lift along both
`s` and `t`. Then `X` is Kolmogorov. -/
theorem t0Space_of_open_quotient_of_quasiSober_of_finiteFibers
    (hπ_openQuot : IsOpenQuotientMap π)
    (hs_finite : ∀ u : U, Set.Finite (s ⁻¹' ({u} : Set U)))
    (hs_gen : GeneralizingMap s) (ht_gen : GeneralizingMap t)
    (hπ_quot : ∀ u v : U, Setoid.ker π u v ↔ ∃ r : R, t r = u ∧ s r = v) :
    T0Space X := by
  letI :=
    t0Space_quotient_ker_of_quasiSober_of_finiteFibers s t π hs_finite hs_gen ht_gen hπ_quot
  let πc : C(U, X) := ⟨π, hπ_openQuot.continuous⟩
  have hπc : Topology.IsQuotientMap πc := hπ_openQuot.isQuotientMap
  exact hπc.homeomorph.t0Space

end
