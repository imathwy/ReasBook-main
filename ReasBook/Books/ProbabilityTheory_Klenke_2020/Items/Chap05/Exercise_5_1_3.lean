import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
variable (hX_iid : IsIID (fun n ↦ X (n + 1)) P)

-- Proof sketch: `ProbabilityTheory.strong_law_ae_real` is the canonical strong-law owner for
-- integrable i.i.d. real random variables. Applied to `fun n ↦ X (n + 1)`, it gives almost-sure
-- convergence of the Cesaro averages to `P[X 1]`; subtracting this from the strong law for the
-- constant sequence `fun _ _ ↦ P[X 1]` yields `X (n + 1) / (n + 1) → 0` almost surely, so the
-- `EReal` limsup is `0`. Thus the textbook nonnegativity assumption is redundant for this
-- consequence and is omitted from the Lean interface.
/-- Exercise 5.1.3 (1): the source-facing limsup conclusion is a canonical consequence of the
strong law for integrable i.i.d. real random variables, so the normalized sequence `Xₙ / n`,
represented in Lean by the terms `X 1 / 1, X 2 / 2, …`, has almost-sure limsup `0` without any
extra nonnegativity hypothesis. -/
theorem ae_limsup_normalized_iid_eq_zero_of_integrable
    (hX1_integrable : Integrable (X 1) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop = 0 := sorry

-- Proof sketch: for every `M > 0`, consider the events
-- `{ω | X (n + 1) ω / (n + 1) ≥ M}`. The tail
-- expectation criterion for nonnegative random variables together with identical distribution
-- gives divergence of the probability series, equivalently `¬ Integrable (X 1) P` under the
-- source-facing hypothesis `0 ≤ᵐ[P] X 1`. Since `hX_iid : IsIID (fun n ↦ X (n + 1)) P`, this
-- one-coordinate nonnegativity propagates to every `X (n + 1)` via `hX_iid.identDistrib n 0`.
-- Independence then lets the second Borel-Cantelli lemma force these events to occur infinitely
-- often almost surely. Then let `M → ∞`.
/-- Exercise 5.1.3 (2): For i.i.d. nonnegative real random variables with infinite nonnegative
expectation, it is enough to assume the source-facing condition `0 ≤ᵐ[P] X 1`, since the
chapter's canonical i.i.d. abstraction `IsIID (fun n ↦ X (n + 1)) P` propagates this to every
coordinate. Then the normalized sequence `Xₙ / n`, represented in Lean by the terms
`X 1 / 1, X 2 / 2, …`, has almost-sure limsup `⊤`. -/
theorem ae_limsup_normalized_iid_nonnegative_eq_top_of_not_integrable
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_not_integrable : ¬ Integrable (X 1) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ (((X (n + 1) ω) / (n + 1 : ℝ)) : EReal)) atTop = ⊤ := sorry
