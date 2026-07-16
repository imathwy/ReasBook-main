import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {E : Type v}
variable [MeasurableSpace Ω] [MeasurableSpace E]

namespace IsExchangeable

variable {X : ℕ → Ω → E} {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
private theorem aemeasurable_swap (hX : IsExchangeable X μ) :
    AEMeasurable (Function.swap X) μ := by
  refine aemeasurable_pi_lambda _ fun i ↦ ?_
  simpa [Function.swap] using (hX.identDistrib 0 i).aemeasurable_snd

-- Proof sketch: apply `isExchangeable_iff_identDistrib_of_pairwise_distinct` to obtain equality in
-- law of all finite injective coordinate restrictions, then use
-- `ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib`, whose owner-level
-- finite-dimensional-marginal characterization of process laws is available under
-- `[IsFiniteMeasure μ]`.
/-- An exchangeable sequence on a finite-measure space has the same law as each strictly
increasing subsequence. -/
theorem identDistrib_subsequence (hX : IsExchangeable X μ) (n : ℕ → ℕ) (hn : StrictMono n) :
    IdentDistrib (Function.swap X) (Function.swap (X ∘ n)) μ μ := by
  let hXn : IsExchangeable (X ∘ n) μ := hX.comp_embedding ⟨n, hn.injective⟩
  rw [identDistrib_iff_forall_finset_identDistrib hX.aemeasurable_swap hXn.aemeasurable_swap]
  intro s
  let e := s.orderIsoOfFin rfl
  let u : Fin s.card ↪ ℕ := (s.orderEmbOfFin rfl).toEmbedding
  let v : Fin s.card ↪ ℕ := ⟨fun i ↦ n (u i), hn.injective.comp u.injective⟩
  have h_tuple :
      IdentDistrib
        (fun ω ↦ fun i : Fin s.card ↦ X (u i) ω)
        (fun ω ↦ fun i : Fin s.card ↦ X (v i) ω) μ μ :=
    (isExchangeable_iff_identDistrib_of_pairwise_distinct X μ).mp hX _ u v
  let es : (Fin s.card → E) ≃ᵐ (s → E) := MeasurableEquiv.piCongrLeft (fun _ : s ↦ E) e
  have h_restrict := h_tuple.comp es.measurable
  have h_left :
      es ∘ (fun ω ↦ fun i : Fin s.card ↦ X (u i) ω) =
        fun ω ↦ s.restrict (Function.swap X ω) := by
    funext ω
    ext j
    let xu : (i : Fin s.card) → (fun _ : s ↦ E) (e i) := fun i ↦ X (u i) ω
    have h := Equiv.piCongrLeft_apply_apply (fun _ : s ↦ E) e xu (e.symm j)
    have hindex : u (e.symm j) = (j : ℕ) := by
      change (s.orderEmbOfFin rfl) ((s.orderIsoOfFin rfl).symm j) = (j : ℕ)
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp
    simpa [xu, es, MeasurableEquiv.piCongrLeft, e, Function.swap, Finset.restrict, hindex] using h
  have h_right :
      es ∘ (fun ω ↦ fun i : Fin s.card ↦ X (v i) ω) =
        fun ω ↦ s.restrict (Function.swap (X ∘ n) ω) := by
    funext ω
    ext j
    let xv : (i : Fin s.card) → (fun _ : s ↦ E) (e i) := fun i ↦ X (v i) ω
    have h := Equiv.piCongrLeft_apply_apply (fun _ : s ↦ E) e xv (e.symm j)
    have hindex : v (e.symm j) = n j := by
      change n ((s.orderEmbOfFin rfl) ((s.orderIsoOfFin rfl).symm j)) = n j
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp
    simpa [xv, es, MeasurableEquiv.piCongrLeft, e, Function.swap, Function.comp, Finset.restrict,
      hindex] using h
  simpa [h_left, h_right] using h_restrict

end IsExchangeable

-- Proof sketch: for the easy direction, every strictly increasing subsequence restricts on each
-- finite coordinate set to an injective tuple, so equality of sequence laws follows from
-- `IsExchangeable.identDistrib_subsequence`. For the converse, apply the subsequence hypothesis to
-- subsequences encoding any prescribed finite injective tuple of indices and recover the
-- finite-dimensional injective-tuple criterion for exchangeability; the process-law step again uses
-- `ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib`, so the canonical statement
-- carries the ambient `[IsFiniteMeasure μ]` hypothesis.
/-- Exercise 13.4.2: an `E`-valued sequence is exchangeable if and only if every strictly
increasing subsequence has the same law as the whole sequence-valued random variable on a
finite-measure space. This is the zero-based Lean version of the textbook statement
`(X₁, X₂, …) =ᵈ (X_{n₁}, X_{n₂}, …)` for every `1 ≤ n₁ < n₂ < ⋯`. -/
theorem isExchangeable_iff_identDistrib_subsequence {X : ℕ → Ω → E} {μ : Measure Ω}
    [IsFiniteMeasure μ] :
    IsExchangeable X μ ↔
      ∀ n : ℕ → ℕ, StrictMono n →
        IdentDistrib (Function.swap X) (Function.swap (X ∘ n)) μ μ := by
  refine ⟨fun hX n hn ↦ hX.identDistrib_subsequence n hn, ?_⟩
  sorry
