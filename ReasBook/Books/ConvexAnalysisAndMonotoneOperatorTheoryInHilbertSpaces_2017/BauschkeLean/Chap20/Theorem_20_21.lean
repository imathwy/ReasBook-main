import Mathlib
import BauschkeLean.Chap01.Fact_1_1
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

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
    ∃ Amax ≥ A, Maximal IsMonotone Amax := by
  let Ext : Type u := {B : SetValuedOperator H H // B.IsMonotone ∧ A ≤ B}
  let base : Ext := ⟨A, ⟨hA, le_rfl⟩⟩
  -- Every chain of monotone extensions has a pointwise-union upper bound, with the empty-chain
  -- case handled by the base extension `A` itself.
  have hChainHasUpperBound :
      ∀ c : Set Ext, IsChain (fun B C : Ext ↦ B ≤ C) c → BddAbove c := by
    intro c hc
    by_cases hne : c.Nonempty
    · let U : SetValuedOperator H H :=
          fun x ↦ {u | ∃ B : Ext, B ∈ c ∧ u ∈ (B : SetValuedOperator H H) x}
      have hmemU :
          ∀ x u, u ∈ U x ↔ ∃ B : Ext, B ∈ c ∧ u ∈ (B : SetValuedOperator H H) x := by
        intro x u
        rfl
      -- Chain comparability moves both graph points into a single monotone extension.
      have hUmono : U.IsMonotone := by
        rw [SetValuedOperator.isMonotone_iff]
        intro x u y v hu hv
        rcases (hmemU x u).1 hu with ⟨B, hBc, huB⟩
        rcases (hmemU y v).1 hv with ⟨C, hCc, hvC⟩
        rcases hc.total hBc hCc with hBC | hCB
        · exact (SetValuedOperator.isMonotone_iff (A := (C : SetValuedOperator H H))).1 C.2.1
            (hBC x huB) hvC
        · exact (SetValuedOperator.isMonotone_iff (A := (B : SetValuedOperator H H))).1 B.2.1
            huB (hCB y hvC)
      -- Any chain member already extends `A`, so one chosen member witnesses `A ≤ U`.
      have hAU : A ≤ U := by
        intro x u hu
        rcases hne with ⟨B, hBc⟩
        exact (hmemU x u).2 ⟨B, hBc, B.2.2 x hu⟩
      have hUpperData : U.IsMonotone ∧ A ≤ U := ⟨hUmono, hAU⟩
      let upper : Ext := ⟨U, hUpperData⟩
      refine ⟨upper, ?_⟩
      intro B hBc
      intro x u hu
      exact (hmemU x u).2 ⟨B, hBc, hu⟩
    · refine ⟨base, ?_⟩
      intro B hBc
      exact (hne ⟨B, hBc⟩).elim
  -- Zorn now supplies a maximal monotone extension in the subtype of all extensions of `A`.
  obtain ⟨m, hm⟩ := fact_1_1 hChainHasUpperBound
  have hmTrue : Maximal (fun _ : Ext ↦ True) m := by
    simpa using (maximal_true (x := m)).2 hm
  have hmExt : Maximal (fun B : SetValuedOperator H H ↦ B.IsMonotone ∧ A ≤ B) m.1 := by
    simpa [Ext] using (maximal_true_subtype (x := m)).1 hmTrue
  have hAm : A ≤ m.1 := hmExt.1.2
  -- Any monotone super-operator of `m` still extends `A`, so subtype maximality upgrades to the
  -- desired maximality among all monotone operators.
  refine ⟨m.1, hAm, ?_⟩
  refine ⟨hmExt.1.1, ?_⟩
  intro B hB hmB
  exact hmExt.2 ⟨hB, le_trans hAm hmB⟩ hmB

end SetValuedOperator
