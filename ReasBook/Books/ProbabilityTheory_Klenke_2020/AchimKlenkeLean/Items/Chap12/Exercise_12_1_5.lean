import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {S : Type v}

variable [MeasurableSpace Ω] [MeasurableSpace S]

/-- A finite family `X : Fin n → Ω → S` admits an infinite exchangeable extension if it is the
initial segment of an infinite exchangeable sequence on the same probability space. -/
def HasInfiniteExchangeableExtension {n : ℕ} (X : Fin n → Ω → S) (μ : Measure Ω) : Prop :=
  ∃ Y : ℕ → Ω → S, IsExchangeable Y μ ∧ X = Y ∘ Fin.valEmbedding

-- Proof sketch: restrict an infinite exchangeable extension to its first `n` coordinates via the
-- chapter-owner reindexing lemma `IsExchangeable.comp_embedding`.
/-- Any finite family admitting an infinite exchangeable extension is exchangeable. -/
theorem HasInfiniteExchangeableExtension.isExchangeable {n : ℕ}
    {X : Fin n → Ω → S} {μ : Measure Ω} (hX : HasInfiniteExchangeableExtension X μ) :
    IsExchangeable X μ := by
  rcases hX with ⟨Y, hY, rfl⟩
  simpa using hY.comp_embedding Fin.valEmbedding

-- Proof sketch: use the classical sampling-without-replacement example, for instance the
-- indicators of the unique marked element in a uniformly chosen point of `Fin n`; this family is
-- exchangeable, but de Finetti's theorem rules out any infinite exchangeable extension when
-- `n ≥ 2`.
/-- Exercise 12.1.5: for every `n ≥ 2`, there exists an exchangeable family
`X₁, …, Xₙ` that does not extend to any infinite exchangeable sequence on the same probability
space. -/
theorem exists_exchangeable_family_without_infinite_extension {n : ℕ} (hn : 1 < n) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ)
      (X : Fin n → Ω → Bool),
      IsExchangeable X μ ∧ ¬ HasInfiniteExchangeableExtension X μ := sorry
