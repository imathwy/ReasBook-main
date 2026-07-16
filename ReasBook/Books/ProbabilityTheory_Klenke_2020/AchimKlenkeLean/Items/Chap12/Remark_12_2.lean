import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {I : Type u} {Ω : Type v} {E : Type w}
variable {J : Type*}

variable [MeasurableSpace Ω] [MeasurableSpace E]

namespace IsExchangeable

variable {X : I → Ω → E} {μ : Measure Ω}

-- Proof sketch: this is exactly the defining permutation-invariance property of an exchangeable
-- family, applied to the chosen finite injective tuple `u` and permutation `σ`.
/-- An exchangeable family is invariant in law under every finite permutation of an injective
coordinate tuple. -/
theorem identDistrib_comp_perm (hX : IsExchangeable X μ) {n : ℕ} (u : Fin n ↪ I)
    (σ : Equiv.Perm (Fin n)) :
    IdentDistrib (fun ω i ↦ X (u (σ i)) ω) (fun ω i ↦ X (u i) ω) μ μ := sorry

-- Proof sketch: apply the characterization of exchangeability to the case `n = 1`, using the
-- unique embeddings `Fin 1 ↪ I` selecting the coordinates `i` and `j`.
/-- Every pair of coordinates in an exchangeable family is identically distributed. -/
theorem identDistrib (hX : IsExchangeable X μ) (i j : I) :
    IdentDistrib (X i) (X j) μ μ := sorry

-- Proof sketch: specialize exchangeability of `X` to the composite embedding `v.trans u`.
/-- Composing an exchangeable family with an injective reindexing preserves exchangeability. -/
theorem comp_embedding (hX : IsExchangeable X μ) (u : J ↪ I) :
    IsExchangeable (fun j ↦ X (u j)) μ := by
  intro n v σ
  simpa using hX (v.trans u) σ

end IsExchangeable

-- Proof sketch: to pass from permutation invariance to the injective-index formulation, reorder
-- the image of one embedding to the image of the other; conversely, specialize the injective case
-- to a tuple and its permuted version.
/-- Remark 12.2: a family is exchangeable if and only if for every `n` and every two injective
choices of `n` indices, the corresponding `n`-dimensional random vectors have the same law. -/
theorem isExchangeable_iff_identDistrib_of_pairwise_distinct (X : I → Ω → E)
    (μ : Measure Ω := by volume_tac) :
    IsExchangeable X μ ↔
      ∀ n, ∀ u v : Fin n ↪ I,
        IdentDistrib (fun ω i ↦ X (u i) ω) (fun ω i ↦ X (v i) ω) μ μ := sorry
