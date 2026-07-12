import StacksProject_2024.Chap10.Lemma_10_24_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/-
Lemma 10.24.2 is a `source-facing` specialization in the localization-glueing exactness domain.
The owner abstraction is `away_localization_glueing_exact`; the primitive data remain
`awayLocalizationFamilyMap` and `awayLocalizationCompatibilityMap`, and this file keeps only the
ring case `M = R` rather than introducing a parallel owner wrapper.
-/

-- Proof sketch: this is the ring case of Lemma `10.24.1`, specialized to the module `M = R`.
/-- Lemma 10.24.2: if the finite family `f : Fin n → R` generates the unit ideal, then the
sequence `0 → R → ∏ i, R_(f_i) → ∏ i j, R_(f_i f_j)` with `α(x) = (x/1)_i` and
`β((x_i)_i) = (x_i|_(f_i f_j) - x_j|_(f_i f_j))_(i,j)` is exact. This is the specialization of
Lemma `10.24.1` to the `R`-module `R`, using the canonical family and compatibility maps from that
owner theorem; as in the source, the direct-sum sequence is written here using finite products. -/
@[stacks 00EJ]
theorem ring_localization_away_glueing_exact
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (awayLocalizationFamilyMap R f) ∧
      Function.Exact (awayLocalizationFamilyMap R f) (awayLocalizationCompatibilityMap R f) := by
  simpa using away_localization_glueing_exact R f hf

end
