import Mathlib
import StacksProject_2024.Chap10.Definition_10_59_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Ideal

section

variable {R : Type u}
variable [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

namespace Ideal

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {I I' : Ideal R}

-- Proof sketch: since `I` and `I'` are ideals of definition, their radicals agree with the
-- maximal ideal, so mathlib's owner theorem `Ideal.exists_pow_le_of_le_radical_of_fg` gives a
-- power of `I'` contained in `I`. Then the quotient maps
-- `M / (I')^(c * (n + 1)) M → M / I^(n + 1) M`
-- compare the two `χ`-functions by surjectivity of the induced map on quotients. Rewriting
-- `c * (n + 1)` as `(2 * c - 1) * n + 1` for `n ≥ 1` gives the stated linear reindexing, with a
-- positive reindexing constant `a = 2 * c - 1`.
/-- Lemma 10.59.4: if `I` and `I'` are ideals of definition of the Noetherian local ring `R` and
`M` is a finite `R`-module, then the Hilbert-Samuel `χ`-function for `I` is eventually bounded
above by the Hilbert-Samuel `χ`-function for `I'` after multiplication by a positive integer. -/
theorem exists_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ a : ℕ, 0 < a ∧ ∀ ⦃n : ℕ⦄, 1 ≤ n →
      χ_ I M n ≤ χ_ I' M (a * n) := sorry

/-- Canonical `atTop` reformulation of Lemma 10.59.4: after multiplying the index by a fixed
positive integer, the Hilbert-Samuel `χ`-function for one ideal of definition is eventually
bounded above by that for the other. This is the bridge from the source-facing `n ≥ 1`
formulation to the chapter's eventual-value API. -/
theorem exists_eventually_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition) :
    ∃ a : ℕ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      χ_ I M n ≤ χ_ I' M (a * n) := by
  rcases exists_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition M hI hI' with
    ⟨a, ha, hle⟩
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hle hn

end Ideal

end
