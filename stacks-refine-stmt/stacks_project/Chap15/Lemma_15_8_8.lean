import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_78_1
import Mathlib.RingTheory.Localization.Away.Basic
import stacks_project.Chap15.Definition_15_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FittingIdeal

universe u v

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

section

variable [Module.Finite R M]

-- Proof sketch: clause (2) is equivalent to clause (3) because Fitting ideals form an increasing
-- sequence. For `(1) → (2)`, localize on a standard-open cover on which `M` is free of rank `r`,
-- use the explicit computation of Fitting ideals for a free module, and descend the equalities by
-- base change. For `(2) → (1)`, use the local generation criterion coming from the previous lemma
-- to reduce locally to a presentation by `r` generators; the vanishing of `Fit_{r-1}(M)` then
-- forces the presentation matrix to vanish, so the localized module is free of rank `r`.
/-- Lemma 15.8.8: for a finite `R`-module `M` and `r : ℕ`, the following are equivalent: `M` is
finite locally free of rank `r`; `Fit_{r-1}(M) = 0` (with the convention `Fit_{-1}(M) = 0`) and
`Fit_r(M) = R`; and `Fit_k(M) = 0` for `k < r` while `Fit_k(M) = R` for `k ≥ r`. -/
theorem finiteLocallyFreeOfRank_tfae_fittingIdeal_conditions (r : ℕ) :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M r
      , precedingFittingIdeal R M r = ⊥ ∧ Fit[R]_(r)(M) = ⊤
      , (∀ k, k < r → Fit[R]_(k)(M) = ⊥) ∧ ∀ k, r ≤ k → Fit[R]_(k)(M) = ⊤
      ] := sorry

end

end
