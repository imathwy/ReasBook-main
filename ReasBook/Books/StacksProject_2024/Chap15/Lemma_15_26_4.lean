import Mathlib
import StacksProject_2024.Chap15.Lemma_15_26_3
import StacksProject_2024.Chap15.Lemma_15_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped FittingIdeal
open scoped AffineBlowupChart

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain-style sampling pass for Lemma 15.26.4.

Primary domain: commutative algebra of Fitting ideals, prime localizations, and affine blowup
strict transforms.

Sampled owner declarations:
* `Module.FiniteLocallyFreeOfRank` from `Chap10/Definition_10_78_1.lean`;
* `fittingIdeal_not_le_prime_tfae_residueField_finrank_and_local_generators` from
  `Chap15/Lemma_15_8_7.lean`;
* `finiteLocallyFreeOfRank_tfae_fittingIdeal_conditions` from `Chap15/Lemma_15_8_8.lean`;
* `fittingIdeal_affineBlowupStrictTransform_eq_top` from `Chap15/Lemma_15_26_3.lean`.

Owner abstraction: this item is `source-facing`. The conclusion should use the chapter owner
`Module.FiniteLocallyFreeOfRank` on the strict transform over the affine blowup chart
`R[Fit[R]_(k)(M) / a]`, while the primewise freeness assumption is theorem input data and should be
stated directly rather than packaged as a parallel local proposition.

Primitive data: the intrinsic ideal `Fit[R]_(k)(M)`, a chart element `a` in that ideal, and the
primewise rank-`k` freeness hypothesis for localizations away from the corresponding closed locus.
Derived API: the finite-locally-free-of-rank conclusion for the strict transform on the chart.

Source/core/bridge triage:
* `source-facing`: the strict-transform finite-locally-free statement below;
* `core/canonical`: `Fit[R]_(k)(M)`, `R[Fit[R]_(k)(M) / a]`,
  `affineBlowupStrictTransform`, and `Module.FiniteLocallyFreeOfRank`;
* `bridge/view`: the Fitting-ideal computations from Lemmas `15.8.8` and `15.26.3`, together with
  the prime-local freeness input.
-/

-- Proof sketch: Lemma `15.26.3` gives `Fit_k(M') = R'` for the strict transform `M'`. By Lemma
-- `15.8.8`, it remains to show `Fit_{k-1}(M') = 0`. After inverting `a`, the affine blowup chart
-- `R[Fit_k(M)/a]` becomes `R_a` by Lemma `10.70.2`, the strict transform becomes `M_a`, and
-- Fitting ideals commute with this base change by Lemma `15.8.4`. The hypothesis implies that
-- `M_a` is finite locally free of rank `k`, so Lemma `15.8.8` forces `Fit_{k-1}(M_a) = 0`, hence
-- also `Fit_{k-1}(M') = 0`.
/-- Lemma 15.26.4: let `I = Fit_k(M)`. If every localization `M_p` with `p ∉ V(I)` is free of
rank `k`, then for every `a ∈ I`, with `R' = R[I/a]`, the strict transform
`M' = (M ⊗[R] R')/(a`-power torsion)` is finite locally free of rank `k`. -/
theorem fittingIdealAffineBlowupStrictTransform_finiteLocallyFreeOfRank (k : ℕ)
    (a : Fit[R]_(k)(M))
    (hM :
      ∀ (p : Ideal R) [p.IsPrime] (_ : ¬ Fit[R]_(k)(M) ≤ p),
        Nonempty
          ((LocalizedModule.AtPrime p M) ≃ₗ[Localization.AtPrime p]
            (Fin k → Localization.AtPrime p))) :
    Module.FiniteLocallyFreeOfRank
      R[Fit[R]_(k)(M) / a] (affineBlowupStrictTransform (Fit[R]_(k)(M)) a M) k := sorry

end
