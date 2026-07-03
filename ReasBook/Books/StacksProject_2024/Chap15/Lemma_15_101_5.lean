import Mathlib
import StacksProject_2024.Chap15.Lemma_15_101_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Domain-style sampling for Lemma 15.101.5:
- primary domain: `I`-adic completion of finite modules, controlled by the inverse system of
  quotient-stage linear isomorphisms;
- sampled owner declarations:
  `moduleIsomorphismStage`,
  `moduleIsomorphismTower`,
  `moduleIsomorphismTower_isMittagLeffler`,
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- best owner abstraction: the source-facing hypothesis is stagewise existence of quotient
  isomorphisms, but the canonical project owner for those stages is `moduleIsomorphismStage I M N`
  from Lemma `15.101.4`; the completed comparison is likewise already owned there by
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- primitive data: the ideal `I` and the finite `A`-modules `M`, `N`;
- derived API: the quotient-stage isomorphism tower and the resulting completed linear
  equivalence.

Source/core/bridge triage:
- `source-facing`: the existence theorem below, matching the Stacks-project statement that
  stagewise quotient isomorphisms force an isomorphism of completions;
- `core/canonical`: `moduleIsomorphismStage`, `moduleIsomorphismTower`, and
  `limit_moduleIsomorphismTower_iso_completedLinearEquiv`;
- `bridge/view`: the indexing convention relating the source quotient `M / I^n M` for `n > 0` to
  stage `n - 1` of `moduleIsomorphismStage`. -/

universe u v w

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]

-- Proof sketch: `moduleIsomorphismTower_isMittagLeffler` supplies the canonical Mittag-Leffler
-- owner for the quotient-isomorphism tower, and
-- `limit_moduleIsomorphismTower_iso_completedLinearEquiv` identifies its inverse limit with the
-- type of completed linear equivalences. The source-facing assumption below is written directly in
-- terms of the owner stage `moduleIsomorphismStage`, where stage `n` encodes the textbook quotient
-- by `I^(n + 1)`.
/-- Lemma 15.101.5: if for every `n : ℕ` the quotient modules
`M / I^(n + 1) M` and `N / I^(n + 1) N` are `A`-linearly isomorphic, then the `I`-adic
completions `M^` and `N^` are linearly isomorphic over the completed ring `A^`. -/
theorem nonempty_completedLinearEquiv_of_quotientLinearEquiv
    (h : ∀ n : ℕ, Nonempty (moduleIsomorphismStage I M N n)) :
    Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := sorry
