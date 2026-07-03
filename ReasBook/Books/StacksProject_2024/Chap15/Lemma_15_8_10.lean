import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap15.Definition_15_8_3
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped FittingIdeal

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-
Domain-style sampling for Lemma 15.8.10:
- primary domain: finitely presented modules over a commutative ring, Fitting ideals, principal
  ideals, torsion-by-an-element submodules, and projective-dimension bounds;
- sampled owner-level declarations:
  `Fit[R]_(k)(M)`,
  `precedingFittingIdeal`,
  `principalIdeal`,
  `Submodule.torsionBy`,
  `Module.FiniteLocallyFreeOfRank`,
  `HasProjectiveDimensionLE`,
  `lequivProdOfRightSplitExact`;
- best owner abstraction: the source-facing lemma should be organized around the intrinsic Fitting
  ideal owner `Fit[R]_(k)(M)` together with the chapter owner `principalIdeal f`; the torsion,
  finite-locally-free, and projective-dimension conclusions are derived through the canonical
  owners `Submodule.torsionBy`, `Module.FiniteLocallyFreeOfRank`, and
  `HasProjectiveDimensionLE`; for the final splitting clause, the chosen linear equivalence is a
  source-facing existence statement whose core split-exact owner is
  `lequivProdOfRightSplitExact`;
- primitive data: the finitely presented module `M`, the index `k`, the nonzerodivisor `f`, the
  intrinsic principal Fitting-ideal equality, and the preceding-Fitting-ideal vanishing;
- derived API: the projective-dimension, torsion-identification, finite-locally-free quotient, and
  noncanonical product-splitting conclusions.

Source/core/bridge triage:
- `source-facing`: the five assertions of Lemma `15.8.10`;
- `core/canonical`: `Fit[R]_(k)(M)`, `precedingFittingIdeal`, `principalIdeal`,
  `Submodule.torsionBy`, `Module.FiniteLocallyFreeOfRank`, `HasProjectiveDimensionLE`, and
  `lequivProdOfRightSplitExact`;
- `bridge/view`: the source notation `M[f^n]` and `M[f^∞]` from Definition `15.89.1`, together
  with the final nonempty linear-equivalence splitting statement; the source `f`-power-torsion
  submodule is stated below through the canonical owner
  `Submodule.torsion' R M (Submonoid.powers f)`. -/

section

variable {k : ℕ} {f : R}
variable (hf : f ∈ nonZeroDivisors R)
variable (hfitk : Fit[R]_(k)(M) = principalIdeal f)
variable (hprecedingFitk : precedingFittingIdeal R M k = ⊥)

-- Proof sketch: choose a finite free presentation of `M`, localize at each prime, and apply the
-- local argument of the Stacks Project proof together with the local-to-global criterion for
-- projective dimension at most `1`.
/-- Lemma 15.8.10 (1): if `Fit_k(M) = (f)` with `f` a nonzerodivisor and `Fit_{k-1}(M) = 0`
using the chapter convention `Fit_{-1}(M) = 0`, then `M` has projective dimension at most `1`. -/
theorem hasProjectiveDimensionLE_one_of_fittingIdeal_eq_principalIdeal :
    HasProjectiveDimensionLE (ModuleCat.of R M) 1 := sorry

-- Proof sketch: the local case identifies the kernel of multiplication by `f` with the
-- `f`-power-torsion part; then equality of submodules is checked after localization and descended
-- back to `R`.
/-- Lemma 15.8.10 (2): under the same hypotheses, the kernel of multiplication by `f` on `M` is
the `f`-power torsion submodule of `M`. -/
theorem fPowerTorsion_eq_torsionBy_of_fittingIdeal_eq_principalIdeal :
    Submodule.torsion' R M (Submonoid.powers f) = Submodule.torsionBy R M f := sorry

-- Proof sketch: use part (1) on the local splitting and the short exact sequence
-- `0 → Submodule.torsionBy R M f → M → M / Submodule.torsionBy R M f → 0`, then descend the
-- bound from localizations to the global module.
/-- Lemma 15.8.10 (3): under the same hypotheses, the `f`-torsion submodule of `M` has projective
dimension at most `1`. -/
theorem torsionBy_hasProjectiveDimensionLE_one_of_fittingIdeal_eq_principalIdeal :
    HasProjectiveDimensionLE (ModuleCat.of R (Submodule.torsionBy R M f)) 1 := sorry

-- Proof sketch: localize at each prime, apply the local normal-form argument to see that the
-- quotient by the `f`-torsion is free of rank `k`, and then use the definition of finite locally
-- free of rank.
/-- Lemma 15.8.10 (4): under the same hypotheses, the quotient of `M` by its `f`-torsion
submodule is finite locally free of rank `k`. -/
theorem quotient_torsionBy_finiteLocallyFreeOfRank_of_fittingIdeal_eq_principalIdeal :
    Module.FiniteLocallyFreeOfRank R (M ⧸ Submodule.torsionBy R M f) k := sorry

-- Proof sketch: once the quotient is finite locally free, it is projective, so the short exact
-- sequence `0 → Submodule.torsionBy R M f → M → M / Submodule.torsionBy R M f → 0` admits a
-- section; applying the canonical split-exact product owner `lequivProdOfRightSplitExact` then
-- yields the required source-facing direct-sum decomposition.
/-- Lemma 15.8.10 (5): under the same hypotheses, `M` splits as the direct sum of its quotient by
the `f`-torsion submodule and the `f`-torsion submodule. -/
theorem nonempty_linearEquiv_quotient_torsionBy_prod_of_fittingIdeal_eq_principalIdeal :
    Nonempty (M ≃ₗ[R] (M ⧸ Submodule.torsionBy R M f) × Submodule.torsionBy R M f) := sorry

end

end
