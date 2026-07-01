import Mathlib
import stacks_project.Chap15.Lemma_15_125_1
import stacks_project.Chap15.Lemma_15_125_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe u v

/-
Domain-style sampling:
- primary domain: local-global decomposition of finitely presented modules into finite direct sums
  of principal quotient modules over generalized valuation rings;
- sampled owner declarations:
  `PreValuationRing`,
  `principalIdeal`,
  `finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients`,
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact`;
- best owner abstraction: this item is `source-facing`, not a new core owner. The ambient
  generalized valuation-ring hypothesis should be expressed through the canonical owner
  `PreValuationRing`, and the cyclic summands should reuse the chapter owner `principalIdeal`;
- primitive data vs. derived API:
  primitive data is the ambient commutative ring `R`, the finitely presented module `M`, and the
  local maximal-ideal hypotheses `PreValuationRing (Localization.AtPrime m)`;
  derived API is the existence of a split inclusion of `M` into a finite direct sum of principal
  quotient modules.

Source/core/bridge triage:
- `source-facing`: the theorem below, which packages the Stacks local-global statement as explicit
  retract data;
- `core/canonical`: `PreValuationRing`, `Module.FinitePresentation`, and the quotient owner
  `principalIdeal`;
- `bridge/view`: `finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients`
  provides the stronger local decomposition over a genuine prevaluation ring, while
  `directSummand_iff_surjective_compRight_of_principalPure_shortExact`
  is the canonical bridge from local decomposition data to the global retract conclusion, so this
  file should reuse that existing split-data surface rather than introduce a parallel local direct-
  summand wrapper.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

-- Proof sketch: by the bridge theorem
-- `directSummand_iff_surjective_compRight_of_principalPure_shortExact`, it
-- suffices to prove the required lifting property for `M`. Check surjectivity after localization
-- at each maximal ideal using the locality result of Algebra, Lemma `10.23.1`; finite
-- presentation identifies localized `Hom` with `Hom` out of the localized module, and the owner
-- lemma `finitelyPresented_module_exists_linearEquiv_directSum_principal_quotients` gives that
-- each `M_m` is a finite direct sum of principal quotients over `Localization.AtPrime m`. Apply
-- Lemma `15.125.1` locally to obtain the chapter's canonical split-data conclusion, then shrink
-- the indexing set to a finite subset because `M` is finite.
/-- Lemma 15.125.4: if every localization of `R` at a maximal ideal is a generalized valuation
ring, then every finitely presented `R`-module is a direct summand of a finite direct sum of
principal quotient modules `R ⧸ (fᵢ)`. -/
theorem finitelyPresented_module_directSummand_finite_directSum_principal_quotients_of_maximal_localizations_preValuationRing
    (hR : ∀ (m : Ideal R) (_ : m.IsMaximal), PreValuationRing (Localization.AtPrime m)) :
    ∃ (n : ℕ) (f : Fin n → R)
      (i : M →ₗ[R] (⨁ j : Fin n, R ⧸ principalIdeal (f j)))
      (s : (⨁ j : Fin n, R ⧸ principalIdeal (f j)) →ₗ[R] M),
      s.comp i = LinearMap.id := sorry

end
