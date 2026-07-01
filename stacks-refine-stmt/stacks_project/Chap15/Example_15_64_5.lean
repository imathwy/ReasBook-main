import Mathlib
import stacks_project.Chap15.Definition_15_61_1
import stacks_project.Chap15.Lemma_15_64_4_K_nneth_Spectral_Sequence

open scoped BigOperators

noncomputable section

universe u

namespace CategoryTheory

open Limits
open MonoidalCategory

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

local notation "Mod" => ModuleCat R

-- Proof sketch: over a Dedekind domain every module has projective dimension at most one, so the
-- higher left derived functors of tensor product vanish in degrees `i ≥ 2`.
/-- Over a Dedekind domain, the higher `Tor` groups of two modules vanish above degree `1`. -/
theorem isZero_tor_of_two_le_of_dedekind_domain
    (M N : Mod) {i : ℕ} (hi : 2 ≤ i) :
    IsZero (Tor[R, i](M, N)) := sorry

end

section

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

/- Domain-style sampling for Example `15.64.5`.
- primary domain: bounded-derived Künneth spectral sequences over a Dedekind domain and the
  resulting short exact sequence in total degree `n`;
- sampled owner declarations in this domain:
  `ShortComplex.ShortExact`,
  `boundedDerivedTensorCohomology`,
  `kunnethDerivedTensorPageTwo`,
  `exists_kunnethDerivedTensorSpectralSequence`;
- best owner abstraction: the canonical owner for the short exact sequence itself is a
  `ShortComplex (ModuleCat R)` together with `ShortComplex.ShortExact`, but the source-facing
  theorem should expose the actual edge maps on the named `E₂`-terms and abutment objects rather
  than an auxiliary short complex up to isomorphism; the terms themselves should be reused from
  the chapter bridge declarations `kunnethDerivedTensorPageTwo` and
  `boundedDerivedTensorCohomology`, not recopied locally;
- primitive vs. derived: the primitive data for the public theorem are the maps
  `ι : kunnethDerivedTensorPageTwo K L 0 n ⟶ boundedDerivedTensorCohomology K L n` and
  `π : boundedDerivedTensorCohomology K L n ⟶ kunnethDerivedTensorPageTwo K L (-1) (n + 1)`
  together with the vanishing relation `ι ≫ π = 0`; the canonical short-complex owner
  `(ShortComplex.mk ι π h).ShortExact` is then the derived exactness packaging;
- source/core/bridge triage:
  `source-facing`: the existence theorem below for the Künneth short exact sequence;
  `core/canonical`: `ShortComplex` and `ShortComplex.ShortExact`;
  `bridge/view`: `kunnethDerivedTensorPageTwo`, `boundedDerivedTensorCohomology`, and the
  spectral-sequence existence theorem `exists_kunnethDerivedTensorSpectralSequence`.

This example is source-facing, but the previous wrapper class duplicated the canonical
short-complex owner and recopied the `E₂`-page formulas already owned upstream. The theorem below
now states the same mathematics directly in the chapter's canonical vocabulary.
-/

-- Proof sketch: start with the Künneth spectral sequence from Lemma `15.64.4`; the previous
-- vanishing theorem kills all `E₂^{p,q}` with `p ≤ -2`, so only the columns `p = 0, -1` remain.
-- The resulting two-line spectral sequence degenerates at `E₂`, and the usual filtration
-- argument yields the short exact sequence in total degree `n`.
/-- Example 15.64.5: over a Dedekind domain, the Künneth spectral sequence of
Lemma `15.64.4` degenerates at the `E_2` page, yielding for every `n` a short exact sequence
`0 → ⨁_{i + j = n} H^i(K) ⊗_R H^j(L) → H^n(K ⊗_R^L L) →
⨁_{i + j = n + 1} Tor_1^R(H^i(K), H^j(L)) → 0`. -/
theorem exists_kunneth_short_exact_sequence_of_dedekind_domain
    (K L : boundedDerivedCategory (ModuleCat R)) (n : ℤ) :
    ∃ (ι :
        kunnethDerivedTensorPageTwo K L 0 n ⟶
          boundedDerivedTensorCohomology K L n)
      (π :
        boundedDerivedTensorCohomology K L n ⟶
          kunnethDerivedTensorPageTwo K L (-1) (n + 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end CategoryTheory
