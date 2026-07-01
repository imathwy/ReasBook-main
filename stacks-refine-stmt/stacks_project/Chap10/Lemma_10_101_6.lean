import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

local notation "IM" => I • (⊤ : Submodule R M)
set_option quotPrecheck false in
local notation "Tor₁[" R "](" N ", " M ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))

/- Domain triage:
- primary domain: commutative algebra of flatness over quotient rings and nilpotent thickenings in
  an Artinian local ring;
- sampled owner declarations:
  `Module.Flat`,
  `flat_of_nilpotent_ideal_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `flat_tfae_tor_vanishing_criteria`,
  `isArtinianRing_iff_isNilpotent_maximalIdeal`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with the nilpotent-ideal
  criterion from `10.99.8` supplying the core reverse implication;
- primitive data: the ring `R`, module `M`, and ideal `I`;
- derived API: quotient flatness over `R ⧸ I` and the vanishing statement `Tor₁^R(R ⧸ I, M) = 0`.

Layering:
- `source-facing`: the Artinian-local iff criterion stated in the textbook;
- `core/canonical`: `Module.Flat` together with the Chapter 10 nilpotent-ideal flatness owner;
- `bridge/view`: the Artinian-local specialization, using that every proper ideal lies in the
  nilpotent maximal ideal.
-/

-- Proof sketch: for the forward implication, reuse the canonical flat base-change and Tor-vanishing
-- owners. For the converse, a proper ideal in an Artinian local ring is nilpotent because it lies
-- in the nilpotent maximal ideal, so the argument reduces to the Chapter 10 nilpotent-thickening
-- criterion specialized to this Artinian-local setting.
/-- Lemma 10.101.6: for an Artinian local ring `R`, an `R`-module `M`, and a proper ideal
`I ⊂ R`, the module `M` is flat over `R` if and only if `M / IM` is flat over `R / I` and
`Tor₁^R(R / I, M)` vanishes. -/
theorem flat_iff_flat_mod_ideal_and_tor_one_quotient_vanishes_of_artinian_local
    (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ IM) ∧
        IsZero (Tor₁[R](R ⧸ I, M)) := by
  sorry

end
