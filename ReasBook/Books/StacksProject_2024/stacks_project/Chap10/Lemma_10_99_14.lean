import StacksProject_2024.stacks_project.Chap10.Lemma_10_99_10_Variant_of_the_local_criterion

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S R' S' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable [IsLocalRing R'] [IsLocalRing S']
variable [IsNoetherianRing R'] [IsNoetherianRing S']
variable (W : Submonoid (S ⊗[R] R'))
variable [Algebra (S ⊗[R] R') S']
variable [IsScalarTower S (S ⊗[R] R') S'] [IsScalarTower R' (S ⊗[R] R') S']
variable [IsLocalization W S']
variable [IsLocalHom (algebraMap R' S')]

variable {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [Module.Finite S M]

local notation "M'" => S' ⊗[S] M

/- Domain-style sampling:
- primary domain: local flatness criteria under localized tensor-product base change in
  commutative algebra;
- sampled owner declarations of the same kind:
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `Tor₁[R](M, N)`,
  `Module.Flat`,
  `flat_tensorProduct_of_flat_of_isLocalization_tensorProduct`;
- best owner abstraction: the flatness owner is `Module.Flat`, and the homological input should use
  the chapter owner notation `Tor₁[R'](M', R' ⧸ I')` rather than a raw derived-functor term;
- primitive data: the local Noetherian target map `R' → S'`, the ideal `I` of `R` together with
  properness of its image `I' = Ideal.map (algebraMap R R') I`, the finite `S`-module `M`, and
  the localization presentation of `S'` over `S ⊗[R] R'`;
- derived API: flatness of `M' = S' ⊗[S] M` over `R'`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.14 itself;
- `core/canonical`: `Module.Flat` together with the chapter owner notation `Tor₁`;
- `bridge/view`: localization/base-change transport of quotient flatness to the square over
  `R' → S'`, followed by the canonical variant local criterion `10.99.10`; the source-side
  local/Noetherian square belongs only to one proof route and is not primitive public data here.
-/

-- Proof sketch: because `S'` is a localization of `S ⊗[R] R'`, the module
-- `M'` is a localization of the ordinary base change `R' ⊗[R] M`. The hypothesis
-- that `M / IM` is flat over `R / I` localizes to flatness of `M' / I'M'` over `R' / I'`.
-- Applying the variant local criterion for flatness over the local map `R' → S'`, it remains to
-- use the assumed vanishing of `Tor₁^{R'}(M', R' / I')`.
/-- Lemma 10.99.14: in a commutative square of local homomorphisms of local Noetherian rings, let
`I` be an ideal of `R` such that `I' = Ideal.map (algebraMap R R') I` is proper, and let `M` be
a finite `S`-module. Put `M' = S' ⊗[S] M`. If `R' → S'` is a local homomorphism of Noetherian
local rings, if `S'` is a localization of `S ⊗[R] R'`, if `M / IM` is flat over `R / I`, and if
`Tor₁^{R'}(M', R' / I')` vanishes, then `M'` is flat over `R'`. -/
theorem flat_tensorProduct_of_flat_mod_ideal_and_tor_one_quotient_vanishing_of_isLocalization_tensorProduct
    (I : Ideal R) (hI : Ideal.map (algebraMap R R') I ≠ ⊤)
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (hTor :
      IsZero (Tor₁[R'](M', R' ⧸ Ideal.map (algebraMap R R') I))) :
    Module.Flat R' M' := by
  apply flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
  · exact hI
  · simpa using hTor
  · sorry

end
