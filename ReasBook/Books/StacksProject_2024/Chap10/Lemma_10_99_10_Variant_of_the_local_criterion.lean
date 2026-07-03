import StacksProject_2024.Chap10.Lemma_10_99_7_Local_criterion_for_flatness
import StacksProject_2024.Chap10.Lemma_10_99_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling for the variant local criterion for flatness:
- primary domain: flatness of a finite module over a local homomorphism of Noetherian local rings,
  detected from a quotient-flatness hypothesis and a `Tor₁` vanishing hypothesis over the
  quotient ring;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Tor₁[R](M, N)`,
  `flat_of_residueField_tor_one_vanishing`,
  `tor_one_vanishes_of_annihilated_by_ideal_pow`;
- best owner abstraction: the public conclusion is the canonical owner `Module.Flat`, and the
  homological input should be expressed by the chapter owner notation `Tor₁[R](M, R ⧸ I)` rather
  than by the raw derived-functor term;
- primitive data: the local map `R → S`, the finite `S`-module `M`, the proper ideal `I`, the
  vanishing of `Tor₁^R(M, R / I)`, and flatness of `M / IM` over `R / I`;
- derived API: the flatness conclusion over `R`.

Source/core/bridge triage:
- `source-facing`: the Stacks variant local criterion itself;
- `core/canonical`: `Module.Flat` together with the chapter owner notation `Tor₁[R](M, N)`;
- `bridge/view`: Lemma `10.99.8` upgrades quotient flatness and quotient `Tor₁` vanishing to the
  residue-field vanishing input for Lemma `10.99.7`, and those intermediate reductions belong to
  the proof route rather than the public statement.
-/

-- Proof sketch: apply Lemma `10.99.8` to the ideal `I` to promote flatness of `M / IM` over
-- `R / I` and the assumed vanishing of `Tor₁^R(M, R / I)` to vanishing of `Tor₁^R(κ(R), M)`,
-- using the symmetry of `Tor` to match the orientation in Lemma `10.99.7`. Then invoke the local
-- criterion for flatness from Lemma `10.99.7`.
/-- Lemma 10.99.10 (Variant of the local criterion): let `R → S` be a local homomorphism of
Noetherian local rings, let `I ≠ R` be an ideal of `R`, and let `M` be a finite `S`-module. If
`Tor₁^R(M, R / I)` vanishes and `M / IM` is flat over `R / I`, then `M` is flat over `R`. -/
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : CategoryTheory.Limits.IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := sorry

end
