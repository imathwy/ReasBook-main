import Mathlib
import StacksProject_2024.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling:
- primary domain: the local flatness criterion for a finite module over a local homomorphism of
  local Noetherian rings, expressed through residue-field `Tor₁`-vanishing;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`,
  `isZero_tor_one_of_isFiniteLength_of_residueField_vanishing`;
- best owner abstraction: the public owner is `Module.Flat`, while the source-facing homological
  hypothesis should use the chapter owner notation `Tor₁[R](ResidueField R, M)` rather than a raw
  derived-functor term;
- primitive data: the local map `R → S`, the finite `S`-module `M`, and the residue-field
  `Tor₁`-vanishing hypothesis;
- derived API: the flatness conclusion over the base ring `R`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.7 itself;
- `core/canonical`: `Module.Flat` together with the canonical `Tor₁` owner from
  `Remark_10_75_9`;
- `bridge/view`: the quotient-by-ideal Tor/kernel comparison and the finite-length propagation of
  Lemma `10.99.6` belong to the proof route, not to the public statement.
-/

-- Proof sketch: by Lemma `10.39.5`, it is enough to prove injectivity of `I ⊗[R] M → M` for every
-- ideal `I` of `R`. Remark `10.75.9` identifies the kernel with `Tor₁^R(M, R / I)`, and Lemma
-- `10.99.6` gives vanishing for ideals of finite colength from the residue-field hypothesis. Use
-- the Artin-Rees argument from the textbook to reduce the general ideal case to finite-colength
-- ideals, then conclude by the faithfully flat maximal-ideal-adic completion from Lemma `10.97.3`.
/-- Lemma 10.99.7 (Local criterion for flatness): if `R → S` is a local homomorphism of local
Noetherian rings, `M` is a finite `S`-module, and `Tor₁^R(ResidueField R, M)` vanishes, then `M`
is flat over `R`. -/
theorem flat_of_residueField_tor_one_vanishing
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) :
    Module.Flat R M := sorry

end
