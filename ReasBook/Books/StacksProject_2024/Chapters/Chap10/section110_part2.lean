import Mathlib
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_110_9 (from Chap10) -/
universe u v

section

variable {R : Type u}
variable [CommRing R]

/- Domain-style sampling:
* primary domain: regular local rings under flat local homomorphisms of commutative rings;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `RingHom.domain_isLocalRing`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `isNoetherianRing_of_faithfullyFlat`,
  `residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae`;
* best owner abstraction: the core owner is `IsRegularLocalRing`; this numbered item is the
  source-facing descent statement for that owner along a flat local algebra map, not a new owner
  or a wrapper around a lower-level package;
* primitive data vs. derived API:
  primitive data are the target ring `S`, the flat local map `R → S`, and regularity of `S`;
  locality of `R`, faithful flatness of `S` over `R`, and Noetherianity of `R` are derived proof
  inputs, so the public theorem header should not keep separate `[IsLocalRing R]` or
  `[IsNoetherianRing R]` assumptions;
* source/core/bridge triage:
  the theorem below is `source-facing`,
  the owner predicate `IsRegularLocalRing` is `core/canonical`,
  and the residue-field/global-dimension criterion for regularity is the main `bridge/view`
  used by the proof sketch.

This file should therefore keep the theorem directly on `IsRegularLocalRing` and avoid introducing
any auxiliary wrapper for regularity descent.
-/
-- Proof sketch: let `d = ringKrullDim S`. A regular local ring has global dimension at most `d`
-- by Proposition `10.110.1`, so after tensoring a finite free resolution of the residue field of
-- `R` with `S`, Lemma `10.109.3` shows the `d`-th syzygy becomes projective over `S`. Lemma
-- `10.78.6` descends this finite projective module back to `R`, which implies that the residue
-- field of `R` has finite projective dimension. Proposition `10.110.5` then yields regularity of
-- `R`.
/-- Lemma 10.110.9: if `R → S` is a flat local homomorphism of local Noetherian rings and `S` is a
regular local ring, then `R` is a regular local ring. -/
theorem isRegularLocalRing_of_flat_localHom_of_regularTarget
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [IsRegularLocalRing S] :
    IsRegularLocalRing R := by
  let _ : IsLocalRing R := RingHom.domain_isLocalRing (algebraMap R S)
  let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let _ : IsNoetherianRing R :=
    isNoetherianRing_of_faithfullyFlat (algebraMap R S) <| by
      rw [RingHom.faithfullyFlat_algebraMap_iff]
      infer_instance
  sorry

end
