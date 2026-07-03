import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_105_24_Olivier (from Chap15) -/
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [StrictHenselianLocalRing A] [Algebra.IsWeaklyEtale A B]

/- Domain-style sampling for Theorem 15.105.24 (Olivier):
- primary domain: local commutative algebra of weakly étale maps over strictly henselian local
  rings;
- sampled owner declarations:
  `StrictHenselianLocalRing`,
  `Algebra.IsWeaklyEtale`,
  `Algebra.IsEpi`,
  `faithfullyFlat_epi_bijective`;
- best owner abstraction: this item is `source-facing`, but the canonical owner controlling the
  final bijectivity step is `Algebra.IsEpi A B`; faithful flatness is derived from the flatness
  field of `Algebra.IsWeaklyEtale` together with `IsLocalHom (algebraMap A B)`;
- primitive data: `StrictHenselianLocalRing A`, `IsLocalHom (algebraMap A B)`, and
  `Algebra.IsWeaklyEtale A B`;
- derived API: the public bridge to `Algebra.IsEpi A B`, then bijectivity of `algebraMap A B`
  via `faithfullyFlat_epi_bijective`.

Source/core/bridge triage:
- `source-facing`: `bijective_algebraMap_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale`;
- `core/canonical`: `Algebra.IsWeaklyEtale`, `Algebra.IsEpi`, and `RingHom.FaithfullyFlat`;
- `bridge/view`: the epimorphism bridge below.
-/

-- Proof sketch: weakly étale maps induce separable residue-field extensions on fibers, while the
-- strict henselian local hypotheses force the closed-fiber residue-field extension to be purely
-- inseparable. Thus the diagonal/base-change fiber is trivial, so the canonical owner
-- `Algebra.IsEpi A B` holds.
/-- A weakly étale local homomorphism out of a strictly henselian local ring is an epimorphism. -/
theorem algebra_isEpi_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale :
    Algebra.IsEpi A B := by
  sorry

-- Proof sketch: once the public epimorphism bridge supplies the canonical owner, the local weakly
-- étale hypotheses give faithful flatness by `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and
-- Lemma `10.107.7` finishes.
/-- Theorem 15.105.24 (Olivier): if `A → B` is a weakly étale local homomorphism of local rings
with `A` strictly henselian, then the structure map `A → B` is bijective, hence an isomorphism. -/
theorem bijective_algebraMap_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale :
    Function.Bijective (algebraMap A B) := by
  let _ : Algebra.IsEpi A B :=
    algebra_isEpi_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
  exact faithfullyFlat_epi_bijective <|
    RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom

end
