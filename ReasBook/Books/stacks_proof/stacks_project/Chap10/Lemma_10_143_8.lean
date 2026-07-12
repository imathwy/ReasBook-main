import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S' : Type v} {S : Type w}
variable [CommRing R] [CommRing S'] [CommRing S]
variable [Algebra R S'] [Algebra R S] [Algebra S' S] [IsScalarTower R S' S]
variable [Etale R S'] [Etale R S]

/- Domain-style sampling:
- primary domain: étale morphisms of commutative rings, especially target-local descent from the
  owner predicates `Etale` and `IsEtaleAt`;
- sampled owner declarations:
  `Algebra.Etale`,
  `RingHom.Etale.ofLocalizationSpanTarget`,
  `map_eq_maximalIdeal_of_exists_etale_away`,
  `isEtaleAt_of_flat_localRingHom_of_map_eq_maximalIdeal_of_separableResidueField`;
- best owner abstraction: the global owner remains `Etale S' S`, while the local bridge owner is
  `IsEtaleAt S' q` at each prime `q : Ideal S`;
- primitive data: the two étale structures over the common base `R` and the compatible
  `S'`-algebra structure on `S`;
- derived API: residue-field separability, local maximal-ideal identification, local flatness of
  `S'_q' → S_q`, and the final target-local reconstruction of `Etale S' S`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that two étale algebras over a common base induce an
  étale map between them;
- `core/canonical`: `Algebra.Etale`, `Algebra.IsEtaleAt`, and `RingHom.Etale`;
- `bridge/view`: the local primewise flatness and residue-field criteria supplied by
  `10.143.5`, `10.143.7`, and `10.128.9`.
-/

-- Proof sketch: étaleness is local on the target, so it suffices to prove `S' → S` is étale at
-- every prime of `S`. For a prime `q ⊂ S` lying over `q' ⊂ S'` and `p ⊂ R`, the chapter-local
-- owners from Lemmas `10.143.5` and `10.143.7` provide the needed maximal-ideal and
-- residue-field criteria, while the global owner remains `Algebra.Etale S' S` rather than a new
-- wrapper around local data.
/-- Lemma 10.143.8: if `R → S` and `R → S'` are étale and `S` is equipped with a compatible
`S'`-algebra structure over `R`, then the induced map `S' → S` is étale. -/
@[stacks 00U7]
theorem etale_of_etale_over_common_base :
    Etale S' S := by
  sorry

end

end Algebra
