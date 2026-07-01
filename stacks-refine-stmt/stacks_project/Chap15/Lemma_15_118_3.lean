import Mathlib.RingTheory.PicardGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Domain-style sampling:
- primary domain: commutative algebra of class groups and Picard groups for domains with
  factorization hypotheses;
- sampled owner declarations:
  `ClassGroup.equivPic`,
  `instSubsingletonPicOfIsDomainOfNonemptyNormalizedGCDMonoid`,
  `UniqueFactorizationMonoid`,
  `subsingleton_classGroup`,
  `Module.Invertible.free_iff_linearEquiv`;
- best owner abstraction: the canonical owner is `CommRing.Pic R`, with the upstream triviality
  owner `instSubsingletonPicOfIsDomainOfNonemptyNormalizedGCDMonoid`;
- primitive vs. derived:
  triviality of the Picard group is already derived upstream from the more primitive canonical
  input `[Nonempty (NormalizedGCDMonoid R)]`; the UFD specialization is therefore source-level
  motivation, not new public data for this file.

Layer triage:
- `source-facing`: the Stacks lemma for unique factorization domains;
- `core/canonical`: the upstream `Subsingleton (CommRing.Pic R)` instance for domains admitting a
  normalized gcd structure, which already covers UFDs by typeclass inference;
- `bridge/view`: the specialization from `[UniqueFactorizationMonoid R]` to the upstream normalized
  gcd Picard-triviality instance, supplied entirely by typeclass inference.
-/

/- Lemma 15.118.3: a unique factorization domain has trivial Picard group. This source-facing
specialization is discharged by the canonical upstream Picard-triviality instance for normalized
gcd domains. -/
theorem subsingleton_picardGroup_of_uniqueFactorizationMonoid :
    Subsingleton (CommRing.Pic R)
  := inferInstance
