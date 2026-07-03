import Mathlib
import stacks_project.Chap10.Lemma_10_106_2
import stacks_project.Chap10.Lemma_10_120_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/- Domain-style sampling for Lemma 15.122.2:
- primary domain: commutative algebra of regular local rings, height-one prime ideals, and the
  canonical factoriality owner `UniqueFactorizationMonoid`;
- sampled owner declarations:
  `regularLocalRing_isDomain`,
  `uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal`,
  `UniqueFactorizationMonoid`,
  `IsRegularLocalRing`;
- best owner abstraction: the public owner is `UniqueFactorizationMonoid R`; the height-one-prime
  principal criterion is derived bridge API imported from Chapter 10 rather than primitive local
  data for this file;
- primitive vs. derived:
  the primitive data are only the ambient regular-local hypotheses on `R`;
  the height-one-principal criterion used in the proof is derived from the Chapter 10 owner bridge.

Source/core/bridge triage:
- `source-facing`: the instance below expressing that a regular local ring is factorial;
- `core/canonical`: `UniqueFactorizationMonoid R`;
- `bridge/view`: `uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal`. -/

-- Proof sketch: by Lemma `10.120.6`, it is enough to prove that every height-one prime ideal of a
-- regular local ring is principal. Proceed by induction on the dimension. Choose
-- `x ∈ maximalIdeal R \ maximalIdeal R ^ 2`; then `R ⧸ (x)` is again regular, hence a domain, so
-- `x` is a prime element. For a height-one prime `p`, either `x ∈ p`, in which case `p = (x)`, or
-- after localizing away from `x`, the localizations at nonmaximal primes are regular local rings
-- of smaller dimension, so the induction hypothesis shows `p` becomes invertible and hence
-- principal on `Rₓ`. A generator coming from a factor of an element of `p` is then prime in `R`
-- by Nagata's criterion, and its principal ideal equals `p`.
/-- Lemma 15.122.2: a regular local ring is a unique factorization domain. -/
instance regularLocalRing_uniqueFactorizationMonoid : UniqueFactorizationMonoid R := by
  refine (uniqueFactorizationMonoid_iff_forall_height_one_prime_isPrincipal).2 ?_
  intro p hp hheight
  sorry

end
