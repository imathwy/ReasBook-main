import Mathlib
import stacks_project.Chap10.Definition_10_136_1
import stacks_project.Chap15.Definition_15_33_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: syntomic and local-complete-intersection properties of commutative ring
  homomorphisms;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Syntomic.flat`,
  `RingHom.Syntomic.hasLocalCompleteIntersectionFibers`,
  `RingHom.IsLocalCompleteIntersection`;
- best owner abstraction: this lemma belongs on the ring-hom owner
  `RingHom.Syntomic`, not on the algebra-map specialization `algebraMap R S`;
- primitive vs. derived: the primitive owner data are already in `RingHom.Syntomic`, while the
  flatness projection is derived API and the local-complete-intersection criterion is the new
  companion characterization supplied here.

Source/core/bridge triage:
- `source-facing`: the equivalence between syntomicity and flat local complete intersection for a
  ring map;
- `core/canonical`: the owner predicates `RingHom.Syntomic` and
  `RingHom.IsLocalCompleteIntersection`;
- `bridge/view`: the algebra-map specialization obtained by instantiating the theorem below with
  `f := algebraMap R S`. -/

namespace Syntomic

-- Proof sketch: for the forward implication, unpack `Syntomic R S`; flatness is built into the
-- definition, and the fiberwise local complete intersection condition can be upgraded to the ring-
-- map local complete intersection criterion via the relative-global-complete-intersection
-- neighborhood theorem together with Lemmas `15.33.3` and `15.33.4`. For the reverse implication,
-- a flat local complete intersection map is of finite presentation, and after base change to each
-- residue field its fibers are local complete intersections, which is exactly the remaining
-- syntomic condition.
/-- Lemma 15.33.5: a ring map is syntomic if and only if it is flat and a local complete
intersection. -/
theorem iff_flat_and_isLocalCompleteIntersection (f : R →+* S) :
    f.Syntomic ↔ f.Flat ∧ f.IsLocalCompleteIntersection := sorry

end Syntomic

end

end RingHom
