import Mathlib
import stacks_project.Chap15.Definition_15_33_2
import stacks_project.Chap15.Definition_15_83_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [RingHom.IsLocalCompleteIntersection (algebraMap A B)]

/- Domain-style sampling for Lemma 15.83.6:
- primary domain: commutative algebra of local complete intersection and perfect ring maps;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.IsPerfectRingMap`,
  `RingHom.IsPseudoCoherentRingMap`,
  `Algebra.isPerfectRingMap_of_flat_of_finitePresentation`;
- best owner abstraction: both the source hypothesis and the target conclusion live on the
  canonical ring-map owners `RingHom.IsLocalCompleteIntersection` and
  `RingHom.IsPerfectRingMap` for `algebraMap A B`; a polynomial presentation from Definition
  `15.33.2` is bridge data only and should not appear in the public API here;
- primitive vs. derived:
  the primitive public datum is only the owner hypothesis
  `[RingHom.IsLocalCompleteIntersection (algebraMap A B)]`;
  the derived API is the perfectness instance and its downstream pseudo-coherence and finite Tor
  dimension consequences.

Source/core/bridge triage:
- `source-facing`: the implication below that a local complete intersection ring map is perfect;
- `core/canonical`: `RingHom.IsLocalCompleteIntersection` and `RingHom.IsPerfectRingMap`;
- `bridge/view`: any chosen finite polynomial presentation witnessing the local complete
  intersection condition, used only in the proof.
-/

-- Proof sketch: apply Definition `15.33.2` to choose a finite polynomial presentation
-- `A[x₁, …, xₙ] ↠ B` whose kernel ideal is Koszul-regular. By Lemma `15.83.2`, it is enough to
-- show that `B` is a perfect module over the polynomial ring. Lemma `15.75.12` reduces this to a
-- local statement on the source polynomial ring, where Definition `15.32.1` lets one replace the
-- kernel ideal by a Koszul-regular generating sequence. Such a sequence gives a finite free, hence
-- finite projective, resolution of the quotient module, so Lemma `15.75.3` yields perfection.
/-- Lemma 15.83.6: a local complete intersection ring map is perfect. -/
instance isPerfectRingMap_of_isLocalCompleteIntersection :
    (algebraMap A B).IsPerfectRingMap := sorry

end

end Algebra
