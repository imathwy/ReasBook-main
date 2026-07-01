import Mathlib
import stacks_project.Chap10.Definition_10_136_5
import stacks_project.Chap10.Lemma_10_136_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

/- Domain-style sampling:
- primary domain: composition stability for syntomic ring maps and relative global complete
  intersections in commutative algebra;
- inspected owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Flat.comp`,
  `RingHom.FinitePresentation.comp`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`;
- best owner abstractions:
  `RingHom.Syntomic` is a ring-hom property, so its canonical composition API should expose the
  owner-namespace theorem `RingHom.Syntomic.comp`, with the bundled witness
  `RingHom.Syntomic.stableUnderComposition` as derived API;
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is already the source-facing algebra owner,
  so composition belongs in the owner namespace rather than as a parallel freestanding theorem;
- primitive vs. derived:
  flatness, finite presentation, and chosen presentation data remain derived API from the two
  owners and should not be repackaged here.
-/

namespace RingHom

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']

namespace Syntomic

-- Proof sketch: the composition of syntomic morphisms is flat by `RingHom.Flat.comp` and finitely
-- presented by `RingHom.FinitePresentation.comp`. For the fiber condition, apply the relative
-- global complete intersection neighborhood criterion from Lemma `10.136.15` and then the
-- composition statement for relative global complete intersections from part `(2)`.
/-- Lemma 10.136.17 (1): the composition of syntomic ring maps is syntomic. -/
theorem comp {f : R →+* S} {g : S →+* S'} (hf : f.Syntomic) (hg : g.Syntomic) :
    (g.comp f).Syntomic := by
  sorry

/-- Companion meta-property witness for Lemma 10.136.17 (1). -/
theorem stableUnderComposition : RingHom.StableUnderComposition RingHom.Syntomic := by
  intro R S T _ _ _ f g hf hg
  exact hf.comp hg

end Syntomic

end RingHom

namespace Algebra

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: choose relative global complete intersection presentations for `S` over `R` and
-- for `S'` over `S`, concatenate the generators and lifted relations to obtain a presentation of
-- `S'` over `R`, and then bound the fiber dimensions by additivity of dimensions along the finite
-- type map between the fibers.
/-- Lemma 10.136.17 (2): relative global complete intersections are stable under composition. -/
theorem comp (hRS : IsRelativeGlobalCompleteIntersection R S)
    (hSS' : IsRelativeGlobalCompleteIntersection S S') :
    IsRelativeGlobalCompleteIntersection R S' := sorry

end IsRelativeGlobalCompleteIntersection

end Algebra

end
