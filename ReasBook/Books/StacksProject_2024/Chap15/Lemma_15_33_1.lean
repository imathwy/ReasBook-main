import Mathlib
import StacksProject_2024.Chap15.Definition_15_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace Algebra.Generators

/- Domain triage:
- primary domain: finite polynomial presentations of commutative algebras and presentation
  independence of local complete intersection kernels;
- sampled owner declarations: `Algebra.Generators.defaultHom`,
  `Algebra.Generators.presentation_cotangent_stable_equiv`,
  `Ideal.IsKoszulRegularIdeal`, and
  `RingTheory.Sequence.isKoszulRegularSequence_of_span_eq`;
- best owner abstraction: the primitive data are the two finite presentation owners
  `P : Generators A B ι` and `Q : Generators A B κ`; the kernel ideals are derived fields of
  those owners, so the independence statement belongs on `Algebra.Generators` rather than as a
  parallel global wrapper;
- primitive vs. derived: `P` and `Q` are primitive public data, while `P.ker`, `Q.ker`, and the
  resulting ring-hom notion of Definition `15.33.2` are derived from that owner data;
- layer triage:
  - `source-facing`: the theorem below asserting that Koszul-regularity of the kernel does not
    depend on the chosen finite presentation;
  - `core/canonical`: `Algebra.Generators`;
  - `bridge/view`: the stable cotangent comparison of Lemma `10.134.15` and the sequence-transfer
    lemmas `15.30.13` through `15.30.15`. -/

-- Proof sketch: compare the two presentations by adjoining both sets of variables and mapping the
-- extra variables to chosen polynomial lifts. The kernel of the combined presentation is generated
-- both by the first kernel together with the new variable differences and by the second kernel
-- together with the opposite variable differences. Lemma `10.134.15` gives the equality of the
-- local conormal ranks, Lemma `15.30.15` transfers Koszul-regularity between generating sequences
-- of the same length for the same ideal, and Lemmas `15.30.13` and `15.30.14` add and then remove
-- the obvious regular variable-difference sequences. Any auxiliary reindexing to `Fin` belongs
-- only inside that proof bridge via `Fintype.ofFinite` and `Fintype.equivFin`, not in the public
-- theorem statement.
/-- Lemma 15.33.1: for two finite polynomial presentations of the same `A`-algebra `B`, the
kernel ideal of one presentation is Koszul-regular if and only if the kernel ideal of the other
presentation is Koszul-regular. Equivalently, Koszul-regularity of the kernel is independent of
the chosen finite presentation. -/
theorem ker_isKoszulRegularIdeal_iff {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Generators A B ι) (Q : Generators A B κ) :
    P.ker.IsKoszulRegularIdeal ↔ Q.ker.IsKoszulRegularIdeal := sorry

end Algebra.Generators

end
