import Mathlib
import StacksProject_2024.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: regular and weakly regular sequences versus Koszul-regularity in commutative
  algebra;
- sampled owner declarations: `RingTheory.Sequence.IsWeaklyRegular`,
  `RingTheory.Sequence.IsRegular`, `RingTheory.Sequence.IsKoszulRegularOn`,
  `RingTheory.Sequence.IsKoszulRegularSequence`;
- best owner abstraction: `IsKoszulRegularOn` is the Chapter 15 owner for module-valued
  Koszul-regularity, with the source-facing list `rs` entering only through the canonical finite
  family `rs.get : Fin rs.length → R`, while the bridge itself should live owner-style under
  `IsWeaklyRegular` and `IsRegular`;
- primitive data: the source list `rs : List R` and the regular-sequence owner hypothesis on that
  list;
- derived API: the bridge from list-level weak/regular sequence hypotheses to the owner predicate
  `IsKoszulRegularOn M rs.get`;
- layer triage: the Stacks lemma here is `source-facing` on the list side and `bridge/view` on the
  conclusion side, so the local list-valued Koszul-complex wrapper should be deleted in favor of
  the owner predicate from `Definition 15.30.1`.
-/

-- Proof sketch: interpret the source list as the canonical finite family `rs.get`. Then induct on
-- the list using `isWeaklyRegular_cons_iff`. Lemma `15.28.8` identifies the Koszul complex of a
-- nonempty family with the homotopy cofiber of multiplication by its last entry, and the
-- resulting long exact homology sequence compares positive homology with the Koszul complex of the
-- tail on the successive quotient module.
namespace IsWeaklyRegular

/-- Lemma 15.30.2, weakly regular owner form: if a list `rs` is weakly regular on `M`, then the
canonical finite family `rs.get` is Koszul-regular on `M`. -/
theorem isKoszulRegularOn {rs : List R} (hreg : IsWeaklyRegular M rs) :
    IsKoszulRegularOn M rs.get := sorry

end IsWeaklyRegular

-- Proof sketch: every regular sequence is weakly regular, so the previous theorem applies to the
-- underlying weakly regular sequence.
namespace IsRegular

/-- Every regular sequence on `M` is Koszul-regular on `M`, expressed through the canonical finite
family owner `IsKoszulRegularOn`. -/
theorem isKoszulRegularOn {rs : List R} (hreg : IsRegular M rs) :
    IsKoszulRegularOn M rs.get :=
  hreg.toIsWeaklyRegular.isKoszulRegularOn

end IsRegular

end RingTheory.Sequence
