import Mathlib.RingTheory.RingHom.QuasiFinite

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain triage:
* primary domain: quasi-finite finite-type ring maps in commutative algebra;
* sampled owner declarations:
  `Algebra.QuasiFiniteAt`, `Algebra.QuasiFinite`,
  `RingHom.QuasiFiniteAt`, `RingHom.QuasiFinite`;
* source-facing layer: Definition `10.122.3` packages finite type together with the canonical
  primewise and global quasi-finite owners;
* core/canonical owners: `Algebra.QuasiFiniteAt` and `Algebra.QuasiFinite`;
* bridge/view: the thin projection/equivalence lemmas exposing the owner predicates under the
  source-facing finite-type packaging.
* primitive data: the finite-type hypothesis and the canonical owner predicates;
* derived API: the projection lemmas and the ambient-finite-type equivalences below.
-/

namespace Algebra.FiniteType

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.122.3 (1): `R → S` is quasi-finite at the prime `q` when it is of finite type
and the canonical owner predicate `Algebra.QuasiFiniteAt R q` holds. -/
def QuasiFiniteAt (q : Ideal S) [q.IsPrime] : Prop :=
  Algebra.FiniteType R S ∧ Algebra.QuasiFiniteAt R q

namespace QuasiFiniteAt

variable {R S}
variable {q : Ideal S} [q.IsPrime]

/-- The finite-type hypothesis carried by the source-facing primewise quasi-finite predicate. -/
theorem finiteType (h : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.FiniteType R S :=
  h.1

/-- The canonical local quasi-finite owner carried by the source-facing finite-type predicate. -/
theorem toQuasiFiniteAt (h : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.QuasiFiniteAt R q :=
  h.2

/-- Under an ambient finite-type hypothesis, the source-facing primewise notion is obtained
directly from the canonical owner. -/
theorem of_quasiFiniteAt [Algebra.FiniteType R S] (h : Algebra.QuasiFiniteAt R q) :
    Algebra.FiniteType.QuasiFiniteAt R S q :=
  ⟨inferInstance, h⟩

/-- Under an ambient finite-type hypothesis, the source-facing primewise notion is equivalent to
the canonical owner `Algebra.QuasiFiniteAt R q`. -/
theorem iff_quasiFiniteAt [Algebra.FiniteType R S] :
    Algebra.FiniteType.QuasiFiniteAt R S q ↔ Algebra.QuasiFiniteAt R q :=
  ⟨toQuasiFiniteAt, of_quasiFiniteAt⟩

end QuasiFiniteAt

/-- Definition 10.122.3 (2): `R → S` is quasi-finite when it is of finite type and quasi-finite in
the canonical sense. -/
def QuasiFinite : Prop :=
  Algebra.FiniteType R S ∧ Algebra.QuasiFinite R S

namespace QuasiFinite

variable {R S}

/-- The finite-type hypothesis carried by the source-facing global quasi-finite predicate. -/
theorem finiteType (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.FiniteType R S :=
  h.1

/-- The canonical global quasi-finite owner carried by the source-facing finite-type predicate. -/
theorem toQuasiFinite (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.QuasiFinite R S :=
  h.2

/-- Under an ambient finite-type hypothesis, the source-facing global notion is obtained directly
from the canonical owner. -/
theorem of_quasiFinite [Algebra.FiniteType R S] (h : Algebra.QuasiFinite R S) :
    Algebra.FiniteType.QuasiFinite R S :=
  ⟨inferInstance, h⟩

/-- Under an ambient finite-type hypothesis, the source-facing global notion is equivalent to the
canonical owner `Algebra.QuasiFinite R S`. -/
theorem iff_quasiFinite [Algebra.FiniteType R S] :
    Algebra.FiniteType.QuasiFinite R S ↔ Algebra.QuasiFinite R S :=
  ⟨toQuasiFinite, of_quasiFinite⟩

end QuasiFinite

end

end Algebra.FiniteType
