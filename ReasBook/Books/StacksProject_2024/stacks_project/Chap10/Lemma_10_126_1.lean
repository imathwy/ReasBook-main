import Mathlib.RingTheory.Finiteness.Descent

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: finite-type algebras under tensor-product base change and faithfully flat descent;
- sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `RingHom.faithfullyFlat_algebraMap_iff`,
  `Algebra.FiniteType`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`,
  `RingHom.FiniteType.codescendsAlong_faithfullyFlat`;
- best owner abstractions: `Algebra.FiniteType` for the finite-type property and
  `(algebraMap R R').FaithfullyFlat` for the faithfully flat base-change hypothesis;
- primitive data: the two algebra structures `R → S` and `R → R'`, together with faithful
  flatness of the canonical ring map `R → R'`;
- derived API: the textbook equivalence between finite type for `S/R` and for the base change
  `R' ⊗[R] S / R'`.

Source/core/bridge triage:
- `source-facing`: the textbook iff statement of Lemma 10.126.1;
- `core/canonical`: `Algebra.FiniteType.baseChange` and
  `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat` together with the canonical
  faithful-flatness owner `(algebraMap R R').FaithfullyFlat`;
- `bridge/view`: `RingHom.faithfullyFlat_algebraMap_iff` and the tensor-product presentation
  `R' ⊗[R] S` of the base-changed algebra.
-/

/-- Lemma 10.126.1: for a faithfully flat base change `R → R'`, the `R`-algebra `S` is of finite
type over `R` if and only if the base-changed algebra `R' ⊗[R] S` is of finite type over `R'`. -/
theorem finiteType_iff_finiteType_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Algebra.FiniteType R S ↔ Algebra.FiniteType R' (R' ⊗[R] S) := by
  letI : Module.FaithfullyFlat R R' :=
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat R'⟩

end
