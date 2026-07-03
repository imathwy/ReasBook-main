import Mathlib
import stacks_project.Chap10.Definition_10_166_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v w

section

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/- Domain-style sampling:
* primary domain: geometric regularity of algebras over a field and faithfully flat descent;
* sampled owner declarations:
  `IsGeometricallyRegular`,
  `IsGeometricallyRegular.isRegularRing_baseChange`,
  `RingHom.FaithfullyFlat.isStableUnderBaseChange`,
  `isRegularRing_of_faithfullyFlat`;
* best owner abstraction: the source-facing property is the owner class
  `IsGeometricallyRegular`; regularity after tensor base change and faithful flatness after
  base change are derived API and should not be repackaged locally;
* primitive data vs. derived API:
  the primitive inputs are only `hff` and `[IsGeometricallyRegular k B]`;
  the tensor-product algebra structures, the base-changed faithfully flat map, and the regularity
  of the base-changed target are canonical derived data.

Source/core/bridge triage:
* `source-facing`: faithful-flat descent of `IsGeometricallyRegular`;
* `core/canonical`: `IsGeometricallyRegular`, `RingHom.FaithfullyFlat`, and
  `IsRegularRing`;
* `bridge/view`: tensor-product base change of `A → B` along `k → K`.
-/

-- Proof sketch: for any finite purely inseparable extension `K/k`, the base-changed map
-- `K ⊗[k] A → K ⊗[k] B` is faithfully flat by base change. Since `B` is geometrically regular
-- over `k`, the ring `K ⊗[k] B` is regular; regularity then descends along faithfully flat maps,
-- giving regularity of `K ⊗[k] A`. This verifies the defining conditions of geometric regularity
-- for `A`.
/-- Lemma 10.166.3: if `A → B` is a faithfully flat `k`-algebra map and `B` is geometrically
regular over `k`, then `A` is geometrically regular over `k`. -/
theorem isGeometricallyRegular_of_faithfullyFlat
    (hff : (algebraMap A B).FaithfullyFlat) [IsGeometricallyRegular k B] :
    IsGeometricallyRegular k A := sorry

end

end Algebra
