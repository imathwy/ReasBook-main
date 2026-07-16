import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v w

section

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable [Algebra.Smooth A B] [IsGeometricallyRegular k A]

/- Domain-style sampling pass:
* primary domain: geometric regularity of algebras over a field and its permanence under smooth
  algebra maps;
* sampled owner declarations:
  `IsGeometricallyRegular`,
  `IsGeometricallyRegular.isRegularRing_baseChange`,
  `Algebra.Smooth.baseChange`,
  `isRegularRing_of_smooth`;
* best owner abstraction: `IsGeometricallyRegular` is the core owner, while smoothness and the
  regularity of tensor base changes are derived API that should not be repackaged locally.

Primitive data vs. derived API:
* primitive public inputs: `[Algebra.Smooth A B]` and `[IsGeometricallyRegular k A]`;
* derived API: for each finite purely inseparable extension `K / k`, the base-changed algebra
  `K ⊗[k] B` is smooth over `K ⊗[k] A`, and its regularity follows from
  `isRegularRing_of_smooth`.

Source/core/bridge triage:
* `source-facing`: `isGeometricallyRegular_of_smooth`;
* `core/canonical`: `IsGeometricallyRegular`;
* `bridge/view`: smooth tensor base change along `k → K`.
-/
-- Proof sketch: for a finite purely inseparable field extension `K/k`, Lemma `10.137.3` gives
-- that `K ⊗[k] A → K ⊗[k] B` is smooth. Geometric regularity of `A` over `k` means `K ⊗[k] A`
-- is regular, and then Lemma `10.163.10` implies `K ⊗[k] B` is regular. This verifies the
-- defining conditions of geometric regularity for `B`.
/-- Lemma 10.166.4: if `A → B` is a smooth map of `k`-algebras and `A` is geometrically regular
over `k`, then `B` is geometrically regular over `k`. -/
theorem isGeometricallyRegular_of_smooth :
    IsGeometricallyRegular k B := sorry

/-- Smooth algebras over geometrically regular `k`-algebras are geometrically regular. -/
instance : IsGeometricallyRegular k B :=
  isGeometricallyRegular_of_smooth

end

end Algebra
