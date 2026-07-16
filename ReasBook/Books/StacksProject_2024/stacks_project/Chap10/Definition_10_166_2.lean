import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_110_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

namespace Algebra

universe u v w

/- Domain-style sampling:
* primary domain: geometric regularity of field algebras via regularity of tensor-product base
  changes;
* sampled owner declarations:
  `Algebra.IsGeometricallyReduced`,
  `Algebra.IsGeometricallyNormal`,
  `AlgebraicGeometry.geometrically`,
  `IsRegularRingMap`;
* best owner abstraction: the chapter's field-algebra owner
  `IsGeometricallyRegular k A`; the scheme-level `geometrically` API is a more general
  ambient owner, but using it directly here would force every downstream algebra lemma through an
  affine bridge;
* primitive data vs. derived API:
  the primitive owner data are exactly the regularity statements for tensor base changes along
  finite purely inseparable field extensions;
  regularity and Noetherianity of the underlying ring are derived consequences. The regular-ring
  bridge must keep `k` explicit, because `IsRegularRing A` alone does not determine the ambient
  field algebra structure.

Source/core/bridge triage:
* `source-facing`: `IsGeometricallyRegular k A`;
* `core/canonical`: `IsRegularRing`;
* `bridge/view`: the tensor-base-change test against finite purely inseparable field extensions.
-/

/-- Definition 10.166.2: a commutative `k`-algebra is geometrically regular over `k` if every
finite purely inseparable field extension of `k` yields a regular tensor base-change ring. -/
@[mk_iff
  isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
class IsGeometricallyRegular (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] :
    Prop where
  isRegularRing_baseChange (K : Type (max u v)) [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] A)

attribute [instance] IsGeometricallyRegular.isRegularRing_baseChange

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- A field is geometrically regular over itself. -/
instance : IsGeometricallyRegular k k := sorry

/-- A geometrically regular algebra over a field is a regular ring. -/
theorem isRegularRing_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsGeometricallyRegular k A] :
    IsRegularRing A := sorry

end

end Algebra
