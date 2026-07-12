import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.PurelyInseparable.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owner
-- `AlgebraicGeometry.UniversallyInjective`, while mathlib's source still lists radicial
-- morphisms as a TODO equivalence rather than a declared owner, so clause `(2)` is formalized
-- directly below.

/- Definition 29.10.1 (1): the source definition of a universally injective morphism is exactly
the canonical mathlib owner `AlgebraicGeometry.UniversallyInjective`. -/
#check AlgebraicGeometry.UniversallyInjective

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

namespace Scheme.Hom

/-- The residue-field map induced by a morphism of schemes defines the canonical algebra structure
on residue fields. -/
noncomputable instance residueFieldAlgebra (f : X ⟶ S) (x : X) :
    Algebra (S.residueField (f x)) (X.residueField x) :=
  (f.residueFieldMap x).hom.toAlgebra

end Scheme.Hom

/-- Definition 29.10.1: a morphism of schemes is radicial if it is injective on points and,
for every point `x : X`, the induced residue-field extension `κ(f(x)) → κ(x)` is purely
inseparable. -/
class Radicial (f : X ⟶ S) : Prop where
  toInjective : Function.Injective f
  residueField_isPurelyInseparable (x : X) :
    IsPurelyInseparable (S.residueField (f x)) (X.residueField x)

/-- A radicial morphism is injective on underlying points. -/
instance [h : Radicial f] : Function.Injective f :=
  h.toInjective

/-- A radicial morphism induces a purely inseparable extension on each residue field. -/
theorem residueField_isPurelyInseparable (x : X) [h : Radicial f] :
    IsPurelyInseparable (S.residueField (f x)) (X.residueField x) := by
  simpa using h.residueField_isPurelyInseparable x

/-- A radicial morphism of schemes is exactly a universally injective morphism. -/
theorem radicial_iff_universallyInjective : Radicial f ↔ UniversallyInjective f := by
  sorry

/-- A radicial morphism is universally injective. -/
instance instUniversallyInjectiveOfRadicial [Radicial f] : UniversallyInjective f :=
  (radicial_iff_universallyInjective f).1 inferInstance

/-- A universally injective morphism is radicial. -/
theorem radicial_of_universallyInjective [UniversallyInjective f] : Radicial f :=
  (radicial_iff_universallyInjective f).2 inferInstance

end

end AlgebraicGeometry
