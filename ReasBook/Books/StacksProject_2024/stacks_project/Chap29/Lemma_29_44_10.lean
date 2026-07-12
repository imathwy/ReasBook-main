import StacksProject_2024.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` found mathlib's canonical instance
  `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite`, saying finite morphisms are locally
  quasi-finite;
- local Chapter 29 precedent defines the Stacks-facing global owner as
  `Scheme.Hom.QuasiFinite`, i.e. quasi-compact plus locally quasi-finite.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.44.10: a finite morphism is quasi-finite. -/
@[stacks 02NU]
theorem quasiFinite_of_finite [IsFinite f] :
    QuasiFinite f := sorry

end Scheme.Hom
end AlgebraicGeometry
