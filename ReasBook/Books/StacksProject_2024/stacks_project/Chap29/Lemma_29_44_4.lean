import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

section

/- Semantic recall: mathlib already exposes the canonical instance
`AlgebraicGeometry.IsFinite.instIsIntegralHom` and the scheme-morphism equivalence
`AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`, so this source item is
kept as the two direct Stacks-facing implications on those owners. -/

variable {X S : Scheme.{u}}

/-- Lemma 29.44.4 (1): a finite morphism is integral. -/
@[stacks 01WJ]
theorem finite_isIntegralHom (f : X ⟶ S) [IsFinite f] :
    IsIntegralHom f :=
  inferInstance

/-- Lemma 29.44.4 (2): an integral morphism which is locally of finite type is finite. -/
@[stacks 01WJ]
theorem integralHom_isFinite (f : X ⟶ S) [IsIntegralHom f] [LocallyOfFiniteType f] :
    IsFinite f :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).2 ⟨inferInstance, inferInstance⟩

end

end AlgebraicGeometry
