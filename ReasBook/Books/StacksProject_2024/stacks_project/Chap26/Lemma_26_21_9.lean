import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the canonical `pullback.mapDesc` instances
`AlgebraicGeometry.IsImmersion.instMapDescScheme` and
`AlgebraicGeometry.IsSeparated.instIsClosedImmersionMapDescScheme`; the quasi-separated clause is
the corresponding quasi-compactness of the same canonical comparison map. -/

variable {X Y T S : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T) (h : T ⟶ S)

/-- Lemma 26.21.9 (1): for morphisms `f : X ⟶ T` and `g : Y ⟶ T` of schemes and a morphism
`h : T ⟶ S`, the induced morphism `X ×_T Y ⟶ X ×_S Y` is an immersion. -/
@[stacks 01KR]
theorem isImmersion_pullbackMapDesc :
    IsImmersion (pullback.mapDesc f g h) := sorry

/-- Lemma 26.21.9 (2): if `h : T ⟶ S` is separated, then the induced morphism
`X ×_T Y ⟶ X ×_S Y` is a closed immersion. -/
@[stacks 01KR]
theorem isClosedImmersion_pullbackMapDesc_of_isSeparated [IsSeparated h] :
    IsClosedImmersion (pullback.mapDesc f g h) := sorry

/-- Lemma 26.21.9 (3): if `h : T ⟶ S` is quasi-separated, then the induced morphism
`X ×_T Y ⟶ X ×_S Y` is quasi-compact. -/
@[stacks 01KR]
theorem quasiCompact_pullbackMapDesc_of_quasiSeparated [QuasiSeparated h] :
    QuasiCompact (pullback.mapDesc f g h) := sorry

end AlgebraicGeometry
