import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism-property owner
-- `AlgebraicGeometry.QuasiSeparated` together with the bridge
-- `AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace`. The immediate dependency
-- `Lemma_29_15_6.lean` records the source hypothesis as `IsLocallyNoetherian X` on the source
-- scheme, so this item is best exposed as the source-facing morphism theorem on `QuasiSeparated`.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.15.7: let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian. Then
`f` is quasi-separated. -/
@[stacks 01T7]
theorem quasiSeparated_of_locallyOfFiniteType [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    QuasiSeparated f := sorry

end AlgebraicGeometry
