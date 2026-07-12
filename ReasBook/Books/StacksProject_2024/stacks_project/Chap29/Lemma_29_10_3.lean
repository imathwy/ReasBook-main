import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recovered the canonical scheme-morphism owner
-- `AlgebraicGeometry.UniversallyInjective` together with the diagonal characterizations
-- `AlgebraicGeometry.UniversallyInjective.iff_diagonal` and
-- `AlgebraicGeometry.IsSeparated.isSeparated_eq_diagonal_isClosedImmersion`. No exact upstream
-- theorem for this Stacks item was found in the current workspace, so the source-facing implication
-- is stated directly on those canonical owners.

/-- Lemma 29.10.3: a universally injective morphism of schemes is separated. -/
@[stacks 05VE]
theorem universallyInjective_isSeparated
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : UniversallyInjective f) :
    IsSeparated f := sorry

end AlgebraicGeometry
