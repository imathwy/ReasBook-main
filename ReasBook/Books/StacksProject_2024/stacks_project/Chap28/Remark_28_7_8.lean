import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_7_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsIntegral`,
-- `ConnectedSpace`, `IrreducibleSpace`, and `IsAffine`. Local Chapter 28 precedent uses
-- `Scheme.isNormal` for normal schemes and `X.presheaf.stalk x` for local rings.

/-- Remark 28.7.8 (1): if a normal scheme `X` is locally Noetherian, then `X` is integral if
and only if `X` is connected. -/
@[stacks 033O]
theorem isIntegral_iff_connectedSpace_of_isNormal_of_isLocallyNoetherian
    (hX : X.isNormal) :
    IsIntegral X ↔ ConnectedSpace X := sorry

/-- Remark 28.7.8 (2): there exists a connected affine normal scheme whose local rings
`O_{X, x}` are domains for all points `x`, but whose underlying topological space is not
irreducible. -/
@[stacks 033O]
theorem exists_connected_affine_normal_stalks_isDomain_not_irreducibleSpace :
    ∃ X : Scheme.{u}, ∃ hAff : IsAffine X, ∃ hNorm : X.isNormal,
      ∃ hConn : ConnectedSpace X, ∃ hStalks : (∀ x : X, IsDomain (X.presheaf.stalk x)),
        ¬ IrreducibleSpace X := sorry

end
