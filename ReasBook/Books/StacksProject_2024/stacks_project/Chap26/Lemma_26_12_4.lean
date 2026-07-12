import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Scheme.IdealSheafData

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical owner
-- `Scheme.IdealSheafData.vanishingIdeal` together with
-- `Scheme.IdealSheafData.coe_support_vanishingIdeal`, so the source-faithful statement is best
-- expressed on ideal-sheaf data for closed subschemes of `X`.

namespace AlgebraicGeometry

/-- The canonical closed subscheme attached to a closed subset is reduced. -/
@[stacks 01J3]
theorem isReduced_subscheme_vanishingIdeal (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal T).subscheme := sorry

/-- Lemma 26.12.4: for a scheme `X` and a closed subset `T ⊆ X`, there exists a unique closed
subscheme of `X`, encoded as ideal-sheaf data `Z : X.IdealSheafData`, whose underlying closed
subset is `T` and which is reduced. -/
@[stacks 01J3]
theorem existsUnique_reduced_subscheme_with_support
    (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    ∃! Z : X.IdealSheafData, Z.support = T ∧ IsReduced Z.subscheme := sorry

/-- A reduced closed subscheme of `X` with underlying closed subset `T` is the canonical
subscheme cut out by `vanishingIdeal T`. -/
@[stacks 01J3]
theorem eq_vanishingIdeal_of_support_eq_of_isReduced
    {X : Scheme.{u}} {T : TopologicalSpace.Closeds X} (Z : X.IdealSheafData)
    (hT : Z.support = T) [IsReduced Z.subscheme] :
    Z = vanishingIdeal T := sorry

end AlgebraicGeometry
