import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry
namespace Scheme

noncomputable section

namespace IdealSheafData

-- Semantic recall: `lean_leansearch` surfaced the canonical owner `Scheme.nilradical`, and local
-- Chapter 26/29 precedent packages the reduced induced closed subscheme on `Z` by
-- `Scheme.IdealSheafData.vanishingIdeal Z`.

variable {X : Scheme.{u}}

/-- Definition 26.12.5 (1): a scheme structure on a closed subset `Z ⊆ X` is a closed subscheme
of `X`, encoded as ideal-sheaf data `Z' : X.IdealSheafData`, whose underlying closed subset is
`Z`. -/
@[stacks 01J4]
class IsSchemeStructureOn (Z' : X.IdealSheafData) (Z : TopologicalSpace.Closeds X) : Prop where
  support_eq : Z'.support = Z

/-- A closed subscheme of `X` is a scheme structure on `Z` exactly when its support is `Z`. -/
theorem support_eq_iff
    {Z' : X.IdealSheafData} {Z : TopologicalSpace.Closeds X} :
    IsSchemeStructureOn Z' Z ↔ Z'.support = Z := sorry

/-- A support equality constructs a scheme structure on the corresponding closed subset. -/
@[stacks 01J4]
theorem isSchemeStructureOn_of_support_eq
    {Z' : X.IdealSheafData} {Z : TopologicalSpace.Closeds X}
    (support_eq : Z'.support = Z) :
    IsSchemeStructureOn Z' Z := sorry

/-- The source-facing specification for `IsSchemeStructureOn`: the closed subscheme datum has
underlying closed subset `Z`. -/
@[stacks 01J4]
theorem isSchemeStructureOn_spec
    {Z' : X.IdealSheafData} {Z : TopologicalSpace.Closeds X} :
    IsSchemeStructureOn Z' Z ↔ Z'.support = Z := sorry

end IdealSheafData

variable (X : Scheme.{u})

/-- Definition 26.12.5 (2): the reduced induced scheme structure on a closed subset `Z ⊆ X` is
the canonical closed subscheme datum `vanishingIdeal Z` constructed in Lemma `26.12.4`. -/
@[stacks 01J4]
abbrev reducedInducedSchemeStructure (Z : TopologicalSpace.Closeds X) : X.IdealSheafData :=
  vanishingIdeal Z

/-- The reduced induced scheme structure on `Z` is a scheme structure on `Z`. -/
instance instIsSchemeStructureOnReducedInducedSchemeStructure
    (Z : TopologicalSpace.Closeds X) :
    IdealSheafData.IsSchemeStructureOn (reducedInducedSchemeStructure X Z) Z := sorry

/-- The support of the reduced induced scheme structure on `Z` is exactly `Z`. -/
theorem support_reducedInducedSchemeStructure (Z : TopologicalSpace.Closeds X) :
    (reducedInducedSchemeStructure X Z).support = Z := sorry

/-- Definition 26.12.5 (3): the reduction `X_red` of a scheme `X` is the reduced induced scheme
structure on `X` itself, formalized as the nilradical subscheme `X.nilradical.subscheme`. -/
@[stacks 01J4]
abbrev reduction : Scheme.{u} :=
  X.nilradical.subscheme

/-- The reduction of `X` is the nilradical subscheme of `X`. -/
theorem reduction_eq_nilradicalSubscheme :
    reduction X = X.nilradical.subscheme := sorry

end

end Scheme

end AlgebraicGeometry
