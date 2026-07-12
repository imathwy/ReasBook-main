import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical closed-subscheme owner
-- `Scheme.IdealSheafData.subscheme`, and direct Lean checks confirmed that `⊔`/`⊓` on
-- `X.IdealSheafData` are the pointwise sum/intersection lattice operations on affine-open ideals.

variable {X : Scheme.{u}}

/-- Definition 29.4.4 (1): for quasi-coherent ideal sheaves `I, J : X.IdealSheafData` defining
closed subschemes of `X`, the scheme theoretic intersection is the closed subscheme of `X` cut
out by the sum ideal sheaf `I + J`, i.e. by `I ⊔ J`. -/
noncomputable abbrev schemeTheoreticIntersection (I J : X.IdealSheafData) : Scheme :=
  (I ⊔ J).subscheme

/-- The scheme theoretic intersection is the subscheme attached to the supremum ideal sheaf. -/
@[simp] theorem schemeTheoreticIntersection_eq_subscheme_sup (I J : X.IdealSheafData) :
    schemeTheoreticIntersection I J = (I ⊔ J).subscheme := rfl

/-- Definition 29.4.4 (2): for quasi-coherent ideal sheaves `I, J : X.IdealSheafData` defining
closed subschemes of `X`, the scheme theoretic union is the closed subscheme of `X` cut out by
the intersection ideal sheaf `I ∩ J`, i.e. by `I ⊓ J`. -/
noncomputable abbrev schemeTheoreticUnion (I J : X.IdealSheafData) : Scheme :=
  (I ⊓ J).subscheme

/-- The scheme theoretic union is the subscheme attached to the infimum ideal sheaf. -/
@[simp] theorem schemeTheoreticUnion_eq_subscheme_inf (I J : X.IdealSheafData) :
    schemeTheoreticUnion I J = (I ⊓ J).subscheme := rfl

end AlgebraicGeometry.Scheme
