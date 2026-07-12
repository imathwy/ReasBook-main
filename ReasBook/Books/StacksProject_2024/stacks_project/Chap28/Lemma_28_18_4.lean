import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

-- Semantic recall: `lean_leansearch` surfaced the canonical map `Scheme.toSpecΓ`, the instance
-- `Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`, and the constructor
-- `Scheme.IsQuasiAffine.mk`. The source lemma is therefore formalized as atomic statements about
-- the canonical morphism `X.toSpecΓ`, without introducing a duplicate wrapper notion.

variable {X : Scheme.{u}}

/-- Lemma 28.18.4 (1): if a scheme `X` is quasi-affine, then its canonical morphism
`X ⟶ Spec(Γ(X, \mathcal{O}_X))` is an open immersion. -/
@[stacks 01P9]
theorem toSpecΓ_isOpenImmersion (hX : X.IsQuasiAffine) :
    IsOpenImmersion X.toSpecΓ := sorry

/-- Lemma 28.18.4 (2): if a scheme `X` is quasi-affine, then its canonical morphism
`X ⟶ Spec(Γ(X, \mathcal{O}_X))` is quasi-compact. -/
@[stacks 01P9]
theorem toSpecΓ_quasiCompact (hX : X.IsQuasiAffine) :
    QuasiCompact X.toSpecΓ := sorry

/-- Lemma 28.18.4 (3): if the canonical morphism `X ⟶ Spec(Γ(X, \mathcal{O}_X))` is a
quasi-compact open immersion, then `X` is quasi-affine. -/
@[stacks 01P9]
theorem of_toSpecΓ_quasiCompact_of_isOpenImmersion
    (hqc : QuasiCompact X.toSpecΓ) (himm : IsOpenImmersion X.toSpecΓ) :
    X.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
