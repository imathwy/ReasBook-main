import Mathlib.AlgebraicGeometry.QuasiAffine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

-- Semantic recall: `lean_leansearch` found `Scheme.IsQuasiAffine.of_isImmersion` as the
-- canonical theorem behind the proof; this source-facing statement keeps the explicit
-- quasi-compact immersion hypotheses `IsImmersion i` and `QuasiCompact i`.

/-- Lemma 28.27.2: let `X` be a quasi-affine scheme. For any quasi-compact immersion
`i : X' ⟶ X`, the scheme `X'` is quasi-affine. -/
@[stacks 0BCK]
theorem of_isImmersion_of_quasiCompact
    {X X' : Scheme.{u}} {i : X' ⟶ X} (hX : X.IsQuasiAffine)
    (hi : IsImmersion i) (hqc : QuasiCompact i) :
    X'.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
