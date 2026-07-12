import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

variable {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsRetrocompact`,
-- `Scheme.IdealSheafData.support`, and affine section ideals; local Chapter 28 precedent
-- represents finite-type ideal sheaves by finite generation of all affine section ideals.

/-- Lemma 28.24.1 (1): if `X` is a quasi-compact and quasi-separated scheme and `U` is an open
subscheme of `X`, then `U` is retrocompact in `X` if and only if `U` is quasi-compact. -/
@[stacks 01PH]
theorem isRetrocompact_iff_isCompact_open_of_qcqs (U : X.Opens) :
    IsRetrocompact (U : Set X) ↔ IsCompact (U : Set X) := sorry

/-- Lemma 28.24.1 (2): if `X` is a quasi-compact and quasi-separated scheme and `U` is an open
subscheme of `X`, then `U` is retrocompact in `X` if and only if `U` is a finite union of affine
opens. -/
@[stacks 01PH]
theorem isRetrocompact_iff_exists_finite_iSup_affineOpens (U : X.Opens) :
    IsRetrocompact (U : Set X) ↔
      ∃ n : ℕ, ∃ V : Fin n → X.affineOpens,
        U = ⨆ i, (V i : X.Opens) := sorry

/-- Lemma 28.24.1 (3): if `X` is a quasi-compact and quasi-separated scheme and `U` is an open
subscheme of `X`, then `U` is retrocompact in `X` if and only if there is a finite type
quasi-coherent ideal sheaf whose vanishing locus is the closed complement `X \ U`, set
theoretically. In this formalization finite type is exposed through finite generation of the
ideal on every affine open. -/
@[stacks 01PH]
theorem isRetrocompact_iff_exists_finiteTypeIdealSheaf_support_compl (U : X.Opens) :
    IsRetrocompact (U : Set X) ↔
      ∃ I : X.IdealSheafData,
        (∀ V : X.affineOpens, (I.ideal V).FG) ∧
          (U : Set X)ᶜ = (I.support : Set X) := sorry

end Scheme
end AlgebraicGeometry
