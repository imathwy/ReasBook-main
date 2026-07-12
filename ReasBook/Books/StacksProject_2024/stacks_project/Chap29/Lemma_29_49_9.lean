import StacksProject_2024.Chap29.Definition_29_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme.RationalMap

/- Semantic recall / owner check:
- `source-facing`: Lemma 29.49.9 (2) is the uniqueness statement for a representative on the
  canonical domain `φ.domain`;
- `core/canonical`: mathlib already owns the canonical representative `φ.toPartialMap`, the
  round-trip theorem `Scheme.RationalMap.toRationalMap_toPartialMap`, and the over-`S` instance on
  `φ.toPartialMap`;
- `bridge/view`: only the uniqueness theorem below, which packages the same-domain consequence of
  `Scheme.PartialMap.toRationalMap_eq_iff` in the source's chosen presentation.
-/

variable {S X Y : Scheme}

/- Lemma 29.49.9 (1): if `X` is reduced and `Y` is separated, then the canonical morphism
`φ.toPartialMap.hom : X.restrict φ.domain.isOpenEmbedding ⟶ Y` represents the rational map `φ`.
This is the canonical owner theorem `Scheme.RationalMap.toRationalMap_toPartialMap`. -/
#check Scheme.RationalMap.toRationalMap_toPartialMap

/-- Lemma 29.49.9 (2): if `X` is reduced and `Y` is separated, then any morphism
`f : X.restrict φ.domain.isOpenEmbedding ⟶ Y` representing `φ` is equal to the canonical
representative `φ.toPartialMap.hom`. -/
@[stacks 0A1Y]
theorem eq_toPartialMap_hom_of_toRationalMap [IsReduced X] [Y.IsSeparated] (φ : X ⤏ Y)
    (f : X.restrict φ.domain.isOpenEmbedding ⟶ Y)
    (hf : (⟨φ.domain, φ.dense_domain, f⟩ : X.PartialMap Y).toRationalMap = φ) :
    f = φ.toPartialMap.hom := by
  open Scheme.PartialMap in
    have hpq : (⟨φ.domain, φ.dense_domain, f⟩ : X.PartialMap Y) = φ.toPartialMap :=
      (equiv_iff_of_domain_eq_of_isSeparated rfl).mp
        (toRationalMap_eq_iff.mp (hf.trans (toRationalMap_toPartialMap φ).symm))
  simpa using congrArg PartialMap.hom hpq

section

variable [S.IsSeparated] [X.Over S] [Y.Over S] [IsReduced X] [Y.IsSeparated]
variable (φ : X ⤏ Y) [φ.IsOver S]

/- Lemma 29.49.9 (3): if `X` and `Y` are schemes over a separated scheme `S`, `X` is reduced,
`Y` is separated, and `φ` is an `S`-rational map, then the canonical representative on `φ.domain`
is a morphism over `S`. This is the canonical instance
`Scheme.instIsOverToPartialMapOfIsSeparatedOfIsOver`. -/
#check Scheme.instIsOverToPartialMapOfIsSeparatedOfIsOver

end

end Scheme.RationalMap
end AlgebraicGeometry
