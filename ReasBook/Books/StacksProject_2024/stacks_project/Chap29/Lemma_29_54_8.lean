import Mathlib
import StacksProject_2024.Chap29.Lemma_29_53_8
import StacksProject_2024.Chap29.«29_54_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: Definition 29.53.3 already reuses mathlib's canonical relative-normalization
-- owner `f.normalization` for a quasi-compact, quasi-separated morphism `f : Y ⟶ X`. Lemma
-- 29.54.8 is source-facing at that owner level: if `Y` is reduced, then the normalization of `X`
-- in `Y` is reduced. For the absolute normalization of `X`, the source specializes to the
-- canonical morphism `genericPointSpectrumCoproductTo X`. The relative statement is already
-- recalled canonically in `Chap29/Lemma_29_53_8.lean` as
-- `Scheme.Hom.instIsReducedNormalization`; this file adds the corresponding absolute
-- specialization directly on that canonical owner. This avoids routing the public theorem through
-- the still-proof-stage `Definition_29_54_1` alias layer.

namespace Scheme

/-- The generic-point residue-field coproduct morphism of a reduced scheme is reduced-source. This
lets the relative-normalization reducedness lemma recover the source-facing normalization of a
scheme. -/
instance instIsReducedGenericPointSpectrumCoproduct (X : Scheme.{u}) [IsReduced X] :
    IsReduced (genericPointSpectrumCoproduct X) := by
  let 𝒰 : (genericPointSpectrumCoproduct X).OpenCover :=
    sigmaOpenCover
      (fun η : genericPoints X ↦
        Spec (CommRingCat.of (X.residueField η.1)))
  letI : ∀ η : 𝒰.I₀, IsReduced (𝒰.X η) := fun η ↦ by
    change IsReduced (Spec (CommRingCat.of (X.residueField η.1)))
    infer_instance
  exact IsReduced.of_openCover _ 𝒰

/-- Lemma 29.54.8 specialized to the canonical generic-point residue-field coproduct:
if `X` is reduced, then the normalization of `X` in `genericPointSpectrumCoproductTo X` is
reduced. Under Definition 29.54.1, this is the reducedness of the absolute normalization `X^ν`.
-/
@[stacks 035T]
theorem isReduced_normalization_of_isReduced
    (X : Scheme.{u}) [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] [IsReduced X] :
    IsReduced (Scheme.Hom.normalization (genericPointSpectrumCoproductTo X)) := by
  letI : IsReduced (genericPointSpectrumCoproduct X) := inferInstance
  infer_instance

end Scheme
end AlgebraicGeometry
