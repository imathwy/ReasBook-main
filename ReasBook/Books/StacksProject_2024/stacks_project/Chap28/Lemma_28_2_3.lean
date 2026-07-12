import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

-- Semantic recall: the canonical owner is `CompactOpens X` for quasi-compact opens. Part (1)
-- uses the quasi-separatedness owner `QuasiSeparatedSpace.inter_isCompact`, and part (2) packages
-- the same compact-intersection content as retrocompactness for compact open subsets.
variable {X : Scheme.{u}} [QuasiSeparatedSpace X]

/-- Lemma 28.2.3 (1): if `U` and `V` are quasi-compact open subsets of a quasi-separated scheme
`X`, then `U ∩ V` is quasi-compact. -/
@[stacks 054D]
theorem compactOpen_inter_isCompact (U V : CompactOpens X) :
    IsCompact ((U : Set X) ∩ (V : Set X)) :=
  QuasiSeparatedSpace.inter_isCompact
    (U : Set X) (V : Set X) U.isOpen U.isCompact V.isOpen V.isCompact

end

section

variable {X : Scheme.{u}} [QuasiSeparatedSpace X]

/-- Lemma 28.2.3 (2): every quasi-compact open subset of a quasi-separated scheme `X` is
retrocompact in `X`. -/
@[stacks 054D]
theorem compactOpen_isRetrocompact (U : CompactOpens X) :
    IsRetrocompact (U : Set X) := by
  intro V hV hV_open
  let Vc : CompactOpens X := ⟨⟨V, hV⟩, hV_open⟩
  have hVc : (Vc : Set X) = V := rfl
  simpa [hVc] using compactOpen_inter_isCompact U Vc

end

end AlgebraicGeometry.Scheme
