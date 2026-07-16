import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pushforward` as the canonical
-- module direct-image owner. Local Chapter 31 precedent fixes weakly associated points through
-- `Scheme.Modules.weakAss`, while nearby image statements use `Set.range f.base`.

/-- Helper: pushforward of a quasi-coherent module along a quasi-compact and quasi-separated
scheme morphism is quasi-coherent. -/
instance instIsQuasicoherentPushforwardOfQuasiCompactQuasiSeparated
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj ℱ).IsQuasicoherent := sorry

variable (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- Lemma 31.5.9: Let `f : X \to S` be a quasi-compact and quasi-separated morphism of schemes.
Let `\mathcal F` be a quasi-coherent `\mathcal O_X`-module. If `s \in S` is not in the image of
`f`, then `s` is not weakly associated to `f_* \mathcal F`. -/
@[stacks 0AVN]
theorem not_mem_weakAss_pushforward_of_not_mem_range
    (s : S) (hs : s ∉ Set.range f.base) :
    s ∉ ((Scheme.Modules.pushforward f).obj ℱ).weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
