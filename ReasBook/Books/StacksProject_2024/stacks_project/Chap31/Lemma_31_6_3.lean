import Mathlib
import StacksProject_2024.Chap10.Lemma_10_66_13
import StacksProject_2024.Chap29.Lemma_29_25_4
import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the mathlib owners `IsFinite` and
-- `Scheme.Modules.pushforward`; local Chapter 31 precedent fixes the scheme-side owner as
-- `Scheme.Modules.weakAss`, while Chapter 10 provides the affine ring-level finite-map analogue
-- `weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite`.

/-- Lemma 31.6.3: let `f : X ⟶ S` be a finite morphism of schemes and let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. Then the weakly associated points of the pushforward
`f_* \mathcal F` are exactly the image under `f` of the weakly associated points of
`\mathcal F`. -/
@[stacks 05EZ]
theorem weakAss_pushforward_eq_image_of_isFinite :
    ((Scheme.Modules.pushforward f).obj ℱ).weakAss = f.base '' ℱ.weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
