import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_25_4
import StacksProject_2024.stacks_project.Chap31.Definition_31_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Z S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical direct-image owner
-- `Scheme.Modules.pushforward`; local Chapter 29 provides the quasi-coherence instance for affine
-- pushforwards, and Chapter 31 fixes `relativeWeakAss` as the source-facing relative owner.

/-- Lemma 31.8.3: let `f : X ⟶ S` be a morphism of schemes, let `i : Z ⟶ X` be a finite
morphism, and let `\mathcal F` be a quasi-coherent `\mathcal O_Z`-module. Then the relative weak
assassin of `i_* \mathcal F` over `X/S` is the image under `i` of the relative weak assassin of
`\mathcal F` over `Z/S`. -/
@[stacks 0CUD]
theorem relativeWeakAss_pushforward_eq_image_of_isFinite
    (f : X ⟶ S) (i : Z ⟶ X) [IsFinite i]
    (ℱ : Z.Modules) [ℱ.IsQuasicoherent] :
    relativeWeakAss f ((Scheme.Modules.pushforward i).obj ℱ) =
      i.base '' (relativeWeakAss (i ≫ f) ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
