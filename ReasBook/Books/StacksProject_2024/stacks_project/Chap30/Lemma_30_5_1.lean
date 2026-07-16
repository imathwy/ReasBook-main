import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_25_4
import StacksProject_2024.stacks_project.Chap30.Lemma_30_2_3

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-module owners
-- `Scheme.Modules.pushforward` and `Scheme.Modules.pullback`, while local Chapter 29/30 precedent
-- already fixes affine pushforward quasi-coherence and higher direct images on the
-- `Functor.rightDerived` surface.

variable {X X' S S' : Scheme.{u}}

/-- Lemma 30.5.1 (1): if `f : X ⟶ S` is affine and `\mathcal F` is a quasi-coherent
`\mathcal O_X`-module, then the ordinary direct image `f_* \mathcal F` identifies with the
degree-zero higher direct image `R^0 f_* \mathcal F`. -/
@[stacks 02KG]
theorem pushforward_isomorphic_degreeZeroHigherDirectImage_of_isAffineHom
    (f : X ⟶ S) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((Scheme.Modules.pushforward f).obj ℱ)
      (((Scheme.Modules.pushforward f).rightDerived 0).obj ℱ) := sorry

/-- Lemma 30.5.1 (2): if `f : X ⟶ S` is affine and `\mathcal F` is a quasi-coherent
`\mathcal O_X`-module, then `f_* \mathcal F` is a quasi-coherent `\mathcal O_S`-module. -/
@[stacks 02KG]
theorem pushforward_obj_isQuasicoherent_of_isAffineHom
    (f : X ⟶ S) [IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (((Scheme.Modules.pushforward f).obj ℱ) : S.Modules).IsQuasicoherent := sorry

/-- Lemma 30.5.1 (3): for an affine morphism `f : X ⟶ S`, a quasi-coherent
`\mathcal O_X`-module `\mathcal F`, and a cartesian base-change square
`\xymatrix{
X' \ar[r]^{g'} \ar[d]_{f'} & X \ar[d]^f \\
S' \ar[r]^g & S,
}`
the pulled-back pushforward `g^* f_* \mathcal F` identifies with the pushforward
`f'_* (g')^* \mathcal F`. -/
@[stacks 02KG]
theorem affineBaseChange_pushforward_isomorphic
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj ℱ)) : S'.Modules)
      (((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj ℱ)) : S'.Modules) :=
  sorry

end AlgebraicGeometry.Scheme
