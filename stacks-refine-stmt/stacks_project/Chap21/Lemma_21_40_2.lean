import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap21.Lemma_21_40_1
import stacks_project.Chap21.Remark_21_38_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.Fiber

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}]
variable [∀ V : X, HasProjectiveResolutions ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v})]
variable [(projectionAbelianInverseImage X P).IsRightAdjoint]
variable [(projectionAbelianLowerShriek X P).Additive]
variable [HasProjectiveResolutions
  (Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v})]

/-- The pullback precomposition functor on fiberwise abelian presheaves, written explicitly so
this file can state the projective-preservation assumption needed by
`fiberCategoryHomologySheaf`. -/
private abbrev fiberPullbackPrecomp
    {U V : X} (f : V ⟶ U) :
    ((P.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      ((P.p.Fiber U)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (Functor.whiskeringLeft (P.p.Fiber U)ᵒᵖ (P.p.Fiber V)ᵒᵖ AddCommGrpCat.{max u v}).obj
    (((canonicalPullbackChoice P.p).pullbackFunctor f).op)

variable [∀ ⦃U V : X⦄ (f : V ⟶ U), (fiberPullbackPrecomp X P f).PreservesProjectiveObjects]

-- Proof sketch: for `n = 0`, this is Lemma `21.38.8`, which identifies `π_! ℱ` with the
-- sheafification of the fiberwise colimit presheaf, i.e. with `L_0(ℱ)`. Lemma `21.40.1` and the
-- vanishing argument from the Stacks proof show that `n ↦ fiberCategoryHomologySheaf X P ℱ.1 n`
-- forms the universal delta functor extending degree zero, so uniqueness of universal delta
-- functors identifies it with the left derived functors of `π_!`.
/-- Lemma 21.40.2: under the assumptions of Situation `21.38.1`, for an abelian sheaf `ℱ` on the
total site of `P` and `n ≥ 0`, the `n`-th left derived functor `L_n\pi_!(\mathcal F)` of the
abelian lower shriek is canonically isomorphic to the sheaf `L_n(\mathcal F)` constructed in
Lemma `21.40.1`, namely `fiberCategoryHomologySheaf X P ℱ.1 n`. -/
theorem projectionAbelianLowerShriek_leftDerived_isomorphic_fiberCategoryHomologySheaf
    (ℱ : Sheaf (inheritedTopology X.siteTopology P) AddCommGrpCat.{max u v}) (n : ℕ) :
    IsIsomorphic
      (((projectionAbelianLowerShriek X P).leftDerived n).obj ℱ)
      (fiberCategoryHomologySheaf X P ℱ.1 n) := sorry

end

end FibredCategoryOver
end CategoryTheory
