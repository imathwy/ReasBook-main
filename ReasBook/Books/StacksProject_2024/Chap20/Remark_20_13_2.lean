import Mathlib
import stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

-- Proof sketch: unfold the definition of module pushforward on sections and then forget the module
-- structures to additive groups. Evaluating `f_* ℱ` on the terminal open subset of `Y` is by
-- definition evaluation of `ℱ` on the inverse image of that open, and `f^{-1}(Y) = X`; applying
-- this termwise to an injective resolution gives the additive-complex identity
-- `Γ(X, \mathcal I^\bullet) = Γ(Y, f_* \mathcal I^\bullet)` used in the remark.
/-- Remark 20.13.2: for a morphism of ringed spaces `f : X ⟶ Y`, the global sections of the
pushforward `f_* \mathcal F`, after forgetting the module structures, agree with the global
sections of `\mathcal F`. Applied termwise to an injective resolution `\mathcal I^\bullet`, this
is the identity
`\Gamma(X, \mathcal I^\bullet) = \Gamma(Y, f_* \mathcal I^\bullet)` used in the explanation of
Lemma `20.13.1`. -/
lemma modulePushforward_underlyingGlobalSections_eq_underlyingGlobalSections
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (ℱ : (RingedSpace.Modules X)) :
    (forget₂ (ModuleCat (globalSectionsRing Y)) AddCommGrpCat).obj
        (((RingedSpace.Hom.pushforward f).obj ℱ).1.obj (op (⊤ : Opens Y.carrier))) =
      (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat).obj
        (ℱ.1.obj (op (⊤ : Opens X.carrier))) := sorry

end AlgebraicGeometry.RingedSpace
