import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsAffineHom` as the canonical
-- owner for affine morphisms, and local Chapter 20/30 precedent fixes higher direct images on the
-- direct derived-pushforward owner `((Scheme.Modules.pushforward f).rightDerived i).obj ℱ`.

/-- Lemma 30.2.3: let `f : X ⟶ S` be an affine morphism of schemes and let `\mathcal F` be a
quasi-coherent `\mathcal O_X`-module. Then `R^i f_* \mathcal F = 0` for all `i > 0`. -/
@[stacks 01XC]
theorem higherDirectImageModule_isZero_of_isAffineHom
    (f : X ⟶ S) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ) := sorry

end AlgebraicGeometry.Scheme
