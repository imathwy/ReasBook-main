import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap18.Lemma_18_27_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.1:
- primary domain: tensor/internal-Hom calculus in the braided monoidal closed category
  `RingedSpace.Modules X`;
- core/canonical owner: the generic theorem
  `CategoryTheory.MonoidalClosed.internalHomTensorIso`;
- bridge/view: the ringed-space specialization obtained by applying that owner theorem to
  `\mathcal O_X`-modules.

This file should therefore stay at the ringed-space specialization layer and avoid replaying the
right-adjoint-uniqueness construction locally. -/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory X.Modules]
variable [BraidedCategory X.Modules]
variable [MonoidalClosed X.Modules]

/-- Lemma 17.22.1: for `\mathcal O_X`-modules `ℱ`, `𝒢`, and `ℋ`, there is a canonical
isomorphism
`𝒣om_{\mathcal O_X}(ℱ ⊗ 𝒢, ℋ) ≅ 𝒣om_{\mathcal O_X}(ℱ, 𝒣om_{\mathcal O_X}(𝒢, ℋ))`.
This is the generic braided closed-monoidal currying isomorphism specialized to
`RingedSpace.Modules X`. -/
@[stacks 01CN]
noncomputable abbrev internalHomTensorIso
    (ℱ 𝒢 ℋ : X.Modules) :=
  (@CategoryTheory.MonoidalClosed.internalHomTensorIso X.Modules _ _ _ _ ℱ 𝒢 ℋ).symm

end AlgebraicGeometry.RingedSpace
