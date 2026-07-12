import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Adjunction
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` surfaced the affine associated-module-sheaf owner
-- `ModuleCat.tilde` and the affine adjunction `tilde.adjunction`; nearby Chapter 26 files use
-- `moduleSpecΓFunctor.obj ℱ` for the `R`-module of global sections on `Spec(R)`.

section

variable (R : CommRingCat.{u})
variable (ℱ : (Spec R).Modules)

/-- Lemma 26.7.4: on the affine scheme `X = Spec(R)`, if `ℱ` is a quasi-coherent
`𝒪_X`-module, then the canonical counit
`\widetilde{Γ(X, ℱ)} ⟶ ℱ` is an isomorphism. Equivalently, `ℱ` is isomorphic to the
sheaf associated to the `R`-module of global sections. -/
@[stacks 01IA]
theorem isIso_tildeCounit_of_isQuasicoherent [ℱ.IsQuasicoherent] :
    IsIso ((counit tilde.adjunction).app ℱ) := sorry

end
