import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Adjunction
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

section

variable (R : CommRingCat.{u})

-- Semantic recall: `lean_leansearch` surfaced `ModuleCat.tilde`, the affine global-sections
-- functor `moduleSpecΓFunctor`, and the affine adjunction `tilde.adjunction`; the source
-- equivalence is recorded through the quasi-coherent landing statement and the two invertible
-- unit/counit conditions for that adjunction on `Spec(R)`.

/-- Lemma 26.7.5 (1): for the affine scheme `X = Spec(R)`, the affine associated-module
sheaf functor `M |-> \widetilde M` lands in quasi-coherent `O_X`-modules. -/
@[stacks 01IB]
theorem affineModuleEquivalence_tilde_isQuasicoherent (M : ModuleCat R) :
    (tilde M).IsQuasicoherent := sorry

/-- Lemma 26.7.5 (2): for `X = Spec(R)`, the unit of the affine
`\widetilde{(-)} |- Gamma(X, -)` adjunction is an isomorphism on every `R`-module. -/
@[stacks 01IB]
theorem affineModuleEquivalence_unit_isIso (M : ModuleCat R) :
    IsIso ((unit tilde.adjunction).app M) := sorry

/-- Lemma 26.7.5 (3): for `X = Spec(R)`, the counit
`\widetilde{Gamma(X, F)} -> F` of the affine `\widetilde{(-)} |- Gamma(X, -)` adjunction is an
isomorphism for every quasi-coherent `O_X`-module `F`. These two isomorphism statements make
the functors `M |-> \widetilde M` and `F |-> Gamma(X, F)` quasi-inverse equivalences between
`R`-modules and quasi-coherent modules on `Spec(R)`. -/
@[stacks 01IB]
theorem affineModuleEquivalence_counit_isIso_of_isQuasicoherent
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    IsIso ((counit tilde.adjunction).app F) := sorry

end
