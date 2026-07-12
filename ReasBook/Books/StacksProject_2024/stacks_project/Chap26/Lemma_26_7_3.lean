import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical affine associated-module owner
-- `ModuleCat.tilde`, the scheme-module functors `Scheme.Modules.pullback` and
-- `Scheme.Modules.pushforward`, and the change-of-rings functors `ModuleCat.extendScalars` and
-- `ModuleCat.restrictScalars`. The tag evidence is consistent: Stacks tag `01I9` is the source
-- URL tag for Lemma 26.7.3.

section

variable (R S : CommRingCat.{u}) (φ : R ⟶ S)

/-- Lemma 26.7.3 (1): for the affine morphism `Spec(S) ⟶ Spec(R)` induced by
`φ : R ⟶ S`, pulling back the affine module sheaf `\widetilde M` identifies functorially in the
`R`-module `M` with the affine module sheaf associated to extension of scalars
`S ⊗_R M`. -/
@[stacks 01I9]
theorem tildePullbackSpecMap_isIsomorphic_extendScalars :
    IsIsomorphic (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ))
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S) := sorry

/-- Lemma 26.7.3 (2): for the affine morphism `Spec(S) ⟶ Spec(R)` induced by
`φ : R ⟶ S`, pushing forward the affine module sheaf `\widetilde N` identifies functorially in the
`S`-module `N` with the affine module sheaf associated to the same module after restriction of
scalars along `R ⟶ S`. -/
@[stacks 01I9]
theorem tildePushforwardSpecMap_isIsomorphic_restrictScalars :
    IsIsomorphic (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ))
      (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R) := sorry

end
