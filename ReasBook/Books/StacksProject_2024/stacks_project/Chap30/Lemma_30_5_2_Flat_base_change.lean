import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the scheme flatness/base-change owner
-- `AlgebraicGeometry.Flat`, `Scheme.Modules.pullback`, and the right-derived-pushforward surface.
-- Local Chapter 30 precedent states global cohomology as
-- `((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X)`.

variable {X X' S S' : Scheme.{u}}

/-- Lemma 30.5.2 (Flat base change) (1): for a cartesian square of schemes
`\xymatrix{
X' \ar[r]^{g'} \ar[d]_{f'} & X \ar[d]^f \\
S' \ar[r]^g & S
}`
with `g` flat and `f` quasi-compact and quasi-separated, pullback along `g` identifies
`R^i f_* \mathcal F` with `R^i f'_* (g')^*\mathcal F` for every quasi-coherent
`\mathcal O_X`-module `\mathcal F`. -/
@[stacks 02KH]
theorem flatBaseChange_pullback_higherDirectImage_isomorphic
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (i : ℕ) :
    IsIsomorphic
      (((Scheme.Modules.pullback g).obj
        (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ)) : S'.Modules)
      ((((Scheme.Modules.pushforward f').rightDerived i).obj
        ((Scheme.Modules.pullback g').obj ℱ)) : S'.Modules) := sorry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {Y : Scheme.{u}}

/-- Lemma 30.5.2 (Flat base change) (2): in the affine-base case
`S = Spec A` and `S' = Spec B`, with `A -> B` flat, the flat base-change map identifies
`H^i(X, \mathcal F) \otimes_A B` with the cohomology of the pulled-back sheaf on
`X' = X \times_{Spec A} Spec B`. The tensor product is written as
`B ⊗[A] H^i(X, \mathcal F)`, using the canonical symmetry over the commutative base. -/
@[stacks 02KH]
theorem cohomology_tensor_isomorphic_of_flat_baseChange
    (f : X ⟶ Spec (CommRingCat.of A))
    (g : Y ⟶ Spec (CommRingCat.of B))
    (h : Y ⟶ X)
    (sq : IsPullback h g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [Module.Flat A B]
    [QuasiCompact f] [QuasiSeparated f]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ)
    [Module A (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))]
    [Module B
      (((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback h).obj ℱ)).H' i
        (⊤ : Opens Y))] :
    IsIsomorphic
      (ModuleCat.of B
        (B ⊗[A] (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' i (⊤ : Opens X))))
      (ModuleCat.of B
        (((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback h).obj ℱ)).H' i
          (⊤ : Opens Y))) := sorry

end AlgebraicGeometry.Scheme
