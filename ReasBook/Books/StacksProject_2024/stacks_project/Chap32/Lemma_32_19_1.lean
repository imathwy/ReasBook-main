import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-module pullback/pushforward
-- owners; local Chapter 30 precedent states higher direct images as
-- `((Scheme.Modules.pushforward f).rightDerived i).obj ℱ` and records base-change comparison
-- clauses with `IsIsomorphic` when no named higher-direct-image comparison map is available.

variable {X Y X' Y' X'' Y'' : Scheme.{u}}

/-- Lemma 32.19.1 (1): if `X` and `Y` are quasi-compact and quasi-separated and all
quasi-coherent higher direct images `R^i f_* \mathcal F` vanish for `i > d`, then after any
cartesian base change square the same vanishing holds for `R^i f'_* \mathcal F'` and every
quasi-coherent `\mathcal O_{X'}`-module `\mathcal F'`. -/
@[stacks 0EX3]
theorem topDegreeBaseChange_higherDirectImageModule_isZero
    (f : X ⟶ Y) (d : ℕ)
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [CompactSpace Y.carrier] [QuasiSeparatedSpace Y.carrier]
    [HasInjectiveResolutions X.Modules]
    (hvanish : ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), d < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X'.Modules]
    (ℱ' : X'.Modules) [ℱ'.IsQuasicoherent]
    (i : ℕ) (hi : d < i) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived i).obj ℱ') := sorry

/-- Lemma 32.19.1 (2): under the same hypotheses and after any cartesian base change square,
top-degree higher direct image satisfies the projection formula for every quasi-coherent
`\mathcal O_{X'}`-module `\mathcal F'` and quasi-coherent `\mathcal O_{Y'}`-module
`\mathcal G'`. -/
@[stacks 0EX3]
theorem topDegreeBaseChange_projectionFormula_higherDirectImageModule
    (f : X ⟶ Y) (d : ℕ)
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [CompactSpace Y.carrier] [QuasiSeparatedSpace Y.carrier]
    [HasInjectiveResolutions X.Modules]
    (hvanish : ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), d < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [MonoidalCategory X'.Modules] [MonoidalCategory Y'.Modules]
    [HasInjectiveResolutions X'.Modules]
    (ℱ' : X'.Modules) [ℱ'.IsQuasicoherent]
    (𝒢' : Y'.Modules) [𝒢'.IsQuasicoherent] :
    IsIsomorphic
      (((Scheme.Modules.pushforward f').rightDerived d).obj
        ((tensorObj ℱ' ((Scheme.Modules.pullback f').obj 𝒢')) : X'.Modules))
      ((tensorObj (((Scheme.Modules.pushforward f').rightDerived d).obj ℱ') 𝒢') : Y'.Modules) := sorry

/-- Lemma 32.19.1 (3): under the same hypotheses and after any cartesian base change square,
formation of the top-degree higher direct image `R^d f'_* \mathcal F'` commutes with arbitrary
further cartesian base change. -/
@[stacks 0EX3]
theorem topDegreeBaseChange_higherDirectImageModule_commutesWithBaseChange
    (f : X ⟶ Y) (d : ℕ)
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [CompactSpace Y.carrier] [QuasiSeparatedSpace Y.carrier]
    [HasInjectiveResolutions X.Modules]
    (hvanish : ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), d < i →
      IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj ℱ))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X'.Modules]
    (ℱ' : X'.Modules) [ℱ'.IsQuasicoherent]
    (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    (sq' : IsPullback h' f'' f' h)
    [HasInjectiveResolutions X''.Modules] :
    IsIsomorphic
      (((Scheme.Modules.pullback h).obj
        (((Scheme.Modules.pushforward f').rightDerived d).obj ℱ')) : Y''.Modules)
      (((Scheme.Modules.pushforward f'').rightDerived d).obj
        ((Scheme.Modules.pullback h').obj ℱ')) := sorry

end AlgebraicGeometry.Scheme
