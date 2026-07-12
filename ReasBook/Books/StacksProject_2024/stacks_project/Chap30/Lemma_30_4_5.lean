import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical `QuasiCompact` and `QuasiSeparated`
-- morphism owners; local Chapter 30 precedent states higher direct images on
-- `((Scheme.Modules.pushforward f).rightDerived p).obj ℱ`.

/-- Lemma 30.4.5 (1): if `f : X ⟶ S` is quasi-compact and quasi-separated, then for every
quasi-coherent `\mathcal O_X`-module `\mathcal F` and every degree `p`, the higher direct image
`R^p f_* \mathcal F` is quasi-coherent on `S`. -/
@[stacks 01XJ]
theorem higherDirectImageModule_isQuasicoherent_of_quasiCompact_quasiSeparated
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived p).obj ℱ).IsQuasicoherent := sorry

/-- Lemma 30.4.5 (2): if, in addition, `S` is quasi-compact, then there is an integer
`n = n(X, S, f)` such that `R^p f_* \mathcal F = 0` for all `p ≥ n` and all quasi-coherent
`\mathcal O_X`-modules `\mathcal F`. -/
@[stacks 01XJ]
theorem eventually_higherDirectImageModule_isZero_of_quasiCompact_base
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S.carrier] [HasInjectiveResolutions X.Modules] :
    ∃ n : ℕ, ∀ (ℱ : X.Modules), ℱ.IsQuasicoherent → ∀ p : ℕ, n ≤ p →
      IsZero (((Scheme.Modules.pushforward f).rightDerived p).obj ℱ) := sorry

/-- Lemma 30.4.5 (3): if `S` is quasi-compact, the same integer `n = n(X, S, f)` can be chosen
uniformly after every base change `S' ⟶ S`: for the base-changed morphism
`f' : X' = S' ×_S X ⟶ S'`, all higher direct images `R^p f'_* \mathcal F'` vanish for `p ≥ n`
and all quasi-coherent sheaves `\mathcal F'` on `X'`. -/
@[stacks 01XJ]
theorem eventually_baseChange_higherDirectImageModule_isZero_of_quasiCompact_base
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S.carrier] :
    ∃ n : ℕ, ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S)
      [HasInjectiveResolutions (pullback f g : Scheme.{u}).Modules]
      (ℱ' : (pullback f g : Scheme.{u}).Modules), ℱ'.IsQuasicoherent → ∀ p : ℕ, n ≤ p →
      IsZero (((Scheme.Modules.pushforward (pullback.snd f g)).rightDerived p).obj ℱ') := sorry

end AlgebraicGeometry.Scheme
