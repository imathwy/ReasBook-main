import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap31.FittingIdealSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped FittingIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the source lemma is stated for the Fitting ideal sheaves `Fit_{r-1}(ℱ)` and
-- `Fit_r(ℱ)`, and Chapter 31 already fixes the canonical sheaf-side owner
-- `Scheme.fittingIdealSheaf`. The predecessor ideal sheaf is therefore kept only as a thin
-- source-facing bridge over that canonical family.

/-- The predecessor Fitting ideal sheaf attached to a finite type quasi-coherent module. On an
affine open `U`, its defining ideal is `Fit_{r-1}(Γ(U, ℱ))`, using the Chapter 15 convention
`Fit_{-1} = 0`. -/
abbrev precedingFittingIdealSheaf
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    S.IdealSheafData :=
  match r with
  | 0 => Scheme.IdealSheafData.ofIdeals fun U : S.affineOpens ↦ (⊥ : Ideal (Γ(S, U)))
  | r + 1 => fittingIdealSheaf ℱ r

/-- The predecessor Fitting ideal sheaf in rank `0` is the zero ideal sheaf. -/
@[simp] theorem precedingFittingIdealSheaf_zero
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] :
    precedingFittingIdealSheaf ℱ 0 =
      Scheme.IdealSheafData.ofIdeals fun U : S.affineOpens ↦ (⊥ : Ideal (Γ(S, U))) :=
  rfl

/-- The predecessor Fitting ideal sheaf in rank `r + 1` is the `r`th Fitting ideal sheaf. -/
@[simp] theorem precedingFittingIdealSheaf_succ
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    precedingFittingIdealSheaf ℱ (r + 1) = fittingIdealSheaf ℱ r :=
  rfl

/-- The affine-open ideals of `precedingFittingIdealSheaf` are the corresponding predecessor
Fitting ideals of affine sections. -/
@[simp] theorem precedingFittingIdealSheaf_ideal
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (r : ℕ) (U : S.affineOpens) :
    (precedingFittingIdealSheaf ℱ r).ideal U =
      precedingFittingIdeal (Γ(S, U)) (Γ(ℱ, U)) r := sorry

/-- The predecessor Fitting ideal sheaf is zero exactly when all of its affine-open ideals are
zero. -/
theorem precedingFittingIdealSheaf_eq_bot_iff
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    precedingFittingIdealSheaf ℱ r = ⊥ ↔
      ∀ U : S.affineOpens, (precedingFittingIdealSheaf ℱ r).ideal U = ⊥ := sorry

/-- The `r`th Fitting ideal sheaf is the unit ideal sheaf exactly when all of its affine-open
ideals are unit ideals. -/
theorem fittingIdealSheaf_eq_top_iff
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    fittingIdealSheaf ℱ r = ⊤ ↔
      ∀ U : S.affineOpens, (fittingIdealSheaf ℱ r).ideal U = ⊤ := sorry

/-- The `r`th Fitting ideal sheaf is zero exactly when all of its affine-open ideals are zero. -/
theorem fittingIdealSheaf_eq_bot_iff
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    fittingIdealSheaf ℱ r = ⊥ ↔
      ∀ U : S.affineOpens, (fittingIdealSheaf ℱ r).ideal U = ⊥ := sorry

/-- Lemma 31.9.5: for a finite type quasi-coherent `\mathcal O_S`-module, the following are
equivalent: being finite locally free of rank `r`; having `Fit_{r-1}(ℱ) = 0` and
`Fit_r(ℱ) = \mathcal O_S`; and having `Fit_k(ℱ) = 0` for `k < r` and
`Fit_k(ℱ) = \mathcal O_S` for `k ≥ r`. In the canonical scheme-side API, these Fitting-ideal
equalities are recorded directly as equalities of `IdealSheafData`. The affine-open ideal formulas
remain available through the companion bridge lemmas above. -/
@[stacks 0C3G]
theorem isFiniteLocallyFreeOfRank_tfae_fittingIdealSheaf_conditions
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    List.TFAE
      [ SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ
      , precedingFittingIdealSheaf ℱ r = ⊥ ∧ fittingIdealSheaf ℱ r = ⊤
      , (∀ k < r, fittingIdealSheaf ℱ k = ⊥) ∧
          ∀ k ≥ r, fittingIdealSheaf ℱ k = ⊤
      ] := sorry

/-- Lemma 31.9.5 (2): a finite type quasi-coherent `\mathcal O_S`-module is finite locally free
of rank `r` exactly when `Fit_{r-1}(ℱ) = 0` and `Fit_r(ℱ) = \mathcal O_S`. In the current
scheme-level owner API, this is recorded directly as the predecessor and `r`th Fitting ideal
sheaves being respectively zero and unit. -/
@[stacks 0C3G]
theorem isFiniteLocallyFreeOfRank_iff_precedingFittingIdealSheaf_eq_bot_and_fittingIdealSheaf_eq_top
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ ↔
      precedingFittingIdealSheaf ℱ r = ⊥ ∧ fittingIdealSheaf ℱ r = ⊤ := sorry

/-- Lemma 31.9.5 (3): a finite type quasi-coherent `\mathcal O_S`-module is finite locally free
of rank `r` exactly when `Fit_k(ℱ) = 0` for `k < r` and `Fit_k(ℱ) = \mathcal O_S` for
`k \ge r`. In the current scheme-level owner API, this is recorded directly as the sheaves
`fittingIdealSheaf ℱ k` being zero below `r` and unit from `r` onward. -/
@[stacks 0C3G]
theorem isFiniteLocallyFreeOfRank_iff_fittingIdealSheaf_eq_bot_below_and_eq_top_from
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ ↔
      (∀ k < r, fittingIdealSheaf ℱ k = ⊥) ∧
        ∀ k ≥ r, fittingIdealSheaf ℱ k = ⊤ := sorry

end AlgebraicGeometry.Scheme
