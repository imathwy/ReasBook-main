import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Lemma_31_9_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` only surfaced module-side local-freeness/rank-at-stalk API.
-- Chapter 31 already fixes the source-facing Fitting open complement as
-- `Scheme.fittingOpenComplement`, and nearby files phrase restriction to an open subscheme through
-- the canonical pullback owner `Scheme.Modules.pullback U.ι`. This statement is therefore
-- recorded directly on the project owners `Scheme.fittingIdealSheaf`,
-- `Scheme.fittingOpenComplement`, `IsBlowup`, `strictTransformModule`, and
-- `SheafOfModules.IsFiniteLocallyFreeOfRank`.

/-- Lemma 31.35.2: let `S` be a scheme, let `\mathcal F` be a finite type quasi-coherent
`\mathcal O_S`-module, and let `Z_k` be the closed subscheme cut out by
`Scheme.fittingIdealSheaf ℱ k`. Assume `ℱ` is locally free of rank `k` on the open complement
`S \setminus Z_k`. If `b : S' ⟶ S` is the blowup of `S` in `Z_k`, then the strict transform of
`ℱ` along `b` is locally free of rank `k`. -/
@[stacks 0CZQ]
theorem strictTransformModule_isFiniteLocallyFreeOfRank_of_isBlowup_fittingIdealSheaf
    {S S' : Scheme.{u}} (b : S' ⟶ S) (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (k : ℕ) [IsBlowup b (Scheme.fittingIdealSheaf ℱ k)]
    (hℱ : SheafOfModules.IsFiniteLocallyFreeOfRank k
      ((Scheme.Modules.pullback (Scheme.fittingOpenComplement ℱ k).ι).obj ℱ)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank k
      (strictTransformModule b ((Scheme.fittingIdealSheaf ℱ k).comap b) (𝟙 S) ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
