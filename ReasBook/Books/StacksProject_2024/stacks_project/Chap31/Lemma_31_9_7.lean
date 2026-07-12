import Mathlib
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap31.Lemma_31_9_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the scheme coproduct API, while local Chapter 31
-- precedent fixes the Fitting-rank strata through `Scheme.fittingIdealSheaf` and represents
-- subfunctors of `Sch/S` by `Subsingleton` plus a `Nonempty` iff.

/-- The open complement of the closed subscheme cut out by the `r`th Fitting ideal sheaf. -/
private abbrev fittingFlatOpenComplement
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    Opens S :=
  ⟨((((fittingIdealSheaf F r).support : TopologicalSpace.Closeds S) : Set S)ᶜ),
    (fittingIdealSheaf F r).support.2.isOpen_compl⟩

/-- The rank-`r` stratum `Z_{r-1} \ Z_r` attached to the Fitting-ideal filtration. -/
private abbrev fittingFlatRankStratum
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] : ℕ → Scheme
  | 0 => (fittingFlatOpenComplement F 0).toScheme
  | r + 1 =>
      (((fittingIdealSheaf F r).subschemeι) ⁻¹ᵁ fittingFlatOpenComplement F (r + 1)).toScheme

/-- The canonical inclusion of the rank-`r` Fitting stratum into the ambient scheme. -/
private abbrev fittingFlatRankStratumι
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] : (r : ℕ) →
      fittingFlatRankStratum F r ⟶ S
  | 0 => (fittingFlatOpenComplement F 0).ι
  | r + 1 =>
      (((fittingIdealSheaf F r).subschemeι) ⁻¹ᵁ fittingFlatOpenComplement F (r + 1)).ι ≫
        (fittingIdealSheaf F r).subschemeι

/-- The coproduct of all Fitting rank strata. -/
private noncomputable abbrev fittingFlatCover
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] : Scheme :=
  ∐ fun r : ℕ ↦ fittingFlatRankStratum F r

/-- The canonical morphism from the coproduct of all rank strata to the ambient scheme. -/
private noncomputable abbrev fittingFlatCoverι
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    fittingFlatCover F ⟶ S :=
  Sigma.desc fun r : ℕ ↦ fittingFlatRankStratumι F r

/-- Lemma 31.9.7 (1): the coproduct of the Fitting rank strata represents the functor on
`Sch/S` that is a singleton exactly when the pulled-back module is flat. -/
@[stacks 05P9]
theorem fittingFlatCover_nonempty_over_hom_iff_isFlat
    {S T : Scheme.{u}} (g : T ⟶ S) (F : S.Modules) [F.IsFinitePresentation] :
    Subsingleton (Over.mk g ⟶ Over.mk (fittingFlatCoverι F)) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingFlatCoverι F)) ↔
        SheafOfModules.IsFlat ((Modules.pullback g).obj F)) := sorry

/-- Lemma 31.9.7 (2): on the rank-`r` Fitting stratum, the restricted module is finite locally
free of rank `r`. -/
@[stacks 05P9]
theorem fittingFlatRankStratum_pullback_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Modules.pullback (fittingFlatRankStratumι F r)).obj F) := sorry

/-- Lemma 31.9.7 (3): each rank-`r` Fitting stratum maps to the ambient scheme by a morphism of
finite presentation. -/
@[stacks 05P9]
theorem fittingFlatRankStratum_hom_finitePresentation
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ) :
    Hom.FinitePresentation (fittingFlatRankStratumι F r) := sorry

/-- Lemma 31.9.7 (4): the coproduct of all Fitting rank strata maps to the ambient scheme by a
morphism of finite presentation. -/
@[stacks 05P9]
theorem fittingFlatCover_hom_finitePresentation
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] :
    Hom.FinitePresentation (fittingFlatCoverι F) := sorry

end AlgebraicGeometry.Scheme
