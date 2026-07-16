import StacksProject_2024.stacks_project.Chap18.Definition_18_17_1
import StacksProject_2024.stacks_project.Chap31.FittingIdealSheaf
import StacksProject_2024.stacks_project.Chap31.IdealSheafDataStalkIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped FittingIdeal

universe u

namespace AlgebraicGeometry.Scheme

-- Source/core/bridge triage:
-- - `source-facing`: local generation by `r` sections near `s`;
-- - `core/canonical`: `SheafOfModules.IsGeneratedBy`, `Scheme.fittingIdealSheaf`, and the
--   Chapter 31 stalk-ideal owner for ideal sheaf data;
-- - `bridge/view`: the stalkwise identification of the `r`th Fitting ideal sheaf with the ring
--   Fitting ideal of the stalk module.

/-- The stalk of the `r`th Fitting ideal sheaf at `s`, expressed through the Chapter 31
stalk-ideal owner, is the `r`th Fitting ideal of the stalk module `ℱ_s`. -/
@[simp]
theorem fittingIdealSheaf_stalkIdeal_eq_stalk_fittingIdeal
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (s : S) (r : ℕ) :
    (fittingIdealSheaf ℱ r).stalkIdeal s =
      Fit[S.presheaf.stalk s]_(r)(RingedSpace.stalkModuleCat ℱ s) := sorry

/-- Lemma 31.9.4, stated on the canonical Chapter 31 owner `Scheme.fittingIdealSheaf`: local
generation by `r` sections near `s` is equivalent to the stalk of the `r`th Fitting ideal sheaf
being the unit ideal at `s`. -/
@[stacks 0C3F]
theorem exists_isGeneratedBy_on_neighborhood_iff_fittingIdealSheaf_stalkIdeal_eq_top
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (s : S) (r : ℕ) :
    (∃ U : S.Opens, s ∈ U ∧ SheafOfModules.IsGeneratedBy (ℱ.over U) r) ↔
      (fittingIdealSheaf ℱ r).stalkIdeal s = ⊤ := sorry

/-- Lemma 31.9.4, restated through the stalk ring formulation: local generation by `r` sections
near `s` is equivalent to the `r`th Fitting ideal of the stalk module `ℱ_s` being the unit ideal
of `\mathcal O_{S, s}`. -/
@[stacks 0C3F]
theorem exists_isGeneratedBy_on_neighborhood_iff_stalk_fittingIdeal_eq_top
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (s : S) (r : ℕ) :
    (∃ U : S.Opens, s ∈ U ∧ SheafOfModules.IsGeneratedBy (ℱ.over U) r) ↔
      Fit[S.presheaf.stalk s]_(r)(RingedSpace.stalkModuleCat ℱ s) = ⊤ := by
  simpa [fittingIdealSheaf_stalkIdeal_eq_stalk_fittingIdeal] using
    exists_isGeneratedBy_on_neighborhood_iff_fittingIdealSheaf_stalkIdeal_eq_top ℱ s r

end AlgebraicGeometry.Scheme
