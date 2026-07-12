import StacksProject_2024.Chap29.Definition_29_5_5
import StacksProject_2024.Chap31.FittingIdealSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.subscheme`,
-- `Scheme.IdealSheafData.support`, and `Scheme.Modules.pushforward`; local Chapter 29/31
-- precedent fixes scheme-theoretic module support as `IsSchemeTheoreticSupport` and the Fitting
-- closed subscheme as `Scheme.fittingIdealSheaf F 0`.

/-- Lemma 31.9.3 (1): if `Z` is the scheme theoretic support of a finite type quasi-coherent
module `F`, then `Z` is contained in the closed subscheme cut out by `Fit_0(F)`. In the
`IdealSheafData` order this is the ideal-sheaf inclusion `Fit_0(F) ≤ I`. -/
@[stacks 0CYX]
theorem fittingIdealSheaf_zero_le_schemeTheoreticSupport
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (I : S.IdealSheafData) (hI : IsSchemeTheoreticSupport F I) :
    fittingIdealSheaf F 0 ≤ I := sorry

/-- Lemma 31.9.3 (2): the underlying closed subset of the scheme theoretic support of a finite
type quasi-coherent module is the ordinary support of the module. -/
@[stacks 0CYX]
theorem schemeTheoreticSupport_support_eq_moduleSupport
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (I : S.IdealSheafData) (hI : IsSchemeTheoreticSupport F I) :
    (I.support : Set S) = moduleSupport F := sorry

/-- Lemma 31.9.3 (3): the closed subscheme cut out by `Fit_0(F)` has underlying closed subset
equal to the ordinary support of the finite type quasi-coherent module `F`. -/
@[stacks 0CYX]
theorem fittingIdealSheaf_zero_support_eq_moduleSupport
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ((fittingIdealSheaf F 0).support : Set S) = moduleSupport F := sorry

/-- Lemma 31.9.3 (4): on the closed subscheme cut out by `Fit_0(F)` there is a finite type
quasi-coherent module whose pushforward to the ambient scheme is `F`. -/
@[stacks 0CYX]
theorem exists_finiteType_quasicoherent_module_pushforward_fittingIdealSheaf_zero
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ G0 : (fittingIdealSheaf F 0).subscheme.Modules,
      ∃ _ : G0.IsQuasicoherent,
        ∃ _ : G0.IsFiniteType,
          Nonempty ((pushforward (fittingIdealSheaf F 0).subschemeι).obj G0 ≅
            F) := sorry

end AlgebraicGeometry.Scheme.Modules
