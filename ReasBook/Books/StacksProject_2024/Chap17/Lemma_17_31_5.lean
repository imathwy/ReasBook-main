import Mathlib
import StacksProject_2024.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/-- The category of `\mathcal O`-module cochain complexes indexed by `\mathbb Z`. -/
abbrev SheafModuleComplex
    {X : TopCat.{u}} (O : X.Sheaf CommRingCat.{u}) :=
  CochainComplex (SheafOfModules (ringSheaf O)) ℤ

/-- The desuspension `K[-1]` of a cochain complex of sheaves of modules. -/
abbrev cochainDesuspension
    {X : TopCat.{u}} {O : X.Sheaf CommRingCat.{u}} (K : SheafModuleComplex O) :
    SheafModuleComplex O :=
  (CochainComplex.shiftFunctor _ (-1)).obj K

/-- The cohomology sheaf `H^n(K)` of a cochain complex of sheaves of modules. -/
abbrev cohomologySheaf
    {X : TopCat.{u}} {O : X.Sheaf CommRingCat.{u}} (K : SheafModuleComplex O) (n : ℤ) :=
  HomologicalComplex.homology K n

-- Proof sketch: construct the comparison map
-- `NL_{\mathcal B/\mathcal A} \otimes_{\mathcal B} \mathcal C ⟶
--   (mappingCone comparison)[-1]`
-- from the functoriality morphism to `NL_{\mathcal C/\mathcal A}` together with the explicit
-- null-homotopy of Remark `10.134.5`, transported to sheaves. Then identify the induced maps on
-- `H^0` and `H^{-1}` stalkwise via Lemma `17.31.4` and apply the algebraic Jacobi-Zariski result
-- `10.134.4`.
/-- Lemma 17.31.5: if `comparison : NL_{\mathcal C/\mathcal A} ⟶ NL_{\mathcal C/\mathcal B}` is
the canonical morphism of naive cotangent complexes of `\mathcal C`-modules and
`NL_{\mathcal B/\mathcal A} \otimes_{\mathcal B} \mathcal C` denotes the corresponding base-change
complex, then there is a canonical map
`NL_{\mathcal B/\mathcal A} \otimes_{\mathcal B} \mathcal C ⟶ Cone(comparison)[-1]`.
Moreover, its induced map on `H^0` is an isomorphism and its induced map on `H^{-1}` is an
epimorphism, which is the input needed for the canonical six-term exact cohomology sequence in the
source statement. -/
theorem naiveCotangent_transitivity_map_exists_with_homology_control
    {X : TopCat.{u}} {O : X.Sheaf CommRingCat.{u}}
    (naiveCotangentTensor : SheafModuleComplex O)
    (naiveCotangentOverA naiveCotangentOverB : SheafModuleComplex O)
    (comparison : naiveCotangentOverA ⟶ naiveCotangentOverB)
    [HomologicalComplex.HasHomotopyCofiber comparison] :
    ∃ c :
      naiveCotangentTensor ⟶
        cochainDesuspension (CochainComplex.mappingCone comparison),
      IsIso (HomologicalComplex.homologyMap c 0) ∧
        Epi (HomologicalComplex.homologyMap c (-1)) := sorry

end TopCat.Sheaf
