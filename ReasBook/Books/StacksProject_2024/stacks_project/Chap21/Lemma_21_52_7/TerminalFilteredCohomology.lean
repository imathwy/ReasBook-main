import StacksProject_2024.Chap07.Lemma_7_17_7

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)

/-- Helper for Lemma 21.52.7: the terminal-object filtered-colimit comparison for set-valued
sections is exactly the Chapter 7 comparison map under the cofinal finite quasi-compact overlap
covering hypothesis. This externalized helper keeps the source route available for the later
additive-owner transport. -/
lemma terminal_filteredColimit_type_sectionsComparison_isIso_external
    {I : Type w} [Category I] [Small.{u} I] [IsFiltered I]
    (F : I ⥤ Sheaf J (Type u)) (X0 : C)
    (hX0covers : J.HasCofinalFiniteQuasiCompactOverlapCoverings X0) :
    IsIso (colimit.post F ((sheafSections J (Type u)).obj (op X0))) := by
  -- The Chapter 7 filtered-colimit sections comparison applies directly at the terminal object.
  exact
    (CategoryTheory.isIso_iff_bijective _).2 <|
      CategoryTheory.sheafFilteredColimitSectionsComparison_bijective_of_cofinalFiniteQuasiCompactOverlapCoverings
        F X0 hX0covers

end

end SheafOfModules.RingedSite
