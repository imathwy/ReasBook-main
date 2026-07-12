import StacksProject_2024.Chap13.Lemma_13_5_7
import StacksProject_2024.Chap24.Definition_24_26_4
import StacksProject_2024.Chap24.Lemma_24_26_1
import StacksProject_2024.Chap24.Lemma_24_26_3

open CategoryTheory
open ComplexShape

noncomputable section

universe u v w

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)

local notation "ModX" => SheafOfModules X.structureSheaf
local notation "KQ" => HomotopyCategory.quotient 𝒜.moduleCat (up ℤ)
local notation "Qis" => HomotopyCategory.quasiIso 𝒜.moduleCat (up ℤ)

local instance : MorphismProperty.IsSaturatedMultiplicativeSystem Qis :=
  quasiIso_isSaturatedMultiplicativeSystem 𝒜

local instance : MorphismProperty.IsCompatibleWithTriangulation Qis :=
  quasiIso_isCompatibleWithTriangulation 𝒜

-- Semantic search note: `lean_leansearch` recalled the localization-descent owner
-- `homological_factorization_isHomological`; the local analogue
-- `exists_filteredGradedZeroHomologyFunctor_factorization` in `Lemma_13_13_4` fixed the
-- source-facing strict-factorization style used below.

/-- Lemma 24.26.6: in Definition 24.26.4, the functor
`H^0 : K(\textit{Mod}(\mathcal A, d)) \to \textit{Mod}(\mathcal O)` from Lemma 24.26.1 factors
through a homological functor `H^0 : D(\mathcal A, d) \to \textit{Mod}(\mathcal O)`. -/
theorem exists_hZeroFactorizationThroughDerivedCategory
    (H0 : HomotopyCategory 𝒜.moduleCat (up ℤ) ⥤ ModX)
    [H0.IsHomological]
    (hH0 : MorphismProperty.IsInvertedBy Qis H0) :
    ∃ H' : derivedCategory 𝒜 ⥤ ModX,
      (Qh 𝒜) ⋙ H' = H0 ∧ H'.IsHomological := sorry

end

end DifferentialGradedAlgebra
end RingedSite
