import Mathlib
import stacks_project.Chap13.Lemma_13_29_1
import stacks_project.Chap17.Lemma_17_17_7

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

section

variable {X : RingedSpace.{u}}

local notation "ModCat" => SheafOfModules (RingedSpace.ringCatSheaf X)

-- Proof sketch: apply Lemma `17.17.7` degreewise to produce epimorphic covers of the terms of the
-- upper truncations of `𝒢`, then feed the resulting object property into Lemma `13.29.1` to build
-- the compatible resolution tower. Exactness of filtered colimits gives the quasi-isomorphism from
-- the colimit complex to `𝒢`.
/-- Lemma 20.26.11: every complex of `\mathcal O_X`-modules on a ringed space admits a compatible
upper-truncation resolution tower by bounded-above complexes whose terms and successive degreewise
cokernels are coproducts of lower-shriek structure sheaves `j_{U!}\mathcal O_U`, and whose
canonical map from the sequential colimit of the tower to the original complex is a
quasi-isomorphism. -/
theorem exists_upperTruncationResolutionTower_of_openSubsetStructureSheafLowerShrieks
    (𝒢 : CochainComplex ModCat ℤ) :
    ∃ T : UpperTruncationResolutionTower (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) 𝒢,
      QuasiIso T.fromColimit := sorry

end

end AlgebraicGeometry.RingedSpace.ModuleSheaf
