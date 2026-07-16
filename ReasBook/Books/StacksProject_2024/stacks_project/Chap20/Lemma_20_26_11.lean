import StacksProject_2024.stacks_project.Chap17.Lemma_17_17_7
import StacksProject_2024.stacks_project.Chap13.UpperTruncationResolutionTowerColimit

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

section

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

/-
Domain-style sampling pass:
- primary domain: upper-truncation resolution towers of complexes of `𝒪_X`-modules on a
  ringed space, specialized from the opens-site ringed-site theorem and expressed with the
  Chapter 17 lower-shriek structure-sheaf generators;
- sampled owner declarations:
  `CategoryTheory.UpperTruncationResolutionTower`,
  `CategoryTheory.exists_upperTruncationResolutionTower`,
  `CategoryTheory.UpperTruncationResolutionTower.fromColimit_quasiIso_of_ringedSite`,
  `isCoproductOfOpenSubsetStructureSheafLowerShrieks X`;
- best owner abstraction: the core owner is the generic Chapter 13 colimit theorem for
  upper-truncation resolution towers on a ringed site; this file is only the source-facing
  opens-site specialization whose property name matches the Chapter 17 lower-shriek presentation
  of `j![X.sheaf, U]`;
- primitive-vs-derived split:
  primitive data: the object property
    `isCoproductOfOpenSubsetStructureSheafLowerShrieks X` on `RingedSpace.Modules X`;
  derived API: the existence of a compatible tower comes from the Chapter 13 owner theorem, and
    the quasi-isomorphic colimit comparison comes from the generic ringed-site colimit owner, so
    this file should not keep a parallel local reconstruction of the tower argument.

Source/core/bridge triage:
- `source-facing`: the Stacks-project existence statement for a lower-shriek-generated
  upper-truncation resolution tower whose colimit comparison is a quasi-isomorphism;
- `core/canonical`:
  `CategoryTheory.exists_upperTruncationResolutionTower` together with
  `CategoryTheory.UpperTruncationResolutionTower.fromColimit_quasiIso_of_ringedSite`;
- `bridge/view`: the source-facing object property
  `isCoproductOfOpenSubsetStructureSheafLowerShrieks X` already lives on the opens site of `X`,
  so no separate localized-structure-module wrapper is needed here.
-/

/-- For an upper-truncation resolution tower on `X.Modules` whose terms and successive degreewise
cokernels are coproducts of lower-shriek structure sheaves `j![X.sheaf, U]`, the canonical map
from the sequential colimit of the tower to the target complex is a quasi-isomorphism. -/
theorem fromColimit_quasiIso_of_openSubsetStructureSheafLowerShrieks
    {K : CochainComplex ModX ℤ}
    (T : UpperTruncationResolutionTower (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) K) :
    QuasiIso T.fromColimit :=
  CategoryTheory.UpperTruncationResolutionTower.fromColimit_quasiIso_of_ringedSite
    X.sheaf T

-- Proof sketch: apply the Chapter 13 upper-truncation existence theorem to the Chapter 17
-- source-facing object property, then use the generic ringed-site colimit theorem to identify the
-- canonical map from the sequential colimit of the tower to `𝒢` as a quasi-isomorphism.

/-- Lemma 20.26.11: every complex of `𝒪_X`-modules on a ringed space admits a compatible
upper-truncation resolution tower by bounded-above complexes whose terms and successive degreewise
cokernels are coproducts of lower-shriek structure sheaves `j![X.sheaf, U]`, and whose
canonical map from the sequential colimit of the tower to the original complex is a
quasi-isomorphism. -/
@[stacks 079T]
theorem exists_upperTruncationResolutionTower_of_openSubsetStructureSheafLowerShrieks
    (𝒢 : CochainComplex ModX ℤ) :
    ∃ T : UpperTruncationResolutionTower (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) 𝒢,
      QuasiIso T.fromColimit := by
  obtain ⟨T⟩ :=
    CategoryTheory.exists_upperTruncationResolutionTower
      (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) 𝒢
  exact ⟨T, fromColimit_quasiIso_of_openSubsetStructureSheafLowerShrieks T⟩

end

end AlgebraicGeometry.RingedSpace.ModuleSheaf
