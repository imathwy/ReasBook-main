import Mathlib
import stacks_project.Chap06.Lemma_6_29_1
import stacks_project.Chap17.Lemma_17_22_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.8:
- primary domain: filtered colimits of represented Hom functors on the owner category
  `(RingedSpace.Modules X)`;
- sampled owner declarations:
  `colimit.post`,
  `coyoneda.obj`,
  `SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`,
  `bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings`;
- best owner abstraction: the source-facing theorem should be stated on `(RingedSpace.Modules X)`,
  with canonical comparison map `colimit.post ℱ (coyoneda.obj (op 𝒢))`;
- primitive data: a ringed space `X`, a finitely presented module `𝒢 : RingedSpace.Modules X`,
  and a filtered diagram `ℱ : Λ ⥤ RingedSpace.Modules X`;
- derived API: the internal-Hom comparison from Lemma `17.22.7` and the top-open sections
  comparison from Lemma `6.29.1`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma on `colim Hom_X(𝒢, ℱ_λ) → Hom_X(𝒢, colim ℱ_λ)`;
- `core/canonical`: `(RingedSpace.Modules X)`, `coyoneda.obj (op 𝒢)`, and `colimit.post`;
- `bridge/view`: the internal-Hom comparison from Lemma `17.22.7` and the top-open sections
  comparison from Lemma `6.29.1`. -/

variable {X : RingedSpace.{u}} {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
local notation "JX" => Opens.grothendieckTopology X
local notation "ModX" => RingedSpace.Modules X

-- Proof sketch: identify `Hom_X(\mathcal G, -)` with global sections of the internal-Hom sheaf,
-- apply Lemma `17.22.7` to replace the internal Hom into `colim_\lambda \mathcal F_\lambda` by the
-- filtered colimit of the internal-Hom sheaves, and then apply Lemma `6.29.1` on the top open of
-- `X` using the cofinal finite-cover hypothesis.
/-- Lemma 17.22.8: if the top open of a ringed space `X` has a cofinal system of finite open
covers with quasi-compact pairwise intersections, then for a finitely presented
`\mathcal O_X`-module `\mathcal G` and a filtered diagram `\mathcal F_\lambda` of
`\mathcal O_X`-modules, the canonical map
`colim_\lambda Hom_X(\mathcal G, \mathcal F_\lambda) \to
Hom_X(\mathcal G, colim_\lambda \mathcal F_\lambda)` is bijective. -/
theorem homColimitComparison_bijective_of_isFinitePresentation
    (hX : HasCofinalFiniteQuasiCompactOverlapCoverings JX (⊤ : Opens X))
    (𝒢 : ModX)
    [𝒢.IsFinitePresentation]
    (ℱ : Λ ⥤ ModX)
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ coyoneda.obj (op 𝒢))] :
    Function.Bijective (colimit.post ℱ (coyoneda.obj (op 𝒢))) := sorry

end AlgebraicGeometry.RingedSpace
