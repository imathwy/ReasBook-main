import StacksProject_2024.stacks_project.Chap10.Definition_10_86_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

/- 
Domain-style sampling for Lemma 21.22.4:
- primary domain: inverse-limit topologies on sequential systems of `A`-modules, compared with the
  `I`-adic topology through the intrinsic kernel associated graded and source stable-image data;
- sampled owner declarations:
  * `CategoryTheory.inverseLimitTopology`;
  * `cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded`;
- owner choice:
  * `source-facing`: the graded direct sum `⊕_n N_n` of the intrinsic stable-image submodules
    `N_n = (idealPowerTower n).stableImage (op n)` coming from the fixed-`n` towers
    `idealPowerTower n`;
  * `core/canonical`: `inverseLimitTopology cohomologySystem` together with the canonical
    filtration owner `inverseLimitKernelIdealFiltration I cohomologySystem hI` and its graded
    module;
  * `bridge/view`: the chapter bridge
    `cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded`,
    specialized to the source stable-image submodules of the towers `idealPowerTower n`.
- primitive data: the ideal `I`, the inverse system `cohomologySystem`, the source towers
  `idealPowerTower`, the `I`-compatibility witness `hI`, and the surjective comparison map;
- derived API: the resulting equality of inverse-limit and `I`-adic topologies.

This file does not reprove the Noetherian-transfer step: it specializes the bridge theorem of
Lemma `21.22.3` to the source graded object built from stable images.
-/

/-- For a fixed ideal-power tower, `idealPowerTowerStableImage idealPowerTower n` is the source
stable-image module `N_n` at stage `n`. -/
abbrev idealPowerTowerStableImage (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    ModuleCat A :=
  ModuleCat.of A ((idealPowerTower n).stableImage (op n))

/-- The source graded object `⨁ n, N n` built from the stable-image modules
`N n = idealPowerTowerStableImage idealPowerTower n`. -/
abbrev idealPowerTowerStableImageDirectSum
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A) : Type u :=
  ⨁ n : ℕ, idealPowerTowerStableImage idealPowerTower n

-- Proof sketch: instantiate Lemma `21.22.3` with the source graded pieces
-- `N_n = (idealPowerTower n).stableImage (op n)`.
/-- Lemma 21.22.4: let `cohomologySystem` model the inverse system
`n ↦ H^p(𝒞, ℱ n)` and let `idealPowerTower n` model the fixed-`n` tower
`m ↦ H^p(𝒞, I^n ℱ (m + 1))`. For each `n`, write
`N n = idealPowerTowerStableImage idealPowerTower n`, the source stable-image module at stage `n`.
If the graded direct sum `⨁ n : ℕ, N n` is Noetherian over the associated graded ring
`⊕_{n ≥ 0} I^n / I^(n + 1)`, and if the source comparison identifies the intrinsic associated
graded object `inverseLimitKernelAssociatedGraded I cohomologySystem hI` of the
kernel filtration on `inverseLimitModule cohomologySystem` as a quotient of `⨁ n : ℕ, N n` by a
surjective `gr_I(A)`-linear map, and the target carries the canonical homogeneous-action instance
`[SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
  (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]`, then the inverse-limit
topology on `inverseLimitModule cohomologySystem` is the `I`-adic topology. -/
@[stacks 0GYT]
lemma cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_eventualImages
    (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A)
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (idealPowerTowerStableImageDirectSum idealPowerTower)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (idealPowerTowerStableImageDirectSum idealPowerTower)]
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]
    (eventualImagesToKernelAssociatedGraded :
      inverseLimitKernelAssociatedGradedHom I cohomologySystem hI
        (idealPowerTowerStableImageDirectSum idealPowerTower))
    (hSurj : Function.Surjective eventualImagesToKernelAssociatedGraded) :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I (inverseLimitModule cohomologySystem) := by
  simpa using
    cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded
      I cohomologySystem (fun n ↦ idealPowerTowerStableImage idealPowerTower n) hI
      eventualImagesToKernelAssociatedGraded hSurj

end

end CategoryTheory
