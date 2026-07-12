import StacksProject_2024.Chap20.Lemma_20_11_8
import StacksProject_2024.Chap20.Lemma_20_12_6

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.12.4:
- primary domain: higher Čech cohomology of `𝒪_X`-modules on indexed families of opens;
- sampled owner declarations:
  `HasVanishingHigherCechOnOpenCoverings`,
  `moduleUnderlyingSheaf`,
  `moduleCechCohomology`,
  `higherCohomology_isZero_of_vanishingHigherCech_on_openCoverings`;
- best owner abstraction: the Chapter 20 source-facing owner
  `HasVanishingHigherCechOnOpenCoverings ℱ`, with the degreewise
  `moduleCechCohomology 𝒰 ℱ p` vanishing as derived API and flasqueness stated through the
  canonical underlying additive-sheaf bridge `((moduleUnderlyingSheaf X).obj ℱ)`;
- primitive data: the module `ℱ : X.Modules` and the flasqueness hypothesis on its underlying
  additive sheaf;
- derived API: vanishing of `moduleCechCohomology 𝒰 ℱ p` for every indexed open family `𝒰` and
  every positive degree `p`.

Source/core/bridge triage:
- `source-facing`: `HasVanishingHigherCechOnOpenCoverings ℱ` for a flasque module `ℱ`;
- `core/canonical`: `moduleCechCohomology` together with the owner theorem
  `higherCohomology_isZero_of_vanishingHigherCech_on_openCoverings`;
- `bridge/view`: `moduleUnderlyingSheaf X`, which is where flasqueness is stated.
-/

-- Proof sketch: apply the Čech-to-cohomology spectral sequence of Lemma `20.11.5` to `ℱ`. By
-- Lemma `20.12.3`, all positive cohomology presheaves of `ℱ` vanish because `ℱ` is flasque, so
-- the spectral sequence is concentrated in the `q = 0` row. The same lemma also gives
-- `H^p(U, ℱ) = 0` for `p > 0`, forcing the surviving row `Čech H^p(𝒰, ℱ)` to vanish for every
-- indexed family `𝒰`.
/-- Lemma 20.12.4: if `ℱ` is a flasque `𝒪_X`-module on a ringed space `X`, then `ℱ` has
vanishing higher Čech cohomology on every indexed family of opens,
equivalently on every open covering of its union. -/
@[stacks 09SZ]
theorem hasVanishingHigherCechOnOpenCoverings_of_module_isFlasque
    (ℱ : X.Modules)
    (hℱ : TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ)) :
    HasVanishingHigherCechOnOpenCoverings ℱ := by
  intro ι 𝒰 p hp
  have hres :
      ∀ ⦃U' : TopologicalSpace.Opens X.carrier⦄
        (hU'fin : IsUnionOfFiniteCechIntersections 𝒰 U'),
        Function.Surjective (((moduleUnderlyingSheaf X).obj ℱ).presheaf.map
          (homOfLE hU'fin.le_iSup).op) := by
    intro U' hU'fin
    exact
      (AddCommGrpCat.epi_iff_surjective _).1
        (hℱ.epi (homOfLE hU'fin.le_iSup).op)
  simpa [moduleCechCohomology, moduleUnderlyingPresheaf] using
    cech_cohomology_isZero_of_surjective_restrictions_to_unions_of_finite_intersections
      𝒰 ((moduleUnderlyingSheaf X).obj ℱ) hres p hp

end AlgebraicGeometry.RingedSpace
