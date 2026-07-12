import StacksProject_2024.Chap20.«20_11_0_2»
import StacksProject_2024.Chap21.Lemma_21_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.13.6:
- primary domain: Leray degeneration consequences for global cohomology of `𝒪_X`-modules
  on a morphism of ringed spaces;
- sampled owner declarations:
  `CategoryTheory.Sheaf.H'`,
  `moduleUnderlyingSheaf`,
  `higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`,
  `RingedSite.Hom.moduleGlobalCohomology_iso_pushforward_of_higherDirectImageModule_isZero`;
- best owner abstraction: the global cohomology groups in the statement are canonically owned by
  `CategoryTheory.Sheaf.H'` on the underlying additive sheaf `((moduleUnderlyingSheaf X).obj ℱ)`,
  so the source-facing Leray degeneration theorems should be stated directly on that owner and
  proved by transporting the Chapter 21 ringed-site Leray degeneration theorems through the
  Chapter 20/21 comparison bridges, rather than through duplicate local Leray wrappers;
- primitive data: a morphism `f : X ⟶ Y`, a module `ℱ : X.Modules`, and vanishing hypotheses on
  the higher direct images `((f _*).rightDerived q).obj ℱ` or on their positive-degree global
  cohomology on `Y`;
- derived API: the global cohomology objects
  `((moduleUnderlyingSheaf X).obj ℱ).H' p ⊤` and
  `((moduleUnderlyingSheaf Y).obj (((f _*).rightDerived q).obj ℱ)).H' p ⊤`.

Source/core/bridge triage:
- `source-facing`: the two degeneration consequences below;
- `core/canonical`: `CategoryTheory.Sheaf.H'` and `moduleUnderlyingSheaf`;
- `bridge/view`: the Chapter 20 and Chapter 21 comparisons that identify module cohomology and
  higher direct images with the cohomology of the underlying additive sheaf.

This file therefore keeps the source-facing Leray statements but removes the parallel
`moduleGlobalCohomology` wrapper from the public theorem surfaces and reuses the existing Chapter
20/21 comparison API as the only bridge layer. -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(f _*).Additive]
variable [HasInjectiveResolutions X.Modules]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]

-- Proof sketch: transport the canonical ringed-site Leray degeneration theorem
-- `RingedSite.Hom.moduleGlobalCohomology_iso_pushforward_of_higherDirectImageModule_isZero`
-- across the Chapter `20/21` comparison bridges
-- `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`,
-- `higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf`, and the
-- public Chapter 20/21 top-open/global-sections comparisons.
/-- Lemma 20.13.6 (1): if the higher direct images `R^q f_* ℱ` vanish for `q > 0`, then the
global degree-`p` cohomology of `ℱ` on `X` is canonically isomorphic to the global degree-`p`
cohomology of `f_* ℱ` on `Y`. -/
@[stacks 01F4]
theorem globalCohomology_iso_pushforward_of_higherDirectImageModule_isZero
    (ℱ : X.Modules)
    (hRq : ∀ q : ℕ, 0 < q → IsZero (((f _*).rightDerived q).obj ℱ))
    (p : ℕ) :
    IsIsomorphic
      (((moduleUnderlyingSheaf X).obj ℱ).H' p ⊤)
      (((moduleUnderlyingSheaf Y).obj ((f _*).obj ℱ)).H' p ⊤) := by
  -- The canonical Leray degeneration theorem already exists on the ringed-site/module-cohomology
  -- surface; this ringed-space statement is only its underlying-sheaf transport.
  sorry

-- Proof sketch: transport the canonical ringed-site Leray degeneration theorem
-- `RingedSite.Hom.moduleGlobalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity`
-- across the same Chapter `20/21` comparison bridges as in part `(1)`.
/-- Lemma 20.13.6 (2): if `H^p(Y, R^q f_* ℱ) = 0` for all `q` and all `p > 0`, then the global
degree-`q` cohomology of `ℱ` on `X` is canonically isomorphic to the degree-`0` cohomology of the
higher direct image `R^q f_* ℱ` on `Y`. -/
@[stacks 01F4]
theorem globalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity
    (ℱ : X.Modules)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero
        (((moduleUnderlyingSheaf Y).obj (((f _*).rightDerived q).obj ℱ)).H' p ⊤))
    (q : ℕ) :
    IsIsomorphic
      (((moduleUnderlyingSheaf X).obj ℱ).H' q ⊤)
      (((moduleUnderlyingSheaf Y).obj (((f _*).rightDerived q).obj ℱ)).H' 0 ⊤) := by
  -- As in part `(1)`, the only intended bridge is from the canonical Chapter `21` theorem to the
  -- Chapter `20` underlying-sheaf cohomology owner on `⊤`.
  sorry

end AlgebraicGeometry.RingedSpace
