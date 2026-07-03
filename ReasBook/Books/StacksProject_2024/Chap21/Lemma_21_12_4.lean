import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable {𝒪 : Sheaf J RingCat.{u}}

-- Proof sketch: compute `H^i(\mathcal C, \mathcal F_{ab})` as the right derived functors of
-- global sections on abelian sheaves, compute module cohomology as the Ext-groups
-- `Ext^i_{\mathrm{Mod}(\mathcal O)}(\mathcal O, \mathcal F)`, and compare the two via the exact
-- forgetful functor `SheafOfModules.toSheaf 𝒪` together with the identification of
-- `Hom_{\mathrm{Mod}(\mathcal O)}(\mathcal O, -)` with global sections.
/-- Lemma 21.12.4 (1): the global cohomology of the underlying abelian sheaf of an
`\mathcal O`-module agrees with the module cohomology computed in `\mathrm{Mod}(\mathcal O)`. -/
theorem underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology
    [HasExt (Sheaf J AddCommGrpCat)] [HasExt (SheafOfModules 𝒪)]
    (ℱ : SheafOfModules 𝒪) (i : ℕ) :
    AddCommGrpCat.of (((SheafOfModules.toSheaf 𝒪).obj ℱ).H i) =
      (Abelian.extFunctorObj (SheafOfModules.unit 𝒪) i).obj ℱ := sorry

-- Proof sketch: first identify `H^i(U, \mathcal F_{ab})` with the global cohomology of the
-- restriction of `\mathcal F` to the localized site `(C/U, J.over U)` by Lemma `21.7.1`.
-- Then apply the global comparison from part `(1)` on the localized ringed site
-- `((C/U, J.over U), \mathcal O_U)`.
/-- Lemma 21.12.4 (2): for any object `U` of the site, the cohomology of the underlying abelian
sheaf over `U` agrees with the module cohomology of the localized module on the localized ringed
site `((C/U, J.over U), \mathcal O_U)`. -/
theorem underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology
    (U : C) [HasExt (SheafOfModules (𝒪.over U))]
    (ℱ : SheafOfModules 𝒪) (i : ℕ) :
    ((SheafOfModules.toSheaf 𝒪).obj ℱ).H' i U =
      (Abelian.extFunctorObj (SheafOfModules.unit (𝒪.over U)) i).obj
        ((SheafOfModules.pushforward (𝟙 (𝒪.over U))).obj ℱ) := sorry
