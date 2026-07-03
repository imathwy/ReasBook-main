import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_36_3
import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- A sheaf of commutative rings on a site, regarded as a `RingCat`-valued sheaf. -/
private abbrev ringedSiteRingSheaf
    (𝒪 : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules
    (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules (ringedSiteRingSheaf 𝒪)

variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

/-- The point stalk functor on `\mathcal O`-modules preserves zero morphisms. -/
local instance point_stalkFunctor_preservesZeroMorphisms
    (p : GrothendieckTopology.Point.{u} J) :
    (point_sheaf_module_stalk_functor p
      (ringedSiteRingSheaf 𝒪)).PreservesZeroMorphisms := sorry

/-- The `CommRingCat`-valued presheaf fiber of `\mathcal O` at the point `p`. -/
private abbrev pointCommPresheafStalk
    (𝒪 : Sheaf J CommRingCat.{u})
    (p : GrothendieckTopology.Point.{u} J) :
    CommRingCat.{u} :=
  (p.presheafFiber : (Cᵒᵖ ⥤ CommRingCat.{u}) ⥤ CommRingCat.{u}).obj 𝒪.obj

/-- The forgotten `RingCat` stalk of `\mathcal O` agrees with the `CommRingCat` presheaf fiber
at `p`. -/
private abbrev pointStalkRingEquivPointCommPresheafStalk
    (p : GrothendieckTopology.Point.{u} J) :
    ↑(point_stalk_ring p (ringedSiteRingSheaf 𝒪)) ≃+*
      ↑(pointCommPresheafStalk 𝒪 p) :=
  let e :
      ↑(point_stalk_ring p (ringedSiteRingSheaf 𝒪)) ≃+*
        ↑(pointCommPresheafStalk 𝒪 p) :=
    ((p.presheafFiberCompIso (forget₂ CommRingCat RingCat)).app 𝒪.obj).ringCatIsoToRingEquiv
  e

/-- The stalk complex of a complex of `\mathcal O`-modules at a point `p`, viewed as a cochain
complex of modules over the stalk ring `\mathcal O_p`. -/
abbrev pointStalkComplex
    (p : GrothendieckTopology.Point.{u} J)
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ) :
    CochainComplex (ModuleCat (pointCommPresheafStalk 𝒪 p)) ℤ :=
  (((ModuleCat.restrictScalars
      (pointStalkRingEquivPointCommPresheafStalk p).symm.toRingHom).mapHomologicalComplex
      (up ℤ)).obj
    (((point_sheaf_module_stalk_functor p
      (ringedSiteRingSheaf 𝒪)).mapHomologicalComplex
      (up ℤ)).obj K))

/-- The tensor-acyclicity condition of More on Algebra, Definition `15.59.1`, applied to the
stalk complex at the point `p`. -/
def pointStalkKFlatCondition
    (p : GrothendieckTopology.Point.{u} J)
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ) : Prop :=
  CochainComplex.IsKFlat (pointStalkComplex p K)

-- Proof sketch: choose a quasi-isomorphism from a K-flat complex with flat terms using Lemma
-- `21.17.11`, apply stalkwise preservation of K-flatness for pullbacks from Lemma `21.18.1`,
-- and reduce to the acyclic case. For an acyclic K-flat complex, use finite-presentation tests
-- for module-theoretic K-flatness and the exactness of taking stalks.
/-- Lemma 21.18.6 (1): if a cochain complex of `\mathcal O`-modules on a ringed site is K-flat,
then for every point `p` of the site its stalk complex `\mathcal K_p^\bullet` is K-flat as a
cochain complex of `\mathcal O_p`-modules. -/
theorem pointStalkKFlatCondition_of_isKFlat
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ)
    (hK : CochainComplex.IsKFlat K)
    (p : GrothendieckTopology.Point.{u} J) :
    pointStalkKFlatCondition p K := sorry

-- Proof sketch: for an acyclic test complex `F^\bullet` of `\mathcal O`-modules, exactness of
-- the total tensor product with `K^\bullet` can be checked on stalks when the site has enough
-- points. Stalk formation commutes with tensor products and direct sums, so the stalkwise
-- K-flatness assumptions identify every stalk tensor complex with an acyclic module-theoretic
-- tensor product.
/-- Lemma 21.18.6 (2): if the site has enough points and every stalk complex
`\mathcal K_p^\bullet` is K-flat over `\mathcal O_p`, then `\mathcal K^\bullet` is K-flat on the
ringed site. -/
theorem isKFlat_of_pointStalkKFlatCondition_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ)
    (hK : ∀ p : GrothendieckTopology.Point.{u} J, pointStalkKFlatCondition p K) :
    CochainComplex.IsKFlat K := sorry

end SheafOfModules.RingedSite
