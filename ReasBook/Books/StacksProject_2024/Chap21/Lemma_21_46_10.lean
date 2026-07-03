import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap18.Lemma_18_36_3
import StacksProject_2024.Chap21.Definition_21_46_1

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- A sheaf of commutative rings on a site, regarded as a `RingCat`-valued sheaf. -/
private abbrev ringedSiteRingSheaf
    (𝒪 : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules
    (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules (ringedSiteRingSheaf 𝒪)

variable [Abelian (RingedSiteModules 𝒪)]
variable [CategoryWithHomology (RingedSiteModules 𝒪)]
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules 𝒪))]

local notation "DMod" => DerivedCategory (RingedSiteModules 𝒪)

/-- The commutative stalk ring `\mathcal O_p` at a point `p` of the ringed site. -/
private abbrev pointCommPresheafStalk
    (𝒪 : Sheaf J CommRingCat.{u})
    (p : GrothendieckTopology.Point.{u} J) :
    CommRingCat.{u} :=
  (p.presheafFiber : (Cᵒᵖ ⥤ CommRingCat.{u}) ⥤ CommRingCat.{u}).obj 𝒪.obj

/-- The forgotten `RingCat` stalk of `\mathcal O` identifies canonically with the commutative
stalk ring `\mathcal O_p`. -/
private abbrev pointStalkRingEquivPointCommPresheafStalk
    (p : GrothendieckTopology.Point.{u} J) :
    ↑(CategoryTheory.point_stalk_ring p (ringedSiteRingSheaf 𝒪)) ≃+*
      ↑(pointCommPresheafStalk 𝒪 p) :=
  ((p.presheafFiberCompIso (forget₂ CommRingCat RingCat)).app 𝒪.obj).ringCatIsoToRingEquiv

/-- The stalk functor on `\mathcal O`-modules at `p`, retargeted to modules over the commutative
stalk ring `\mathcal O_p`. -/
private abbrev pointModuleFunctor
    (p : GrothendieckTopology.Point.{u} J) :
    RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) :=
  CategoryTheory.point_sheaf_module_stalk_functor p (ringedSiteRingSheaf 𝒪) ⋙
    ModuleCat.restrictScalars (pointStalkRingEquivPointCommPresheafStalk p).symm.toRingHom

-- Proof sketch: `CategoryTheory.point_sheaf_module_stalk_functor` is exact by Lemma `18.36.3`,
-- and restriction of scalars along the canonical ring equivalence between the forgotten stalk ring
-- and the commutative stalk ring preserves exact sequences.
/-- The point-stalk functor on `\mathcal O`-modules is exact. -/
private theorem pointModuleFunctor_exact
    (p : GrothendieckTopology.Point.{u} J) :
    exactFunctor (RingedSiteModules 𝒪) (ModuleCat (pointCommPresheafStalk 𝒪 p))
      (pointModuleFunctor p) := sorry

/-- The exact-functor package attached to the point-stalk functor on `\mathcal O`-modules. -/
private abbrev pointModuleExactFunctor
    (p : GrothendieckTopology.Point.{u} J) :
    RingedSiteModules 𝒪 ⥤ₑ ModuleCat (pointCommPresheafStalk 𝒪 p) :=
  let F : RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) := pointModuleFunctor p
  let _ : PreservesFiniteLimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).1
  let _ : PreservesFiniteColimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).2
  ExactFunctor.of F

-- Proof sketch: both the site-theoretic stalk functor and restriction of scalars are additive,
-- so the exact point-stalk functor is additive as well.
/-- The exact point-stalk functor on `\mathcal O`-modules is additive. -/
private theorem pointModuleExactFunctor_additive
    (p : GrothendieckTopology.Point.{u} J) :
    let F : RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) := pointModuleFunctor p
    F.Additive := sorry

/-- The derived point-stalk functor `E ↦ E_p` from `D(\mathcal O)` to `D(\mathcal O_p)`. -/
private abbrev pointStalkDerived
    (p : GrothendieckTopology.Point.{u} J) :
    DMod ⥤ DerivedCategory (ModuleCat (pointCommPresheafStalk 𝒪 p)) :=
  let F :
      RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) := pointModuleFunctor p
  let _ : F.Additive :=
    show F.Additive from pointModuleExactFunctor_additive p
  let _ : PreservesFiniteLimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).1
  let _ : PreservesFiniteColimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).2
  F.mapDerivedCategory

-- Proof sketch: regard the point stalk as the exact stalk functor on `\mathcal O`-modules and
-- apply the pullback-style tor-amplitude preservation statement from Lemma `21.46.5` to this
-- pointwise realization of `E_p`.
/-- If `E` has tor-amplitude in `[a, b]`, then the derived point stalk `E_p` has tor-amplitude in
`[a, b]` over the stalk ring `\mathcal O_p`. -/
theorem hasTorAmplitudeIn_pointStalkDerived
    (E : DMod) (a b : ℤ) (hE : HasTorAmplitudeIn E a b)
    (p : GrothendieckTopology.Point.{u} J) :
    CategoryTheory.HasTorAmplitudeIn ((pointStalkDerived p).obj E) a b := sorry

-- Proof sketch: the forward implication is `hasTorAmplitudeIn_pointStalkDerived`. For the
-- converse, test the defining homology-vanishing condition for `HasTorAmplitudeIn E a b` against an
-- arbitrary `\mathcal O`-module; after passing to every point stalk, the corresponding stalkwise
-- homology vanishes by the pointwise tor-amplitude hypothesis, and Lemma `18.14.4` lets one
-- conclude globally when the site has enough points.
/-- Lemma 21.46.10: if the ringed site `(\mathcal C, \mathcal O)` has enough points, then an
object `E` of `D(\mathcal O)` has tor-amplitude in `[a, b]` if and only if, for every point `p`
of the site, the derived point stalk `E_p` of `E` has tor-amplitude in `[a, b]` over
`\mathcal O_p`. -/
theorem hasTorAmplitudeIn_iff_forall_pointStalkDerived_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ p : GrothendieckTopology.Point.{u} J,
        CategoryTheory.HasTorAmplitudeIn ((pointStalkDerived p).obj E) a b := sorry

end

end SheafOfModules.RingedSite
