import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap12.Remark_12_29_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_6
import StacksProject_2024.stacks_project.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom

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

variable [CategoryWithHomology (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [MonoidalCategory (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [MonoidalPreadditive (ModuleCat (RingedSite.ofCommRingSheaf J 𝒪))]
variable [MonoidalCategory (ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪))]

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => ModuleCat (RingedSite.ofCommRingSheaf J 𝒪)
local notation "DMod" => ModuleDerived X

private noncomputable abbrev sourcePointStalkRingEquiv
    (p : GrothendieckTopology.Point.{u} J) :
    ↑(p.stalkRing (ringSheaf J 𝒪)) ≃+* ↑(sourcePointRing 𝒪 p) :=
  ((p.presheafFiberCompIso (forget₂ CommRingCat RingCat)).app 𝒪.obj).ringCatIsoToRingEquiv

local instance ringedSiteModuleCategory_preadditive :
    Preadditive Mod :=
  (inferInstance : Abelian Mod).toPreadditive

instance stalkFunctor_preservesFiniteLimits
    (p : GrothendieckTopology.Point.{u} J) :
    PreservesFiniteLimits (stalkFunctor 𝒪 p) := by
  let F : Mod ⥤ ModuleCat (p.stalkRing (ringSheaf J 𝒪)) :=
    p.sheafModuleStalkFunctor (ringSheaf J 𝒪)
  let e : ↑(p.stalkRing (ringSheaf J 𝒪)) ≃+* ↑(sourcePointRing 𝒪 p) :=
    sourcePointStalkRingEquiv p
  let G : ModuleCat (p.stalkRing (ringSheaf J 𝒪)) ⥤ ModuleCat (sourcePointRing 𝒪 p) :=
    ModuleCat.restrictScalars (e.symm.toRingHom)
  let hF : exactFunctor _ _ F := p.sheafModuleStalk_exact (ringSheaf J 𝒪)
  let hG : exactFunctor _ _ G := restrictScalars_exact (e.symm.toRingHom)
  let _ : PreservesFiniteLimits F := (CategoryTheory.exactFunctor_iff F).1 hF |>.1
  let _ : PreservesFiniteLimits G := (CategoryTheory.exactFunctor_iff G).1 hG |>.1
  simpa [stalkFunctor] using (inferInstance : PreservesFiniteLimits (F ⋙ G))

instance stalkFunctor_preservesFiniteColimits
    (p : GrothendieckTopology.Point.{u} J) :
    PreservesFiniteColimits (stalkFunctor 𝒪 p) := by
  let F : Mod ⥤ ModuleCat (p.stalkRing (ringSheaf J 𝒪)) :=
    p.sheafModuleStalkFunctor (ringSheaf J 𝒪)
  let e : ↑(p.stalkRing (ringSheaf J 𝒪)) ≃+* ↑(sourcePointRing 𝒪 p) :=
    sourcePointStalkRingEquiv p
  let G : ModuleCat (p.stalkRing (ringSheaf J 𝒪)) ⥤ ModuleCat (sourcePointRing 𝒪 p) :=
    ModuleCat.restrictScalars (e.symm.toRingHom)
  let hF : exactFunctor _ _ F := p.sheafModuleStalk_exact (ringSheaf J 𝒪)
  let hG : exactFunctor _ _ G := restrictScalars_exact (e.symm.toRingHom)
  let _ : PreservesFiniteColimits F := (CategoryTheory.exactFunctor_iff F).1 hF |>.2
  let _ : PreservesFiniteColimits G := (CategoryTheory.exactFunctor_iff G).1 hG |>.2
  simpa [stalkFunctor] using (inferInstance : PreservesFiniteColimits (F ⋙ G))

/- Domain-style sampling for Lemma 21.46.10:
- primary domain: tor-amplitude in derived categories of sheaves of modules, tested stalkwise on a
  ringed site with enough points;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `CategoryTheory.sourcePointRing`,
  `SheafOfModules.RingedSite.stalkFunctor`,
  `Functor.mapDerivedCategory`;
- best owner abstraction: the source-facing tor-amplitude predicate is owned by
  `HasTorAmplitudeIn`, while the canonical commutative stalk-realization owner is the Chapter 21
  stalk functor `stalkFunctor 𝒪 p`; the derived stalk functor is obtained directly from this owner
  by `mapDerivedCategory`;
- primitive data: `E : D(𝒪)`, bounds `a, b`, and a point `p`;
- derived API: stalkwise tor-amplitude preservation and the enough-points detection theorem.

Source/core/bridge triage:
- `source-facing`: the two tor-amplitude theorems below;
- `core/canonical`: `HasTorAmplitudeIn`,
  `sourcePointRing`, and the Chapter 21 stalk owner `stalkFunctor 𝒪 p`;
- `bridge/view`: the derived stalk functor below, obtained from the canonical stalk functor by
  `mapDerivedCategory`. -/

/-- The derived point-stalk functor `E ↦ E_p` from `D(𝒪)` to `D(𝒪_p)`. -/
abbrev pointStalkDerived
    (p : GrothendieckTopology.Point.{u} J) :
    DMod ⥤ DerivedCategory (ModuleCat (sourcePointRing 𝒪 p)) :=
  (stalkFunctor 𝒪 p).mapDerivedCategory

-- Proof sketch: regard the point stalk as the exact stalk functor on `𝒪`-modules and
-- apply the pullback-style tor-amplitude preservation statement from Lemma `21.46.5` to this
-- pointwise realization of `E_p`.
namespace HasTorAmplitudeIn

/-- If `E` has tor-amplitude in `[a, b]`, then the derived point stalk `E_p` has tor-amplitude in
`[a, b]` over the stalk ring `𝒪_p`. -/
theorem pointStalkDerived
    {E : DMod} {a b : ℤ} (hE : HasTorAmplitudeIn E a b)
    (p : GrothendieckTopology.Point.{u} J) :
    CategoryTheory.HasTorAmplitudeIn ((pointStalkDerived p).obj E) a b := sorry

end HasTorAmplitudeIn

-- Proof sketch: the forward implication is `HasTorAmplitudeIn.pointStalkDerived`. For the
-- converse, test the defining homology-vanishing condition for `HasTorAmplitudeIn E a b` against
-- an arbitrary `𝒪`-module; after passing to every point stalk, the corresponding stalkwise
-- homology vanishes by the pointwise tor-amplitude hypothesis, and Lemma `18.14.4` lets one
-- conclude globally when the site has enough points.
/-- Lemma 21.46.10: if the ringed site `(𝒞, 𝒪)` has enough points, then an object `E` of `D(𝒪)`
has tor-amplitude in `[a, b]` if and only if, for every point `p` of the site, the derived point
stalk `E_p` of `E` has tor-amplitude in `[a, b]` over `𝒪_p`. -/
@[stacks 0DJJ]
theorem hasTorAmplitudeIn_iff_forall_pointStalkDerived_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ p : GrothendieckTopology.Point.{u} J,
        CategoryTheory.HasTorAmplitudeIn ((pointStalkDerived p).obj E) a b := sorry

end

end SheafOfModules.RingedSite
