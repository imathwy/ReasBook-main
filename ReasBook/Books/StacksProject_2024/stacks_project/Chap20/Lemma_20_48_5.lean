import StacksProject_2024.Chap07.Example_7_33_5
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap20.Definition_20_48_1_Core
import StacksProject_2024.Chap20.Tor_amplitude_on_opens_ringed_site
import StacksProject_2024.Chap21.Lemma_21_46_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]

local notation "DMod" => DerivedCategory (Modules X)
local notation "PointStalkMod" x =>
  ModuleCat (CategoryTheory.sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x))
local notation "StalkMod" x => ModuleCat (X.presheaf.stalk x)

/-
Domain-style sampling for Lemma 20.48.5:
- primary domain: tor-amplitude in derived categories of `𝒪_X`-modules and detection by
  stalk functors;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `SheafOfModules.RingedSite.pointStalkDerived`,
  `CategoryTheory.sourcePointRing`,
  `pointGrothendieckTopology_sheafFiber_obj_iso_stalk`,
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`,
  `SheafOfModules.RingedSite.hasTorAmplitudeIn_iff_forall_pointStalkDerived_of_hasEnoughPoints`,
  `CategoryTheory.HasTorAmplitudeIn`;
- best owner abstraction:
  `source-facing`: the ringed-space tor-amplitude statement detected on points of `X`;
  `core/canonical`: the Chapter 21 derived point-stalk owner
    `pointStalkDerived (Opens.pointGrothendieckTopology x)` together with the opens-site
    tor-amplitude owner theorem
    `hasTorAmplitudeIn_iff_forall_pointStalkDerived_of_hasEnoughPoints` and the module-category
    owner `CategoryTheory.HasTorAmplitudeIn`;
  `bridge/view`: the ring-equivalence transport from the Chapter 21 source-point stalk ring
    `sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x)` to the usual stalk ring
    `X.presheaf.stalk x`, packaged below as `stalkDerived`.

Primitive vs. derived:
- primitive data: the ringed-space object `E`, the interval bounds `a, b`, and the exact
  opens-site derived point stalk of Chapter 21, together with the canonical ring equivalence to
  the ordinary stalk ring;
- derived API: the ordinary-stalk derived functor `stalkDerived`, the iff theorem below, and the
  companion introduction/elimination lemmas.
-/

private abbrev pointStalkRingEquivStalkRing (x : X) :
    CategoryTheory.sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x) ≃+*
      X.presheaf.stalk x :=
  Iso.commRingCatIsoToRingEquiv
    (CategoryTheory.pointGrothendieckTopology_sheafFiber_obj_iso_stalk x X.sheaf)

/-- The derived stalk functor `E ↦ E_x` from `D(𝒪_X)` to `D(𝒪_{X, x})`, obtained from the
Chapter 21 derived point-stalk functor by transporting scalars along the canonical identification
of the opens-site point stalk ring with `𝒪_{X, x}`. -/
abbrev stalkDerived (x : X) :
    DMod ⥤ DerivedCategory (StalkMod x) :=
  pointStalkDerived (Opens.pointGrothendieckTopology x) ⋙
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (pointStalkRingEquivStalkRing x).symm).functor.mapDerivedCategory

-- Proof sketch: rewrite Chapter 20 tor-amplitude on `X` as Chapter 21 tor-amplitude on the opens
-- ringed site by `hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn`, specialize the Chapter
-- 21 enough-points theorem to `X.sheaf`, and then transport each canonical point stalk along the
-- ring equivalence `sourcePointRing X.sheaf (Opens.pointGrothendieckTopology x) ≃ X.presheaf.stalk x`
-- encoded by `stalkDerived`.
/-- Lemma 20.48.5: an object `E` of `D(𝒪_X)` has tor-amplitude in `[a, b]` if and only if, for
every point `x : X`, the derived stalk object `E_x` in `D(𝒪_{X, x})` has tor-amplitude in
`[a, b]`. -/
@[stacks 09U9]
theorem hasTorAmplitudeIn_iff_forall_stalk
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj E) a b := sorry

namespace HasTorAmplitudeIn

/-- A tor-amplitude bound on `E` may be checked on all derived stalks `E_x`. -/
theorem forall_stalk
    {E : DMod} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj E) a b :=
  (hasTorAmplitudeIn_iff_forall_stalk E a b).1 hE

end HasTorAmplitudeIn

/-- If all derived stalks `E_x` have tor-amplitude in `[a, b]`, then so does `E`. -/
theorem hasTorAmplitudeIn_of_forall_stalk
    {E : DMod} {a b : ℤ}
    (hE : ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj E) a b) :
    HasTorAmplitudeIn E a b :=
  (hasTorAmplitudeIn_iff_forall_stalk E a b).2 hE

end

end AlgebraicGeometry.RingedSpace
