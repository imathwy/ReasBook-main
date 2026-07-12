import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Definition_21_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- 
Domain-style sampling for Definition 20.49.1:
- primary domain: perfect complexes and perfect derived `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `RingedSite.CochainComplex.IsPerfect`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`,
  `opensRingedSite`,
  `DerivedCategory.Q`;
- best owner abstraction: the Chapter 20 ringed-space owners should be the opens-ringed-space
  specialization of the canonical Chapter 21 perfectness owners on ringed sites; the
  representative criterion remains the source-facing companion API.

Source/core/bridge triage:
- `source-facing`: the ringed-space perfectness owners
  `AlgebraicGeometry.RingedSpace.CochainComplex.IsPerfect` and
  `AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect`;
- `core/canonical`: `RingedSite.CochainComplex.IsPerfect`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`, and `opensRingedSite`;
- `bridge/view`: the representative criterion
  `isPerfect_iff_exists_perfect_representative`.
-/
namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "CpxOX" => CochainComplex ModX ℤ
local notation "DModX" => DerivedCategory ModX
local notation "SiteModX" => ModuleCat (opensRingedSite X)
local notation "SiteDModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)

namespace CochainComplex

/-- Definition 20.49.1 (1): a complex of `𝒪_X`-modules is perfect. This is the opens-ringed-space
specialization of the canonical Chapter 21 perfectness owner on a ringed site. -/
abbrev IsPerfect (E : CpxOX) : Prop :=
  (RingedSite.CochainComplex.IsPerfect : CochainComplex SiteModX ℤ → Prop) E

end CochainComplex

namespace DerivedCategory

/-- Definition 20.49.1 (2): an object of `D(𝒪_X)` is perfect. This is the opens-ringed-space
specialization of the canonical Chapter 21 perfectness owner on a ringed site. -/
abbrev IsPerfect (E : DModX) : Prop :=
  (RingedSite.Hom.ModuleDerived.IsPerfect : SiteDModX → Prop) E

/-- A chosen perfect representative complex presents a perfect object of `D(𝒪_X)`. -/
theorem of_iso_q_obj {E : DModX} {K : CpxOX} (e : E ≅ DerivedCategory.Q.obj K)
    (hK : CochainComplex.IsPerfect K) :
    IsPerfect E :=
  RingedSite.Hom.ModuleDerived.of_iso_q_obj e hK

/-- A perfect derived `𝒪_X`-module admits a perfect representative complex. -/
theorem exists_perfect_representative {E : DModX} (hE : IsPerfect E) :
    ∃ K : CpxOX,
      ∃ _ : E ≅ DerivedCategory.Q.obj K,
        CochainComplex.IsPerfect K :=
  hE

/-- Unfolding `DerivedCategory.IsPerfect` gives the representative criterion from Definition
20.49.1. -/
theorem isPerfect_iff_exists_perfect_representative
    (E : DModX) :
    IsPerfect E ↔
      ∃ K : CpxOX,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsPerfect K :=
  Iff.rfl

end DerivedCategory

end AlgebraicGeometry.RingedSpace
