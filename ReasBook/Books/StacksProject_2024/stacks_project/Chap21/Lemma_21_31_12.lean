import StacksProject_2024.stacks_project.Chap21.«21_31_0_1»
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived

open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace
open scoped CategoryTheory
open scoped CategoryTheory.GrothendieckTopology
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

/- Domain-style sampling for Lemma 21.31.12:
- primary domain: cohomology and hypercohomology comparison between the small Zariski site of
  `X ∈ LC_{qc}` and the localized qc site `LC_{qc}/X`;
- inspected owner declarations:
  `lcZar_piInverse_cohomology_isomorphic`,
  `comparisonPushforward_aInverseAb_isomorphic_piInverseAb`,
  `smallDerived_isomorphic_localizationPushforward_aInverseDerived`,
  `siteAbelianSectionsDerived`,
  `Sheaf.constantSheafOverObjIso`;
- best owner abstraction: the source-facing statements remain the direct small-vs-qc comparison,
  but their canonical proof-side owner layer is already assembled upstream in the Chapter `21.31`
  owner theorems for `π_X⁻¹`, `a_X⁻¹`, and `R a_{X,*}`; the theorem surfaces here should therefore
  stay source-facing while reusing only the intrinsic owners
  `SmallAbSheaf`, `a[hle, πFunctor X]⁻¹`, `Sheaf.cohomologyFunctor`, `constantSheaf`,
  `RΓ[...]`, and `D⁺`;
- primitive vs derived:
  primitive data are the actual Grothendieck topologies `τzar`, `τqc`, the comparison hypothesis
  `τzar ≤ τqc`, and the chosen small-to-big Zariski functor `πFunctor`;
  derived API is the three comparison isomorphisms below.

Source/core/bridge triage:
- `source-facing`: the three comparison statements of Lemma `21.31.12`;
- `core/canonical`: `SmallAbSheaf`, `Sheaf (τqc.over X) AddCommGrpCat`, `piInverseAb`,
  `comparisonTopologyPullbackAb`, `Sheaf.cohomologyFunctor`, `constantSheaf`, and `D⁺`;
- `bridge/view`: the appearance of `a_X^{-1}` through the owner notation
  `a[hle, πFunctor X]⁻¹`, backed by the bridge owner `aInverseAb`; for clause `(3)`, the
  comparison object `a_X^{-1}\underline A` remains only in the companion bridge lemma below,
  while the source-facing theorem itself lands directly on the canonical constant sheaf on
  `τqc.over X`.
-/

section

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (hle : τzar ≤ τqc)
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u},
  HasWeakSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u},
  HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u},
  HasExt (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [∀ X : LCCat.{u}, HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u}, HasSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u}, HasExt (Sheaf (τqc.over X) AddCommGrpCat.{u + 1})]

section

variable (X : LCCat.{u})

local notation "Xzar" => Opens.grothendieckTopology X.obj
local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹

-- Proof sketch: compose the Chapter `21.7` global-cohomology comparison for `π_X⁻¹` with
-- `comparisonPushforward_aInverseAb_isomorphic_piInverseAb` to compare the small-site cohomology
-- of `ℱ` with the qc-site cohomology of `a_X⁻¹ ℱ`.
/-- Lemma 21.31.12 (1): for an abelian sheaf `ℱ` on `X ∈ LC_{qc}`, the global cohomology
`H^n(X, ℱ)` is canonically isomorphic to the qc cohomology `H^n_{qc}(X, a_X⁻¹ ℱ)`. Here
`a_X⁻¹` is the composite
`π_X^{-1} : Sh(X) ⥤ Sh(LC_{Zar}/X)` followed by the topology-comparison pullback
`ε_X⁻¹ : Sh(LC_{Zar}/X) ⥤ Sh(LC_{qc}/X)`. -/
@[stacks 09X4]
theorem smallCohomology_iso_qcCohomology_of_aInverse
    (ℱ : SmallAbSheaf X) (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor Xzar n).obj ℱ)
      ((Sheaf.cohomologyFunctor (τqc.over X) n).obj (aX⁻¹.obj ℱ)) := by
  sorry

-- Proof sketch: first identify the small constant sheaf restricted to `LC_{Zar}/X` with the
-- constant sheaf on that slice site, then apply the qc/Zariski comparison pullback to transport
-- that constant object to `LC_{qc}/X`.
omit [∀ X : LCCat.{u},
  HasExt (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
  [∀ X : LCCat.{u}, HasExt (Sheaf (τqc.over X) AddCommGrpCat.{u + 1})] in
/-- Companion bridge for Lemma 21.31.12 (3): the canonical inverse image `a_X^{-1}` sends the
small constant sheaf `A` to the canonical constant sheaf on `LC_{qc}/X`. -/
theorem aInverse_constantSheaf_isomorphic_constantSheaf
    (A : AddCommGrpCat.{u + 1}) :
    IsIsomorphic
      (aX⁻¹.obj ((constantSheaf Xzar AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf (τqc.over X) AddCommGrpCat.{u + 1}).obj A) := by
  sorry

-- Proof sketch: specialize clause `(1)` to the small constant sheaf `A`, then
-- transport the qc-side cohomology across the companion bridge
-- `aInverse_constantSheaf_isomorphic_constantSheaf` so that the source-facing conclusion lands on
-- the canonical constant sheaf on `LC_{qc}/X`.
/-- Lemma 21.31.12 (3): for an abelian group `A`, the small-site cohomology of the constant sheaf
`A` on `X` is canonically isomorphic to the qc cohomology of the canonical constant
sheaf on `LC_{qc}/X`. The companion bridge
`aInverse_constantSheaf_isomorphic_constantSheaf` identifies the intermediate comparison object
`a_X⁻¹ A` with that canonical qc constant sheaf. -/
@[stacks 09X4]
theorem constantSheaf_smallCohomology_iso_qcCohomology
    (A : AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor Xzar n).obj
        ((constantSheaf Xzar AddCommGrpCat.{u + 1}).obj A))
      ((Sheaf.cohomologyFunctor (τqc.over X) n).obj
        ((constantSheaf (τqc.over X) AddCommGrpCat.{u + 1}).obj A)) := by
  sorry

end

end

section

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (hle : τzar ≤ τqc)
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u},
  HasWeakSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u},
  HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u}, HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
variable [∀ X : LCCat.{u}, HasSheafify (τqc.over X) AddCommGrpCat.{u + 1}]

section Derived

variable [∀ X : LCCat.{u},
  IsGrothendieckAbelian (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [∀ X : LCCat.{u}, IsGrothendieckAbelian (Sheaf (τqc.over X) AddCommGrpCat.{u + 1})]

variable (X : LCCat.{u})
variable [Functor.Additive (piInverseAb (τzar.over X) (πFunctor X))]
variable [CategoryTheory.Limits.PreservesFiniteLimits (piInverseAb (τzar.over X) (πFunctor X))]
variable [CategoryTheory.Limits.PreservesFiniteColimits
  (piInverseAb (τzar.over X) (πFunctor X))]

local notation "Xzar" => Opens.grothendieckTopology X.obj
local notation "Xid" => Over.mk (𝟙 X)
local notation "Xtop" => (⊤ : Opens X.obj)
local notation "RΓqc" => RΓ[τqc.over X](Xid)
local notation "RΓsmall" => RΓ[Xzar](Xtop)
local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹

-- Proof sketch: apply the Chapter `21.31` owner
-- `smallDerived_isomorphic_localizationPushforward_aInverseDerived`, then compute
-- hypercohomology by the canonical terminal-object derived-sections owners on the small and qc
-- sites.
/-- Lemma 21.31.12 (2): for `K ∈ D⁺(SmallAbSheaf X)`, the degree-`n` hypercohomology `H^n(X, K)`
is canonically isomorphic to the qc hypercohomology `H^n_{qc}(X, a_X⁻¹ K)`. The small-site and qc
sides are stated directly on the canonical terminal-object derived-sections owners `RΓsmall` and
`RΓqc`. The derived inverse image is the canonical derived lift of `a[hle, πFunctor X]⁻¹`.
-/
@[stacks 09X4]
theorem smallHypercohomology_iso_qcHypercohomology_of_aInverse
    (K : D⁺((SmallAbSheaf X)))
    (n : ℕ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        ((RΓsmall).obj K.toDerived))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        ((RΓqc).obj ((aX⁻¹.mapDerivedCategory).obj K.toDerived))) := by
  sorry

end Derived

end

end CategoryTheory.GrothendieckTopology
