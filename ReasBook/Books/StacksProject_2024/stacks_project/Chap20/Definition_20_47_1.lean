import StacksProject_2024.stacks_project.Chap20.Definition_20_46_1
import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1_Core
import StacksProject_2024.stacks_project.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Definition 20.47.1 adds the open-cover strict-perfect approximation criterion to the core
pseudo-coherence owners from `Definition_20_47_1_Core`. -/

local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => DerivedCategory ModX
local notation "Mod[" U "]" => openSubspaceModuleCategory X U
local notation "Cpx[" U "]" => CochainComplex (Mod[U]) ℤ
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U

open _root_.AlgebraicGeometry.RingedSpace.CochainComplex

namespace ModuleDerived

/-- The restriction `E↾[U]` admits a strict-perfect approximation in degree `m` if it receives a
morphism from a strictly perfect complex inducing cohomology isomorphisms in degrees `> m` and an
epimorphism in degree `m`. -/
abbrev HasStrictlyPerfectApproximationInDegreeOnOpen
    (E : DModX) (U : Opens X.carrier) (m : ℤ) : Prop :=
  ∃ Ei : Cpx[U],
    ∃ α : DerivedCategory.Q.obj Ei ⟶ (DRes[U]).obj E,
      IsStrictlyPerfect Ei ∧
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor (Mod[U]) j).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor (Mod[U]) m).map α)

/-- A derived `𝒪_X`-module is `m`-pseudo-coherent exactly when it admits a strict-perfect
approximation in degree `m` on each member of some open cover. -/
theorem isMPseudoCoherent_iff_exists_openCover
    (E : DModX) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, HasStrictlyPerfectApproximationInDegreeOnOpen E (U i) m :=
  sorry

/-- An open cover whose restricted derived objects all admit strict-perfect approximations in
degree `m` exhibits `m`-pseudo-coherence. -/
theorem isMPseudoCoherent_of_isOpenCover
    {ι : Type u} {U : ι → Opens X.carrier} {E : DModX} {m : ℤ}
    (hU : IsOpenCover U)
    (hE : ∀ i : ι, HasStrictlyPerfectApproximationInDegreeOnOpen E (U i) m) :
    IsMPseudoCoherent E m :=
  (isMPseudoCoherent_iff_exists_openCover E m).2 ⟨ι, U, hU, hE⟩

section OpensRingedSite

variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (RingedSite.Hom.ModuleCat ((opensRingedSite X).localization U))]

/-- The Chapter 20 `m`-pseudo-coherence owner on a ringed space bridges to the canonical
Chapter 21 owner on the opens ringed site of `X`. -/
theorem IsMPseudoCoherent.opensRingedSite
    {E : DModX} {m : ℤ} (hE : IsMPseudoCoherent E m) :
    RingedSite.Hom.ModuleDerived.IsMPseudoCoherent (X := opensRingedSite X) E m := by
  sorry

end OpensRingedSite

end ModuleDerived

end AlgebraicGeometry.RingedSpace

end
