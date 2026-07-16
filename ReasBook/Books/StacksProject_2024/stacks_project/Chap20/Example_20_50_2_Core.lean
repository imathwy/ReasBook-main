import StacksProject_2024.stacks_project.Chap20.«20_9_0_1»
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.stacks_project.Chap20.Definition_20_46_1
import StacksProject_2024.stacks_project.Chap21.Example_21_48_2_Core
import StacksProject_2024.stacks_project.Chap20.OpensInstances

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "CpxX" => CochainComplex (Modules X) ℤ

/- Domain-style sampling for the Chapter 20 local strict-perfectness owner used in Example 20.50.2
and Lemma 20.50.3:
- primary domain: local strict perfectness for complexes of `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect`,
  `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`,
  `moduleSheafRestrictionToOpen`,
  `cochainComplex_isLocallyStrictlyPerfect_iff_site`;
- best owner abstraction:
  `source-facing`: `AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyStrictlyPerfect`;
  `core/canonical`: the ringed-site owner
    `SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect`;
  `bridge/view`: `cochainComplex_isLocallyStrictlyPerfect_iff_site`.
- primitive data: an open cover of `X` with strictly perfect restrictions;
- derived API: only the source-facing owner and the bridge to the ringed-site formulation.

These declarations should live in a lightweight core file so downstream uses do not import the
heavier duality construction from Example 20.50.2. -/

private abbrev restrictedComplex
    (U : Opens X) :
    CpxX ⥤
      CochainComplex
        (SheafOfModules ((TopCat.Sheaf.pullback RingCat U.inclusion').obj (ringCatSheaf X))) ℤ :=
  (moduleSheafRestrictionToOpen U (ringCatSheaf X)).mapHomologicalComplex (up ℤ)

/-- A complex of `𝒪_X`-modules is locally strictly perfect if some open cover of `X` has strictly
perfect restrictions. -/
class CochainComplex.IsLocallyStrictlyPerfect (E : CpxX) : Prop where
  out :
    ∃ (ι : Type u) (U : ι → Opens X),
      IsOpenCover U ∧
        ∀ i : ι,
          CochainComplex.IsStrictlyPerfect ((restrictedComplex (U i)).obj E)

/-- Unfolding `IsLocallyStrictlyPerfect` gives the explicit open-cover criterion by strictly
perfect restrictions. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff
    (E : CpxX) :
    CochainComplex.IsLocallyStrictlyPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X),
        IsOpenCover U ∧
          ∀ i : ι,
            CochainComplex.IsStrictlyPerfect ((restrictedComplex (U i)).obj E) := by
  constructor
  · intro hE
    exact hE.out
  · intro hE
    exact ⟨hE⟩

section Site

variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]
variable [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [∀ U : Opens X,
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The Chapter 20 open-cover formulation of local strict perfectness is equivalent to the
all-opens local-cover formulation. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff_site
    (E : CpxX) :
    CochainComplex.IsLocallyStrictlyPerfect E ↔
      SheafOfModules.RingedSite.CochainComplex.IsLocallyStrictlyPerfect E := by
  sorry

end Site

end AlgebraicGeometry.RingedSpace
