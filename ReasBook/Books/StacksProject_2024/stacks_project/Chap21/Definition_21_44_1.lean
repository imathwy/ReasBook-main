import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Retract
import StacksProject_2024.Chap20.Definition_20_46_1
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap18.Definition_18_17_1
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v

namespace RingedSite
namespace CochainComplex

section

variable {X : RingedSite.{u, v}}

open AlgebraicGeometry.RingedSpace.CochainComplex in
local notation "RingedSpaceIsStrictlyPerfect" => IsStrictlyPerfect

open AlgebraicGeometry.RingedSpace.CochainComplex in
local notation "ringedSpaceIsStrictlyPerfectIff" => isStrictlyPerfect_iff

open RingedSpace.CochainComplex in
local notation "ringedSpaceBounded" => IsStrictlyPerfect.bounded

open RingedSpace.CochainComplex in
local notation "ringedSpaceTermRetractClosure" => IsStrictlyPerfect.term_retractClosure

/-- The strict-perfectness owner on a bundled ringed site `X`: a complex of `𝒪_X`-modules
is bounded and every term is a direct summand of a finite free `𝒪_X`-module. This bundled-site
surface reuses the Chapter 20 owner on complexes of modules over the sheaf of rings
`X.structureSheaf`. -/
abbrev IsStrictlyPerfect
    (E : CochainComplex (_root_.SheafOfModules X.structureSheaf) ℤ) : Prop :=
  RingedSpaceIsStrictlyPerfect E

/-- A strictly perfect complex is bounded above and below. -/
theorem IsStrictlyPerfect.bounded
    {E : CochainComplex (_root_.SheafOfModules X.structureSheaf) ℤ} (hE : IsStrictlyPerfect E) :
    ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b :=
  ringedSpaceBounded hE

/-- In a strictly perfect complex, each term lies in the retract closure of finite free
`𝒪_X`-modules. -/
theorem IsStrictlyPerfect.term_retractClosure
    {E : CochainComplex (_root_.SheafOfModules X.structureSheaf) ℤ} (hE : IsStrictlyPerfect E)
    (i : ℤ) :
    SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf (E.X i) :=
  ringedSpaceTermRetractClosure hE i

/-- The bundled-site owner is exactly the Chapter 20 strict-perfectness predicate on
`X.structureSheaf`. -/
theorem isStrictlyPerfect_iff_ringedSpace
    (E : CochainComplex (_root_.SheafOfModules X.structureSheaf) ℤ) :
    IsStrictlyPerfect E ↔
      RingedSpaceIsStrictlyPerfect E :=
  Iff.rfl

/-- Unfolding `IsStrictlyPerfect` gives boundedness together with the termwise finite-free
retract-closure condition. -/
theorem isStrictlyPerfect_iff
    (E : CochainComplex (_root_.SheafOfModules X.structureSheaf) ℤ) :
    IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf (E.X i) := by
  rw [isStrictlyPerfect_iff_ringedSpace]
  simpa using ringedSpaceIsStrictlyPerfectIff E

end

section

variable {X : RingedSite.{u, v}}
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X.siteTopology.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

open RingedSpace.CochainComplex in
local notation "ringedSpaceTermRetractFree" => IsStrictlyPerfect.term_retract_free

/-- In a strictly perfect complex, each term is a retract of a finite free `𝒪_X`-module. -/
theorem IsStrictlyPerfect.term_retract_free
    {E : CochainComplex (_root_.SheafOfModules X.structureSheaf) ℤ} (hE : IsStrictlyPerfect E)
    (i : ℤ) :
    ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract (E.X i)
        (_root_.SheafOfModules.free I : _root_.SheafOfModules X.structureSheaf)) := by
  simpa using ringedSpaceTermRetractFree hE i

end

end CochainComplex
end RingedSite

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

open RingedSpace.CochainComplex in
local notation "RingedSpaceIsStrictlyPerfect" => IsStrictlyPerfect

open RingedSite.CochainComplex in
local notation "RingedSiteIsStrictlyPerfect" => IsStrictlyPerfect

open RingedSite.CochainComplex in
local notation "ringedSiteIsStrictlyPerfectIffRingedSpace" => isStrictlyPerfect_iff_ringedSpace

open RingedSite.CochainComplex in
local notation "ringedSiteIsStrictlyPerfectIff" => isStrictlyPerfect_iff

private abbrev ringedSiteModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  _root_.SheafOfModules (RingedSite.ofCommRingSheaf J 𝒪).structureSheaf

private abbrev ringedSiteComplex (E : CochainComplex Mod ℤ) :
    CochainComplex (ringedSiteModule J 𝒪) ℤ :=
  E

/-- Definition 21.44.1: a complex of `𝒪_X`-modules on a ringed site is strictly perfect
if it is zero in all but finitely many degrees and each term is a direct summand of a finite free
`𝒪_X`-module. This is the site-presentation bridge to the bundled owner on
`X := RingedSite.ofCommRingSheaf J 𝒪`. -/
@[stacks 08FL]
abbrev CochainComplex.IsStrictlyPerfect (E : CochainComplex Mod ℤ) : Prop :=
  RingedSiteIsStrictlyPerfect (ringedSiteComplex E)

/-- The site-presented strict-perfectness predicate is exactly the bundled ringed-site owner on
`X := RingedSite.ofCommRingSheaf J 𝒪`. -/
theorem CochainComplex.isStrictlyPerfect_iff_ringedSite
    (E : CochainComplex Mod ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      RingedSiteIsStrictlyPerfect (ringedSiteComplex E) :=
  Iff.rfl

/-- The site-presented strict-perfectness predicate is exactly the Chapter 20 strict-perfectness
owner on `ringSheaf J 𝒪`. -/
theorem CochainComplex.isStrictlyPerfect_iff_ringedSpace
    (E : CochainComplex Mod ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      RingedSpaceIsStrictlyPerfect E := by
  simpa using ringedSiteIsStrictlyPerfectIffRingedSpace (ringedSiteComplex E)

/-- A strictly perfect complex on `(C, J, 𝒪)` is bounded above and below. -/
theorem CochainComplex.IsStrictlyPerfect.bounded
    {E : CochainComplex Mod ℤ}
    (hE : CochainComplex.IsStrictlyPerfect E) :
    ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b :=
  hE.1

/-- In a strictly perfect complex on `(C, J, 𝒪)`, each term lies in the retract closure of finite
free `𝒪`-modules. -/
theorem CochainComplex.IsStrictlyPerfect.term_retractClosure
    {E : CochainComplex Mod ℤ} (hE : CochainComplex.IsStrictlyPerfect E) (i : ℤ) :
    SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J 𝒪) (E.X i) :=
  hE.2 i

/-- Unfolding the site-presented strict-perfect owner gives boundedness together with the
termwise finite-free retract-closure condition. -/
theorem CochainComplex.isStrictlyPerfect_iff (E : CochainComplex Mod ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty (ringSheaf J 𝒪) (E.X i) :=
by
  rw [CochainComplex.isStrictlyPerfect_iff_ringedSite]
  simpa using ringedSiteIsStrictlyPerfectIff (ringedSiteComplex E)

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- In a strictly perfect complex, each term is a retract of a finite free `𝒪_X`-module. -/
theorem CochainComplex.IsStrictlyPerfect.term_retract_free
    {E : CochainComplex Mod ℤ}
    (hE : CochainComplex.IsStrictlyPerfect E) (i : ℤ) :
    ∃ I : Type (max u v), Finite I ∧
      Nonempty
        (Retract (E.X i)
          (SheafOfModules.free I : Mod)) := by
  simpa using
    (SheafOfModules.finiteFreeRetractModuleProperty_iff (E.X i)).1
      (CochainComplex.IsStrictlyPerfect.term_retractClosure hE i)

end

end SheafOfModules.RingedSite
