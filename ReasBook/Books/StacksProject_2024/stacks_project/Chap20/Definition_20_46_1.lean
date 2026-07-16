import Mathlib.CategoryTheory.Retract
import StacksProject_2024.stacks_project.Chap18.Definition_18_17_1

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The object property of `𝒪`-modules that are retracts of finite free modules. -/
abbrev finiteFreeRetractModuleProperty
    (𝒪 : Sheaf J RingCat.{max u v}) : ObjectProperty (SheafOfModules 𝒪) :=
  ObjectProperty.retractClosure
    (fun M : SheafOfModules 𝒪 ↦ _root_.SheafOfModules.IsFiniteFree M)

end

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Definition 20.46.1:
- primary domain: strictly perfect cochain complexes of module sheaves over a sheaf of rings on a
  topological space;
- sampled owner declarations:
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `SheafOfModules.finiteFreeRetractModuleProperty`;
- best owner abstraction: the source-facing and canonical owner is the single predicate
  `CochainComplex.IsStrictlyPerfect` on complexes of `SheafOfModules R`;
- primitive data: strict lower and upper bounds together with, in each degree, a retract
  presentation by a finite free module sheaf, recorded via
  `SheafOfModules.finiteFreeRetractModuleProperty R`;
- derived API: the boundedness projection, the termwise retract-closure and finite-free-retract
  companions, plus the unfolding bridge theorem used by later ringed-space constructions.

Source/core/bridge triage:
- `source-facing`: Definition 20.46.1 itself, namely strict perfectness for complexes of
  `𝒪_X`-modules;
- `core/canonical`: the same owner `CochainComplex.IsStrictlyPerfect`, which is the intrinsic
  chapter predicate and not a later downstream wrapper;
- `bridge/view`: `CochainComplex.isStrictlyPerfect_iff`, which unfolds the owner into boundedness
  plus the canonical termwise owner `SheafOfModules.finiteFreeRetractModuleProperty`, and the
  companion theorem `CochainComplex.IsStrictlyPerfect.term_retract_free`, which recovers the
  textbook retract-of-finite-free formulation degreewise.

This file owns the notion directly. Later files should reuse this owner instead of defining a
parallel copy downstream. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{max u v}}

local notation "Mod" => SheafOfModules R
namespace CochainComplex

/-- Definition 20.46.1: a complex of modules over a sheaf of rings is strictly perfect if it is
bounded and each term lies in `SheafOfModules.finiteFreeRetractModuleProperty R`. -/
@[stacks 08C4]
def IsStrictlyPerfect
    (E : CochainComplex Mod ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R (E.X i)

/-- A strictly perfect complex is bounded above and below. -/
theorem IsStrictlyPerfect.bounded {E : CochainComplex Mod ℤ}
    (hE : IsStrictlyPerfect E) :
    ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b :=
  hE.1

/-- In a strictly perfect complex, each term lies in the retract closure of finite free module
sheaves. -/
theorem IsStrictlyPerfect.term_retractClosure {E : CochainComplex Mod ℤ}
    (hE : IsStrictlyPerfect E) (i : ℤ) :
    SheafOfModules.finiteFreeRetractModuleProperty R (E.X i) :=
  hE.2 i

/-- Unfolding `CochainComplex.IsStrictlyPerfect` yields boundedness together with the canonical
termwise owner `SheafOfModules.finiteFreeRetractModuleProperty R`. -/
theorem isStrictlyPerfect_iff
    (E : CochainComplex Mod ℤ) :
    IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty R (E.X i) :=
  Iff.rfl

end CochainComplex

end

end AlgebraicGeometry.RingedSpace

namespace SheafOfModules

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]

/-- A module lies in `finiteFreeRetractModuleProperty` exactly when it is a direct retract of a
finite free module. -/
theorem finiteFreeRetractModuleProperty_iff
    {𝒪 : Sheaf J RingCat.{max u v}} (M : SheafOfModules 𝒪) :
    finiteFreeRetractModuleProperty 𝒪 M ↔
      ∃ I : Type (max u v), Finite I ∧
        Nonempty (Retract M (_root_.SheafOfModules.free I : SheafOfModules.{max u v} 𝒪)) := by
  constructor
  · intro hM
    -- Rewrite the owner as retract-closure membership and unpack the ambient finite-free model.
    have hM' :
        CategoryTheory.ObjectProperty.retractClosure
          (_root_.SheafOfModules.IsFiniteFree : ObjectProperty (SheafOfModules 𝒪)) M := by
      simpa [finiteFreeRetractModuleProperty] using hM
    obtain ⟨P, hP, ⟨r⟩⟩ :=
      (CategoryTheory.ObjectProperty.prop_retractClosure_iff
        (_root_.SheafOfModules.IsFiniteFree : ObjectProperty (SheafOfModules 𝒪))
        M).mp hM'
    -- Replace the abstract finite-free model by the canonical free sheaf from its iso witness.
    obtain ⟨I, hI, ⟨e⟩⟩ := _root_.SheafOfModules.IsFiniteFree.exists_iso_free (ℱ := P)
    refine ⟨I, hI, ⟨r.trans (Retract.ofIso e)⟩⟩
  · rintro ⟨I, hI, ⟨r⟩⟩
    -- A retract of the canonical free sheaf lies in the retract-closure of finite free modules.
    let _ : Finite I := hI
    have hM' :
        CategoryTheory.ObjectProperty.retractClosure
          (_root_.SheafOfModules.IsFiniteFree : ObjectProperty (SheafOfModules 𝒪)) M :=
      CategoryTheory.ObjectProperty.prop_retractClosure inferInstance r
    simpa [finiteFreeRetractModuleProperty] using hM'

/-- A direct retract of a finite free module satisfies `finiteFreeRetractModuleProperty`. -/
theorem finiteFreeRetractModuleProperty_of_retract_free
    {𝒪 : Sheaf J RingCat.{max u v}} {M : SheafOfModules 𝒪} {L : Type (max u v)}
    [Finite L] (r : Retract M (_root_.SheafOfModules.free L : SheafOfModules.{max u v} 𝒪)) :
    finiteFreeRetractModuleProperty 𝒪 M :=
  CategoryTheory.ObjectProperty.prop_retractClosure inferInstance r

end

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable {R : Sheaf J RingCat.{max u v}}

local notation "Mod" => SheafOfModules R
namespace CochainComplex

/-- In a strictly perfect complex, each term is a retract of a finite free module sheaf. -/
theorem IsStrictlyPerfect.term_retract_free {E : CochainComplex Mod ℤ}
    (hE : IsStrictlyPerfect E) (i : ℤ) :
    ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract (E.X i) (SheafOfModules.free.{max u v} I : Mod)) := by
  simpa using
    (SheafOfModules.finiteFreeRetractModuleProperty_iff (E.X i)).1
      (IsStrictlyPerfect.term_retractClosure hE i)

end CochainComplex

end

end AlgebraicGeometry.RingedSpace
