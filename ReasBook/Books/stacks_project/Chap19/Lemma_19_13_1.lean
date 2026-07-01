import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open Opposite

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 19.13.1:
- primary domain: representability of `Type`-valued presheaves via adjointness in category theory;
- sampled owner declarations:
  `Functor.IsRepresentable`,
  `Functor.IsRightAdjoint`,
  `isRightAdjoint_of_preservesLimits_of_isCoseparating`,
  `Functor.representable_preservesLimits`;
- best owner abstraction: `F.IsRightAdjoint` for `F : Aᵒᵖ ⥤ Type v`;
- primitive data: the presheaf `F`;
- derived API: representability and preservation of limits.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a presheaf is representable iff it commutes with
  colimits, equivalently preserves limits;
- `core/canonical`: `F.IsRightAdjoint`;
- `bridge/view`: the two thin theorems below passing between `F.IsRightAdjoint`,
  `F.IsRepresentable`, and `PreservesLimits F`.

The previous file stored the source statement directly as a standalone theorem with no connection
to the owner abstraction. The refined file keeps the source-facing theorem, but factors the proof
through the canonical adjointness owner already used upstream in Chapter 4 and mathlib.
-/

section

variable {A : Type u} [Category.{v} A]

/-- A `Type`-valued presheaf on `A` that is a right adjoint is representable. -/
theorem isRepresentable_of_isRightAdjoint (F : Aᵒᵖ ⥤ Type v) [F.IsRightAdjoint] :
    F.IsRepresentable := by
  let adj : F.leftAdjoint ⊣ F := Adjunction.ofIsRightAdjoint F
  refine ⟨(F.leftAdjoint.obj PUnit).unop, ⟨?_⟩⟩
  refine
    { homEquiv := fun {X} ↦
        { toFun := fun f ↦ Equiv.punitArrowEquiv _ ((adj.homEquiv PUnit (op X)) f.op)
          invFun := fun x ↦
            ((adj.homEquiv PUnit (op X)).symm ((Equiv.punitArrowEquiv _).symm x)).unop
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_comp := ?_ }
  · intro f
    simp
  · intro x
    simp
  · intro X X' f g
    exact congrFun (adj.homEquiv_naturality_right g.op f.op) PUnit.unit

end

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- A `Type`-valued presheaf on the opposite of a Grothendieck abelian category that preserves
limits is a right adjoint. -/
theorem isRightAdjoint_of_preservesLimits (F : Aᵒᵖ ⥤ Type v) [PreservesLimits F] :
    F.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (isCoseparator_coseparator (Aᵒᵖ)) F

/-- Lemma 19.13.1: a set-valued functor on the opposite of a Grothendieck abelian category is
representable if and only if it commutes with colimits in `A`, equivalently if it preserves
limits as a functor `Aᵒᵖ ⥤ Type v`. -/
theorem isRepresentable_iff_preservesLimits (F : Aᵒᵖ ⥤ Type v) :
    F.IsRepresentable ↔ PreservesLimits F := by
  constructor
  · intro
    infer_instance
  · intro
    let _ : F.IsRightAdjoint := isRightAdjoint_of_preservesLimits F
    exact isRepresentable_of_isRightAdjoint F

end

end CategoryTheory
