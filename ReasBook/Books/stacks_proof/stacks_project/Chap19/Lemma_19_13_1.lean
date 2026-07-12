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
  `Adjunction.corepresentableBy`,
  `isRightAdjoint_of_preservesLimits_of_isCoseparating`,
  `Functor.representable_preservesLimits`;
- best owner abstraction: `F.IsRightAdjoint` for `F : Aᵒᵖ ⥤ Type v`;
- primitive data: the presheaf `F`;
- derived API: the adjunction-built corepresentability data
  `Adjunction.corepresentableBy`, the canonical `coyoneda`/`yoneda` comparison isomorphisms, and
  preservation of limits.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a presheaf is representable iff it commutes with
  colimits, equivalently preserves limits;
- `core/canonical`: `F.IsRightAdjoint`;
- `bridge/view`: the two thin theorems below passing between `F.IsRightAdjoint`,
  `F.IsRepresentable`, and `PreservesLimits F`.

The previous file reconstructed the representability data by hand from the adjunction. The refined
file keeps the source-facing theorem, but factors it through the canonical adjunction owner API
`Adjunction.corepresentableBy` together with the standard `Coyoneda.punitIso` and
`Coyoneda.objOpOp` bridges already provided by mathlib.
-/

section

variable {A : Type u} [Category.{v} A]

/-- A `Type`-valued presheaf on `A` that is a right adjoint is representable. -/
theorem isRepresentable_of_isRightAdjoint (F : Aᵒᵖ ⥤ Type v) [F.IsRightAdjoint] :
    F.IsRepresentable := by
  let adj : F.leftAdjoint ⊣ F := Adjunction.ofIsRightAdjoint F
  refine ⟨(F.leftAdjoint.obj PUnit).unop, ⟨Functor.representableByEquiv.symm ?_⟩⟩
  exact
    (Coyoneda.objOpOp (F.leftAdjoint.obj PUnit).unop).symm ≪≫
      (adj.corepresentableBy PUnit).toIso ≪≫
      Functor.isoWhiskerLeft F Coyoneda.punitIso ≪≫
      Functor.rightUnitor F

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
@[stacks 07D7]
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
