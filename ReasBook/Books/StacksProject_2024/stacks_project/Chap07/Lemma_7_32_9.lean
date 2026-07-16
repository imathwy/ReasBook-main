import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace MorphismOfTopoiIn

/- Source/core/bridge triage for Lemma 7.32.9:
- source-facing item: the canonical section of the counit map `(p_* E)_p → E`
- core/canonical owner: the derived adjunction `p.typeAdjunction`
- derived API used here: terminality of `Type` together with preservation of terminal objects by the
  left adjoint `p.typeInverseImage`
-/

-- Proof sketch: the backward map is the canonical counit `p.typeAdjunction.counit.app E`. For the
-- forward map, send `e : E` through the morphism `PUnit ⟶ E` picking out `e`, apply the
-- endofunctor `p_* ⋙ p⁻¹`, and use that the counit is an isomorphism on the terminal object.
-- Naturality of the counit and the triangle identity then show that the composite back to `E` is
-- the identity.
variable (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w})

private abbrev pointPushforwardFiberEndofunctor : Type w ⥤ Type w :=
  p.typePushforward ⋙ p.typeInverseImage

private noncomputable def pointPushforwardFiberTerminalIso :
    (pointPushforwardFiberEndofunctor p).obj PUnit.{w + 1} ≅ PUnit.{w + 1} :=
  ((pointPushforwardFiberEndofunctor p).mapIso Types.terminalIso).symm ≪≫
    PreservesTerminal.iso (pointPushforwardFiberEndofunctor p) ≪≫
    Types.terminalIso

private noncomputable def pointPushforwardFiberTerminalPoint :
    (pointPushforwardFiberEndofunctor p).obj PUnit.{w + 1} :=
  (pointPushforwardFiberTerminalIso p).inv PUnit.unit

private abbrev pointPushforwardFiberCounit :
    pointPushforwardFiberEndofunctor p ⟶ 𝟭 (Type w) :=
  p.typeAdjunction.counit

/-- The canonical section `E → (p_* E)_p = p^{-1}(p_* E)` from Lemma 7.32.9. -/
def pointPushforwardFiberSection (E : Type w) :
    E → p.typeInverseImage.obj (p.typePushforward.obj E) :=
  fun e ↦
    (pointPushforwardFiberEndofunctor p).map (fun _ : PUnit.{w + 1} ↦ e)
      (pointPushforwardFiberTerminalPoint p)

/-- Lemma 7.32.9: for a point `p` of the topos `Sh(C)` and a set `E`, the canonical counit map
`(p_* E)_p = p^{-1} p_* E → E` admits the canonical section
`pointPushforwardFiberSection p E`. -/
theorem pointPushforwardFiber_counit_leftInverse (E : Type w) :
    Function.LeftInverse ((pointPushforwardFiberCounit p).app E) (pointPushforwardFiberSection p E) := by
  intro e
  simpa [pointPushforwardFiberSection] using
    congrFun
      ((pointPushforwardFiberCounit p).naturality (fun _ : PUnit.{w + 1} ↦ e))
      (pointPushforwardFiberTerminalPoint p)

/-- The counit map `p^{-1}(p_* E) → E` from Lemma 7.32.9 is split epic, with section
`pointPushforwardFiberSection p E`. -/
theorem pointPushforwardFiber_counit_isSplitEpi (E : Type w) :
    IsSplitEpi ((pointPushforwardFiberCounit p).app E) := by
  exact (CategoryTheory.isSplitEpi_iff_surjective _).2 <|
    Function.LeftInverse.surjective (pointPushforwardFiber_counit_leftInverse p E)

end MorphismOfTopoiIn

end CategoryTheory

end
