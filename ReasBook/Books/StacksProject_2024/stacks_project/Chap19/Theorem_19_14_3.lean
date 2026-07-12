import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-
Domain-style sampling:
* primary domain: the Gabriel-Popescu module embedding for Grothendieck abelian categories.
* inspected owner declarations: `tensorObj`, `tensorObjPreadditiveCoyonedaObjAdjunction`,
  `GabrielPopescu.full`, and `GabrielPopescu.preservesFiniteLimits`.
* best owner abstraction: the canonical functor pair
  `tensorObj U ⊣ preadditiveCoyonedaObj U` attached to a separator `U`.
* source/core/bridge triage:
  - `source-facing`: `exists_gabriel_popescu_functors`;
  - `core/canonical`: the owner pair `tensorObj U ⊣ preadditiveCoyonedaObj U`;
  - `bridge/view`: the exactness theorem `tensorObj_exact` under a separator hypothesis.
* primitive data: an object `U` together with `hU : IsSeparator U`; the source-facing existence
  theorem specializes this to `separator A`.
* derived API: exactness of `tensorObj U`, the canonical adjunction, and the full/faithful
  properties of `preadditiveCoyonedaObj U`.
-/

/-- For a separator `U`, the canonical Gabriel-Popescu left adjoint `tensorObj U` is exact. -/
theorem tensorObj_exact (U : A) (hU : IsSeparator U) :
    exactFunctor _ _ (tensorObj U) := by
  letI : PreservesFiniteLimits (tensorObj U) := GabrielPopescu.preservesFiniteLimits U hU
  exact (exactFunctor_iff (tensorObj U)).2 ⟨inferInstance, inferInstance⟩

/-- The existence form of the Gabriel-Popescu theorem for a Grothendieck abelian category. -/
-- Proof sketch: take `R := (End (separator A))ᵐᵒᵖ`, `G := preadditiveCoyonedaObj (separator A)`,
-- and `F := ExactFunctor.of (tensorObj (separator A))`. The adjunction is the canonical
-- `tensorObjPreadditiveCoyonedaObjAdjunction`, fullness comes from `GabrielPopescu.full`,
-- faithfulness from `isSeparator_iff_faithful_preadditiveCoyonedaObj`, and exactness of `F`
-- combines `GabrielPopescu.preservesFiniteLimits` with the fact that a left adjoint preserves
-- finite colimits.
theorem exists_gabriel_popescu_functors :
    ∃ (R : Type v) (_ : Ring R) (G : A ⥤ ModuleCat.{v} R) (F : ModuleCat.{v} R ⥤ₑ A),
      ∃ _ : F.1 ⊣ G, G.Full ∧ G.Faithful := by
  let U := separator A
  have hU : IsSeparator U := by
    simpa [U] using isSeparator_separator A
  letI : (preadditiveCoyonedaObj U).Full := GabrielPopescu.full U hU
  letI : (preadditiveCoyonedaObj U).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU
  have hExact : exactFunctor _ _ (tensorObj U) := tensorObj_exact U hU
  letI : PreservesFiniteLimits (tensorObj U) := (exactFunctor_iff _).1 hExact |>.1
  letI : PreservesFiniteColimits (tensorObj U) := (exactFunctor_iff _).1 hExact |>.2
  refine ⟨(End U)ᵐᵒᵖ, inferInstance, preadditiveCoyonedaObj U, ExactFunctor.of (tensorObj U), ?_⟩
  refine ⟨?_, inferInstance, inferInstance⟩
  simpa using tensorObjPreadditiveCoyonedaObjAdjunction U

end CategoryTheory.IsGrothendieckAbelian
