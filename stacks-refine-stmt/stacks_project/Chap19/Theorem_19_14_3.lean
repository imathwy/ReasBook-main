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
* layer: `bridge/view`; the source theorem is an existence statement, while the canonical owner API
  already lives on `tensorObj U` and `preadditiveCoyonedaObj U`.
* primitive data: the separator object `separator A`.
* derived API: exactness of `tensorObj (separator A)`, the adjunction, and the full/faithful
  properties of `preadditiveCoyonedaObj (separator A)`.
-/

/-- Theorem 19.14.3 for the canonical separator: the functor
`preadditiveCoyonedaObj (separator A)` is fully faithful, and its left adjoint
`tensorObj (separator A)` is exact. -/
theorem separator_gabriel_popescu :
    exactFunctor _ _ (tensorObj (separator A)) ∧
      (preadditiveCoyonedaObj (separator A)).Full ∧
      (preadditiveCoyonedaObj (separator A)).Faithful := by
  let U := separator A
  have hU : IsSeparator U := isSeparator_separator A
  letI : PreservesFiniteLimits (tensorObj U) := GabrielPopescu.preservesFiniteLimits U hU
  letI : (preadditiveCoyonedaObj U).Full := GabrielPopescu.full U hU
  letI : (preadditiveCoyonedaObj U).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU
  refine ⟨?_, inferInstance, inferInstance⟩
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
  have h :
      exactFunctor _ _ (tensorObj (separator A)) ∧
        (preadditiveCoyonedaObj (separator A)).Full ∧
        (preadditiveCoyonedaObj (separator A)).Faithful :=
    separator_gabriel_popescu
  rcases h with ⟨hExact, hFull, hFaithful⟩
  letI : PreservesFiniteLimits (tensorObj (separator A)) := (exactFunctor_iff _).1 hExact |>.1
  letI : PreservesFiniteColimits (tensorObj (separator A)) := (exactFunctor_iff _).1 hExact |>.2
  refine ⟨(End (separator A))ᵐᵒᵖ, inferInstance, preadditiveCoyonedaObj (separator A),
    ExactFunctor.of (tensorObj (separator A)), ?_⟩
  refine ⟨?_, hFull, hFaithful⟩
  simpa using tensorObjPreadditiveCoyonedaObjAdjunction (separator A)

end CategoryTheory.IsGrothendieckAbelian
