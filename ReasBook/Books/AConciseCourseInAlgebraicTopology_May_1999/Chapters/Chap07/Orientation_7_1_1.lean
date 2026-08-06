import Mathlib.Tactic.Recall
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2

open CategoryTheory
open HomotopicalAlgebra

universe v u

-- Semantic recall via `lean_leansearch`: the abstract duality is exposed by
-- `HomotopicalAlgebra.fibration_op_iff`, and the topological covering-space model is encoded by
-- `IsCoveringMap.liftHomotopy`.

section

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] {X Y : C}

/-
Orientation 7.1.1 (1): fibrations are introduced as the homotopical dual of cofibrations.

This is a canonical recall item: mathlib exposes the duality through
`HomotopicalAlgebra.fibration_op_iff`.
-/
recall HomotopicalAlgebra.fibration_op_iff {C : Type u} [Category.{v, u} C] {X Y : C}
    (f : X ⟶ Y) [CategoryWithCofibrations C] : Fibration f.op ↔ Cofibration f

end

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : ContinuousMap E B}

/-- A covering map has the covering homotopy property, using mathlib's lifted homotopy
construction. -/
theorem hasCoveringHomotopyProperty (cov : IsCoveringMap p) :
    HasCoveringHomotopyProperty p where
  homotopyLift {A} [TopologicalSpace A] [CompactlyGeneratedWeakHausdorffSpace A]
      {f₀ f₁ : C(A, B)} (H : f₀.Homotopy f₁) {g₀ : C(A, E)}
      (hg₀ : p.comp g₀ = f₀) := by
    let h₀ : ∀ a, H.toContinuousMap (0, a) = p (g₀ a) := fun a ↦ by
      simpa using (H.apply_zero a).trans (ContinuousMap.congr_fun hg₀ a).symm
    let lifted := cov.liftHomotopy H.toContinuousMap g₀ h₀
    refine ⟨lifted.curry 1, ?_, ?_⟩
    · refine
        { toContinuousMap := lifted
          map_zero_left := ?_
          map_one_left := ?_ }
      · intro a
        simpa [lifted] using cov.liftHomotopy_zero H.toContinuousMap g₀ h₀ a
      · intro a
        rfl
    · ext x
      simpa [lifted] using congr_fun (cov.liftHomotopy_lifts H.toContinuousMap g₀ h₀) x

/-- Surjective covering maps motivate fibrations via the homotopy lifting property
formalized in `IsFibration`. -/
theorem isFibration (cov : IsCoveringMap p) (hsurj : Function.Surjective p) : IsFibration p where
  toHasCoveringHomotopyProperty := cov.hasCoveringHomotopyProperty
  surjective := hsurj

end IsCoveringMap
