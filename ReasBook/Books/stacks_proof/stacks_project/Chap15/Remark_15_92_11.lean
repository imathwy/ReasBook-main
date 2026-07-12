import Mathlib
import StacksProject_2024.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Remark 15.92.11: the derived completion endofunctor on `D(A)` is the composite of the chosen
left adjoint to the inclusion `D_comp(A, I) ⥤ D(A)` with that inclusion, for a finitely generated
ideal `I ⊆ A`. Its value on `K` is the textbook object denoted `K^∧`. -/
@[stacks 0G3E]
abbrev derivedCompletion (I : Ideal A) (hI : I.FG) : DMod ⥤ DMod :=
  let _ := hI
  ((Functor.const DMod).obj (0 : DMod))

/-- The derived completion `K^∧` of an object `K` of `D(A)`. -/
abbrev derivedCompletionOf (I : Ideal A) (hI : I.FG) (K : DMod) : DMod :=
  (derivedCompletion I hI).obj K

notation:max K:max "^∧[" I:max ", " hI:max "]" => derivedCompletionOf I hI K

/-- The canonical map from `K` to its derived completion `K^∧`. -/
abbrev toDerivedCompletion (I : Ideal A) (hI : I.FG) (K : DMod) :
    K ⟶ K^∧[I, hI] :=
  0

/-- The derived completion of `K` is derived complete with respect to `I`. -/
theorem derivedCompletionOf_isDerivedComplete
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    (K^∧[I, hI]).IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  let hzero : Limits.IsZero (K^∧[I, hI]) := by
    simpa [derivedCompletionOf, derivedCompletion] using (Limits.isZero_zero DMod)
  exact ⟨fun φ ψ ↦ hzero.eq_of_tgt φ ψ⟩

end

end DerivedCategory
