import Mathlib.CategoryTheory.Triangulated.Functor
import StacksProject_2024.Chap22.Lemma_22_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace DifferentialGradedCategory

namespace DgFunctor

section

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DifferentialGradedCategory R A] [DifferentialGradedCategory R B]
variable [HasShift (K R A) ℤ] [HasShift (K R B) ℤ]
variable [HasZeroObject (K R A)] [HasZeroObject (K R B)]
variable [Preadditive (K R A)] [Preadditive (K R B)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]
variable [∀ n : ℤ, (shiftFunctor (K R B) n).Additive]
variable [Pretriangulated (K R A)] [Pretriangulated (K R B)]

/-
Source/core/bridge triage for Lemma 22.27.17:
- `source-facing`: a DG functor `F : 𝒜 ⥤ 𝒝` induces an exact functor `K(𝒜) ⥤ K(𝒝)`;
- `core/canonical`: `Functor.IsTriangulated` on the induced homotopy-category functor;
- `bridge/view`: the source hypothesis `F(x[1]) = F(x)[1]` is recorded locally by a
  `CommShift ℤ` witness on `F.mapK`.
-/

variable (F : DgFunctor R A B) [F.mapK.CommShift ℤ]

/-- Companion instance: once the source shift-compatibility `F(x[1]) = F(x)[1]` has been bridged
to a `CommShift ℤ` witness on `F.mapK`, the induced functor on homotopy categories is
triangulated. -/
instance instIsTriangulatedMapK : F.mapK.IsTriangulated := by
  sorry

/-- Lemma 22.27.17: let `R` be a ring and let `F : 𝒜 ⥤ 𝒝` be a functor between differential
graded categories over `R` satisfying axioms `(A)`, `(B)`, and `(C)` such that `F(x[1]) = F(x)[1]`.
In the current Chapter 22 API, the induced exact functor `K(𝒜) ⥤ K(𝒝)` is represented by the
project-local owner `F.mapK` with the standard class-based surface
`[F.mapK.CommShift ℤ] [F.mapK.IsTriangulated]`. -/
@[stacks 0FQF]
theorem mapK_exact : F.mapK.IsTriangulated := inferInstance

end

end DgFunctor

end DifferentialGradedCategory
