import Mathlib.Data.EReal.Operations

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace EReal

/-- The canonical real scalar action on `EReal` is multiplication by the coerced real. -/
noncomputable instance : SMul ℝ EReal where
  smul a x := (a : EReal) * x

@[simp] theorem real_smul_def (a : ℝ) (x : EReal) : a • x = (a : EReal) * x :=
  rfl

end EReal

/-- Text 1.0.18: an operator between real scalar-action spaces is positively homogeneous when it
commutes with scalar multiplication by every positive real scalar. -/
def PositivelyHomogeneous {X : Type u} {Y : Type v} [SMul ℝ X] [SMul ℝ Y] (T : X → Y) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : X, T (a • x) = a • T x

namespace PositivelyHomogeneous

variable {X : Type u} {Y : Type v} [SMul ℝ X] [SMul ℝ Y] {T : X → Y}

/-- A positively homogeneous operator maps a positive scalar multiple to the corresponding
scalar multiple of the image. -/
theorem map_smul_of_pos (hT : PositivelyHomogeneous T) {a : ℝ} (ha : 0 < a) (x : X) :
    T (a • x) = a • T x :=
  hT ha x

end PositivelyHomogeneous
