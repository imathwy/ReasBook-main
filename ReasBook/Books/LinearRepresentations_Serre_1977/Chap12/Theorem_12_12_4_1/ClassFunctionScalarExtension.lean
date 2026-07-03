import Mathlib

noncomputable section

universe u v w

namespace Representation

section ScalarExtensionValueMap

variable (G : Type u)
variable (K : Type v) [Field K] [Algebra ℚ K]
variable (L : Type w) [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]

/-- The coefficientwise scalar-extension map on `G`-indexed functions. This is the canonical
bridge/view from a `K`-valued class function to its realization over `L`. -/
abbrev classFunctionScalarExtension : (G → K) →ₗ[ℚ] G → L :=
  ((Algebra.linearMap K L).restrictScalars ℚ).compLeft G

end ScalarExtensionValueMap

end Representation
