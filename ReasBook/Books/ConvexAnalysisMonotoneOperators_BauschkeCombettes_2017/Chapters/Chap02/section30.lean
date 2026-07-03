import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_2_30 (from Chap02) -/
universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Lemma 2.30: an inner product space equipped with its weak topology is a Hausdorff space.

This is the standard `T2Space (WeakSpace 𝕜 E)` instance specialized to inner product spaces. -/
theorem innerProductSpace_weakSpace_t2Space : T2Space (WeakSpace 𝕜 E) :=
  inferInstance
