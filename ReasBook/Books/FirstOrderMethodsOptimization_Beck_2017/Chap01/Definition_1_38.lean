import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {m : ℕ} (E : Fin m → Type u) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

/- Definition 1.38 is recall-only: once Definition 1.35 identifies the Cartesian product of the
Euclidean spaces `E i` with `PiLp (2 : ENNReal) E`, the remaining Euclidean-space structure is
owned by mathlib through the canonical finite-dimensionality instance below and the canonical `L²`
norm formula `PiLp.norm_eq_of_L2`. -/
#check (inferInstance : FiniteDimensional ℝ (PiLp (2 : ENNReal) E))

/- The norm on the finite Cartesian product is the canonical `L²` norm formula. -/
recall PiLp.norm_eq_of_L2

end
