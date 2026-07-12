import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Lemma 10.19.1: an ideal `I` is contained in the Jacobson radical of `R` if and only if every
element of `1 + I` is a unit of `R`. -/
-- Proof sketch: rewrite `Ring.jacobson R` as `Ideal.jacobson (⊥ : Ideal R)`. The forward
-- direction evaluates the owner characterization `Ideal.mem_jacobson_bot` at `y = 1`;
-- conversely, use `Ideal.mem_jacobson_bot` and test `f` against the elements `f * y`.
@[stacks 0AME]
theorem ideal_le_ring_jacobson_iff_isUnit_one_add :
    I ≤ Ring.jacobson R ↔ ∀ f ∈ I, IsUnit (1 + f) := by
  rw [← jacobson_bot]
  constructor
  · intro h f hf
    simpa [add_comm] using (mem_jacobson_bot.mp (h hf)) 1
  · intro h f hf
    exact mem_jacobson_bot.2 fun y ↦ by
      simpa [add_comm] using h (f * y) (I.mul_mem_right y hf)

end
