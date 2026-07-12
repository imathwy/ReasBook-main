import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Ideal

open Submodule.IsPrincipal

section

variable {R : Type u} [CommSemiring R]

/-- Lemma 10.28.1 (Stacks, Tag `05K8`): if `J` is principal and `I ≤ J`, then
`I = J * (I.colon J)`. -/
-- This is the source-facing bridge statement; the proof is a direct reduction to the
-- `Submodule.IsPrincipal` owner API and `Ideal.eq_span_singleton_mul`.
@[stacks 05K8]
theorem eq_mul_colon_of_le {I J : Ideal R} (hJ : J.IsPrincipal) (hIJ : I ≤ J) :
    I = J * (I.colon J) := by
  letI := hJ
  rw [← span_singleton_generator J, eq_span_singleton_mul]
  refine ⟨?_, fun z hz ↦ ?_⟩
  · rintro y hy
    rcases (mem_iff_eq_smul_generator J).1 (hIJ hy) with ⟨z, rfl⟩
    exact ⟨z, mem_colon_span_singleton.2 (by simpa [smul_eq_mul, mul_comm] using hy),
      by simp [smul_eq_mul, mul_comm]⟩
  · simpa [mul_comm] using (mem_colon_span_singleton.1 hz)

end

end Ideal
