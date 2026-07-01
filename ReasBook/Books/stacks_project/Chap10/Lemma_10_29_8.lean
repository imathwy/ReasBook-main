import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Free R A] [Module.Finite R A]

/- Lemma 10.29.8 uses the canonical theorem `isNilpotent_tensor_residueField_iff`, which
characterizes fiberwise nilpotence by the non-leading coefficients of the characteristic
polynomial. -/
recall isNilpotent_tensor_residueField_iff

/-- Lemma 10.29.8: equivalently, if `P(T) = T^n + r_{n-1} T^{n-1} + ··· + r₀` is the
characteristic polynomial of `Algebra.lmul R A f`, then the fiber of `f` over `p` is nilpotent if
and only if `p ∈ V(r₀, …, r_{n-1})`. -/
theorem fiber_nilpotent_iff_mem_zeroLocus_charpoly_coeffs
    (f : A) (p : PrimeSpectrum R) :
    IsNilpotent ((algebraMap A (A ⊗[R] p.asIdeal.ResidueField)) f) ↔
      p ∈ zeroLocus
        (Set.range fun i : Fin (Module.finrank R A) ↦
          (Algebra.lmul R A f).charpoly.coeff i) := by
  simpa [mem_zeroLocus, Set.range_subset_iff] using
    (isNilpotent_tensor_residueField_iff f p.asIdeal).trans Nat.forall_lt_iff_fin

end
