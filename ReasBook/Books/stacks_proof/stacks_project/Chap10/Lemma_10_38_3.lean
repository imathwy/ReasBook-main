import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_38_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

section Algebra

variable [Algebra R S]

attribute [local instance] Polynomial.algebra

local instance (I : Ideal R) : IsScalarTower R (reesAlgebra I) S[X] :=
  IsScalarTower.subalgebra' R R[X] S[X] (reesAlgebra I)

private theorem isIntegralOverIdeal_zero_algebraMap (I : Ideal R) :
    (algebraMap R S).IsIntegralOverIdeal I 0 := by
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (0 : S)]
  simpa using (isIntegral_zero : _root_.IsIntegral (reesAlgebra I) (0 : S[X]))

private theorem isIntegralOverIdeal_add_algebraMap {I : Ideal R} {x y : S}
    (hx : (algebraMap R S).IsIntegralOverIdeal I x)
    (hy : (algebraMap R S).IsIntegralOverIdeal I y) :
    (algebraMap R S).IsIntegralOverIdeal I (x + y) := by
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I x] at hx
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I y] at hy
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (x + y)]
  simpa [C_add, add_mul] using hx.add hy

private theorem isIntegralOverIdeal_smul_algebraMap (I : Ideal R) {r : R} {s : S}
    (hs : (algebraMap R S).IsIntegralOverIdeal I s) :
    (algebraMap R S).IsIntegralOverIdeal I (r • s) := by
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I s] at hs
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (r • s)]
  simpa [Algebra.smul_def, C_mul, mul_assoc] using hs.smul r

/-- Lemma 10.38.3 (1): the elements of `S` that are integral over the ideal `I` form the
canonical `R`-submodule of `S`. -/
@[stacks 00H4]
def integralOverIdealSubmodule (I : Ideal R) : Submodule R S where
  carrier := { s | (algebraMap R S).IsIntegralOverIdeal I s }
  zero_mem' := isIntegralOverIdeal_zero_algebraMap I
  add_mem' := by
    intro x y hx hy
    exact isIntegralOverIdeal_add_algebraMap hx hy
  smul_mem' := by
    intro r s hs
    exact isIntegralOverIdeal_smul_algebraMap I hs

/-- Membership in the canonical submodule from Lemma 10.38.3 (1) is exactly integrality over
the ideal `I`. -/
theorem mem_integralOverIdealSubmodule_iff (I : Ideal R) (s : S) :
    s ∈ integralOverIdealSubmodule I ↔ (algebraMap R S).IsIntegralOverIdeal I s :=
  Iff.rfl

/-- Elements integral over an ideal are closed under scalar multiplication by the base ring. -/
theorem IsIntegralOverIdeal.smul {I : Ideal R} {r : R} {s : S}
    (hs : (algebraMap R S).IsIntegralOverIdeal I s) :
    (algebraMap R S).IsIntegralOverIdeal I (r • s) := by
  change s ∈ integralOverIdealSubmodule I at hs
  change r • s ∈ integralOverIdealSubmodule I
  exact (integralOverIdealSubmodule I).smul_mem r hs

end Algebra

/-- Zero is integral over any ideal. -/
theorem isIntegralOverIdeal_zero (φ : R →+* S) (I : Ideal R) :
    φ.IsIntegralOverIdeal I 0 := by
  letI := φ.toAlgebra
  change (0 : S) ∈ integralOverIdealSubmodule I
  exact (integralOverIdealSubmodule I).zero_mem

/-- Elements integral over an ideal are closed under addition. -/
theorem IsIntegralOverIdeal.add {φ : R →+* S} {I : Ideal R} {x y : S}
    (hx : φ.IsIntegralOverIdeal I x) (hy : φ.IsIntegralOverIdeal I y) :
    φ.IsIntegralOverIdeal I (x + y) := by
  letI := φ.toAlgebra
  change x ∈ integralOverIdealSubmodule I at hx
  change y ∈ integralOverIdealSubmodule I at hy
  change x + y ∈ integralOverIdealSubmodule I
  exact (integralOverIdealSubmodule I).add_mem hx hy

/-- Lemma 10.38.3 (2): if `s` is integral over `R` and `s'` is integral over the ideal `I`, then
`s * s'` is integral over `I`. -/
@[stacks 00H4]
theorem IsIntegralElem.mul_isIntegralOverIdeal {φ : R →+* S} {I : Ideal R} {s s' : S}
    (hs : φ.IsIntegralElem s) (hs' : φ.IsIntegralOverIdeal I s') :
    φ.IsIntegralOverIdeal I (s * s') := by
  letI := φ.toAlgebra
  letI : Algebra R[X] S[X] := Polynomial.algebra R S
  letI : IsScalarTower R (reesAlgebra I) S[X] :=
    IsScalarTower.subalgebra' R R[X] S[X] (reesAlgebra I)
  change (algebraMap R S).IsIntegralOverIdeal I (s * s')
  change (algebraMap R S).IsIntegralOverIdeal I s' at hs'
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I s'] at hs'
  rw [isIntegralOverIdeal_iff_isIntegral_C_mul_X I (s * s')]
  have hsC : _root_.IsIntegral (reesAlgebra I) (C s : S[X]) := by
    exact (show _root_.IsIntegral R (C s : S[X]) from by
      simpa using hs.map (CAlgHom : S →ₐ[R] S[X]).toRingHom).tower_top
  simpa [C_mul, mul_assoc] using hsC.mul hs'

end RingHom

end
