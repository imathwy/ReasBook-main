import Mathlib
import StacksProject_2024.Chap15.Lemma_15_29_2
import StacksProject_2024.Chap15.Lemma_15_29_3

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open scoped TensorProduct

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]
variable {r : ℕ}

/-- Helper for Lemma 15.29.5: the tensor-description comparison for the extended alternating Čech
complex, duplicated at the ambient module universe of `M`. -/
noncomputable def extendedAlternatingCechComplex_iso_tensorObj_universe
    (f : Fin r → R) :
    extendedAlternatingCechComplex f M ≅
      (((tensorLeft (ModuleCat.of R M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCechComplex f R)) := by
  -- Route correction: the source proof still wants the owner-level tensor bridge from
  -- Lemma `15.29.2`; this theorem-local copy only repairs the module-universe mismatch.
  -- Reuse the canonical tensor-description bridge at the larger ambient module universe.
  simpa using
    (stacks_project.Chap15.Lemma_15_29_2.extendedAlternatingCechComplex_iso_tensorObj
      (R := R) (r := r) f M)

/-- Helper for Lemma 15.29.5: the base-change comparison for the extended alternating Čech
complex, duplicated at the ambient module universe of `M`. -/
noncomputable def extendedAlternatingCechComplex_iso_extendScalars_universe
    (f : Fin r → R) :
    extendedAlternatingCechComplex (fun i ↦ algebraMap R S (f i)) (S ⊗[R] M) ≅
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (extendedAlternatingCechComplex f M)) := by
  -- Route correction: keep the source base-change route intact and repair it once at the owner
  -- level, instead of forcing the target proof through `ULift` or ad hoc universe transports.
  -- Reuse the canonical base-change comparison at the larger ambient module universe.
  simpa using
    (stacks_project.Chap15.Lemma_15_29_3.extendedAlternatingCechComplex_iso_extendScalars
      (R := R) (S := S) (r := r) f M)

end
