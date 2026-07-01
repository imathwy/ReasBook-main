import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped Matrix
open Module

namespace LinearMap

variable (R : Type u) {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 9.20.4:
- primary domain: trace and determinant transitivity for linear endomorphisms over a free scalar
  tower.
- sampled owner declarations:
  `LinearMap.trace_eq_matrix_trace`,
  `LinearMap.restrictScalars_toMatrix`,
  `Algebra.trace_eq_matrix_trace`,
  `Algebra.trace_trace`.
- best owner abstraction:
  - `source-facing`: the trace/determinant formulas for an `S`-linear endomorphism viewed over the
    base extension `S/R`, interpreted with the zero-by-default trace/determinant conventions;
  - `core/canonical`: `LinearMap.trace`, `Algebra.trace`, and `LinearMap.det_restrictScalars`;
  - `bridge/view`: restriction of scalars `f.restrictScalars R`, together with the scalar-tower
    bases `Free.chooseBasis R S` and `Free.chooseBasis S A`.

Primitive data is only the endomorphism `f : A →ₗ[S] A`; the matrix expressions are derived API
used to connect the source-facing trace statement to the canonical owners, while the infinite-basis
branches are governed by the zero-by-default trace owners `LinearMap.trace` and `Algebra.trace`.
Clause `(1)` remains the minimal bridge theorem because mathlib has the algebra-side analogue
`Algebra.trace_trace` but no endomorphism-level `LinearMap.trace_restrictScalars`, while clause
`(2)` should be a direct recall of the existing owner theorem rather than a parallel local wrapper.

Source/core/bridge triage:
- `(1)` is a `source-facing` bridge statement relating the module-theoretic trace owner
  `LinearMap.trace` to the scalar-extension owner `Algebra.trace`.
- `(2)` is `core/canonical`, so it should stay a direct recall of
  `LinearMap.det_restrictScalars`.
-/

section TraceRestrictScalars

variable [AddCommMonoid A] [Module R A] [Module S A] [IsScalarTower R S A]
variable [Module.Free R S] [Module.Free S A]

/- Lemma 9.20.4 (1): for a free `S`-module `A` over a free extension `S/R`, the zero-by-default
trace of an `S`-linear endomorphism viewed over `R` is the algebra trace from `S` to `R` of its
`S`-linear trace. This is the source-facing bridge theorem; with `R` as an explicit ambient
input, it has the ordinary call shape `LinearMap.trace_restrictScalars R f`. -/
theorem trace_restrictScalars (f : A →ₗ[S] A) :
    trace R A (f.restrictScalars R) = Algebra.trace R S (trace S A f) := by
  classical
  by_cases hR : Subsingleton R
  · exact Subsingleton.elim _ _
  letI := not_subsingleton_iff_nontrivial.mp hR
  by_cases hA : Subsingleton A
  · letI := hA
    have hf : f = 0 := by ext a; exact Subsingleton.elim _ _
    subst hf
    simp
  letI := not_subsingleton_iff_nontrivial.mp hA
  let bS := Free.chooseBasis R S
  let bA := Free.chooseBasis S A
  have := Module.nontrivial S A
  cases fintypeOrInfinite (Free.ChooseBasisIndex R S)
  · cases fintypeOrInfinite (Free.ChooseBasisIndex S A)
    · let M := toMatrix bA bA f
      rw [trace_eq_matrix_trace R (bS.smulTower' bA), restrictScalars_toMatrix,
        trace_eq_matrix_trace S bA]
      calc
        Matrix.trace ((M.map (Algebra.leftMulMatrix bS)).comp _ _ _ _ _)
            = ∑ y, Matrix.trace (Algebra.leftMulMatrix bS (M y y)) := by
                simp [Matrix.trace, Matrix.diag, Matrix.comp_apply, Fintype.sum_prod_type]
        _ = ∑ y, Algebra.trace R S (M y y) := by
                simp [Algebra.trace_eq_matrix_trace bS]
        _ = Algebra.trace R S (∑ y, M y y) := by
                rw [map_sum]
        _ = Algebra.trace R S (Matrix.trace M) := by
                simp [Matrix.trace]
    ·
      have hA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s S A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis bA (Module.Finite.of_basis b)
      have hRA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s R A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis (bS.smulTower bA) (Module.Finite.of_basis b)
      simp [LinearMap.trace, hA_noBasis, hRA_noBasis]
  ·
      have hS_noBasis : ¬∃ s : Finset S, Nonempty (Basis s R S) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis bS (Module.Finite.of_basis b)
      have hRA_noBasis : ¬∃ s : Finset A, Nonempty (Basis s R A) := by
        rintro ⟨s, ⟨b⟩⟩
        exact Module.not_finite_of_infinite_basis (bS.smulTower bA) (Module.Finite.of_basis b)
      rw [Algebra.trace_eq_zero_of_not_exists_basis R hS_noBasis,
        LinearMap.zero_apply]
      simp [LinearMap.trace, hRA_noBasis]

end TraceRestrictScalars

section DetRestrictScalars

variable [AddCommGroup A] [Module R A] [Module S A] [IsScalarTower R S A]
variable [Module.Free R S] [Module.Free S A]

/- Lemma 9.20.4 (2): the determinant formula is the canonical theorem
`LinearMap.det_restrictScalars`. -/
recall det_restrictScalars

end DetRestrictScalars

end LinearMap
