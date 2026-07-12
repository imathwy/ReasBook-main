import Mathlib
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Lemma_31_5_5
import StacksProject_2024.Chap31.Lemma_31_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced the Noetherian ring-level emptiness criterion for
-- associated primes, while local Chapter 31 precedent uses the sheaf-side owners
-- `Scheme.Modules.associatedPoints` and `Scheme.Modules.weakAss`; the locally Noetherian bridge
-- `associatedPoints_eq_weakAss_of_isLocallyNoetherian` lets this lemma reuse the canonical zero
-- criterion `isZero_iff_weakAss_eq_empty`.

/-- Lemma 31.2.6: for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a locally Noetherian
scheme `X`, `\mathcal F = 0` if and only if `Ass(\mathcal F) = \emptyset`. -/
@[stacks 05AG]
theorem isZero_iff_associatedPoints_eq_empty :
    IsZero ℱ ↔ associatedPoints ℱ = (∅ : Set X) := by
  rw [associatedPoints_eq_weakAss_of_isLocallyNoetherian ℱ]
  exact isZero_iff_weakAss_eq_empty ℱ

/-- Pointwise reformulation of `isZero_iff_associatedPoints_eq_empty`. -/
theorem isZero_iff_forall_not_mem_associatedPoints :
    IsZero ℱ ↔ ∀ x : X, x ∉ associatedPoints ℱ := by
  constructor
  · intro hzero x hx
    have hEmpty : associatedPoints ℱ = (∅ : Set X) :=
      (isZero_iff_associatedPoints_eq_empty ℱ).1 hzero
    have : x ∈ (∅ : Set X) := by simpa [hEmpty] using hx
    simpa using this
  · intro h
    apply (isZero_iff_associatedPoints_eq_empty ℱ).2
    ext x
    constructor
    · intro hx
      exact False.elim <| h x hx
    · intro hx
      cases hx

end AlgebraicGeometry.Scheme.Modules
