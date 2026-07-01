import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open MvPolynomial

/- Domain-style sampling:
* primary domain: finite-presentation criteria for flat finite modules over weighted-graded
  polynomial rings;
* sampled owner declarations:
  `Module.FinitePresentation`,
  `weightedHomogeneousSubmodule`,
  `DirectSum.Decomposition`,
  `GradedModule.linearEquiv`;
* best owner abstraction: the conclusion is the canonical owner
  `Module.FinitePresentation (MvPolynomial σ R) M`, and the graded-module structure is
  already expressed by mathlib's external owner pair
  `[DirectSum.Decomposition ℳ]` together with
  `[SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]`;
* primitive data: the weighted polynomial ring `MvPolynomial σ R` on a finite variable type `σ`,
  the positive weight function `w : σ → ℕ+`, and the `ℤ`-graded module structure `ℳ`;
* derived API: only the finite-presentation conclusion over `MvPolynomial σ R`;
* bridge/view: the source weights are positive naturals, viewed in the chapter's `ℤ`-graded
  module interface through the canonical coercion `ℕ+ → ℤ`.

Source/core/bridge triage:
* `source-facing`: the weighted-graded local finite-presentation theorem below;
* `core/canonical`: `Module.FinitePresentation` and the weighted grading owner
  `weightedHomogeneousSubmodule`;
* `bridge/view`: the passage from `w : σ → ℕ+` to the induced `ℤ`-grading. -/

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {σ : Type*} [Finite σ]
variable {M : Type v} [AddCommMonoid M] [Module R M] [Module (MvPolynomial σ R) M]
variable [IsScalarTower R (MvPolynomial σ R) M]

local notation "P" => MvPolynomial σ R

-- Proof sketch: choose homogeneous generators of the finite graded module `M` and present it by a
-- finite direct sum of weighted shifts of `MvPolynomial σ R`. Degreewise, the kernel has
-- short exact sequences whose middle and right terms are finite free over the local ring `R`, so
-- each graded piece of the kernel is finite free over `R`. After tensoring with the residue field,
-- the kernel over `MvPolynomial σ R ⊗[R] κ` is finitely generated because that polynomial
-- ring is Noetherian; then graded Nakayama lifts finitely many homogeneous generators back to the
-- kernel over `R`, giving a finite presentation of `M` over `MvPolynomial σ R`.
/-- Lemma 15.25.3: if `R` is a local ring, `MvPolynomial σ R` on a finite variable type `σ` is
given the weighted grading with variable-weights `w : σ → ℕ+` viewed as degrees in `ℤ`, and a
`ℤ`-graded module `M` over this polynomial ring is finite over `MvPolynomial σ R` and flat over
`R`, then `M` is finitely presented as an `MvPolynomial σ R`-module. -/
theorem finitePresentation_of_local_flat_finite_weighted_graded_mvPolynomial_module
    (w : σ → ℕ+) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R (fun i ↦ (w i : ℤ))) ℳ]
    [Module.Finite P M] [Module.Flat R M] :
    Module.FinitePresentation P M := sorry

end
