import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {𝒜 : ℕ → AddSubgroup R} [GradedRing 𝒜]
variable {ℬ : ℕ → AddSubgroup S} [GradedRing ℬ]

/-- Lemma 10.56.3: if the structure map `R → S` preserves the `ℕ`-gradings, then the integral
closure of `R` in `S` is a graded `R`-subalgebra of `S`. The canonical owner-level Lean form is
that the underlying subsemiring of `integralClosure R S` is homogeneous for the grading on `S`. -/
-- Proof sketch: equip the target with the algebra structure coming from the graded ring
-- homomorphism, then show each homogeneous projection of an integral element is integral by the
-- Laurent-polynomial argument from the source and integrality transitivity.
lemma integralClosure_isHomogeneous [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) :
    DirectSum.SetLike.IsHomogeneous ℬ (integralClosure R S).toSubsemiring := sorry

/-- Companion bridge: the owner-level homogeneous-subsemiring statement implies the homogeneous
`R`-submodule statement for the same integral closure. -/
theorem integralClosure_toSubmodule_isHomogeneous [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ 𝒜 i → algebraMap R S r ∈ ℬ i) :
    (integralClosure R S).toSubmodule.IsHomogeneous ℬ := by
  simpa [Submodule.IsHomogeneous] using integralClosure_isHomogeneous hgraded

end
