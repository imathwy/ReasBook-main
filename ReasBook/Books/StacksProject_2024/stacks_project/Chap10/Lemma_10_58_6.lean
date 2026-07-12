import Mathlib

universe u v w

section

local instance : AddAction ℕ ℤ where
  vadd n d := n + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → Submodule R S)
variable (ℳ : ℤ → Submodule S M)
variable [GradedRing 𝒜]
variable [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

local instance : Module (𝒜 0) M := Module.restrictScalars (𝒜 0) S M

/- Domain triage:
* `source-facing`: Lemma `10.58.6` asserts that each graded piece `Mₙ` of a finite graded
  `S`-module is finite over the degree-zero ring `S₀ = 𝒜 0`.
* `core/canonical` owners: the ambient graded module is carried by
  `DirectSum.Decomposition ℳ` and `SetLike.GradedSMul 𝒜 ℳ`, ring finiteness over `S₀` is carried
  by `Algebra.FiniteType S₀ S`, and module finiteness is carried by `Module.Finite`.
* `bridge/view`: this theorem passes from the owner-level finiteness of the graded ring/module to
  the individual component `ℳ n`.

Primitive data are the graded ring, the graded module, and the ambient finiteness hypotheses. The
finiteness of each component is derived API; it should not be stored as extra graded-module data.

Relevant owner declarations sampled for this refinement:
* `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`
* `sufficiently_divisible_veronese_generated_in_degree_one`
* `span_eq_top_of_quotient_span_eq_top_of_homogeneous`
-/

variable [Module.Finite S M] [Algebra.FiniteType (𝒜 0) S]

/-- Lemma 10.58.6: if a finite graded module `M = ⨁_{n ∈ ℤ} Mₙ` over `S` has grading compatible
with a graded ring `S` of finite type over its degree-zero part, then each homogeneous piece `Mₙ`
is a finite `S₀`-module. -/
-- Proof sketch: use the chapter's graded-module owner API from Lemma `10.56.1` to choose a
-- finite homogeneous generating set of `M`, and the mathlib/project finite-type owner API from
-- `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero` and Lemma `10.56.2` to
-- choose homogeneous positive-degree generators of `S` over `S₀`. Then every element of `Mₙ` is
-- an `S₀`-linear combination of finitely many monomials in those generators whose total degree is
-- `n`.
theorem finite_degree_component_of_finiteType (n : ℤ) :
    Module.Finite (𝒜 0) (ℳ n) := sorry

end
