import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar
open Set

section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type v}
variable {C : Set E}
variable (f : I → E → EReal)
variable (hf : ∀ i : I, Function.IsClosedProperConvex (𝕜 := ℝ) (f i))
variable (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (hno_common :
  ¬ ∃ y : E, Set.RecedesInDirection ℝ C y ∧
    ∀ i : I, y ∈ Function.recessionCone ((f i)₀⁺))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.3.1 says that an arbitrary family of closed proper convex
  inequalities on a closed convex set `C` has a common nonpositive point whenever every finite
  subsystem of size at most `dim E + 1` is strictly feasible at every positive level and there is
  no common recession direction for the family inside `C`.
- `core/canonical`: the chapter owner abstraction is the source-facing alternative
  `xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate` from
  `Theorem_21_3`, together with the support-bounded multiplier refinement
  `exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le`.
- `bridge/view`: the only extra work in this corollary is to show that the multiplier branch of
  the Chapter 21 alternative is impossible under the small-subsystem strict-feasibility
  hypothesis; that contradiction is exposed as a companion theorem, while the main corollary stays
  in the textbook pointwise language.

Domain-style sampling used here:
- `xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate`;
- `exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le`.

Primitive data vs derived API:
- primitive inputs: the family `f`, the owner hypothesis `∀ i, (f i).IsClosedProperConvex`, the
  closed convex set `C`, the direct no-common-recession hypothesis, and strict finite-subsystem
  feasibility;
- derived companion owner output: impossibility of a finitely supported nonnegative multiplier
  certificate on `C`;
- derived public output: a point `x ∈ C` with `f i x ≤ 0` for every `i`, obtained directly from
  the source-facing Chapter 21 alternative.

Layer target:
- `source-facing` for `exists_point_of_small_subsystems_strictly_feasible`, with the owner
  certificate-elimination step exposed as a reusable companion theorem.
-/

include f hf hC_closed hC_convex hno_common

theorem no_nonnegative_multiplier_certificate_of_small_subsystems_strictly_feasible
    (h_small_feasible :
      ∀ (J : Finset I) (_ : J.card ≤ Module.finrank ℝ E + 1) (ε : ℝ) (_ : 0 < ε),
        ∃ x : E, x ∈ C ∧ ∀ i ∈ J, f i x < ε)
    :
    ¬ ∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.IsNonnegativeMultiplierCertificateOn C f epsilon := by
  intro hcert
  rcases
      exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le
        f hf hC_closed hC_convex hno_common hcert with
    ⟨weights, epsilon, hcard, hcertificate⟩
  rcases hcertificate with ⟨hweights_nonneg, hepsilon_pos, hcertificate_on_C⟩
  -- Choose a point that strictly satisfies the support subsystem at a sufficiently small positive
  -- level relative to the total multiplier mass. Evaluating the certificate there yields
  -- `epsilon < epsilon`, a contradiction.
  sorry

/-- Corollary 21.3.1: let `fᵢ`, `i ∈ I`, be closed proper convex functions on a finite-dimensional
real normed space, and let `C` be a closed convex set. If there is no common recession direction
for the family that is also a recession direction of `C`, and if for every `ε > 0` every finite
subsystem with at most `Module.finrank ℝ E + 1` inequalities `fᵢ(x) < ε` has a solution in `C`,
then there exists `x ∈ C` such that `fᵢ x ≤ 0` for every `i`. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement with the bound `n + 1`. -/
theorem exists_point_of_small_subsystems_strictly_feasible
    (h_small_feasible :
      ∀ (J : Finset I) (_ : J.card ≤ Module.finrank ℝ E + 1) (ε : ℝ) (_ : 0 < ε),
        ∃ x : E, x ∈ C ∧ ∀ i ∈ J, f i x < ε)
    :
    ∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0 := by
  have hxor :
      Xor'
        (∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0)
        (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
          weights.IsNonnegativeMultiplierCertificateOn C f epsilon) :=
    xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate
      f hf hC_closed hC_convex hno_common
  rcases hxor.or with hpoint | hcert
  · exact hpoint
  · exact False.elim <|
      (no_nonnegative_multiplier_certificate_of_small_subsystems_strictly_feasible
        f hf hC_closed hC_convex hno_common h_small_feasible) hcert

omit f hf hC_closed hC_convex hno_common

end
