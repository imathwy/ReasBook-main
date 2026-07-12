import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

section

variable {E : Type*} {Y : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" a ", " α "]" =>
  (LinearConstraintRelation.leFeasible (X := E) a α : Set E)
local notation "targetSet[" a0 ", " α0 "]" =>
  (closedHalfSpaceLE a0 α0 : Set E)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 22.3 is the finite-system Farkas criterion for when one weak linear
  inequality is a consequence of a consistent finite family of weak linear inequalities.
- `core/canonical`: the left-hand side is the owner inclusion
  `solutionSet[a, α] ⊆ targetSet[a0, α0]`, reusing the chapter feasible-set owner
  `LinearConstraintRelation.leFeasible` and half-space owner `closedHalfSpaceLE`, with coefficient
  data organized on the intrinsic pairing side `a : I → Y`; the right-hand side is the standard
  finite nonnegative-multiplier certificate written as a pointwise weighted-pairing identity over
  all `x : E`, plus the scalar bound inequality.
- `bridge/view`: the functional-dual and textbook vector forms are recovered by specializing
  `Y` to canonical pairing models (`E →ₗ[ℝ] ℝ`, `E →L[ℝ] ℝ`, or `E` with inner product). The pointwise
  implication surface is already owned upstream by
  `is_linear_inequality_consequence_leFeasible_iff`, so this file keeps that implication form only as a
  thin companion theorem rather than as a second main public entry.

Domain-style sampling used here:
- `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `LinearConstraintRelation.leFeasible` from `Chap01.Corollary_2_1_1`;
- `is_linear_inequality_consequence_leFeasible_iff` from `Chap04.Text_22_2_2`;
- `xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate` and the
  chapter owner layer `a : I → E →ₗ[ℝ] ℝ` from `Chap04.Theorem_22_1`.

Primitive data vs derived API:
- primitive inputs: the pairing-side coefficient family `a : I → Y`, the bounds `α : I → ℝ`, and
  the target inequality `(a0, α0)` with `a0 : Y`;
- core owner abstraction: `solutionSet[a, α]` and `targetSet[a0, α0]`;
- derived API: the pointwise implication form of consequence, obtained from the owner inclusion by
  `is_linear_inequality_consequence_leFeasible_iff`, and concrete functional/vector specializations
  obtained by canonical pairing instances.

Layer target: `core/canonical`, with the main theorem stated on the chapter owner objects and the
textbook implication form retained as a bridge/view companion.

Abstraction checks for this item:
- ambient structure: this file now lives on the pairing owner layer
  `[HasLinearPairing E Y ℝ]`; no norm/topology/finite-dimensional assumptions are required to state
  the owner inclusion or the multiplier certificate.
- scalar layer: the theorem remains over `ℝ` because the Chapter 22 multiplier certificate and the
  upstream alternative used to justify it are real-valued in this project (`aᵢ x ≤ αᵢ` with
  `αᵢ : ℝ` and multipliers `λᵢ : ℝ`). A genuine scalar generalization should start upstream at the
  Chapter 21/22 certificate owners rather than adding a local ad hoc scalar parameter here.
-/

-- Proof sketch: the functional inequality `a₀ x ≤ α₀` is a consequence exactly when the
-- augmented mixed system consisting of the strict inequality `(-a₀) x < -α₀` together with the
-- original weak inequalities is infeasible. Apply Theorem 22.2 with `k = 1` to this mixed
-- system. Its transposition certificate has a positive coefficient on the strict inequality;
-- divide the other coefficients by that positive coefficient to obtain the desired nonnegative
-- multipliers, and conversely clear denominators to recover the Theorem 22.2 certificate.
/-- Theorem 22.3 on the chapter functional-owner layer: if the weak owner feasible set
`solutionSet[a, α]` is nonempty, then the inequality `a₀ x ≤ α₀` is a consequence of this system
if and only if there is a nonnegative multiplier family with weighted pairing identity
`∀ x, ∑ i, λᵢ * ⟪x, aᵢ⟫ = ⟪x, a₀⟫` and
`∑ i, λᵢ αᵢ ≤ α₀`. The textbook finite-dimensional real inner-product-space statement is
recovered by `InnerProductSpace.toDual`. -/
theorem linear_inequality_consequence_iff_exists_nonnegative_multiplier
    (a0 : Y) (α0 : ℝ) (a : I → Y) (α : I → ℝ)
    (hconsistent : (solutionSet[a, α]).Nonempty) :
    solutionSet[a, α] ⊆ targetSet[a0, α0] ↔
      ∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E,
            ∑ i, weights i * (⟪x, a i⟫ₚ : ℝ) = (⟪x, a0⟫ₚ : ℝ)) ∧
          (∑ i, weights i * α i) ≤ α0 := sorry

/-- Companion pointwise form of Theorem 22.3: the owner inclusion
`solutionSet[a, α] ⊆ targetSet[a0, α0]` is exactly the textbook implication that every
simultaneous solution of the system satisfies the target inequality. -/
theorem is_linear_inequality_consequence_iff_exists_nonnegative_multiplier
    (a0 : Y) (α0 : ℝ) (a : I → Y) (α : I → ℝ)
    (hconsistent : ∃ x : E, ∀ i : I, (⟪x, a i⟫ₚ : ℝ) ≤ α i) :
    (∀ x : E, (∀ i : I, (⟪x, a i⟫ₚ : ℝ) ≤ α i) → (⟪x, a0⟫ₚ : ℝ) ≤ α0) ↔
      ∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E,
            ∑ i, weights i * (⟪x, a i⟫ₚ : ℝ) = (⟪x, a0⟫ₚ : ℝ)) ∧
          (∑ i, weights i * α i) ≤ α0 := by
  have hsolutionSet : (solutionSet[a, α]).Nonempty := by
    simpa [Set.Nonempty, LinearConstraintRelation.mem_leFeasible] using hconsistent
  simpa using
    (is_linear_inequality_consequence_leFeasible_iff a0 α0 a α).symm.trans
      (linear_inequality_consequence_iff_exists_nonnegative_multiplier
        a0 α0 a α hsolutionSet)

end
