import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_19_4_1 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: `latticeGraph_adj_iff` says that adjacent vertices differ by `±1` in exactly one
-- coordinate and agree in all others; that coordinatewise description is equivalent to the
-- update-form textbook description used below.
/-- Adjacency in the canonical lattice graph is exactly the one-coordinate `±1` update condition
used in the textbook nearest-neighbor description. -/
theorem latticeGraph_adj_iff_update {d : ℕ} (x y : LatticePoint d) :
    (latticeGraph d).Adj x y ↔
      ∃ i : Fin d, y = Function.update x i (x i + 1) ∨ y = Function.update x i (x i - 1) := sorry

section Exercise1941

variable {d : ℕ}
variable (P : LatticePoint d → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint d)
variable [NeZero d]
variable [IsMarkovProcessRealization
  (fun n ↦ dirac_convolution_kernel (symmetricSimpleRandomWalkStepPMF d).toMeasure ^ n) P X]

-- Proof sketch: use the canonical Chapter 19 finite-boundary conductance formula
-- `conductance C x0 * escapeToSetProbability P X x0 {x1}` for the singleton boundary `{x1}`,
-- compute the local conductance at `x0` as `2d`, and identify the corresponding hitting
-- probability with the symmetry value `1 / 2` for a neighboring edge.
/-- Exercise 19.4.1 (1): in the unit nearest-neighbor network on `ℤ^d`, the canonical
finite-boundary conductance from `x0` to the singleton boundary `{x1}` is `d` whenever `x0` and
`x1` are neighbors. -/
theorem latticeNearestNeighbor_effectiveConductance_eq_dimension
    {x0 x1 : LatticePoint d} (hneighbor : (latticeGraph d).Adj x0 x1) :
    conductance (simpleGraphWeights (latticeGraph d)) x0 *
        escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) =
      (d : ℝ≥0∞) := sorry

-- Proof sketch: when `d ≤ 2`, the simple symmetric walk on `ℤ^d` is recurrent. Starting from
-- `x0`, the first positive hit of the two-point boundary `{x0, x1}` is therefore almost sure, and
-- symmetry across the edge `{x0, x1}` makes the two possible first hits equiprobable.
/-- Exercise 19.4.1 (2): if `d ≤ 2`, then for symmetric simple random walk on `ℤ^d` started at a
neighbor `x0` of `x1`, the probability of hitting `x1` before the first positive-time return to
`x0` is `1 / 2`. -/
theorem simpleRandomWalk_escapeBeforeNeighbor_eq_half_of_dimension_le_two
    (hd : d ≤ 2) {x0 x1 : LatticePoint d} (hneighbor : (latticeGraph d).Adj x0 x1) :
    escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) = (1 / 2 : ℝ≥0∞) := sorry

-- Proof sketch: for `d ≥ 3`, condition on the event that the walk ever re-enters the two-point
-- boundary `{x0, x1}` after time `0`. By symmetry of the edge `{x0, x1}`, the two mutually
-- exclusive first-hit alternatives `τ_{x1} < τ_{x0}` and `τ_{x0} < τ_{x1}` have equal mass inside
-- that conditioning event, yielding the displayed conditional-probability identity.
/-- Exercise 19.4.1 (3): if `d ≥ 3`, then conditioning on the event that the walk started from
`x0` ever hits one of the two neighbors `x0` or `x1` again at positive time, the event
`τ_{x1} < τ_{x0}` has conditional probability `1 / 2`. This is encoded by the identity
`P[τ_{x1} < τ_{x0}] = (1 / 2) P[τ_{ {x0,x1} } < ∞]`. -/
theorem simpleRandomWalk_escapeBeforeNeighbor_eq_half_mul_hitPairProbability_of_three_le_dimension
    (hd : 3 ≤ d) {x0 x1 : LatticePoint d} (hneighbor : (latticeGraph d).Adj x0 x1) :
    escapeToSetProbability P X x0 ({x1} : Set (LatticePoint d)) =
      (1 / 2 : ℝ≥0∞) *
        (P x0 : Measure Ω) {ω |
          hittingAfter X ({x0, x1} : Set (LatticePoint d)) 1 ω < ⊤} := sorry

end Exercise1941

end ProbabilityTheory

/-! ### Example_19_4 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Example 19.4:
- `source-facing`: `firstEntranceValueFunction`, the boundary-value extension defined from the
  first entrance law.
- `core/canonical`: `MeasureTheory.hittingAfter` for the entrance time, `IsHarmonicOutside` for
  harmonicity, and `SolvesDirichletProblem` for the combined boundary-value package.
- `bridge/view`: the Dirichlet-problem theorem below uses the canonical ambient extension of the
  subtype datum `g : A → ℝ` by `0` off `A`; this does not change the source semantics because the
  owner predicate only records boundary agreement on `A`. -/

/-- The boundary reward obtained by stopping `X` at the canonical first entrance time
`hittingAfter X A 1` and evaluating the boundary datum `g`; it is set to `0` on paths that never
enter `A`. -/
private def firstEntranceReward (X : ℕ → Ω → E) (A : Set E) (g : A → ℝ) : Ω → ℝ :=
  fun ω ↦
    if hτ : hittingAfter X A 1 ω < ⊤ then
      g ⟨stoppedValue X (hittingAfter X A 1) ω, by
        simpa [stoppedValue] using
          (hittingAfter_mem_set_of_ne_top hτ.ne)⟩
    else
      0

/-- The function obtained from boundary data `g` on `A` by taking the expected boundary value at
the first entrance into `A` when the initial state lies outside `A`. -/
def firstEntranceValueFunction (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (A : Set E) (g : A → ℝ) : E → ℝ :=
  fun x ↦
    if hx : x ∈ A then
      g ⟨x, hx⟩
    else
      ∫ ω, firstEntranceReward X A g ω ∂(P x : Measure Ω)

-- Proof sketch: unfold `firstEntranceValueFunction`; on `A` the definition uses the first branch
-- of the `if`, so the boundary-value extension agrees with `g`.
/-- On the boundary set `A`, the first-entrance value function agrees with the prescribed boundary
data. -/
theorem firstEntranceValueFunction_eq_of_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : A → ℝ) {x : E}
    (hx : x ∈ A) :
    firstEntranceValueFunction P X A g x = g ⟨x, hx⟩ := sorry

-- Proof sketch: unfold `firstEntranceValueFunction`; outside `A` the definition uses the
-- expectation of the stopped boundary reward.
/-- Outside `A`, the first-entrance value function is the expected boundary reward at the first
entrance into `A`. -/
theorem firstEntranceValueFunction_eq_of_not_mem
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (g : A → ℝ) {x : E}
    (hx : x ∉ A) :
    firstEntranceValueFunction P X A g x =
      ∫ ω, firstEntranceReward X A g ω ∂(P x : Measure Ω) := sorry

section

variable {κ : Kernel E E} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ κ ^ n) P X]

-- Proof sketch: apply the Markov property at time `1` and then at the first entrance time into
-- `A` to identify the outside values of `firstEntranceValueFunction` with their one-step kernel
-- averages. The assumption that the first entrance time is almost surely finite from every
-- starting state outside `A`, expressed in the canonical `∀ᵐ` stopping-time form, ensures the
-- stopped boundary reward represents the boundary data seen at the entrance point, and boundedness
-- of `g` on `A` provides the needed integrability.
/-- Example 19.4: if the first entrance time into `A` is almost surely finite from every starting
state outside `A`, and `f` is defined by the boundary data `g` on `A` and by the expected boundary
value at the first entrance into `A` on `E \ A`, then `f` is harmonic on `E \ A`. -/
theorem firstEntranceValueFunction_isHarmonicOutside
    (A : Set E) (g : A → ℝ)
    (hg_bdd : ∃ C : ℝ, ∀ a : A, |g a| ≤ C)
    (hτ : ∀ x : E, x ∉ A → ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω ≠ ⊤) :
    IsHarmonicOutside κ A (firstEntranceValueFunction P X A g) := sorry

-- Proof sketch: combine `firstEntranceValueFunction_isHarmonicOutside` with
-- `firstEntranceValueFunction_eq_of_mem`. The ambient boundary datum is the canonical bridge
-- `x ↦ if hx : x ∈ A then g ⟨x, hx⟩ else 0`, whose values on `A` are definitionally the original
-- subtype datum `g`.
/-- The first-entrance value function solves the Chapter 19 Dirichlet problem for the ambient
boundary extension of `g` obtained by setting the value to `0` off `A`. -/
theorem firstEntranceValueFunction_solvesDirichletProblem
    (A : Set E) (g : A → ℝ)
    (hg_bdd : ∃ C : ℝ, ∀ a : A, |g a| ≤ C)
    (hτ : ∀ x : E, x ∉ A → ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω ≠ ⊤) :
    SolvesDirichletProblem κ A
      (fun x ↦ if hx : x ∈ A then g ⟨x, hx⟩ else 0)
      (firstEntranceValueFunction P X A g) := sorry

end

end ProbabilityTheory
