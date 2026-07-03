

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_11_15 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω}
variable {X : ℕ → Ω → ℤ}

section SymmetricSimpleRandomWalk

variable (hX_law : ∀ n,
  HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)

local notation "Xℝ" => fun n ω ↦ (X n ω : ℝ)
local notation "X∞" => fun n ω ↦ (((X n ω : ℤ) : ℝ) : EReal)

/-
Example 11.15 is `source-facing`: its public content is the almost-sure oscillation and failure of
convergence or uniform integrability for a symmetric simple random walk on `ℤ`. The
`core/canonical` owner layer is the increment process `n ↦ X (n + 1) - X n`, the Chapter 2 random-walk partial-sum
theorem `ae_limsup_random_walk_partial_sum_eq_top_of_independent_fair_signs`, the Chapter 9 owner
theorem `symmetricSimpleRandomWalk_squareIntegrable_martingale`, and the Chapter 11 owner
convergence theorem `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`. The relevant
`bridge/view` is the centered walk `n ↦ X n - X 0`, obtained by translating the path by its
initial offset. This file keeps only those source-facing consequences and does not introduce a
parallel walk wrapper around that owner data.
-/
local instance : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure

include hX_law

-- Proof sketch: subtract the initial position `X 0` to obtain the zero-start walk with the same
-- increments, rewrite that centered walk as partial sums of its increment process
-- `n ↦ X (n + 1) - X n`, apply Exercise 2.3.1 to those independent fair-sign increments, and
-- finally translate back by the finite initial offset.
/-- Almost surely, a symmetric simple random walk has `limsup X_n = +∞`. -/
theorem ae_limsup_symmetricSimpleRandomWalk_eq_top
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ X∞ n ω) atTop = ⊤ := by
  sorry

-- Proof sketch: apply the preceding `limsup` statement to the reflected walk `-X`, which is again
-- a symmetric simple random walk, and translate `limsup (-X_n) = +∞` into
-- `liminf X_n = -∞`.
/-- Almost surely, a symmetric simple random walk has `liminf X_n = -∞`. -/
theorem ae_liminf_symmetricSimpleRandomWalk_eq_bot
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ∀ᵐ ω ∂P, liminf (fun n ↦ X∞ n ω) atTop = ⊥ := by
  sorry

-- Proof sketch: combine the two preceding almost-sure oscillation statements on the same
-- full-measure event.
/-- Example 11.15: a symmetric simple random walk on `ℤ` oscillates almost surely between `+∞`
and `-∞`; equivalently, its pathwise `limsup` is `∞` and its `liminf` is `-∞`. -/
theorem symmetricSimpleRandomWalk_ae_limsup_eq_top_and_liminf_eq_bot
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ∀ᵐ ω ∂P,
      limsup (fun n ↦ X∞ n ω) atTop = ⊤ ∧ liminf (fun n ↦ X∞ n ω) atTop = ⊥ := by
  sorry

-- Proof sketch: on any path with `limsup X_n = +∞` and `liminf X_n = -∞`, the sequence cannot
-- converge in `EReal`, even allowing the improper limits `±∞`.
/-- A symmetric simple random walk does not converge almost surely, even in the improper extended
real sense. -/
theorem symmetricSimpleRandomWalk_not_ae_improperly_convergent
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ¬ ∀ᵐ ω ∂P, ∃ ℓ : EReal,
        Tendsto (fun n ↦ X∞ n ω) atTop (𝓝 ℓ) := by
  sorry

-- Proof sketch: if the walk were uniformly integrable, then its centered version
-- `n ↦ X n - X 0`, which has the same increments and starts at `0`, would also be uniformly
-- integrable. Apply Theorem 11.7 to the martingale from
-- `symmetricSimpleRandomWalk_squareIntegrable_martingale` for that centered walk to obtain
-- almost-sure convergence to an integrable limit, then translate back; this contradicts
-- `symmetricSimpleRandomWalk_not_ae_improperly_convergent`.
/-- A symmetric simple random walk on `ℤ`, viewed as a real-valued martingale, is not uniformly
integrable. -/
theorem symmetricSimpleRandomWalk_not_uniformIntegrable
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ¬ UniformIntegrable Xℝ 1 P := by
  sorry

end SymmetricSimpleRandomWalk
