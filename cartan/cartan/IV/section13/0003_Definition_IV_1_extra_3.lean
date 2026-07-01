import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling:
-- * source-facing owner here: the convergence locus/domain of a formal double series
-- * mathlib owner pattern for convergence data:
--   `FormalMultilinearSeries.le_radius_of_summable_norm` and
--   `FormalMultilinearSeries.summable_norm_mul_pow`, where the primitive input is a
--   norm-based
--   summability condition at nonnegative radii
-- * local chapter owners reused downstream: `formalSeriesConvergenceLocus` and
--   `formalSeriesConvergenceDomain`
--
-- The primitive datum is the weighted summability condition itself; the public
-- source-facing owner
-- is the nonnegative convergence locus, and the convergence domain is its interior.

universe u

variable {𝕜 : Type u} [SeminormedAddCommGroup 𝕜]

/-- The set `Γ` of points `(r₁, r₂)` in the nonnegative quadrant for which the associated series of
positive terms `∑ ‖a p q‖ r₁^p r₂^q` is summable. -/
def formalSeriesConvergenceLocus (a : ℕ → ℕ → 𝕜) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2)}

/-- Membership in the convergence locus unfolds to nonnegativity of the radii and summability of
the associated positive-term double series. -/
theorem mem_formalSeriesConvergenceLocus_iff (a : ℕ → ℕ → 𝕜) (r : ℝ × ℝ) :
    r ∈ formalSeriesConvergenceLocus a ↔
      0 ≤ r.1 ∧ 0 ≤ r.2 ∧
        Summable (fun n : ℕ × ℕ ↦ ‖a n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2) :=
  Iff.rfl

/-- Definition IV.1-extra-3: the domain of convergence of the formal double series
`∑ a p q X^p Y^q` is the interior, in `ℝ × ℝ`, of the set `Γ` of nonnegative radii for which the
associated series of positive terms is summable. -/
def formalSeriesConvergenceDomain (a : ℕ → ℕ → 𝕜) : Set (ℝ × ℝ) :=
  interior (formalSeriesConvergenceLocus a)

/-- Membership in the domain of convergence unfolds to interior membership in the convergence
locus. -/
theorem mem_formalSeriesConvergenceDomain_iff (a : ℕ → ℕ → 𝕜) (r : ℝ × ℝ) :
    r ∈ formalSeriesConvergenceDomain a ↔ r ∈ interior (formalSeriesConvergenceLocus a) :=
  Iff.rfl
