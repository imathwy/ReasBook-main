import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Proposition_10_56
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Proposition_10_58

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f h hμ : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
variable {Lf : NNReal} {α β : PosReal}
variable [hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β]

/- Theorem 10.57 is `source-facing`: it is the explicit `O(1 / ε)` iteration-complexity bound for
the S-FISTA iterates.

Domain sampling in the local Chapter 10 API identifies the existing owners that should remain on
the public surface:
- `IsSFISTAProblem` from Proposition 10.56 for Assumption 10.56;
- `IsSmoothApproximation` from Definition 10.43 for the chosen smoothing `h_μ`;
- `IsSFISTAProblem.bounded_real_sublevel_radius` from Proposition 10.56 for the canonical
  sublevel-radius owner used at the level `H(x⁰) + ε / 2`;
- `s_fista_curvature_bound` from Proposition 10.58 for the source-facing smoothed curvature
  parameter `L̃ = L_f + α / μ`;
- `s_fista_x` from Proposition 10.58 as the canonical S-FISTA iterate owner, with the regularizer
  side conditions supplied here by the `IsSFISTAProblem` instances from Proposition 10.56.

The genuinely new source data in this item are the explicit smoothing parameter `μ` and the scalar
quantity `Γ = (R_{H(x⁰) + ε / 2} + ‖x⁰‖)^2`, so these are added as thin helper definitions rather
than wrapped into a new trajectory or problem package. -/

-- Proof sketch: the numerator `(α / β) ε` is positive and the denominator
-- `√(αβ) + √(αβ + L_f ε)` is positive, so the fraction is positive; the square root of a positive
-- real is again positive.
/-- The explicit smoothing parameter used in Theorem 10.57 has positive real value. -/
theorem s_fista_complexity_smoothing_parameter_pos
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) :
    0 <
      Real.sqrt
        (((α : ℝ) / (β : ℝ)) * (ε : ℝ) /
          (Real.sqrt ((α : ℝ) * (β : ℝ)) +
            Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ)))) := sorry

/-- The smoothing parameter
`μ = √((α / β) ε / (√(αβ) + √(αβ + L_f ε)))` used in Theorem 10.57. -/
def s_fista_complexity_smoothing_parameter
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) : PosReal :=
  ⟨Real.sqrt
      (((α : ℝ) / (β : ℝ)) * (ε : ℝ) /
        (Real.sqrt ((α : ℝ) * (β : ℝ)) +
          Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ)))),
    s_fista_complexity_smoothing_parameter_pos ε α β Lf⟩

-- Proof sketch: unfold `s_fista_complexity_smoothing_parameter`; coercing the resulting
-- `PosReal` to `ℝ` returns exactly the defining square-root formula.
/-- Coercing the smoothing parameter from Theorem 10.57 to `ℝ` recovers its defining formula. -/
@[simp] theorem s_fista_complexity_smoothing_parameter_coe
    (ε : PosReal) (α β : PosReal) (Lf : NNReal) :
    ((s_fista_complexity_smoothing_parameter ε α β Lf : PosReal) : ℝ) =
      Real.sqrt
        (((α : ℝ) / (β : ℝ)) * (ε : ℝ) /
          (Real.sqrt ((α : ℝ) * (β : ℝ)) +
            Real.sqrt ((α : ℝ) * (β : ℝ) + (Lf : ℝ) * (ε : ℝ)))) := sorry

/-- The quantity `Γ = (R_{H(x⁰) + ε / 2} + ‖x⁰‖)^2` appearing in the S-FISTA complexity bound. -/
def s_fista_complexity_gamma (Rlevel : PosReal) (x0 : E) : ℝ :=
  ((Rlevel : ℝ) + ‖x0‖) ^ (2 : ℕ)

section

variable
  (ε : PosReal)
  (x0 : E)

local notation "μ" => s_fista_complexity_smoothing_parameter ε α β Lf
local notation "Hsf" => H[f.toEReal, h.toEReal, g]
set_option quotPrecheck false in
local notation "xμ" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  s_fista_x f hμ g Lf α μ x0

-- Proof sketch: instantiate the S-FISTA rate estimate for the smoothing
-- `μ = s_fista_complexity_smoothing_parameter ε α β Lf`, use the chosen approximation
-- `hhμ : IsSmoothApproximation h hμ α β μ`, and apply the resulting explicit lower bound on
-- `k` for a supplied sublevel-radius witness `R_{H(x⁰) + ε / 2}`.
/-- Bridge/view theorem: if a radius `R_{H(x⁰) + ε / 2}` is supplied explicitly as a sublevel
bound, then the corresponding lower bound on `k` yields an `ε`-accurate S-FISTA iterate for the
original objective `H`. -/
theorem s_fista_objective_gap_le_epsilon_of_iteration_bound_of_sublevel_radius
    (hhμ :
      IsSmoothApproximation h hμ α β μ)
    (Rlevel : PosReal)
    (hlevel :
      ∀ ⦃x : E⦄,
        Hsf x ≤
          Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) →
            ‖x‖ ≤ (Rlevel : ℝ))
    (k : ℕ)
    (hiter :
      2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
          Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
            Real.sqrt (ε : ℝ) ≤
        (k : ℝ)) :
    Hsf (xμ k) -
      (HOpt : EReal) ≤
        ((ε : ℝ) : EReal) := sorry

-- Proof sketch: derive the required sublevel-radius witness from the canonical bridge
-- `IsSFISTAProblem.bounded_real_sublevel_radius` once at the fixed level `H(x⁰) + ε / 2`, then
-- apply the explicit-radius theorem above uniformly in `k`.
/-- Theorem 10.57: assuming Proposition 10.56, if `hμ` is the smoothing used by S-FISTA with
`μ = √((α / β) ε / (√(αβ) + √(αβ + L_f ε)))`, then there exists a radius
`R_{H(x⁰) + ε / 2}` supplied by Proposition 10.56 together with its defining initial-sublevel
bound property such that, for every iteration index `k`, if
`2 √(2 α β Γ) / ε + √(2 L_f Γ) / √ε ≤ k` with
`Γ = (R_{H(x⁰) + ε / 2} + ‖x⁰‖)^2`, then the original objective gap at the `k`th S-FISTA iterate
is at most `ε`. -/
theorem s_fista_objective_gap_le_epsilon_of_iteration_bound
    (hhμ :
      IsSmoothApproximation h hμ α β μ) :
    ∃ Rlevel : PosReal,
      (∀ ⦃x : E⦄,
          Hsf x ≤
            Hsf x0 + (((ε : ℝ) / 2 : ℝ) : EReal) →
              ‖x‖ ≤ (Rlevel : ℝ)) ∧
      ∀ k : ℕ,
        2 * Real.sqrt (2 * (α : ℝ) * (β : ℝ) * s_fista_complexity_gamma Rlevel x0) / (ε : ℝ) +
            Real.sqrt (2 * (Lf : ℝ) * s_fista_complexity_gamma Rlevel x0) /
              Real.sqrt (ε : ℝ) ≤
          (k : ℝ) →
          Hsf (xμ k) -
            (HOpt : EReal) ≤
              ((ε : ℝ) : EReal) := by
  sorry

end

end
