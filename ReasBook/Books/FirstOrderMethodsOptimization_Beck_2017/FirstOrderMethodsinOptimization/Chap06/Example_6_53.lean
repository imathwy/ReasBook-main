import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open Metric

variable {E : Type u} [NormedAddCommGroup E]
variable (C : Set E) (hC_nonempty : C.Nonempty)

/- Example 6.53 is `source-facing` in the chapter's Moreau-envelope/distance-to-set domain.
Domain sampling shows that the owner abstractions already live upstream:
- `M[μ, f]` from Definition 6.7 is the chapter owner for Moreau envelopes;
- `extendedIndicator` from Chapter 2 is the canonical owner for the indicator `δ_C`;
- `Metric.infDist` together with `Metric.infDist_eq_iInf` is the metric owner for the distance to
  a set;
- the projection APIs from Theorem 6.24 and Proposition 3.12 are `bridge/view` consequences, not
  primitive data for the half-squared-distance identity.

The primitive input for the main identity is only the nonempty set `C` and the positive parameter
`μ`. The complete-convex projection-point formula is a stronger bridge/view recorded separately
below. -/

-- Proof sketch: unfold `M[μ, extendedIndicator C]` as the infimum of
-- `u ↦ δ_C(u) + (1 / (2 * μ)) ‖x - u‖²`. Since `δ_C(u)` is `0` on `C` and `⊤` off `C`, the
-- infimum reduces to the infimum of the quadratic term over `C`, which is exactly
-- `(1 / (2 * μ)) * (infDist x C)^2`.
/-- Helper for Example 6.53: collapsing the indicator in the Moreau-envelope formula reduces the
ambient infimum to the quadratic distance infimum over the subtype `C`. -/
lemma moreau_indicator_apply_eq_iInf_quad_dist (μ : PosReal) (x : E) :
    M[μ, extendedIndicator C] x =
      ⨅ u : C, ((((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Collapse the indicator to `0` on `C` and `⊤` off `C`, leaving only the quadratic term.
  rw [moreau_envelope_apply]
  by_cases hC : C.Nonempty
  · letI : Nonempty C := Set.Nonempty.to_subtype hC
    refine le_antisymm ?_ ?_
    · refine le_ciInf ?_
      intro u
      simpa [extendedIndicator, dist_eq_norm, u.2] using
        (ciInf_le'
          (f := fun v : E ↦
            extendedIndicator C v + ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal))
          (u : E))
    · refine le_ciInf ?_
      intro u
      by_cases hu : u ∈ C
      · simpa [extendedIndicator, dist_eq_norm, hu] using
          (ciInf_le'
            (f := fun v : C ↦
              ((((1 / (2 * μ) : ℝ) * dist x v ^ (2 : ℕ)) : ℝ) : EReal))
            (⟨u, hu⟩ : C))
      · have htop :
            extendedIndicator C u +
                ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) = ⊤ := by
          rw [show extendedIndicator C u = ⊤ by simp [extendedIndicator, hu], EReal.top_add_coe]
        rw [htop]
        exact le_top
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    subst hC_empty
    have hleft :
        (⨅ u : E,
            extendedIndicator (∅ : Set E) u +
              ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal)) = ⊤ := by
      have hconst :
          (fun u : E ↦
            extendedIndicator (∅ : Set E) u +
              ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal)) = fun _ ↦ (⊤ : EReal) := by
        funext u
        rw [show extendedIndicator (∅ : Set E) u = ⊤ by simp [extendedIndicator], EReal.top_add_coe]
      rw [hconst]
      simp
    have hright :
        (⨅ u : (∅ : Set E), ((((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ)) : ℝ) : EReal)) = ⊤ := by
      exact
        (iInf_of_empty
          (f := fun u : (∅ : Set E) ↦
            ((((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ)) : ℝ) : EReal)))
    rw [hleft, hright]

/-- Helper for Example 6.53: when `C` is nonempty, the quadratic infimum over `C` is the quadratic
of `infDist x C`, scaled by `1 / (2 * μ)`. -/
lemma iInf_quad_dist_eq_quadratic_infDist (hC : C.Nonempty) (μ : PosReal) (x : E) :
    (⨅ u : C, ((((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ)) : ℝ) : EReal)) =
      ((((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
  let A : Set ℝ := (dist x ·) '' C
  have hA_nonempty : A.Nonempty := by
    -- Pick one point of `C` to certify that the distance image is nonempty.
    rcases hC with ⟨u, hu⟩
    exact ⟨dist x u, ⟨u, hu, rfl⟩⟩
  have hA_bdd : BddBelow A := by
    -- Every distance is nonnegative, so `0` is a lower bound for the image set.
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact dist_nonneg
  have hmono : MonotoneOn (fun r : ℝ ↦ r ^ (2 : ℕ)) A := by
    -- Squaring is monotone on the nonnegative distance image.
    intro a ha b hb hab
    rcases ha with ⟨u, hu, rfl⟩
    rcases hb with ⟨v, hv, rfl⟩
    exact (sq_le_sq₀ dist_nonneg dist_nonneg).2 hab
  have hcont : ContinuousWithinAt (fun r : ℝ ↦ r ^ (2 : ℕ)) A (sInf A) := by
    -- The squaring map is continuous at the infimum of the distance image.
    exact (continuous_pow 2).continuousWithinAt
  have hsquare :
      (sInf A) ^ (2 : ℕ) = sInf ((fun r : ℝ ↦ r ^ (2 : ℕ)) '' A) := by
    -- Transport the distance infimum through squaring on this nonnegative set.
    simpa [A] using
      (MonotoneOn.map_csInf_of_continuousWithinAt hcont hmono hA_nonempty hA_bdd)
  have hinf : sInf A = infDist x C := by
    -- Identify the `sInf` of the distance image with the standard metric infimum distance.
    simpa [A, Metric.infDist_eq_iInf, sInf_image'] using
      (Metric.isGLB_infDist (x := x) (s := C) hC).csInf_eq
  have hsq_iInf :
      (⨅ u : C, dist x u ^ (2 : ℕ)) = (infDist x C) ^ (2 : ℕ) := by
    -- Re-express the squared-distance `iInf` through the squared `sInf` description above.
    simpa [hinf, A, Metric.infDist_eq_iInf, sInf_image', Set.image_image] using hsquare.symm
  have ha_nonneg : 0 ≤ ((1 / (2 * μ) : ℝ)) := by
    -- The Moreau scaling factor is nonnegative because `μ > 0`.
    have hμ : (0 : ℝ) < (μ : ℝ) := by
      exact μ.2
    have hden : 0 < ((2 : ℝ) * (μ : ℝ)) := by
      nlinarith
    have hpos : 0 < (1 / ((2 : ℝ) * (μ : ℝ))) := by
      exact one_div_pos.mpr hden
    exact le_of_lt hpos
  have h_real :
      (⨅ u : C, ((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ))) =
        ((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) := by
    -- Pull the nonnegative scalar out of the infimum and then substitute the squared-distance
    -- identity.
    calc
      (⨅ u : C, ((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ))) =
          (⨅ u : C, dist x u ^ (2 : ℕ) * ((1 / (2 * μ) : ℝ))) := by
            simp_rw [mul_comm]
      _ = (⨅ u : C, dist x u ^ (2 : ℕ)) * ((1 / (2 * μ) : ℝ)) := by
            symm
            exact Real.iInf_mul_of_nonneg ha_nonneg (fun u : C ↦ dist x u ^ (2 : ℕ))
      _ = (infDist x C) ^ (2 : ℕ) * ((1 / (2 * μ) : ℝ)) := by
            rw [hsq_iInf]
      _ = ((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) := by
            ring
  have hquad_bdd :
      BddBelow (Set.range fun u : C ↦ ((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ))) := by
    -- The quadratic family is bounded below by `0`.
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨u, rfl⟩
    exact mul_nonneg ha_nonneg (sq_nonneg _)
  letI : Nonempty C := Set.Nonempty.to_subtype hC
  have hquad_top_bdd :
      BddBelow
        (Set.range
          fun u : C ↦ (((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ) : ℝ) : WithTop ℝ)) := by
    -- The same lower bound works after coercing the real family into `WithTop ℝ`.
    rcases hquad_bdd with ⟨a, ha⟩
    refine ⟨(a : WithTop ℝ), ?_⟩
    intro y hy
    rcases hy with ⟨u, rfl⟩
    change (a : WithTop ℝ) ≤ (((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ) : ℝ) : WithTop ℝ)
    exact_mod_cast ha ⟨u, rfl⟩
  -- Rewrite the `EReal`-valued infimum through the corresponding `WithTop ℝ` and real-valued
  -- infima, then use the real identity proved above.
  change
    (⨅ u : C, ((((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ) : ℝ) : WithTop ℝ) :
      WithBot (WithTop ℝ))) =
      ((((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ) : ℝ) : WithTop ℝ) :
        WithBot (WithTop ℝ))
  rw [← WithBot.coe_iInf
    (f := fun u : C ↦ (((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ) : ℝ) : WithTop ℝ))
    hquad_top_bdd]
  have hcoetop :
      (⨅ u : C, (((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ) : ℝ) : WithTop ℝ)) =
        (((⨅ u : C, ((1 / (2 * μ) : ℝ) * dist x u ^ (2 : ℕ))) : ℝ) : WithTop ℝ) := by
    exact (WithTop.coe_iInf hquad_bdd).symm
  rw [hcoetop]
  exact
    congrArg
      (fun r : ℝ ↦ (((r : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)))
      h_real

/-- Helper for Example 6.53: with the nonempty hypothesis present, the Moreau envelope of the
indicator `δ_C` is the scaled half squared distance to `C`. -/
theorem moreau_envelope_extendedIndicator_eq_half_sq_infDist_of_nonempty
    (hC : C.Nonempty) (μ : PosReal) :
    M[μ, extendedIndicator C] =
      fun x ↦ ((((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
  funext x
  -- First reduce the Moreau envelope to the quadratic infimum over the set `C`.
  rw [moreau_indicator_apply_eq_iInf_quad_dist (C := C) μ x]
  -- Then rewrite that infimum as the scaled square of `infDist x C`.
  exact iInf_quad_dist_eq_quadratic_infDist (C := C) hC μ x

/-- Helper for Example 6.53: for the empty set, the generated wrapper formula disagrees with the
actual Moreau envelope, so the wrapper needs an explicit nonempty hypothesis. -/
lemma moreau_envelope_extendedIndicator_empty_ne_half_sq_infDist
    (μ : PosReal) :
    M[μ, extendedIndicator (∅ : Set E)] ≠
      fun x ↦ ((((1 / (2 * μ) : ℝ) * (infDist x (∅ : Set E)) ^ (2 : ℕ)) : ℝ) : EReal) := by
  intro hEq
  have hleft :
      M[μ, extendedIndicator (∅ : Set E)] (0 : E) = (⊤ : EReal) := by
    -- The indicator of the empty set is everywhere `⊤`, so the Moreau envelope stays `⊤`.
    rw [moreau_envelope_apply]
    have hconst :
        (fun u : E ↦
          extendedIndicator (∅ : Set E) u +
            ((((1 / (2 * μ) : ℝ) * ‖(0 : E) - u‖ ^ (2 : ℕ)) : ℝ) : EReal)) =
          fun _ ↦ (⊤ : EReal) := by
      funext u
      rw [show extendedIndicator (∅ : Set E) u = ⊤ by simp [extendedIndicator], EReal.top_add_coe]
    rw [hconst]
    simp
  have hright :
      (fun x ↦ ((((1 / (2 * μ) : ℝ) * (infDist x (∅ : Set E)) ^ (2 : ℕ)) : ℝ) : EReal))
        (0 : E) =
        (0 : EReal) := by
    -- The empty-set infimum distance is `0`, so the candidate right-hand side vanishes at `0`.
    simp [Metric.infDist_empty]
  have htop_eq_zero : (⊤ : EReal) = (0 : EReal) := by
    -- Evaluate the claimed function equality at `0` to reach the contradiction.
    calc
      (⊤ : EReal) = M[μ, extendedIndicator (∅ : Set E)] (0 : E) := by
        symm
        exact hleft
      _ =
          (fun x ↦ ((((1 / (2 * μ) : ℝ) * (infDist x (∅ : Set E)) ^ (2 : ℕ)) : ℝ) : EReal))
            (0 : E) := by
          simpa using congrFun hEq (0 : E)
      _ = (0 : EReal) := hright
  exact EReal.top_ne_coe 0 htop_eq_zero

/-- Example 6.53: for a nonempty set `C`, the Moreau envelope of the indicator `δ_C` is the half
squared distance to `C`, scaled by `μ⁻¹`. -/
theorem moreau_envelope_extendedIndicator_eq_half_sq_infDist
    (μ : PosReal) :
    M[μ, extendedIndicator C] =
      fun x ↦ ((((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Route correction: the source-faithful proof is already packaged in the theorem
  -- `moreau_envelope_extendedIndicator_eq_half_sq_infDist_of_nonempty` above, but this wrapper
  -- omits the needed hypothesis from its type, so the empty-set counterexample blocks closure.
  -- TODO: regenerate the wrapper theorem with an explicit `C.Nonempty` hypothesis and then close
  -- it by `simpa` from `moreau_envelope_extendedIndicator_eq_half_sq_infDist_of_nonempty`.
  sorry

section ProjectionFormula

variable [InnerProductSpace ℝ E]
variable (hC_complete : IsComplete C) (hC_convex : Convex ℝ C)

local notation "P" => metricProjection C hC_nonempty hC_complete hC_convex

-- Proof sketch: apply the general Moreau-envelope evaluation theorem
-- `moreau_envelope_eq_of_scaled_prox_eq_singleton` to `f = extendedIndicator C`. The proximal set
-- of `(μ : EReal) • extendedIndicator C` is the same as the projection set onto `C`, and for a
-- nonempty complete convex set this set is the singleton containing `metricProjection C ... x`.
-- Substituting that singleton minimizer gives the displayed identity.
/-- Helper for Example 6.53: the quadratic penalty at the metric projection is the quadratic of the
distance `infDist x C`. -/
lemma metricProjection_penalty_eq_quadratic_infDist
    (μ : PosReal) (x : E) :
    ((((1 / (2 * μ) : ℝ) * ‖x - P x‖ ^ (2 : ℕ)) : ℝ) : EReal) =
      ((((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Rewrite the distance to `C` through the metric projection point.
  rw [infDist_eq_dist_metricProjection C hC_nonempty hC_complete hC_convex x, dist_eq_norm]

/-- Under the stronger nonempty complete convex hypotheses, the Moreau envelope of `δ_C` can be
written using the point-valued metric projection `P_C`. -/
theorem moreau_envelope_extendedIndicator_eq_indicator_metricProjection_add_sq_dist
    (μ : PosReal) (x : E) :
    M[μ, extendedIndicator C] x =
      extendedIndicator C (P x) +
        ((((1 / (2 * μ) : ℝ) * ‖x - P x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  calc
    M[μ, extendedIndicator C] x =
        ((((1 / (2 * μ) : ℝ) * (infDist x C) ^ (2 : ℕ)) : ℝ) : EReal) := by
      -- Reuse the proved nonempty version of the source-facing half-squared-distance formula at
      -- the point `x`.
      simpa using
        congrFun (moreau_envelope_extendedIndicator_eq_half_sq_infDist_of_nonempty
          (C := C) hC_nonempty μ) x
    _ = ((((1 / (2 * μ) : ℝ) * ‖x - P x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      -- Replace `infDist x C` by the distance to the projection point.
      symm
      exact metricProjection_penalty_eq_quadratic_infDist
        (C := C) (hC_nonempty := hC_nonempty) (hC_complete := hC_complete)
        (hC_convex := hC_convex) μ x
    _ = extendedIndicator C (P x) +
        ((((1 / (2 * μ) : ℝ) * ‖x - P x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      -- The metric projection belongs to `C`, so the indicator contribution vanishes.
      have hproj_mem : extendedIndicator C (P x) = 0 := by
        simp [extendedIndicator, (P x).2]
      rw [hproj_mem, zero_add]

end ProjectionFormula

end
