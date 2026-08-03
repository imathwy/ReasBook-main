import Mathlib.Topology.MetricSpace.HausdorffDistance
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_12
import BauschkeLean.Chap21.Corollary_21_23

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: Corollary 21.24 is the surjectivity criterion for a maximally monotone
--   operator whose values escape to infinity.
-- - `core/canonical`: Chapter 11 packages the growth hypothesis as `ERealFunction.Coercive`, and
--   Chapter 21 packages surjectivity as `range_eq_univ_iff_inverse_isLocallyBounded`.
-- - `bridge/view`: the growth hypothesis yields the reusable local boundedness conclusion for the
--   inverse operator.

-- Semantic recall: the source condition `lim_{‖x‖ → +∞} inf ‖A x‖ = +∞` is canonically packaged as
-- the coercivity of the `EReal`-valued coercion of `x ↦ Metric.infEDist (0 : H) (A x)`. The
-- textbook norm-at-infinity filter is recovered by the companion bridge theorem below, and
-- `Metric.infEDist` preserves the source's `+∞` empty-set convention.
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The Chapter 11 coercive owner for Corollary 21.24 is equivalent to the textbook growth
condition `Metric.infEDist (0 : H) (A x) → +∞` as `‖x‖ → +∞`. -/
theorem coercive_infEDist_zero_iff_tendsto_norm_atTop (A : SetValuedOperator H H) :
    ERealFunction.Coercive (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal)) ↔
      Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal)) := by
  rw [ERealFunction.coercive_iff_tendsto_norm_atTop]
  simpa using
    (EReal.tendsto_coe_ennreal :
      Filter.Tendsto
          (fun x : H ↦ ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds ((⊤ : ENNReal) : EReal)) ↔
        Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal)))

/-- Helper for Corollary 21.24: any value `v ∈ A x` gives an upper bound on the distance from
`0` to the value set `A x`. -/
lemma infEDist_zero_le_norm_of_mem_value
    (A : SetValuedOperator H H) {x v : H} (hv : v ∈ A x) :
    ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal) ≤ ‖v‖ := by
  -- Compare the infimal distance with the distance to the concrete point `v ∈ A x`.
  calc
    ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal) ≤ (edist (0 : H) v : EReal) := by
      exact (EReal.coe_ennreal_le_coe_ennreal_iff).2 (Metric.infEDist_le_edist_of_mem hv)
    _ = ‖v‖ := by
      rw [edist_dist, dist_eq_norm, EReal.coe_ennreal_ofReal, max_eq_left (norm_nonneg _)]
      simp

/-- Helper for Corollary 21.24: the inverse image of a unit ball is contained in a coercive
lower level set of `x ↦ Metric.infEDist (0 : H) (A x)`. -/
lemma inverse_image_ball_subset_lowerLevelSet_infEDist_zero
    (A : SetValuedOperator H H) (u : H) :
    (A⁻¹).image (Metric.ball u 1) ⊆
      ERealFunction.lowerLevelSet
        (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal))
        (‖u‖ + 1) := by
  intro x hx
  rcases (SetValuedOperator.mem_image (A⁻¹) (Metric.ball u 1) x).1 hx with ⟨v, hvball, hvx⟩
  have hvA : v ∈ A x := by
    simpa [SetValuedOperator.mem_inverse_iff] using hvx
  rw [ERealFunction.mem_lowerLevelSet_iff]
  -- The unit-ball witness controls `‖v‖`, hence it controls the infimal distance.
  calc
    (Metric.infEDist (0 : H) (A x) : EReal) ≤ ‖v‖ :=
      infEDist_zero_le_norm_of_mem_value A hvA
    _ ≤ ‖u‖ + 1 := by
      have hvball' : ‖v - u‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hvball
      have hvnorm : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
        have hdecomp : v = u + (v - u) := by
          abel_nf
        calc
          ‖v‖ = ‖u + (v - u)‖ := congrArg norm hdecomp
          _ ≤ ‖u‖ + ‖v - u‖ := norm_add_le _ _
      have hsum_lt : ‖u‖ + ‖v - u‖ < ‖u‖ + 1 := by
        linarith
      have hvnormE : (‖v‖ : EReal) ≤ ‖u‖ + ‖v - u‖ := by
        exact_mod_cast hvnorm
      have hsum_ltE : ((‖u‖ + ‖v - u‖ : ℝ) : EReal) < ‖u‖ + 1 := by
        exact_mod_cast hsum_lt
      exact le_of_lt (lt_of_le_of_lt hvnormE hsum_ltE)

/-- Helper for Corollary 21.24: coercivity of `x ↦ Metric.infEDist (0 : H) (A x)` yields local
boundedness of the inverse at a prescribed point. -/
lemma inverse_isLocallyBoundedAt_of_coercive_infEDist_zero
    (A : SetValuedOperator H H)
    (hcoe : ERealFunction.Coercive (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal)))
    (u : H) :
    (A⁻¹).IsLocallyBoundedAt u := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hlevel :
      Bornology.IsBounded
        (ERealFunction.lowerLevelSet
          (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal))
          (‖u‖ + 1)) :=
    (ERealFunction.coercive_iff_bounded_lowerLevelSet
      (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal))).1 hcoe (‖u‖ + 1)
  -- The source proof's bounded neighborhood is now the bounded coercive sublevel set.
  exact hlevel.subset (inverse_image_ball_subset_lowerLevelSet_infEDist_zero A u)

/-- Canonical helper for Corollary 21.24: the coercivity of
the `EReal`-valued coercion of `x ↦ Metric.infEDist (0 : H) (A x)` forces the inverse of a
maximally monotone operator to be locally bounded everywhere. -/
theorem inverse_isLocallyBounded_of_maximal_of_coercive_infEDist_zero
    (A : SetValuedOperator H H) (_hA : Maximal IsMonotone A)
    (hcoe : ERealFunction.Coercive (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal))) :
    (A⁻¹).IsLocallyBounded := by
  intro u
  -- The proof follows Corollary 21.23's route: show local boundedness of the inverse everywhere.
  exact inverse_isLocallyBoundedAt_of_coercive_infEDist_zero A hcoe u

/-- Source-facing bridge for Corollary 21.24: the textbook norm-at-infinity growth of
`Metric.infEDist (0 : H) (A x)` forces the inverse of a maximally monotone operator to be locally
bounded everywhere. -/
theorem inverse_isLocallyBounded_of_maximal_of_tendsto_infEDist_zero
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hinf :
      Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal))) :
    (A⁻¹).IsLocallyBounded := by
  exact inverse_isLocallyBounded_of_maximal_of_coercive_infEDist_zero A hA
    ((coercive_infEDist_zero_iff_tendsto_norm_atTop A).2 hinf)

/-- Canonical coercive formulation of Corollary 21.24: if
the `EReal`-valued coercion of `x ↦ Metric.infEDist (0 : H) (A x)` is coercive, then `A` is
surjective, i.e. `A.range = Set.univ`. -/
theorem range_eq_univ_of_maximal_of_coercive_infEDist_zero
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hcoe : ERealFunction.Coercive (fun x : H ↦ (Metric.infEDist (0 : H) (A x) : EReal))) :
    A.range = Set.univ := by
  exact (range_eq_univ_iff_inverse_isLocallyBounded A hA).2
    (inverse_isLocallyBounded_of_maximal_of_coercive_infEDist_zero A hA hcoe)

/-- Corollary 21.24: let `A : H → 2^H` be maximally monotone. If
`Metric.infEDist (0 : H) (A x) → +∞` as `‖x‖ → +∞`, then `A` is surjective, i.e.
`A.range = Set.univ`. -/
theorem range_eq_univ_of_maximal_of_tendsto_infEDist_zero
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hinf :
      Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal))) :
    A.range = Set.univ := by
  exact range_eq_univ_of_maximal_of_coercive_infEDist_zero A hA
    ((coercive_infEDist_zero_iff_tendsto_norm_atTop A).2 hinf)

end SetValuedOperator
