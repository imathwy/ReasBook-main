import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap20.Definition_20_51
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap21.Definition_21_10

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 21.11: the source-faithful auxiliary function is the normalized
supremum of the graph-point affine defects. -/
private noncomputable def normalized_graph_sup (A : SetValuedOperator H H) : H → EReal :=
  fun x ↦
    ⨆ p : gra A, (((⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) : ℝ) : EReal))

/-- Helper for Proposition 21.11: each normalized graph branch is affine and hence belongs to
`Γ(H)`. -/
private lemma normalized_graph_branch_mem_gamma
    (A : SetValuedOperator H H) (p : gra A) :
    (fun x : H ↦ (((⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) : ℝ) : EReal))) ∈ Γ(H) := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The branch is affine, so Jensen's inequality is an equality after a scalar normalization.
    intro x y a ha0 ha1
    apply le_of_eq
    have hden : 0 < 1 + ‖p.1.1‖ := by positivity
    have hreal :
        ⟪a • x + (1 - a) • y - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) =
          a * (⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖)) +
            (1 - a) * (⟪y - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖)) := by
      have hnum :
          ⟪a • x + (1 - a) • y - p.1.1, p.1.2⟫_ℝ =
            a * ⟪x - p.1.1, p.1.2⟫_ℝ + (1 - a) * ⟪y - p.1.1, p.1.2⟫_ℝ := by
        have hleft :
            ⟪a • x + (1 - a) • y - p.1.1, p.1.2⟫_ℝ =
              a * ⟪x, p.1.2⟫_ℝ + (1 - a) * ⟪y, p.1.2⟫_ℝ + ⟪-p.1.1, p.1.2⟫_ℝ := by
          rw [sub_eq_add_neg, inner_add_left, inner_add_left, real_inner_smul_left,
            real_inner_smul_left]
        have hright :
            a * ⟪x - p.1.1, p.1.2⟫_ℝ + (1 - a) * ⟪y - p.1.1, p.1.2⟫_ℝ =
              a * ⟪x, p.1.2⟫_ℝ + (1 - a) * ⟪y, p.1.2⟫_ℝ + ⟪-p.1.1, p.1.2⟫_ℝ := by
          have hx' : ⟪x - p.1.1, p.1.2⟫_ℝ = ⟪x, p.1.2⟫_ℝ + ⟪-p.1.1, p.1.2⟫_ℝ := by
            rw [sub_eq_add_neg, inner_add_left]
          have hy' : ⟪y - p.1.1, p.1.2⟫_ℝ = ⟪y, p.1.2⟫_ℝ + ⟪-p.1.1, p.1.2⟫_ℝ := by
            rw [sub_eq_add_neg, inner_add_left]
          rw [hx', hy']
          ring
        calc
          ⟪a • x + (1 - a) • y - p.1.1, p.1.2⟫_ℝ
              = a * ⟪x, p.1.2⟫_ℝ + (1 - a) * ⟪y, p.1.2⟫_ℝ + ⟪-p.1.1, p.1.2⟫_ℝ := hleft
          _ = a * ⟪x - p.1.1, p.1.2⟫_ℝ + (1 - a) * ⟪y - p.1.1, p.1.2⟫_ℝ := hright.symm
      rw [hnum]
      ring_nf
    rw [show (1 - a : EReal) = ((1 - a : ℝ) : EReal) by norm_num, ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  · -- Continuity of the affine real branch upgrades to lower semicontinuity after coercion.
    have hcont :
        Continuous fun x : H ↦ ⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) := by
      exact ((continuous_id.sub continuous_const).inner continuous_const).div_const _
    simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

/-- Helper for Proposition 21.11: the normalized graph supremum belongs to `Γ(H)`. -/
private lemma normalized_graph_sup_mem_gamma
    (A : SetValuedOperator H H) :
    normalized_graph_sup A ∈ Γ(H) := by
  -- Proposition 9.3 packages the pointwise supremum of the affine graph branches.
  refine ERealFunction.iSup_mem_gamma
    (fun p : gra A ↦
      fun x : H ↦ (((⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) : ℝ) : EReal)))
    (fun p ↦ normalized_graph_branch_mem_gamma A p)

/-- Helper for Proposition 21.11: a nonempty graph keeps the normalized supremum strictly above
`-∞` at every point. -/
private lemma normalized_graph_sup_ne_bot_of_graph_nonempty
    (A : SetValuedOperator H H) (hgraph : (gra A).Nonempty) (x : H) :
    ⊥ < normalized_graph_sup A x := by
  rcases hgraph with ⟨p, hp⟩
  let q : gra A := ⟨p, hp⟩
  have hq :
      (((⟪x - q.1.1, q.1.2⟫_ℝ / (1 + ‖q.1.1‖) : ℝ) : EReal)) ≤ normalized_graph_sup A x := by
    exact le_iSup
      (fun r : gra A ↦ (((⟪x - r.1.1, r.1.2⟫_ℝ / (1 + ‖r.1.1‖) : ℝ) : EReal))) q
  have hq_bot :
      (⊥ : EReal) <
        (((⟪x - q.1.1, q.1.2⟫_ℝ / (1 + ‖q.1.1‖) : ℝ) : EReal)) := by
    exact EReal.bot_lt_coe _
  exact lt_of_lt_of_le hq_bot hq

/-- Helper for Proposition 21.11: every first-coordinate Fitzpatrick-domain witness produces a
finite value of the normalized graph supremum. -/
private lemma fst_image_dom_fitzpatrick_subset_dom_normalized_graph_sup
    (A : SetValuedOperator H H) (hgraph : (gra A).Nonempty) :
    Prod.fst '' ERealFunction.dom (F[A]) ⊆ ERealFunction.dom (normalized_graph_sup A) := by
  intro x hx
  rcases hx with ⟨⟨x, u⟩, hxu, rfl⟩
  have hFA_top : F[A] (x, u) ≠ ⊤ := (ERealFunction.mem_dom_iff_ne_top _ _).1 hxu
  have hFA_bot : F[A] (x, u) ≠ ⊥ := by
    exact ne_of_gt (fitzpatrickFunction_ne_bot_of_graph_nonempty A hgraph (x, u))
  let M : ℝ := max (F[A] (x, u)).toReal ‖u‖
  have hbranch :
      ∀ p : gra A,
        (((⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) : ℝ) : EReal)) ≤ (M : EReal) := by
    intro p
    have hfitz :
        (((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)) ≤ F[A] (x, u) := by
      exact le_iSup
        (fun q : gra A ↦
          (((⟪q.1.1, u⟫_ℝ + ⟪x, q.1.2⟫_ℝ - ⟪q.1.1, q.1.2⟫_ℝ : ℝ) : EReal))) p
    have hfitz_real :
        ⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ ≤ (F[A] (x, u)).toReal := by
      exact EReal.toReal_le_toReal hfitz (EReal.coe_ne_bot _) hFA_top
    have hinner_aux :
        ⟪x - p.1.1, p.1.2⟫_ℝ ≤
          (F[A] (x, u)).toReal + ‖p.1.1‖ * ‖u‖ := by
      have hcs : |⟪p.1.1, u⟫_ℝ| ≤ ‖p.1.1‖ * ‖u‖ := by
        simpa using abs_real_inner_le_norm p.1.1 u
      have hneg_inner : -⟪p.1.1, u⟫_ℝ ≤ ‖p.1.1‖ * ‖u‖ := by
        have := abs_le.mp hcs
        linarith
      have hsplit : ⟪x - p.1.1, p.1.2⟫_ℝ =
          ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ := by
        rw [inner_sub_left]
      rw [hsplit]
      linarith
    have hbound :
        ⟪x - p.1.1, p.1.2⟫_ℝ ≤ M * (1 + ‖p.1.1‖) := by
      calc
        ⟪x - p.1.1, p.1.2⟫_ℝ
            ≤ (F[A] (x, u)).toReal + ‖p.1.1‖ * ‖u‖ := hinner_aux
        _ ≤ M + ‖p.1.1‖ * M := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
        _ = M * (1 + ‖p.1.1‖) := by ring
    have hden : 0 < 1 + ‖p.1.1‖ := by positivity
    have hdiv :
        ⟪x - p.1.1, p.1.2⟫_ℝ / (1 + ‖p.1.1‖) ≤ M := by
      exact (div_le_iff₀ hden).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)
    exact_mod_cast hdiv
  have hsup : normalized_graph_sup A x ≤ (M : EReal) := by
    refine iSup_le hbranch
  refine (ERealFunction.mem_dom_iff_ne_top _ _).2 ?_
  exact ne_of_lt (lt_of_le_of_lt hsup (EReal.coe_lt_top M))

/-- Helper for Proposition 21.11: a bounded real image on an open ball yields a uniform finite
upper bound on the normalized graph supremum over a strict closed subball. -/
private lemma upper_bound_on_closed_subball_of_bounded_toReal_image_ball
    {f : H → EReal} {z : H} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hball_dom : Metric.ball z ρ ⊆ ERealFunction.dom f)
    (hbounded :
      Bornology.IsBounded (((fun x ↦ (f x : EReal).toReal) '' Metric.ball z ρ) : Set ℝ)) :
    ∃ δ > 0, ∃ R : NNReal,
      ∀ x ∈ Metric.closedBall z (2 * δ), f x ≤ (((R : NNReal) : ℝ) : EReal) := by
  obtain ⟨B, hB_pos, hBsubset⟩ := hbounded.subset_closedBall_lt 0 (0 : ℝ)
  let δ : ℝ := ρ / 3
  have hδ : 0 < δ := by
    -- Shrinking to one third leaves room for the doubled closed subball inside the ambient ball.
    dsimp [δ]
    positivity
  let R : NNReal := ⟨B, le_of_lt hB_pos⟩
  refine ⟨δ, hδ, R, ?_⟩
  intro x hx
  have hdouble_lt : 2 * δ < ρ := by
    -- The radius choice guarantees `2δ < ρ`.
    dsimp [δ]
    nlinarith
  have hx_ball : x ∈ Metric.ball z ρ :=
    Metric.closedBall_subset_ball hdouble_lt hx
  have hfx_top : f x ≠ ⊤ := (ERealFunction.mem_dom_iff_ne_top _ _).1 (hball_dom hx_ball)
  have htoReal_mem :
      (f x : EReal).toReal ∈ Metric.closedBall (0 : ℝ) B := by
    exact hBsubset (Set.mem_image_of_mem (fun y ↦ (f y : EReal).toReal) hx_ball)
  have htoReal_le_B : (f x : EReal).toReal ≤ B := by
    -- The bounded image lies in a closed ball centered at `0`, so each value is bounded above by
    -- its radius.
    have habs : |(f x : EReal).toReal| ≤ B := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using htoReal_mem
    exact (abs_le.mp habs).2
  calc
    f x ≤ (((f x : EReal).toReal : ℝ) : EReal) := EReal.le_coe_toReal hfx_top
    _ ≤ (((R : NNReal) : ℝ) : EReal) := by
      exact_mod_cast htoReal_le_B

/-- Helper for Proposition 21.11: every nonnegative radius admits a boundary vector whose inner
product with `v` realizes `r * ‖v‖`. -/
private lemma exists_vector_mem_closedBall_inner_eq_radius_mul_norm
    {r : ℝ} (hr : 0 ≤ r) (v : H) :
    ∃ w ∈ Metric.closedBall (0 : H) r, ⟪w, v⟫_ℝ = r * ‖v‖ := by
  by_cases hv : v = 0
  · refine ⟨0, ?_, ?_⟩
    · -- The zero vector lies in every closed ball of nonnegative radius.
      simpa [Metric.mem_closedBall, dist_eq_norm] using hr
    · simp [hv]
  · let w : H := (r * ‖v‖⁻¹) • v
    have hv_norm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hcoeff_nonneg : 0 ≤ r * ‖v‖⁻¹ := by
      exact mul_nonneg hr (inv_nonneg.mpr (norm_nonneg v))
    have hw_norm : ‖w‖ = r := by
      -- The chosen coefficient normalizes `v` to the prescribed radius.
      dsimp [w]
      rw [norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
      calc
        (r * ‖v‖⁻¹) * ‖v‖ = r * (‖v‖⁻¹ * ‖v‖) := by ring
        _ = r := by rw [inv_mul_cancel₀ hv_norm, mul_one]
    refine ⟨w, ?_, ?_⟩
    · -- The normalized direction has exactly the prescribed norm `r`.
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa [sub_eq_add_neg, hw_norm] using hw_norm.le
    · -- The same normalization turns the inner product into `r * ‖v‖`.
      dsimp [w]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two]
      calc
        (r * ‖v‖⁻¹) * (‖v‖ * ‖v‖) = r * (‖v‖⁻¹ * ‖v‖) * ‖v‖ := by ring
        _ = r * 1 * ‖v‖ := by rw [inv_mul_cancel₀ hv_norm]
        _ = r * ‖v‖ := by ring

/-- Helper for Proposition 21.11: a closed-subball upper bound on the normalized graph supremum
forces a uniform norm bound on graph values over the inner open ball. -/
private lemma norm_le_of_mem_graph_of_mem_ball_of_closed_subball_bound
    (A : SetValuedOperator H H) {z : H} {δ : ℝ} (hδ : 0 < δ) {R : NNReal}
    (hbound :
      ∀ x ∈ Metric.closedBall z (2 * δ),
        normalized_graph_sup A x ≤ (((R : NNReal) : ℝ) : EReal))
    {y v : H} (hy : y ∈ Metric.ball z δ) (hv : v ∈ A y) :
    ‖v‖ ≤ ((R : ℝ) * (1 + δ + ‖z‖) / δ) := by
  obtain ⟨w, hw_closed, hw_inner⟩ :=
    exists_vector_mem_closedBall_inner_eq_radius_mul_norm
      (r := 2 * δ) (by positivity) v
  have hzw_closed : z + w ∈ Metric.closedBall z (2 * δ) := by
    -- Translating the boundary vector from the origin places `z + w` on the desired closed
    -- subball around `z`.
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      using hw_closed
  have hp :
      (((⟪z + w - y, v⟫_ℝ / (1 + ‖y‖) : ℝ) : EReal)) ≤ normalized_graph_sup A (z + w) := by
    -- Evaluate the supremum defining `normalized_graph_sup` at the graph point `(y, v)`.
    let p : gra A := ⟨(y, v), hv⟩
    exact le_iSup
      (fun q : gra A ↦ (((⟪z + w - q.1.1, q.1.2⟫_ℝ / (1 + ‖q.1.1‖) : ℝ) : EReal))) p
  have hdiv_real :
      ⟪z + w - y, v⟫_ℝ / (1 + ‖y‖) ≤ (R : ℝ) := by
    have hdiv :
        (((⟪z + w - y, v⟫_ℝ / (1 + ‖y‖) : ℝ) : EReal)) ≤ (((R : NNReal) : ℝ) : EReal) :=
      hp.trans (hbound (z + w) hzw_closed)
    exact EReal.toReal_le_toReal hdiv (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
  have hmain :
      ⟪z + w - y, v⟫_ℝ ≤ (R : ℝ) * (1 + ‖y‖) := by
    -- Clear the positive denominator from the normalized graph inequality.
    have hden : 0 < 1 + ‖y‖ := by positivity
    exact (div_le_iff₀ hden).1 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv_real)
  have hmain' :
      ⟪z - y, v⟫_ℝ + 2 * δ * ‖v‖ ≤ (R : ℝ) * (1 + ‖y‖) := by
    -- The boundary vector contributes the exact `2δ‖v‖` term from the textbook estimate.
    have hsplit : z + w - y = (z - y) + w := by
      abel_nf
    have hrewrite :
        ⟪z + w - y, v⟫_ℝ = ⟪z - y, v⟫_ℝ + 2 * δ * ‖v‖ := by
      rw [hsplit, inner_add_left, hw_inner]
    simpa [hrewrite] using hmain
  have hy_norm_lt : ‖z - y‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hinner_lower : -(‖z - y‖ * ‖v‖) ≤ ⟪z - y, v⟫_ℝ := by
    -- Cauchy-Schwarz controls the possibly negative inner-product correction term.
    have habs : |⟪z - y, v⟫_ℝ| ≤ ‖z - y‖ * ‖v‖ := by
      simpa using abs_real_inner_le_norm (z - y) v
    exact (abs_le.mp habs).1
  have hdelta_term :
      δ * ‖v‖ ≤ 2 * δ * ‖v‖ + ⟪z - y, v⟫_ℝ := by
    have hprod : ‖z - y‖ * ‖v‖ ≤ δ * ‖v‖ := by
      exact (mul_le_mul_of_nonneg_right (le_of_lt hy_norm_lt) (norm_nonneg v))
    have hneg_term : -(δ * ‖v‖) ≤ ⟪z - y, v⟫_ℝ := by
      exact (neg_le_neg hprod).trans hinner_lower
    linarith
  have hdelta_bound : δ * ‖v‖ ≤ (R : ℝ) * (1 + ‖y‖) := by
    exact hdelta_term.trans (by
      simpa [add_comm, add_left_comm, add_assoc] using hmain')
  have hy_norm_lt' : ‖y‖ < δ + ‖z‖ := by
    -- A point of `ball z δ` has norm controlled by `δ + ‖z‖`.
    calc
      ‖y‖ = ‖(y - z) + z‖ := by
        congr 1
        abel_nf
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ < δ + ‖z‖ := by
        simpa [norm_sub_rev] using add_lt_add_right hy_norm_lt ‖z‖
  have hright_le :
      (R : ℝ) * (1 + ‖y‖) ≤ (R : ℝ) * (1 + δ + ‖z‖) := by
    have hone_le : 1 + ‖y‖ ≤ 1 + δ + ‖z‖ := by
      linarith
    exact mul_le_mul_of_nonneg_left hone_le (show 0 ≤ (R : ℝ) by exact_mod_cast R.2)
  have hfinal_mul : δ * ‖v‖ ≤ (R : ℝ) * (1 + δ + ‖z‖) := hdelta_bound.trans hright_le
  exact (le_div_iff₀ hδ).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfinal_mul)

-- Domain-style sampling: mathlib only provides the single-valued bornology owner
-- `LocallyBoundedMap`, so this proposition uses the source-facing Chapter 21 owner
-- `SetValuedOperator.IsLocallyBoundedAt` from Definition 21.10.

/-- Proposition 21.11: if `A : H → 2^H` is monotone and `z ∈ interior (Prod.fst '' dom (F[A]))`,
then `A` is locally bounded at `z`. The textbook projection `Q₁ : H × H → H` is represented by
`Prod.fst`. -/
theorem isLocallyBoundedAt_of_mem_interior_fst_image_dom_fitzpatrick
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) {z : H}
    (hz : z ∈ interior (Prod.fst '' ERealFunction.dom (F[A]))) :
    A.IsLocallyBoundedAt z := by
  classical
  by_cases hgraph : (gra A).Nonempty
  · let f : H → EReal := normalized_graph_sup A
    have hf_gamma : f ∈ Γ(H) := normalized_graph_sup_mem_gamma A
    have hf_ne_bot : ∀ x : H, ⊥ < f x := by
      intro x
      simpa [f] using normalized_graph_sup_ne_bot_of_graph_nonempty A hgraph x
    have hsubset_dom :
        Prod.fst '' ERealFunction.dom (F[A]) ⊆ ERealFunction.dom f := by
      simpa [f] using fst_image_dom_fitzpatrick_subset_dom_normalized_graph_sup A hgraph
    -- The Fitzpatrick-domain interior transfers directly to the normalized supremum domain.
    have hz_dom_f : z ∈ interior (ERealFunction.dom f) := by
      exact interior_mono hsubset_dom hz
    have hf_proper : IsProper f := by
      refine ⟨?_, ?_⟩
      · intro x
        exact ne_of_gt (hf_ne_bot x)
      · exact ⟨z, interior_subset hz_dom_f⟩
    let φ : H → Set.Ioi (⊥ : EReal) := properIoi f hf_proper
    have hφ_gammaZero : φ ∈ Γ₀(H) := by
      exact properIoi_mem_gammaZero_of_mem_gamma hf_proper hf_gamma
    have hz_eff : z ∈ interior (effectiveDomain φ) := by
      simpa [φ, f, ERealFunction.effectiveDomain, ERealFunction.dom]
        using hz_dom_f
    have hz_local :
        z ∈
          {x : H | ∃ ρ : ℝ, 0 < ρ ∧
            Metric.ball x ρ ⊆ effectiveDomain φ ∧
              ContinuousAt (fun y ↦ (φ y : EReal).toReal) x} := by
      have hEq :=
        continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
          φ hφ_gammaZero.2 (Or.inr (Or.inl hφ_gammaZero.1))
      rw [hEq]
      exact hz_eff
    rcases hz_local with ⟨ρ, hρ, hball_dom, hcont⟩
    have htfae :=
      ERealFunction.convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
        φ hφ_gammaZero.2 (interior_subset hz_eff)
    have hbounded_ball :
        ∃ ρ > 0,
          Metric.ball z ρ ⊆ effectiveDomain φ ∧
            Bornology.IsBounded (((fun y ↦ (φ y : EReal).toReal) '' Metric.ball z ρ) : Set ℝ) := by
      -- Route correction: use Theorem 8.38 to convert the Corollary 8.39 continuity witness into
      -- bounded real image on a neighborhood ball before taking the closed-subball shrink.
      have hcont_ball :
          ∃ ρ > 0,
            Metric.ball z ρ ⊆ effectiveDomain φ ∧
              ContinuousAt (fun y ↦ (φ y : EReal).toReal) z := by
        exact ⟨ρ, hρ, hball_dom, hcont⟩
      exact (List.TFAE.out htfae 1 2).mp hcont_ball
    rcases hbounded_ball with ⟨ρ', hρ', hball_dom', hbounded'⟩
    have hball_dom_f : Metric.ball z ρ' ⊆ ERealFunction.dom f := by
      -- For the proper `Γ₀` representative, the effective domain is exactly the raw domain of `f`.
      simpa [φ, f, properIoi_apply, ERealFunction.effectiveDomain, ERealFunction.dom]
        using hball_dom'
    have hbounded_f :
        Bornology.IsBounded (((fun y ↦ (f y : EReal).toReal) '' Metric.ball z ρ') : Set ℝ) := by
      simpa [φ, f, properIoi_apply] using hbounded'
    obtain ⟨δ, hδ, R, hRbound⟩ :=
      upper_bound_on_closed_subball_of_bounded_toReal_image_ball
        (f := f) hρ' hball_dom_f hbounded_f
    refine ⟨δ, hδ, ?_⟩
    refine (Metric.isBounded_iff_subset_closedBall (0 : H)).2 ?_
    refine ⟨((R : ℝ) * (1 + δ + ‖z‖) / δ), ?_⟩
    intro u hu
    rcases (SetValuedOperator.mem_image A (Metric.ball z δ) u).1 hu with ⟨y, hy, huy⟩
    have hu_norm :
        ‖u‖ ≤ ((R : ℝ) * (1 + δ + ‖z‖) / δ) := by
      -- The closed-subball bound on `f` feeds directly into the textbook graph estimate.
      exact norm_le_of_mem_graph_of_mem_ball_of_closed_subball_bound
        (A := A) hδ (R := R) (by simpa [f] using hRbound) hy huy
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_norm
  · refine ⟨1, zero_lt_one, ?_⟩
    have himage : A.image (Metric.ball z 1) = ∅ := by
      ext u
      constructor
      · intro hu
        rcases (SetValuedOperator.mem_image A (Metric.ball z 1) u).1 hu with ⟨x, hx, hux⟩
        exact (hgraph ⟨(x, u), hux⟩).elim
      · intro hu
        simpa using hu
    simpa [himage] using (Metric.isBounded_empty : Bornology.IsBounded (∅ : Set H))

end SetValuedOperator
