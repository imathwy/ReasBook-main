

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_14 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

section Core

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 2.14 is source-facing in the strong-convexity domain on real vector spaces equipped
with an arbitrary seminorm.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* mathlib `StrongConvexOn`
* mathlib `strongConvexOn_iff_convex`
* project `ConvexOn.lower_tangent_plane` in `Definition_2_2`

Source/core/bridge triage:
* source-facing: `StrongConvexOnWith p μ Q f`, which keeps the textbook seminorm `p` explicit
* core/canonical: `StrongConvexOn Q μ f` in the ambient-norm specialization
  `p = normSeminorm`
* bridge/view: `strongConvexOnWith_normSeminorm_iff`

Primitive data:
* convexity of `Q`
* positivity of `μ`
* the `p`-strong segment inequality
* for the finite-dimensional ambient-norm bridge, the extra separation hypothesis
  `[Seminorm.IsNorm p]`
* for minimizer existence on closed feasible sets, continuity of `f` on `Q`

Derived API:
* the convexity consequence `StrongConvexOnWith.convexOn`
* over real normed spaces, the ambient-norm bridge to `StrongConvexOn`
* over finite-dimensional real normed spaces, the bridge
  `StrongConvexOnWith.exists_pos_strongConvexOn`
* on closed nonempty feasible sets in finite-dimensional real normed spaces, the
  unique-minimizer theorem
  `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed`
* over complete real inner-product spaces, the lower tangent quadratic bound under an explicit
  gradient witness for both `StrongConvexOnWith` and its ambient-norm owner `StrongConvexOn`,
  together with the quadratic-growth corollaries at a feasible minimizer
-/

/-- Definition 2.14 in owner form: a function on a convex set `Q` is `μ`-strongly convex with
respect to a seminorm `p` when `μ > 0` and it satisfies the intrinsic strong-convexity inequality
`f (a • x + b • y) ≤ a • f x + b • f y - a * b * (μ / 2) * p (x - y)^2`
for all `x, y ∈ Q` and all nonnegative `a, b` with `a + b = 1`. The tangent-plane inequality is
kept as a companion theorem under an explicit ambient differentiability hypothesis. The stronger
assumption `[Seminorm.IsNorm p]` is imposed only on the later norm-comparison bridge theorems. -/
def StrongConvexOnWith
    (p : Seminorm ℝ E) (μ : ℝ) (Q : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ Q ∧
    0 < μ ∧
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a • x + b • y) ≤
          a • f x + b • f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ))

variable {p : Seminorm ℝ E} {μ : ℝ} {Q : Set E} {f : E → ℝ}

/-- Strong convexity with respect to a seminorm implies ordinary convexity on the same feasible
set. -/
-- Proof sketch: drop the nonnegative quadratic correction term in the defining strong-convexity
-- inequality and keep the convexity data already packaged in `StrongConvexOnWith`.
theorem StrongConvexOnWith.convexOn
    (hf : StrongConvexOnWith p μ Q f) :
    ConvexOn ℝ Q f := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- The strong-convexity correction term is nonnegative, so dropping it gives Jensen convexity.
  refine (hf.2.2 hx hy ha hb hab).trans ?_
  have hμ_nonneg : 0 ≤ μ := le_of_lt hf.2.1
  have hcorr : 0 ≤ a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
    positivity
  linarith

/-- Nonnegative weighted sums preserve strong convexity on the intersection of the feasible
sets, with modulus equal to the corresponding weighted sum of moduli. -/
-- Proof sketch: convexity of `Q₁ ∩ Q₂` comes from the two owner hypotheses. On each segment in
-- the intersection, multiply the two strong-convexity inequalities by `α` and `β`, then add.
theorem StrongConvexOnWith.nonneg_combo_inter
    {Q₁ Q₂ : Set E} {f₁ f₂ : E → ℝ} {μ₁ μ₂ α β : ℝ}
    (hf₁ : StrongConvexOnWith p μ₁ Q₁ f₁)
    (hf₂ : StrongConvexOnWith p μ₂ Q₂ f₂)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hμ : 0 < α * μ₁ + β * μ₂) :
    StrongConvexOnWith p (α * μ₁ + β * μ₂) (Q₁ ∩ Q₂) (α • f₁ + β • f₂) := by
  refine ⟨hf₁.1.inter hf₂.1, hμ, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Scale the two owner inequalities by `α` and `β`, then add the resulting estimates.
  have h₁ := hf₁.2.2 hx.1 hy.1 ha hb hab
  have h₂ := hf₂.2.2 hx.2 hy.2 ha hb hab
  have h₁' := mul_le_mul_of_nonneg_left h₁ hα
  have h₂' := mul_le_mul_of_nonneg_left h₂ hβ
  have hadd := add_le_add h₁' h₂'
  calc
    (α • f₁ + β • f₂) (a • x + b • y)
        = α * f₁ (a • x + b • y) + β * f₂ (a • x + b • y) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    _ ≤
        α * (a • f₁ x + b • f₁ y - a * b * ((μ₁ / 2) * (p (x - y)) ^ (2 : ℕ))) +
          β * (a • f₂ x + b • f₂ y - a * b * ((μ₂ / 2) * (p (x - y)) ^ (2 : ℕ))) := hadd
    _ = a • (α • f₁ + β • f₂) x + b • (α • f₁ + β • f₂) y -
          a * b * (((α * μ₁ + β * μ₂) / 2) * (p (x - y)) ^ (2 : ℕ)) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring

/-- A feasible minimizer of a function that is strongly convex with respect to a
seminorm satisfies the standard quadratic growth bound on the feasible set. -/
-- Proof sketch: apply the strong-convexity inequality on the segment from `xStar` to `x`, use
-- the minimizing property at `xStar`, and optimize the resulting one-variable bound.
theorem StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem
    (hf : StrongConvexOnWith p μ Q f) {xStar : E}
    (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn f Q xStar)
    (x : E) (hx : x ∈ Q) :
    f x ≥ f xStar + (μ / 2) * (p (x - xStar)) ^ (2 : ℕ) := by
  let c : ℝ := (μ / 2) * (p (x - xStar)) ^ (2 : ℕ)
  have hμ_nonneg : 0 ≤ μ := le_of_lt hf.2.1
  have hc_nonneg : 0 ≤ c := by
    positivity
  have hxStar_min : ∀ z ∈ Q, f xStar ≤ f z := isMinOn_iff.mp hxStar
  by_cases hc : c = 0
  · -- If the correction term vanishes, the minimizing property already gives the claim.
    have hmin : f xStar ≤ f x := hxStar_min x hx
    simpa [c, hc] using hmin
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (by simpa [eq_comm] using hc)
    by_contra hfx
    have hdiff_nonneg : 0 ≤ f x - f xStar := by
      have hmin : f xStar ≤ f x := hxStar_min x hx
      linarith
    have hlt_fx : f x < f xStar + c := lt_of_not_ge hfx
    have hlt : f x - f xStar < c := by
      linarith
    let t : ℝ := (c - (f x - f xStar)) / (2 * c)
    have ht_pos : 0 < t := by
      dsimp [t]
      have hnum : 0 < c - (f x - f xStar) := by
        linarith
      have hden : 0 < 2 * c := by
        positivity
      exact div_pos hnum hden
    have ht_le : t ≤ 1 := by
      dsimp [t]
      have hden : 0 < 2 * c := by
        positivity
      rw [div_le_one hden]
      linarith
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have h1t_nonneg : 0 ≤ 1 - t := by
      linarith
    let z : E := t • x + (1 - t) • xStar
    have hz : z ∈ Q := hf.1 hx hxStar_mem ht_nonneg h1t_nonneg (by ring)
    have hz_min : f xStar ≤ f z := hxStar_min z hz
    have hstrong := hf.2.2 hx hxStar_mem ht_nonneg h1t_nonneg (by ring)
    have hsegment :
        f xStar ≤ (1 - t) * f xStar + t * f x - t * (1 - t) * c := by
      simpa [z, c, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm,
        add_assoc] using
        (le_trans hz_min hstrong)
    have hbound : f x - f xStar ≥ (1 - t) * c := by
      nlinarith [hsegment, ht_pos]
    have hstrict : f x - f xStar < (1 - t) * c := by
      have ht_formula : (1 - t) * c = (c + (f x - f xStar)) / 2 := by
        dsimp [t]
        field_simp [hc_pos.ne']
        ring
      rw [ht_formula]
      nlinarith
    linarith

end Core

section Normed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : ℝ} {Q : Set E} {f : E → ℝ}

/-- With the ambient norm, `StrongConvexOnWith` is exactly the positive-parameter part of
mathlib's canonical predicate `StrongConvexOn`. -/
-- Proof sketch: unfold `StrongConvexOnWith`, `StrongConvexOn`, and `UniformConvexOn` at the
-- ambient norm, then rearrange the conjunctions.
theorem strongConvexOnWith_normSeminorm_iff :
    StrongConvexOnWith (normSeminorm ℝ E) μ Q f ↔
      0 < μ ∧ StrongConvexOn Q μ f := by
  -- With the ambient norm, the source owner is definitionally the positive-parameter part of
  -- `StrongConvexOn`.
  constructor
  · intro h
    refine ⟨h.2.1, h.1, ?_⟩
    simpa [StrongConvexOn, UniformConvexOn] using h.2.2
  · rintro ⟨hμ, hconv, hineq⟩
    refine ⟨hconv, hμ, ?_⟩
    simpa [StrongConvexOn, UniformConvexOn] using hineq

scoped[StrongConvex] notation:50 f:50 " ∈ " "𝓛^1[" μ:50 "]" =>
  StrongConvexOnWith (normSeminorm ℝ _) μ Set.univ f

open scoped StrongConvex

/-- Whole-space membership in the source class `𝓛^1[μ]` is exactly the positive-parameter part
of the canonical owner `StrongConvexOn Set.univ μ`. -/
theorem mem_strongConvexClass_iff :
    f ∈ 𝓛^1[μ] ↔ 0 < μ ∧ StrongConvexOn Set.univ μ f := by
  simpa using
    (strongConvexOnWith_normSeminorm_iff :
      f ∈ 𝓛^1[μ] ↔ 0 < μ ∧ StrongConvexOn Set.univ μ f)

end Normed

section FiniteDimensional

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {μ : ℝ} {Q : Set E} {f : E → ℝ}

/-- On a finite-dimensional real normed space, strong convexity with respect to a separated
seminorm produces ordinary ambient-norm strong convexity for some positive modulus. -/
-- Proof sketch: a genuine norm `p` on a finite-dimensional real normed space dominates the
-- ambient norm up to a positive constant. Insert that comparison into the defining
-- `StrongConvexOnWith p μ Q f` inequality to
-- obtain `StrongConvexOnWith (normSeminorm ℝ E) ν Q f` for some `ν > 0`, then rewrite with
-- `strongConvexOnWith_normSeminorm_iff`.
theorem StrongConvexOnWith.exists_pos_strongConvexOn
    (hf : StrongConvexOnWith p μ Q f) :
    ∃ ν > 0, StrongConvexOn Q ν f := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  let ν : ℝ := μ / C ^ (2 : ℕ)
  have hμ_nonneg : 0 ≤ μ := le_of_lt hf.2.1
  have hν_pos : 0 < ν := by
    dsimp [ν]
    have hC2_pos : 0 < C ^ (2 : ℕ) := by
      positivity
    exact div_pos hf.2.1 hC2_pos
  have hnorm_version : StrongConvexOnWith (normSeminorm ℝ E) ν Q f := by
    refine ⟨hf.1, hν_pos, ?_⟩
    intro x hx y hy a b ha hb hab
    have hbase := hf.2.2 hx hy ha hb hab
    have hsq :
        ‖x - y‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * (p (x - y)) ^ (2 : ℕ) := by
      have hxy := hnorm_le (x - y)
      have hright_nonneg : 0 ≤ C * p (x - y) := by
        exact mul_nonneg hC_pos.le (apply_nonneg p (x - y))
      have hsq_mul :
          ‖x - y‖ * ‖x - y‖ ≤ (C * p (x - y)) * (C * p (x - y)) := by
        exact mul_le_mul hxy hxy (norm_nonneg _) hright_nonneg
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq_mul
    have hcorr :
        (ν / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ (μ / 2) * (p (x - y)) ^ (2 : ℕ) := by
      have hfactor_nonneg : 0 ≤ ν / 2 := by
        positivity
      have hmul :
          (ν / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
            (ν / 2) * (C ^ (2 : ℕ) * (p (x - y)) ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hsq hfactor_nonneg
      have hC2_ne : C ^ (2 : ℕ) ≠ 0 := by
        positivity
      calc
        (ν / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
            (ν / 2) * (C ^ (2 : ℕ) * (p (x - y)) ^ (2 : ℕ)) := hmul
        _ = (μ / 2) * (p (x - y)) ^ (2 : ℕ) := by
          dsimp [ν]
          field_simp [hC2_ne]
    have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
    have hscaled :
        a * b * ((ν / 2) * ‖x - y‖ ^ (2 : ℕ)) ≤
          a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hcorr hab_nonneg
    have hsub :
        a • f x + b • f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) ≤
          a • f x + b • f y - a * b * ((ν / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
      exact sub_le_sub_left hscaled (a • f x + b • f y)
    exact hbase.trans hsub
  refine ⟨ν, hν_pos, ?_⟩
  exact (strongConvexOnWith_normSeminorm_iff.mp hnorm_version).2

/-- Helper for Definition 2.14: the sublevel set through a feasible base point is bounded for a
positive strongly convex function on a closed feasible set. -/
-- Proof sketch: minimize `f` on the compact unit ball around `x₀`, then compare any farther
-- sublevel point with its radial contraction back to that ball.
lemma sublevel_bounded_of_pos_strongConvexOn_at_basepoint
    {ν : ℝ} (hf : StrongConvexOn Q ν f) (hν : 0 < ν)
    (hf_cont : ContinuousOn f Q) (hQ_closed : IsClosed Q) {x0 : E} (hx0 : x0 ∈ Q) :
    Bornology.IsBounded (Q ∩ f ⁻¹' Set.Iic (f x0)) := by
  let K : Set E := Q ∩ Metric.closedBall x0 1
  have hx0K : x0 ∈ K := by
    refine ⟨hx0, ?_⟩
    simp [Metric.mem_closedBall]
  have hK_closed : IsClosed K := hQ_closed.inter Metric.isClosed_closedBall
  have hK_compact : IsCompact K := by
    exact Metric.isCompact_of_isClosed_isBounded hK_closed
      (Metric.isBounded_closedBall.subset (by
        intro x hx
        exact hx.2))
  have hK_subsetQ : K ⊆ Q := by
    intro x hx
    exact hx.1
  -- Choose the minimum of `f` on the compact unit ball around the base point.
  obtain ⟨zMin, hzMinK, hzMin⟩ :=
    hK_compact.exists_isMinOn ⟨x0, hx0K⟩ (hf_cont.mono hK_subsetQ)
  let B : ℝ := 1 + 2 * (f x0 - f zMin) / ν
  have hB_ge_one : 1 ≤ B := by
    have hzMin_le : f zMin ≤ f x0 := hzMin hx0K
    have hdiff_nonneg : 0 ≤ f x0 - f zMin := by
      linarith
    have hnonneg : 0 ≤ 2 * (f x0 - f zMin) / ν := by
      positivity
    dsimp [B]
    linarith
  -- Every point in the basepoint sublevel set lies in the closed ball of radius `B` around `x₀`.
  refine (Metric.isBounded_iff_subset_closedBall x0).2 ?_
  refine ⟨B, ?_⟩
  intro x hx
  rcases hx with ⟨hxQ, hfx⟩
  by_cases hR_le : ‖x - x0‖ ≤ 1
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hR_le.trans hB_ge_one
  · let R : ℝ := ‖x - x0‖
    have hR_def : R = ‖x - x0‖ := rfl
    have hR_gt : 1 < R := by
      dsimp [R]
      linarith
    have hR_pos : 0 < R := lt_trans zero_lt_one hR_gt
    let t : ℝ := 1 / R
    let z : E := AffineMap.lineMap x0 x t
    have ht_pos : 0 < t := by
      dsimp [t]
      exact one_div_pos.mpr hR_pos
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have ht_lt_one : t < 1 := by
      dsimp [t]
      simpa [one_div] using inv_lt_one_of_one_lt₀ hR_gt
    have h1t_nonneg : 0 ≤ 1 - t := by
      linarith
    have hzQ : z ∈ Q := by
      simpa [z, AffineMap.lineMap_apply_module] using
        (hf.1 hx0 hxQ h1t_nonneg ht_nonneg (by ring))
    have hz_ball : z ∈ Metric.closedBall x0 1 := by
      have hz_norm : ‖z - x0‖ = 1 := by
        calc
          ‖z - x0‖ = ‖t • (x - x0)‖ := by
            simp [z, AffineMap.lineMap_apply_module', sub_eq_add_neg]
          _ = |t| * ‖x - x0‖ := norm_smul t (x - x0)
          _ = t * R := by
            rw [abs_of_pos ht_pos, hR_def]
          _ = 1 := by
            dsimp [t]
            field_simp [hR_pos.ne']
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz_norm.le
    have hzK : z ∈ K := ⟨hzQ, hz_ball⟩
    have hzMin_le : f zMin ≤ f z := hzMin hzK
    have hstrong := hf.2 hx0 hxQ h1t_nonneg ht_nonneg (by ring)
    -- Strong convexity along the ray from `x₀` to `x` turns the sublevel condition into a radius
    -- estimate after evaluating at the contracted point `z`.
    have hupper : f z ≤ f x0 - (ν / 2) * (R - 1) := by
      have hfactor : (1 - t) * t * R ^ (2 : ℕ) = R - 1 := by
        dsimp [t]
        field_simp [hR_pos.ne']
      have hfx_le : f x ≤ f x0 := hfx
      calc
        f z ≤ (1 - t) * f x0 + t * f x - (1 - t) * t * ((ν / 2) * ‖x0 - x‖ ^ (2 : ℕ)) := by
          simpa [z, AffineMap.lineMap_apply_module] using hstrong
        _ ≤ f x0 - (1 - t) * t * ((ν / 2) * ‖x0 - x‖ ^ (2 : ℕ)) := by
          nlinarith
        _ = f x0 - (ν / 2) * (R - 1) := by
          have hrewrite : (1 - t) * t * ((ν / 2) * R ^ (2 : ℕ)) = (ν / 2) * (R - 1) := by
            rw [← hfactor]
            ring
          rw [norm_sub_rev, ← hR_def, hrewrite]
    have hR_bound : R ≤ B := by
      have hzMin_le_upper : f zMin ≤ f x0 - (ν / 2) * (R - 1) := by
        exact le_trans hzMin_le hupper
      have hbound' : ν * (R - 1) ≤ 2 * (f x0 - f zMin) := by
        nlinarith
      have hR_sub : R - 1 ≤ 2 * (f x0 - f zMin) / ν := by
        exact (le_div_iff₀ hν).2 (by simpa [mul_comm] using hbound')
      dsimp [B]
      linarith
    simpa [Metric.mem_closedBall, dist_eq_norm, hR_def] using hR_bound

/-- Theorem 2.32 in owner form: on a nonempty closed feasible set in a finite-dimensional real
normed space, strong convexity with respect to any norm-like seminorm and continuity on the
feasible set have a unique feasible minimizer. -/
-- Proof sketch: pass to an ambient-norm strong-convexity modulus, bound the basepoint sublevel
-- set, then combine compact attainment with strict-convex uniqueness.
theorem StrongConvexOnWith.existsUnique_isMinOn_of_isClosed
    (hf : StrongConvexOnWith p μ Q f)
    (hf_cont : ContinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! xStar : E, xStar ∈ Q ∧ IsMinOn f Q xStar := by
  rcases hQ_nonempty with ⟨x0, hx0⟩
  obtain ⟨ν, hν, hstrong⟩ := hf.exists_pos_strongConvexOn
  let S : Set E := Q ∩ f ⁻¹' Set.Iic (f x0)
  -- Route correction: the existence proof now closes by compactifying a single basepoint
  -- sublevel set instead of appealing to later constrained-sublevel owner API.
  have hS_closed : IsClosed S := by
    simpa [S] using hf_cont.preimage_isClosed_of_isClosed hQ_closed isClosed_Iic
  have hS_bounded : Bornology.IsBounded S := by
    simpa [S] using sublevel_bounded_of_pos_strongConvexOn_at_basepoint
      hstrong hν hf_cont hQ_closed hx0
  have hS_compact : IsCompact S := by
    exact Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hS_cont : ContinuousOn f S := by
    exact hf_cont.mono (by
      intro x hx
      exact hx.1)
  have hx0S : x0 ∈ S := by
    refine ⟨hx0, ?_⟩
    change f x0 ≤ f x0
    exact le_rfl
  -- Minimize on the compact sublevel set, then show the same point minimizes on all of `Q`.
  obtain ⟨xStar, hxStarS, hxStarMinS⟩ :=
    hS_compact.exists_isMinOn (s := S) ⟨x0, hx0S⟩ hS_cont
  have hxStarQ : xStar ∈ Q := hxStarS.1
  have hxStarMinQ : IsMinOn f Q xStar := by
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxStarMinS hyS
    · have hy_gt : f x0 < f y := by
        refine lt_of_not_ge ?_
        intro hy_le
        apply hyS
        exact ⟨hyQ, hy_le⟩
      have hxStar_le_x0 : f xStar ≤ f x0 := hxStarMinS hx0S
      exact le_trans hxStar_le_x0 hy_gt.le
  refine ⟨xStar, ?_, ?_⟩
  · exact ⟨hxStarQ, hxStarMinQ⟩
  · intro y hy
    exact (hstrong.strictConvexOn hν).eq_of_isMinOn hy.2 hxStarMinQ hy.1 hxStarQ

end FiniteDimensional

section InnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {p : Seminorm ℝ E} {μ : ℝ} {Q : Set E} {f : E → ℝ}

omit [CompleteSpace E] in
/-- Helper for Definition 2.14: subtracting the fixed quadratic correction from the restriction of
`f` to the segment from `x` to `y` produces a convex one-variable function on `[0,1]`. -/
-- Proof sketch: apply the strong-convexity inequality to two points on the segment, rewrite the
-- segment difference as `(s - t) • (y - x)`, and absorb the correction with the scalar identity
-- for weighted squares.
lemma strongConvexOnWith_segment_aux_convexOn
    (hf : StrongConvexOnWith p μ Q f) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t ↦
        f (AffineMap.lineMap x y t) - ((μ / 2) * (p (y - x)) ^ (2 : ℕ)) * t ^ (2 : ℕ)) := by
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro s hs t ht a b ha hb hab
  let seg : ℝ → E := AffineMap.lineMap x y
  let c : ℝ := (μ / 2) * (p (y - x)) ^ (2 : ℕ)
  have hseg_maps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := hf.1.mapsTo_lineMap hx hy
  have hsQ : seg s ∈ Q := hseg_maps hs
  have htQ : seg t ∈ Q := hseg_maps ht
  have hstrong := hf.2.2 hsQ htQ ha hb hab
  have hseg_combo : seg (a * s + b * t) = a • seg s + b • seg t := by
    obtain rfl := eq_sub_of_add_eq hab
    simp [seg, AffineMap.lineMap_apply_module, smul_add, add_smul, smul_smul]
    module
  have hseg_sub : seg s - seg t = (s - t) • (y - x) := by
    simp [seg, AffineMap.lineMap_apply_module', sub_eq_add_neg]
    module
  have hpseg :
      (p (seg s - seg t)) ^ (2 : ℕ) = (s - t) ^ (2 : ℕ) * (p (y - x)) ^ (2 : ℕ) := by
    rw [hseg_sub, map_smul_eq_mul]
    rw [Real.norm_eq_abs, mul_pow, sq_abs]
  -- The quadratic correction is chosen so that the strong-convexity penalty becomes exactly the
  -- missing Jensen correction for `t ↦ c * t^2`.
  calc
    f (AffineMap.lineMap x y (a * s + b * t)) - c * (a * s + b * t) ^ (2 : ℕ)
        = f (seg (a * s + b * t)) - c * (a * s + b * t) ^ (2 : ℕ) := by
            rfl
    _ = f (a • seg s + b • seg t) - c * (a * s + b * t) ^ (2 : ℕ) := by
          rw [hseg_combo]
    _ ≤ a • f (seg s) + b • f (seg t) -
          a * b * ((μ / 2) * (p (seg s - seg t)) ^ (2 : ℕ)) -
          c * (a * s + b * t) ^ (2 : ℕ) := by
            gcongr
    _ = a * f (seg s) + b * f (seg t) -
          a * b * (c * (s - t) ^ (2 : ℕ)) -
          c * (a * s + b * t) ^ (2 : ℕ) := by
            rw [hpseg]
            simp [c, mul_assoc, mul_left_comm, mul_comm]
    _ = a * (f (seg s) - c * s ^ (2 : ℕ)) + b * (f (seg t) - c * t ^ (2 : ℕ)) := by
          obtain rfl := eq_sub_of_add_eq hab
          ring
    _ = a • (f (seg s) - c * s ^ (2 : ℕ)) + b • (f (seg t) - c * t ^ (2 : ℕ)) := by
          simp [smul_eq_mul]

/-- If `f` is strongly convex on `Q` and is ambiently differentiable at the base point `x ∈ Q`,
then the tangent plane at `x` is a quadratic lower bound on `Q`. -/
-- Proof sketch: restrict the strong-convexity inequality to the segment
-- `((1 - t) • x + t • y)`, subtract the fixed quadratic correction to get a convex auxiliary
-- function on `[0,1]`, and apply the Chapter 2 lower-tangent theorem at `t = 0`.
theorem StrongConvexOnWith.lower_tangent_quadratic
    (hf : StrongConvexOnWith p μ Q f) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    (hgrad : HasGradientAt f (∇ f x) x) :
    f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2 := by
  let seg : ℝ → E := AffineMap.lineMap x y
  let c : ℝ := (μ / 2) * (p (y - x)) ^ (2 : ℕ)
  let φ : ℝ → ℝ := fun t ↦ f (seg t) - c * t ^ (2 : ℕ)
  have hseg_maps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := hf.1.mapsTo_lineMap hx hy
  -- Route correction: the tangent argument closes cleanly once the corrected segment function is
  -- treated as a one-variable convex function on `[0,1]`.
  have hφ_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
    simpa [φ, seg, c] using strongConvexOnWith_segment_aux_convexOn hf hx hy
  have hcomp_deriv :
      HasDerivWithinAt (fun t : ℝ ↦ f (seg t)) (inner ℝ (∇ f x) (y - x))
        (Set.Icc (0 : ℝ) 1) 0 := by
    -- Compose the ambient derivative of `f` at `x` with the segment parameterization.
    simpa [seg] using
      hgrad.hasFDerivAt.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hseg_maps (AffineMap.lineMap_apply_zero x y).symm
  have hquad_deriv :
      HasDerivWithinAt (fun t : ℝ ↦ c * t ^ (2 : ℕ)) 0 (Set.Icc (0 : ℝ) 1) 0 := by
    -- The quadratic correction has zero derivative at the left endpoint.
    simpa using (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul c).hasDerivWithinAt
  have hφ_deriv :
      HasDerivWithinAt φ (inner ℝ (∇ f x) (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ] using hcomp_deriv.sub hquad_deriv
  have hφ_grad :
      HasGradientWithinAt φ (inner ℝ (∇ f x) (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    rw [hasGradientWithinAt_iff_hasFDerivWithinAt]
    simpa using hφ_deriv.hasFDerivWithinAt
  have htangent :=
    hφ_conv.lower_tangent_plane_of_hasGradientWithinAt (0 : ℝ) (by simp)
      (inner ℝ (∇ f x) (y - x)) hφ_grad 1 (by simp)
  have hφ0 : φ 0 = f x := by
    simp [φ, seg, c]
  have hφ1 : φ 1 = f y - c := by
    simp [φ, seg, c]
  have hinner_one :
      inner ℝ (inner ℝ (∇ f x) (y - x)) (1 : ℝ) = inner ℝ (∇ f x) (y - x) := by
    have hmul : inner ℝ (inner ℝ (∇ f x) (y - x)) (1 : ℝ) =
        (1 : ℝ) * inner ℝ (∇ f x) (y - x) := by
      exact RCLike.inner_apply _ _
    simpa using hmul
  have htangent' : f y - c ≥ f x + inner ℝ (∇ f x) (y - x) := by
    simpa [hφ0, hφ1, hinner_one] using htangent
  have hresult : f y ≥ f x + inner ℝ (∇ f x) (y - x) + c := by
    linarith
  simpa [c] using hresult

/-- The owner lower-tangent inequality only needs an explicit gradient witness at the base point.
-/
-- Proof sketch: rewrite the canonical gradient `∇ f x` appearing in
-- `lower_tangent_quadratic` using `hgrad.gradient`.
theorem StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt
    (hf : StrongConvexOnWith p μ Q f) {x y g : E} (hx : x ∈ Q) (hy : y ∈ Q)
    (hgrad : HasGradientAt f g x) :
    f y ≥ f x + inner ℝ g (y - x) + (μ / 2) * (p (y - x)) ^ 2 := by
  -- Replace the canonical gradient by the explicit witness supplied by `HasGradientAt`.
  simpa [hgrad.gradient] using
    (StrongConvexOnWith.lower_tangent_quadratic hf hx hy
      (by simpa [hgrad.gradient] using hgrad))

namespace StrongConvexOn

/-- The ambient-norm owner `StrongConvexOn` gives the same quadratic lower tangent inequality
under an explicit gradient witness, without introducing a separate local wrapper API. -/
theorem lower_tangent_quadratic_of_hasGradientAt
    (hf : StrongConvexOn Q μ f) {x y g : E} (hx : x ∈ Q) (hy : y ∈ Q)
    (hgrad : HasGradientAt f g x) :
    f y ≥ f x + inner ℝ g (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let h : E → ℝ := fun u ↦ f u - (μ / 2) * ‖u‖ ^ (2 : ℕ)
  have hconv : ConvexOn ℝ Q h := by
    simpa [h] using (strongConvexOn_iff_convex.mp hf)
  have hnormSq :
      HasFDerivAt (fun u : E ↦ ‖u‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hquad :
      HasGradientAt (fun u : E ↦ (μ / 2) * ‖u‖ ^ (2 : ℕ)) (μ • x) x := by
    have hsmul :
        HasFDerivAt (fun u : E ↦ (μ / 2) * ‖u‖ ^ (2 : ℕ))
          ((μ / 2) • (2 • innerSL ℝ x)) x := by
      simpa [smul_eq_mul] using hnormSq.const_smul (μ / 2)
    have hlin :
        ((μ / 2) • (2 • innerSL ℝ x)) =
          InnerProductSpace.toDual ℝ E (μ • x) := by
      ext u
      simp [InnerProductSpace.toDual_apply_apply, two_smul]
      ring
    have hsmul' :
        HasFDerivAt (fun u : E ↦ (μ / 2) * ‖u‖ ^ (2 : ℕ))
          (InnerProductSpace.toDual ℝ E (μ • x)) x := by
      exact hlin ▸ hsmul
    convert hsmul'.hasGradientAt using 1
    all_goals simp
  have hgrad_h : HasGradientAt h (g - μ • x) x := by
    simpa [h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hgrad.hasFDerivAt.sub hquad.hasFDerivAt).hasGradientAt
  have hgrad_h_within : HasGradientWithinAt h (g - μ • x) Q x := by
    convert
      (hgrad_h.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt :
        HasGradientWithinAt h _ Q x) using 1
    simp
  have htangent :
      h y ≥ h x + inner ℝ (g - μ • x) (y - x) := by
    exact hconv.lower_tangent_plane_of_hasGradientWithinAt x hx (g - μ • x)
      hgrad_h_within y hy
  have hshifted :
      f y - (μ / 2) * ‖y‖ ^ (2 : ℕ) ≥
        f x - (μ / 2) * ‖x‖ ^ (2 : ℕ) +
          inner ℝ g (y - x) - μ * inner ℝ x (y - x) := by
    simpa [h, sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_smul_left, add_assoc,
      add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using htangent
  have hinner : inner ℝ x (y - x) = inner ℝ x y - ‖x‖ ^ (2 : ℕ) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have hnorm :
      ‖y - x‖ ^ (2 : ℕ) = ‖y‖ ^ (2 : ℕ) - 2 * inner ℝ x y + ‖x‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hbound :
      f y ≥
        f x - (μ / 2) * ‖x‖ ^ (2 : ℕ) +
          (μ / 2) * ‖y‖ ^ (2 : ℕ) +
          inner ℝ g (y - x) - μ * inner ℝ x (y - x) := by
    linarith
  calc
    f y ≥
        f x - (μ / 2) * ‖x‖ ^ (2 : ℕ) +
          (μ / 2) * ‖y‖ ^ (2 : ℕ) +
          inner ℝ g (y - x) - μ * inner ℝ x (y - x) := hbound
    _ = f x + inner ℝ g (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      rw [hinner, hnorm]
      ring

end StrongConvexOn

end InnerProduct

/-! ### Lemma_2_14 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 2.14 lies in the real-inner-product projection domain.

Sampled owner-style declarations:
* `IsProjectionPointOn Q y p` in `Chap07/Definition_7_3`, the owner predicate for projection data;
* `IsProjectionPointOn.isMinOn` in `Definition_2_33`, the minimizing-property bridge;
* `IsProjectionPointOn.inner_sub_nonneg` in `Lemma_2_13`, the projection variational inequality;
* `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the chosen-point bridge already
  available upstream.

Source/core/bridge triage:
* source-facing: the Pythagorean inequality for a projection point onto a convex set;
* core/canonical: `IsProjectionPointOn Q y p`;
* bridge/view: specializing from the chosen `euclideanProjection` to the owner predicate via
  `euclideanProjection_isProjectionPointOn`.

Primitive data:
* the convex set `Q`, ambient point `y`, projection point `p`, and feasible point `x`.

Derived API:
* the variational inequality `IsProjectionPointOn.inner_sub_nonneg`.

Accordingly, this file keeps only the owner-level theorem. The chosen Euclidean-projection
specialization is already recovered canonically by combining this theorem with
`euclideanProjection_isProjectionPointOn`, and the Euclidean-space statement is just its
specialization to `ℝⁿ`, so no parallel local corollary is kept. -/

namespace IsProjectionPointOn

/-- Lemma 2.14: every feasible point of a convex set in a real inner product space lies no closer
to an ambient point `y` than a projection point `p` does, with the usual Pythagorean
squared-distance decomposition. -/
-- Proof sketch: write `x - y = (x - p) + (p - y)`. The projection variational inequality gives
-- `0 ≤ ⟪x - p, p - y⟫`, and `norm_add_sq_real` then expands `‖x - y‖²` as the left-hand side plus
-- the nonnegative mixed term `2 ⟪x - p, p - y⟫`.
theorem pythagorean_ineq
    {Q : Set E} (hQ_convex : Convex ℝ Q) {y p x : E}
    (hp : IsProjectionPointOn Q y p) (hx : x ∈ Q) :
    ‖x - p‖ ^ 2 + ‖p - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hinner : 0 ≤ inner ℝ (x - p) (p - y) := by
    simpa [real_inner_comm] using hp.inner_sub_nonneg hQ_convex hx
  calc
    ‖x - p‖ ^ 2 + ‖p - y‖ ^ 2
        ≤ ‖x - p‖ ^ 2 + 2 * inner ℝ (x - p) (p - y) + ‖p - y‖ ^ 2 := by
          nlinarith
    _ = ‖(x - p) + (p - y)‖ ^ 2 := by rw [norm_add_sq_real]
    _ = ‖x - y‖ ^ 2 := by abel_nf

end IsProjectionPointOn

end

/-! ### Proposition_2_14 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Proposition 2.14 lies in the regularized minimization owner domain on a real inner-product space.

Sampled owner-style declarations in this domain:
* `quadraticallyRegularizedObjective` in `Definition_1_4_17`, the chapter owner of the centered
  quadratic regularization;
* mathlib `strongConvexOn_iff_convex`, the canonical owner criterion for strong convexity in a real
  inner-product space;
* `StrongConvexOn.add_convexOn` in `Proposition_2_3`, the bridge adding a convex perturbation to a
  strongly convex owner;
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Theorem_2_30`, the canonical quadratic-growth
  consequence at a minimizer.

Best owner abstraction:
* source-facing: Proposition 2.14, the regularized minimizer estimate;
* core/canonical: `quadraticallyRegularizedObjective f δ x0` together with whole-space
  `StrongConvexOn Set.univ δ` and `IsMinOn`;
* bridge/view: the Euclidean `ℝⁿ` specialization obtained by instantiating
  `E := EuclideanSpace ℝ (Fin n)`.

Primitive data:
* the convex objective `f`,
* the base point `x0`,
* the regularization parameter `δ > 0`,
* a minimizer `xStar` of `f`,
* a minimizer `xDeltaStar` of `quadraticallyRegularizedObjective f δ x0`.

Derived API for the proof:
* `quadraticallyRegularizedObjective_zero_strongConvexOn`, the owner strong-convexity theorem for
  the centered quadratic penalty;
* `StrongConvexOn.add_convexOn` upgrades `quadraticallyRegularizedObjective f δ x0` to a
  `δ`-strongly convex objective on `Set.univ`;
* `StrongConvexOn.quadratic_growth_of_isMinOn` gives the quadratic growth estimate at the
  regularized minimizer.

No parallel public wrapper around that owner strong-convexity API is introduced here.
-/

/-- Proposition 2.14: if `xStar` minimizes a convex function `f` on a real inner-product space and
`xDeltaStar`
minimizes the quadratically regularized objective
`x ↦ f x + (δ / 2) ‖x - x₀‖²` with `δ > 0`, then the regularized minimizer satisfies the squared
distance contraction
`‖xDeltaStar - x₀‖² + ‖xDeltaStar - xStar‖² ≤ ‖x₀ - xStar‖²`. The textbook `ℝⁿ` statement is the
Euclidean specialization. -/
-- Proof sketch: the centered quadratic penalty is `δ`-strongly convex, so adding it to the
-- convex objective `f` makes `quadraticallyRegularizedObjective f δ x0` `δ`-strongly convex on
-- `Set.univ`. Applying the owner quadratic-growth theorem at the minimizer `xDeltaStar` and then
-- comparing the objective values of `xStar` and `xDeltaStar` yields the displayed squared-distance
-- inequality.
theorem regularized_minimizer_sqdist_add_sqdist_le_sqdist
    (f : E → ℝ) (hf_conv : ConvexOn ℝ Set.univ f)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 xDeltaStar : E) {δ : ℝ} (hδ : 0 < δ)
    (hxDeltaStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xDeltaStar) :
    ‖xDeltaStar - x0‖ ^ 2 + ‖xDeltaStar - xStar‖ ^ 2 ≤ ‖x0 - xStar‖ ^ 2 := by
  have hsum :
      f + quadraticallyRegularizedObjective (fun _ : E ↦ 0) δ x0 =
        quadraticallyRegularizedObjective f δ x0 := by
    funext x
    simp [quadraticallyRegularizedObjective_apply]
  have hstrong : StrongConvexOn Set.univ δ (quadraticallyRegularizedObjective f δ x0) := by
    rw [← hsum]
    exact
      (quadraticallyRegularizedObjective_zero_strongConvexOn x0 δ).add_convexOn hf_conv
  have hquad := StrongConvexOn.quadratic_growth_of_isMinOn hstrong hxDeltaStar xStar
  have hmin : f xStar ≤ f xDeltaStar := hxStar (by simp)
  have hquad' :
      f xStar + (δ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) ≥
        f xDeltaStar + (δ / 2) * ‖xDeltaStar - xStar‖ ^ (2 : ℕ) +
          (δ / 2) * ‖xDeltaStar - x0‖ ^ (2 : ℕ) := by
    simpa [quadraticallyRegularizedObjective_apply, add_assoc, add_left_comm, add_comm,
      norm_sub_rev xStar xDeltaStar, norm_sub_rev xStar x0] using hquad
  nlinarith [hδ, hmin, hquad']

/-- If the reference radius `R₀` dominates the distance from `x₀` to a minimizer `xStar`, then
the minimizer of the quadratically regularized objective lies in the closed ball of radius `R₀`
centered at `x₀`. -/
-- Proof sketch: apply
-- `regularized_minimizer_sqdist_add_sqdist_le_sqdist` to get
-- `‖xDeltaStar - x₀‖² ≤ ‖x₀ - xStar‖²`, combine this with `‖x₀ - xStar‖ ≤ R₀`, and take square
-- roots using nonnegativity of norms.
theorem regularized_minimizer_norm_le_of_norm_le
    (f : E → ℝ) (hf_conv : ConvexOn ℝ Set.univ f)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 xDeltaStar : E) {δ : ℝ} (hδ : 0 < δ)
    (hxDeltaStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xDeltaStar)
    {R0 : ℝ} (hR0 : ‖x0 - xStar‖ ≤ R0) :
    ‖xDeltaStar - x0‖ ≤ R0 := by
  have hsq : ‖xDeltaStar - x0‖ ^ 2 ≤ ‖x0 - xStar‖ ^ 2 := by
    have hsq_add :=
      regularized_minimizer_sqdist_add_sqdist_le_sqdist
        f hf_conv xStar hxStar x0 xDeltaStar hδ hxDeltaStar
    nlinarith [sq_nonneg ‖xDeltaStar - xStar‖]
  have hR0_nonneg : 0 ≤ R0 := le_trans (norm_nonneg _) hR0
  have hx0_sq : ‖x0 - xStar‖ ^ 2 ≤ R0 ^ 2 := by
    simpa [pow_two] using (sq_le_sq₀ (norm_nonneg _) hR0_nonneg).2 hR0
  have hDelta_sq : ‖xDeltaStar - x0‖ ^ 2 ≤ R0 ^ 2 := le_trans hsq hx0_sq
  simpa [pow_two] using
    (sq_le_sq₀ (norm_nonneg _) hR0_nonneg).1 (by simpa [pow_two] using hDelta_sq)

/-! ### Text_2_14 (from Chap02) -/
open scoped SmoothConvex

noncomputable section

variable {n : ℕ}

/- Text 2.14 is organized around the owner objective `quadraticHardInstanceFamily L k` and its
canonical stationary point `quadraticHardInstanceStationaryPoint k` from Text 2.13.

Sampled owner-style declarations in this domain:
- `quadraticHardInstanceFamily_mem_smooth_convex_objective` in `Text_2_11`
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in `Definition_2_20`

Primitive data:
- the hard-instance objective `quadraticHardInstanceFamily (L : ℝ) k`.

Derived API:
- the canonical stationary point is a global minimizer;
- the canonical whole-space owner problem on `Set.univ`;
- evaluating the objective at that minimizer gives the closed-form optimal value.

This file therefore keeps the source-facing minimizer and optimal-value statements, but derives
them through the existing smooth-convex owner abstraction and the Chapter 1/2 optimal-value owner
API rather than a parallel local `sInf`-based value wrapper. The raw infimum-of-range identity is
kept only as a companion bridge.
-/

/-- The canonical stationary point of the quadratic hard instance is a global minimizer of the
owner objective `quadraticHardInstanceFamily (L : ℝ) k`. -/
-- Proof sketch: combine
-- `quadraticHardInstanceFamily_mem_smooth_convex_objective` with
-- `quadraticHardInstanceStationaryPoint_hasGradientAt_zero`; convex differentiable functions on
-- `Set.univ` are globally minimized by specializing the constrained first-order owner theorem to
-- the zero-gradient case.
theorem quadraticHardInstanceStationaryPoint_isMinOn
    (L : NNReal) (k : Fin n) :
    IsMinOn (quadraticHardInstanceFamily (L : ℝ) k) Set.univ
      (quadraticHardInstanceStationaryPoint k) := by
  have hf := quadraticHardInstanceFamily_mem_smooth_convex_objective L k
  have hstat :
      HasGradientAt (quadraticHardInstanceFamily (L : ℝ) k) 0
        (quadraticHardInstanceStationaryPoint k) :=
    quadraticHardInstanceStationaryPoint_hasGradientAt_zero (L : ℝ) k
  refine (hf.convexOn.isMinOn_iff_variational_inequality_of_hasGradientAt (by simp) hstat).2 ?_
  intro x hx
  simp

private theorem quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction
    (L : NNReal) (k : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k) =
      smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1)
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) := by
  simp [quadraticHardInstanceFamily, quadraticHardInstanceStationaryPoint]
  congr
  ext i
  change (quadraticHardInstanceStationaryPoint k) (Fin.castLE (Nat.succ_le_of_lt k.2) i) = _
  have hi : Fin.castLE (Nat.succ_le_of_lt k.2) i ≤ k :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.2)
  simp [quadraticHardInstanceStationaryPoint_apply, hi]
  ring

/-- Helper for Text 2.14: splitting a path-tridiagonal matrix entry into diagonal, forward, and
backward neighbor contributions gives the scalar identity used to read off each row. -/
private theorem pathTridiagonal_entry_mul_eq_diag_sub_neighbors
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    pathTridiagonalMatrix (Nat.succPNat m) i j * y j =
      (if i = j then 2 * y j else 0) -
      (if (i : ℕ) + 1 = (j : ℕ) then y j else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then y j else 0) := by
  -- Split the matrix entry into the three source-proof cases: diagonal, forward edge, and
  -- backward edge.
  by_cases hij : i = j
  · subst hij
    simp [pathTridiagonalMatrix_apply]
  · by_cases hnext : (i : ℕ) + 1 = (j : ℕ)
    · have hprev : ¬ (j : ℕ) + 1 = (i : ℕ) := by
        omega
      simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
    · by_cases hprev : (j : ℕ) + 1 = (i : ℕ)
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]

/-- Helper for Text 2.14: the first row of the path tridiagonal system is `2 y₀ - y₁`. -/
private theorem pathTridiagonal_mulVec_apply_head
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) 0 =
      2 * y 0 - y ⟨1, by omega⟩ := by
  -- Expand the first row and isolate the only two nonzero contributions.
  change ∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) 0 j * y j = _
  rw [show (∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) 0 j * y j) =
      (∑ j : Fin (k + 2), ((if (0 : Fin (k + 2)) = j then 2 * y j else 0) -
        (if (1 : ℕ) = (j : ℕ) then y j else 0) -
        (if (j : ℕ) + 1 = (0 : ℕ) then y j else 0))) by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa using pathTridiagonal_entry_mul_eq_diag_sub_neighbors y 0 j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdiag : (∑ j : Fin (k + 2), if (0 : Fin (k + 2)) = j then 2 * y j else 0) = 2 * y 0 := by
    rw [Fintype.sum_eq_single 0]
    · simp
    · intro j hj
      have hneq : ¬ (0 : Fin (k + 2)) = j := by
        simpa using hj.symm
      simp [hneq]
  have hnext : (∑ j : Fin (k + 2), if (1 : ℕ) = (j : ℕ) then y j else 0) = y ⟨1, by omega⟩ := by
    rw [Fintype.sum_eq_single ⟨1, by omega⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ 1 := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq : ¬ (1 : ℕ) = (j : ℕ) := by
        simpa [eq_comm] using hne
      simp [hneq]
  have hprev : (∑ j : Fin (k + 2), if (j : ℕ) + 1 = (0 : ℕ) then y j else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp
  -- The remaining scalar expression is exactly the head equation.
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.14: every interior row of the path tridiagonal system is
`2 yᵢ - yᵢ₋₁ - yᵢ₊₁`. -/
private theorem pathTridiagonal_mulVec_apply_middle
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) (t : ℕ)
    (ht0 : t < k + 2) (ht1 : t + 1 < k + 2) (ht2 : t + 2 < k + 2) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) ⟨t + 1, ht1⟩ =
      2 * y ⟨t + 1, ht1⟩ - y ⟨t, ht0⟩ - y ⟨t + 2, ht2⟩ := by
  -- Expand an interior row and keep only the diagonal and two adjacent entries.
  change ∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) ⟨t + 1, ht1⟩ j * y j = _
  rw [show (∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) ⟨t + 1, ht1⟩ j * y j) =
      (∑ j : Fin (k + 2), ((if (⟨t + 1, ht1⟩ : Fin (k + 2)) = j then 2 * y j else 0) -
        (if t + 2 = (j : ℕ) then y j else 0) -
        (if (j : ℕ) + 1 = t + 1 then y j else 0))) by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa using pathTridiagonal_entry_mul_eq_diag_sub_neighbors y ⟨t + 1, ht1⟩ j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin (k + 2), if (⟨t + 1, ht1⟩ : Fin (k + 2)) = j then 2 * y j else 0) =
        2 * y ⟨t + 1, ht1⟩ := by
    rw [Fintype.sum_eq_single ⟨t + 1, ht1⟩]
    · simp
    · intro j hj
      have hneq : ¬ (⟨t + 1, ht1⟩ : Fin (k + 2)) = j := by
        simpa using hj.symm
      simp [hneq]
  have hnext : (∑ j : Fin (k + 2), if t + 2 = (j : ℕ) then y j else 0) = y ⟨t + 2, ht2⟩ := by
    rw [Fintype.sum_eq_single ⟨t + 2, ht2⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ t + 2 := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq : ¬ t + 2 = (j : ℕ) := by
        simpa [eq_comm] using hne
      simp [hneq]
  have hprev : (∑ j : Fin (k + 2), if (j : ℕ) + 1 = t + 1 then y j else 0) = y ⟨t, ht0⟩ := by
    rw [Fintype.sum_eq_single ⟨t, ht0⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ t := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq' : ¬ (j : ℕ) = t := hne
      simp [hneq']
  -- The three surviving terms reconstruct the middle-row recurrence.
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.14: the last row of the path tridiagonal system is `2 y_k - y_{k-1}`. -/
private theorem pathTridiagonal_mulVec_apply_tail
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) (Fin.last (k + 1)) =
      2 * y (Fin.last (k + 1)) - y ⟨k, by omega⟩ := by
  -- Expand the last row and isolate the diagonal and predecessor terms.
  change ∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) (Fin.last (k + 1)) j * y j = _
  rw [show (∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) (Fin.last (k + 1)) j * y j) =
      (∑ j : Fin (k + 2), ((if Fin.last (k + 1) = j then 2 * y j else 0) -
        (if k + 2 = (j : ℕ) then y j else 0) -
        (if (j : ℕ) + 1 = k + 1 then y j else 0))) by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa [Fin.val_last] using
        pathTridiagonal_entry_mul_eq_diag_sub_neighbors y (Fin.last (k + 1)) j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin (k + 2), if Fin.last (k + 1) = j then 2 * y j else 0) =
        2 * y (Fin.last (k + 1)) := by
    rw [Fintype.sum_eq_single (Fin.last (k + 1))]
    · simp
    · intro j hj
      have hneq : ¬ Fin.last (k + 1) = j := by
        simpa using hj.symm
      simp [hneq]
  have hnext : (∑ j : Fin (k + 2), if k + 2 = (j : ℕ) then y j else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hne : ¬ k + 2 = (j : ℕ) := by
      exact Ne.symm (Nat.ne_of_lt j.2)
    simp [hne]
  have hprev : (∑ j : Fin (k + 2), if (j : ℕ) + 1 = k + 1 then y j else 0) = y ⟨k, by omega⟩ := by
    rw [Fintype.sum_eq_single ⟨k, by omega⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ k := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq' : ¬ (j : ℕ) = k := hne
      simp [hneq']
  -- This is exactly the tail boundary equation from the source tridiagonal system.
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.14: the affine-profile stationary point solves the tridiagonal system
`A_k y = e₁`. -/
private theorem pathTridiagonal_mulVec_stationaryPoint
    (k : ℕ) :
    Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k))
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) =
        (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)).ofLp := by
  cases' k with k
  · ext i
    fin_cases i
    -- In dimension one, the matrix equation is a direct scalar calculation.
    simp [Matrix.mulVec, dotProduct, pathTridiagonalMatrix_apply,
      smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
    norm_num
  · ext i
    by_cases hi0 : i = 0
    · subst hi0
      -- The head row realizes the `2 y₀ - y₁ = 1` equation.
      rw [pathTridiagonal_mulVec_apply_head]
      simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
      field_simp
      simp
      ring_nf
      split_ifs with hzero
      · simp
      · exfalso
        exact hzero rfl
    · by_cases hilast : i = Fin.last (k + 1)
      · subst hilast
        -- The tail row realizes the boundary equation `2 y_k - y_{k-1} = 0`.
        rw [pathTridiagonal_mulVec_apply_tail]
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
        field_simp
        ring_nf
      · let t := i.1 - 1
        have hi_pos' : 1 ≤ i.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
          intro hzero
          apply hi0
          ext
          simpa using hzero))
        have hi_le_last : i.1 ≤ k + 1 := Nat.le_of_lt_succ i.2
        have hi_ne_last_val : i.1 ≠ k + 1 := by
          intro hi_last
          apply hilast
          ext
          simpa [Fin.val_last] using hi_last
        have hi_lt_last : i.1 < k + 1 := lt_of_le_of_ne hi_le_last hi_ne_last_val
        have ht0 : t < k + 2 := by
          dsimp [t]
          omega
        have ht1 : t + 1 < k + 2 := by
          dsimp [t]
          omega
        have ht2 : t + 2 < k + 2 := by
          dsimp [t]
          omega
        have hi_eq : i = ⟨t + 1, ht1⟩ := by
          ext
          dsimp [t]
          rw [Nat.sub_add_cancel hi_pos']
        -- Every interior row realizes the affine-profile recurrence.
        rw [hi_eq, pathTridiagonal_mulVec_apply_middle k _ t ht0 ht1 ht2]
        have hne0 : (⟨t + 1, ht1⟩ : Fin (k + 2)) ≠ 0 := by
          intro hzero
          apply hi0
          calc
            i = ⟨t + 1, ht1⟩ := hi_eq
            _ = 0 := hzero
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single, hne0]
        field_simp
        ring_nf

/-- Helper for Text 2.14: after substituting `A_k x̄ = e₁`, the quadratic term collapses to the
head coordinate of the affine profile. -/
private theorem smoothLowerBoundFunctionStationaryPoint_dotProduct_mulVec_eq_head
    (k : Fin n) :
    dotProduct
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1))
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1))
          (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1))) =
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) 0 := by
  -- Replace the residual by `e₁`; then only the head coordinate survives in the dot product.
  rw [pathTridiagonal_mulVec_stationaryPoint k.1]
  change
    ∑ x : Fin (Nat.succPNat k.1),
        smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1) x *
          (EuclideanSpace.single (0 : Fin (Nat.succPNat k.1)) (1 : ℝ)).ofLp x =
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) 0
  rw [Fintype.sum_eq_single 0]
  · have hsingle0 :
        (EuclideanSpace.single (0 : Fin (Nat.succPNat k.1)) (1 : ℝ)).ofLp 0 = 1 := by
        simp [EuclideanSpace.single]
    rw [hsingle0]
    ring
  · intro j hj
    have hj0 : j ≠ (0 : Fin (Nat.succPNat k.1)) := by
      simpa [eq_comm] using hj
    have hsinglej :
        (EuclideanSpace.single (0 : Fin (Nat.succPNat k.1)) (1 : ℝ)).ofLp j = 0 := by
      change Function.update (fun _ : Fin (Nat.succPNat k.1) ↦ (0 : ℝ))
          (0 : Fin (Nat.succPNat k.1)) 1 j = 0
      rw [Function.update_of_ne hj0]
    rw [hsinglej]
    ring

/-- Evaluating the quadratic hard instance at its canonical stationary point gives the closed-form
value from Text 2.14. -/
-- Proof sketch: first pass from the ambient hard-instance owner to the core prefix owner
-- `smoothLowerBoundFunction` using
-- `quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction`; then evaluate the
-- prefix quadratic at `smoothLowerBoundFunctionStationaryPoint` using
-- `smoothLowerBoundFunction_apply` and the explicit affine-profile coordinates.
theorem quadraticHardInstanceFamily_stationaryPoint_value
    (L : NNReal) (k : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k) =
      ((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) := by
  -- Rewrite the ambient hard-instance value as the prefix quadratic at the affine-profile point.
  rw [quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction]
  rw [smoothLowerBoundFunction_apply]
  -- Collapse the quadratic term using the source linear system `A_k x̄ = e₁`.
  rw [smoothLowerBoundFunctionStationaryPoint_dotProduct_mulVec_eq_head]
  have hhead :
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) 0 =
        1 - 1 / (((k.1 + 2 : ℕ) : ℝ)) := by
    -- The head coordinate is the first term of the explicit affine profile.
    simp [smoothLowerBoundFunctionStationaryPoint_apply]
    ring
  -- Substitute the explicit head coordinate and simplify the scalar expression.
  rw [hhead]
  ring

/-- Text 2.14: for the canonical smoothness parameter `L : NNReal`, the optimal value of the
quadratic hard-instance objective `f_k` is `((L : ℝ) / 8) * (-1 + 1 / (k + 1))`; in the file's
zero-based `Fin` indexing, `k : Fin n` represents the textbook index `k + 1`, so the denominator
becomes `k.1 + 2`. -/
-- Proof sketch: package `quadraticHardInstanceFamily (L : ℝ) k` as the canonical unconstrained
-- owner problem on `Set.univ`, apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` at the minimizing stationary
-- point, and then rewrite the attained value with
-- `quadraticHardInstanceFamily_stationaryPoint_value`.
theorem quadraticHardInstanceFamily_optimal_value
    (L : NNReal) (k : Fin n) :
    (SetConstrainedMinimizationProblem.mk Set.univ
      (quadraticHardInstanceFamily (L : ℝ) k)).optimalValue =
      ((((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) : ℝ) : EReal) := by
  calc
    (SetConstrainedMinimizationProblem.mk Set.univ
      (quadraticHardInstanceFamily (L : ℝ) k)).optimalValue =
        (quadraticHardInstanceFamily (L : ℝ) k
          (quadraticHardInstanceStationaryPoint k) : EReal) := by
            exact
              (SetConstrainedMinimizationProblem.mk Set.univ
                (quadraticHardInstanceFamily (L : ℝ) k)).optimalValue_eq_of_isMinOn
                  (by simp) (quadraticHardInstanceStationaryPoint_isMinOn L k)
    _ =
        ((((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) : ℝ) : EReal) := by
          rw [quadraticHardInstanceFamily_stationaryPoint_value L k]

/-- Companion bridge: the raw infimum of the range of the quadratic hard-instance objective is
the same closed-form value as the owner-level optimal value. -/
-- Proof sketch: use the source-facing minimizer theorem to obtain an attained infimum of the raw
-- range via `IsMinOn.isGLB`, then evaluate the objective at the stationary point.
theorem quadraticHardInstanceFamily_csInf_range
    (L : NNReal) (k : Fin n) :
    sInf (Set.range (quadraticHardInstanceFamily (L : ℝ) k)) =
      ((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) := by
  have hmin := quadraticHardInstanceStationaryPoint_isMinOn L k
  have hglb :
      IsGLB (Set.range (quadraticHardInstanceFamily (L : ℝ) k))
        (quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k)) := by
    simpa [Set.range] using hmin.isGLB (by simp)
  calc
    sInf (Set.range (quadraticHardInstanceFamily (L : ℝ) k)) =
        quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k) := by
          exact hglb.csInf_eq ⟨_, ⟨quadraticHardInstanceStationaryPoint k, rfl⟩⟩
    _ = ((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) :=
      quadraticHardInstanceFamily_stationaryPoint_value L k
