import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.Corollary_12_18
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap16.Proposition_16_38
import BauschkeLean.Chap16.Corollary_16_57
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section ToERealHelpers

variable {H : Type u} [NormedAddCommGroup H]

variable [InnerProductSpace ℝ H]

/-- A lower semicontinuous convex real-valued function becomes a member of `Γ₀(H)` after the
canonical coercion `toEReal`. -/
theorem toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ
    (f : H → ℝ) (hlsc : LowerSemicontinuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    f.toEReal ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    have h1ma : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have hsum : a + (1 - a) = 1 := by ring
    have hreal : f (a • x + (1 - a) • y) ≤ a • f x + (1 - a) • f y :=
      hconv.2 (by simp) (by simp) ha0 h1ma hsum
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a • f x + (1 - a) • f y : ℝ) : EReal)
    exact_mod_cast hreal
  · simpa [Function.comp] using
      continuous_coe_real_ereal.comp_lowerSemicontinuous hlsc
        (show Monotone ((↑) : ℝ → EReal) from by
          intro a b hab
          exact_mod_cast hab)

end ToERealHelpers

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Corollary 17 19: if an `]-∞,+∞]`-valued function has nonempty effective domain,
then its Fenchel conjugate never takes the value `-∞`. -/
theorem conjugate_ne_bot_of_effectiveDomain_nonempty
    {g : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain g).Nonempty) (u : H) :
    g.asEReal∗ u ≠ ⊥ := by
  have hproper : IsProper g.asEReal := by
    refine ⟨fun x ↦ ne_of_gt (g x).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  exact conjugate_ne_bot_of_isProper hproper u

/-- Helper for Corollary 17 19: the canonical `Γ₀(H)`-packaged Fenchel conjugate. -/
noncomputable abbrev gammaZeroConjugate
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨g.asEReal∗ u,
      bot_lt_iff_ne_bot.mpr (conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty u)⟩

/- Lean cannot infer the `Γ₀(H)` witness from `g` alone, so the packaged source-facing conjugate
keeps that witness explicit and writes the canonical `Γ₀(H)` Fenchel conjugate as `g∗[hg]`. -/
scoped notation:max g "∗[" hg "]" => gammaZeroConjugate g hg

omit [CompleteSpace H] in
/-- Helper for Corollary 17 19: coercing the packaged Fenchel conjugate back to `EReal` recovers
the raw Fenchel conjugate. -/
@[simp] theorem gammaZeroConjugate_apply
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (u : H) :
    (g∗[hg] u : EReal) = g.asEReal∗ u :=
  rfl

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 17 19: a `β`-Lipschitz real-valued function has recession function
bounded above by `β ‖·‖` after the canonical coercion to `]-∞,+∞]`. -/
lemma recessionFunction_toEReal_le_mul_norm_of_lipschitz
    (f : H → ℝ) (β : NNReal) (hLip : LipschitzWith β f)
    (hdom : (effectiveDomain f.toEReal).Nonempty) :
    ∀ y : H, (recessionFunction f.toEReal hdom y : EReal) ≤
      ((β : ℝ) * ‖y‖ : ℝ) := by
  intro y
  -- Unfold the recession function and bound each translated increment by the Lipschitz estimate.
  rw [recessionFunction_apply]
  refine sSup_le ?_
  rintro _ ⟨x, -, rfl⟩
  have hdist :
      dist (f (x + y)) (f x) ≤ (β : ℝ) * dist (x + y) x := by
    simpa using hLip.dist_le_mul (x + y) x
  have hnorm :
      ‖f (x + y) - f x‖ ≤ (β : ℝ) * ‖y‖ := by
    simpa [dist_eq_norm] using hdist
  have hreal :
      f (x + y) - f x ≤ (β : ℝ) * ‖y‖ := by
    exact le_trans (le_abs_self _) hnorm
  -- Recast the real inequality into `EReal` after identifying the increment term.
  change (((f (x + y) : ℝ) : EReal) - ((f x : ℝ) : EReal)) ≤
    (((β : ℝ) * ‖y‖ : ℝ) : EReal)
  rw [← EReal.coe_sub]
  exact_mod_cast hreal

omit [CompleteSpace H] in
/-- Helper for Corollary 17 19: a support function is bounded by `β ‖·‖` exactly when its set is
contained in the closed ball `B(0;β)`. -/
lemma supportFunction_le_mul_norm_iff_subset_closedBall
    (C : Set H) (β : NNReal) :
    (∀ y : H, σ[C] y ≤ ((β : ℝ) * ‖y‖ : ℝ)) ↔ C ⊆ Metric.closedBall (0 : H) β := by
  constructor
  · intro hsupport x hx
    -- Test the support-function bound at the point `x` itself to recover a norm estimate on `x`.
    have hnorm_sq_le : (((‖x‖ ^ 2 : ℝ) : EReal)) ≤ σ[C] x := by
      rw [supportFunction_eq_sSup_image]
      have hinner :
          (((⟪x, x⟫_ℝ : ℝ) : EReal)) ≤
            sSup ((fun y : H ↦ ((⟪y, x⟫_ℝ : ℝ) : EReal)) '' C) :=
        le_sSup ⟨x, hx, rfl⟩
      simpa [real_inner_self_eq_norm_sq] using hinner
    have hsq_bound :
        (((‖x‖ ^ 2 : ℝ) : EReal)) ≤ (((β : ℝ) * ‖x‖ : ℝ) : EReal) :=
      le_trans hnorm_sq_le (hsupport x)
    have hsq_bound_real : ‖x‖ ^ 2 ≤ (β : ℝ) * ‖x‖ := by
      exact_mod_cast hsq_bound
    have hnorm_le : ‖x‖ ≤ (β : ℝ) := by
      nlinarith [β.2, norm_nonneg x, hsq_bound_real]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le
  · intro hC
    -- The preexisting support-function bound applies once every point of `C` satisfies `‖x‖ ≤ β`.
    have hC_norm : ∀ x ∈ C, ‖x‖ ≤ (β : ℝ) := by
      intro x hx
      have hx_ball : x ∈ Metric.closedBall (0 : H) β := hC hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx_ball
    simpa using
      supportFunction_le_mul_norm_of_norm_bound
        (C := C) (R := (β : ℝ)) β.2 hC_norm

omit [CompleteSpace H] in
/-- Helper for Corollary 17 19: every subgradient of `f.toEReal` lies in the effective domain of
the packaged Fenchel conjugate. -/
lemma mem_effectiveDomain_gammaZeroConjugate_of_mem_range_subdifferential
    (f : H → ℝ) (hf : f.toEReal ∈ Γ₀(H)) {u : H}
    (hu : u ∈ SetValuedOperator.range (∂ f.toEReal)) :
    u ∈ effectiveDomain ((f.toEReal)∗[hf]) := by
  rw [SetValuedOperator.mem_range_iff] at hu
  rcases hu with ⟨x, hx_sub⟩
  have hupper :
      (f.toEReal.asEReal∗ u : EReal) ≤ (((⟪x, u⟫_ℝ - f x : ℝ) : EReal)) := by
    rw [conjugate_apply]
    refine iSup_le fun y ↦ ?_
    have hsub_y :
        (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (f x : EReal)) ≤ (f y : EReal) := by
      simpa [Function.toEReal_apply] using
        (mem_subdifferential_iff (f := f.toEReal) (x := x) (u := u)).1 hx_sub y
    have hsub_y_real : ⟪y - x, u⟫_ℝ + f x ≤ f y := by
      exact_mod_cast hsub_y
    have hterm_real : ⟪y, u⟫_ℝ - f y ≤ ⟪x, u⟫_ℝ - f x := by
      have hinner : ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
        simp [sub_eq_add_neg, inner_add_left]
      nlinarith [hsub_y_real, hinner]
    change (((⟪y, u⟫_ℝ - f y : ℝ) : EReal)) ≤ (((⟪x, u⟫_ℝ - f x : ℝ) : EReal))
    exact_mod_cast hterm_real
  have hlower :
      (((⟪x, u⟫_ℝ - f x : ℝ) : EReal)) ≤ (f.toEReal.asEReal∗ u : EReal) := by
    rw [conjugate_apply]
    exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal))) x
  rw [mem_effectiveDomain_iff]
  have hEq :
      (f.toEReal.asEReal∗ u : EReal) = (((⟪x, u⟫_ℝ - f x : ℝ) : EReal)) :=
    le_antisymm hupper hlower
  rw [gammaZeroConjugate_apply, hEq]
  exact EReal.coe_lt_top (⟪x, u⟫_ℝ - f x)

omit [CompleteSpace H] in
/-- Helper for Corollary 17 19: a recession bound forces every finite conjugate point into the
closed ball `B(0;β)`. -/
lemma mem_closedBall_of_recession_bound_of_mem_effectiveDomain_gammaZeroConjugate
    (f : H → ℝ) (β : NNReal) (hf : f.toEReal ∈ Γ₀(H))
    (hrec : ∀ y : H, (recessionFunction f.toEReal hf.2.nonempty y : EReal) ≤
      ((β : ℝ) * ‖y‖ : ℝ))
    {u : H} (hu : u ∈ effectiveDomain ((f.toEReal)∗[hf])) :
    u ∈ Metric.closedBall (0 : H) β := by
  have hu_top : (f.toEReal.asEReal∗ u : EReal) ≠ ⊤ := by
    have hu' : (((f.toEReal)∗[hf] u : Set.Ioi (⊥ : EReal)) : EReal) < ⊤ :=
      mem_effectiveDomain_iff.mp hu
    exact ne_of_lt <| by
      simpa [gammaZeroConjugate_apply] using hu'
  have hu_bot : (f.toEReal.asEReal∗ u : EReal) ≠ ⊥ :=
    conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty u
  have hnorm_sq_le_beta_real : ‖u‖ ^ 2 ≤ (β : ℝ) * ‖u‖ := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have happrox_conj :
        (((((f.toEReal.asEReal∗ u : EReal)).toReal - ε : ℝ) : EReal)) <
          (f.toEReal.asEReal∗ u : EReal) := by
      rw [← EReal.coe_toReal hu_top hu_bot]
      exact_mod_cast sub_lt_self (((f.toEReal.asEReal∗ u : EReal)).toReal) hε
    have happrox :
        (((((f.toEReal.asEReal∗ u : EReal)).toReal - ε : ℝ) : EReal)) <
          ⨆ x : H, (((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal)) := by
      simpa [conjugate_apply] using happrox_conj
    rcases lt_iSup_iff.mp happrox with ⟨x, hx⟩
    have hupper :
        ((((⟪x + u, u⟫_ℝ : ℝ) : EReal) - (f (x + u) : EReal))) ≤
          (f.toEReal.asEReal∗ u : EReal) := by
      rw [conjugate_apply]
      exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal))) (x + u)
    have hx_real : ((f.toEReal.asEReal∗ u : EReal)).toReal - ε < ⟪x, u⟫_ℝ - f x := by
      rw [← EReal.coe_toReal hu_top hu_bot] at hx
      exact_mod_cast hx
    have hupper_real : ⟪x + u, u⟫_ℝ - f (x + u) ≤ ((f.toEReal.asEReal∗ u : EReal)).toReal := by
      rw [← EReal.coe_toReal hu_top hu_bot] at hupper
      exact_mod_cast hupper
    have hinner : ⟪x + u, u⟫_ℝ = ⟪x, u⟫_ℝ + ‖u‖ ^ 2 := by
      simpa [real_inner_self_eq_norm_sq] using inner_add_left x u u
    have hincrement_real : ‖u‖ ^ 2 - ε < f (x + u) - f x := by
      nlinarith [hx_real, hupper_real, hinner]
    have hincrement :
        (((‖u‖ ^ 2 - ε : ℝ) : EReal)) ≤
          (recessionFunction f.toEReal hf.2.nonempty u : EReal) := by
      rw [recessionFunction_apply]
      refine le_trans ?_ (le_sSup ⟨x, by simp [Function.effectiveDomain_toEReal], rfl⟩)
      change (((‖u‖ ^ 2 - ε : ℝ) : EReal)) ≤ (((f (x + u) - f x : ℝ) : EReal))
      exact le_of_lt <| by
        exact_mod_cast hincrement_real
    have hε :
        (((‖u‖ ^ 2 - ε : ℝ) : EReal)) ≤ (((β : ℝ) * ‖u‖ : ℝ) : EReal) :=
      le_trans hincrement (hrec u)
    have hε_real : ‖u‖ ^ 2 - ε ≤ (β : ℝ) * ‖u‖ := by
      exact_mod_cast hε
    nlinarith
  have hnorm_le : ‖u‖ ≤ (β : ℝ) := by
    nlinarith [β.2, norm_nonneg u, hnorm_sq_le_beta_real]
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le

-- Proof sketch: first use the canonical Chapter 9 owner theorem
-- `toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ` to package `f.toEReal` as a
-- member of `Γ₀(H)`, then work with the canonical conjugate owner `(f.toEReal)∗[hf]` and the
-- recession owner `recessionFunction f.toEReal hf.2.nonempty`. Apply Corollary 16.57 for
-- `(ii) → (i)`, combine Corollaries 16.39 and 16.30 with the closedness of the ball for
-- `(ii) ↔ (iii)`, and use Proposition 13.49 together with the support function of the closed ball
-- for `(iii) ↔ (iv)`.
/-- Corollary 17 19: for a lower semicontinuous convex real-valued function on a real Hilbert
space, the following are equivalent: `β`-Lipschitz continuity, containment of the range of the
subdifferential in `B(0;β)`, containment of the effective domain of the Fenchel conjugate in
`B(0;β)`, and the recession bound `rec f ≤ β ‖·‖`. -/
theorem lipschitzWith_tfae_subdifferential_range_conjugateDomain_recession_bound
    (f : H → ℝ) (β : NNReal) (hlsc : LowerSemicontinuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f) :
    let hf := toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ f hlsc hconv
    List.TFAE
      [LipschitzWith β f,
        SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β,
        effectiveDomain ((f.toEReal)∗[hf]) ⊆ Metric.closedBall (0 : H) β,
        ∀ y : H, (recessionFunction f.toEReal hf.2.nonempty y : EReal) ≤
          ((β : ℝ) * ‖y‖ : ℝ)] := by
  let hf : f.toEReal ∈ Γ₀(H) :=
    toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ f hlsc hconv
  change List.TFAE
    [LipschitzWith β f,
      SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β,
      effectiveDomain ((f.toEReal)∗[hf]) ⊆ Metric.closedBall (0 : H) β,
      ∀ y : H, (recessionFunction f.toEReal hf.2.nonempty y : EReal) ≤
        ((β : ℝ) * ‖y‖ : ℝ)]
  have h42 :
      (∀ y : H, (recessionFunction f.toEReal hf.2.nonempty y : EReal) ≤
          ((β : ℝ) * ‖y‖ : ℝ)) →
        SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β := by
    intro hrec u hu_range
    rw [SetValuedOperator.mem_range_iff] at hu_range
    rcases hu_range with ⟨x, hu_sub⟩
    have hx_dom : x ∈ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hinner_le_increment :
        (((‖u‖ ^ 2 : ℝ) : EReal)) ≤
          ((f.toEReal (x + u) : EReal) - (f.toEReal x : EReal)) := by
      have hsupport :
          (((⟪(x + u) - x, u⟫_ℝ : ℝ) : EReal) + (f.toEReal x : EReal)) ≤
            (f.toEReal (x + u) : EReal) := by
        simpa using
          (mem_subdifferential_iff (f := f.toEReal) (x := x) (u := u)).1 hu_sub (x + u)
      have hx_top : (f.toEReal x : EReal) ≠ ⊤ := by
        simp [Function.toEReal_apply]
      have hx_bot : (f.toEReal x : EReal) ≠ ⊥ := by
        simp [Function.toEReal_apply]
      refine
        (EReal.le_sub_iff_add_le (Or.inl hx_bot) (Or.inl hx_top)).2 ?_
      simpa [Function.toEReal_apply, real_inner_self_eq_norm_sq] using hsupport
    have hincrement_le_rec :
        ((f.toEReal (x + u) : EReal) - (f.toEReal x : EReal)) ≤
          (recessionFunction f.toEReal hf.2.nonempty u : EReal) := by
      rw [recessionFunction_apply]
      exact le_sSup ⟨x, hx_dom, rfl⟩
    have hnorm_sq_le_beta :
        (((‖u‖ ^ 2 : ℝ) : EReal)) ≤ (((β : ℝ) * ‖u‖ : ℝ) : EReal) := by
      exact le_trans (le_trans hinner_le_increment hincrement_le_rec) (hrec u)
    have hnorm_sq_le_beta_real : ‖u‖ ^ 2 ≤ (β : ℝ) * ‖u‖ := by
      exact_mod_cast hnorm_sq_le_beta
    have hnorm_le : ‖u‖ ≤ (β : ℝ) := by
      nlinarith [β.2, norm_nonneg u, hnorm_sq_le_beta_real]
    -- Testing the recession bound in the direction `u` recovers the norm bound on `u`.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le
  have h21 :
      SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β →
        LipschitzWith β f := by
    intro hrange
    by_cases hH : Nonempty H
    · rcases hH with ⟨x0⟩
      have hcont : Continuous f := by
        refine continuous_iff_continuousAt.mpr ?_
        intro x
        have hx_local :
            x ∈
              {x : H |
                ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f.toEReal ∧
                  ContinuousAt (fun y : H ↦ (f.toEReal y : EReal).toReal) x} := by
          -- Corollary 8.39 specializes to the full-domain real-valued function `f`.
          rw [continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous
            (g := f.toEReal) hf]
          simp [Function.effectiveDomain_toEReal]
        rcases hx_local with ⟨ρ, hρ, -, hxcont⟩
        simpa [Function.toEReal_apply] using hxcont
      let S : Set ℝ := (fun u : H ↦ ‖u‖) '' SetValuedOperator.range (∂ f.toEReal)
      have hS_nonempty : S.Nonempty := by
        -- Pick one subdifferentiable point, then choose any subgradient there.
        have hx0_dom : x0 ∈ effectiveDomain f.toEReal := by
          simp [Function.effectiveDomain_toEReal]
        rcases exists_subdifferentiableAt_sequence_tendsto_of_mem_effectiveDomain_of_mem_gammaZero
            (f := f.toEReal) hf hx0_dom with
          ⟨xSeq, hxSeq_sub, -, -⟩
        have hxSeq_dom : xSeq 0 ∈ SetValuedOperator.dom (∂ f.toEReal) :=
          (subdifferentiableAt_iff_mem_dom (f.toEReal) (xSeq 0)).1 (hxSeq_sub 0)
        rw [SetValuedOperator.mem_dom_iff] at hxSeq_dom
        rcases hxSeq_dom with ⟨u, hu⟩
        refine ⟨‖u‖, ?_⟩
        refine ⟨u, ?_, rfl⟩
        rw [SetValuedOperator.mem_range_iff]
        exact ⟨xSeq 0, hu⟩
      have hS_bddAbove : BddAbove S := by
        refine ⟨(β : ℝ), ?_⟩
        rintro s ⟨u, hu, rfl⟩
        have hu_ball : u ∈ Metric.closedBall (0 : H) β := hrange hu
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      have hsSup_nonneg : 0 ≤ sSup S := by
        rcases hS_nonempty with ⟨s, hs⟩
        have hs_nonneg : 0 ≤ s := by
          rcases hs with ⟨u, -, rfl⟩
          exact norm_nonneg u
        exact le_trans hs_nonneg (le_csSup hS_bddAbove hs)
      let γ : NNReal := ⟨sSup S, hsSup_nonneg⟩
      have hγ_lub : IsLUB S (γ : ℝ) := by
        simpa [γ] using isLUB_csSup hS_nonempty hS_bddAbove
      have hLipγ : LipschitzWith γ f := by
        -- Corollary 16.57 is the owner theorem once the norm supremum is packaged as an `IsLUB`.
        exact
          lipschitzWith_of_continuous_convexOn_univ_of_isLUB_norm_range_subdifferential
            (f := f) (β := γ) hcont hconv hγ_lub
      have hγ_le_β : γ ≤ β := by
        change (γ : ℝ) ≤ (β : ℝ)
        exact hγ_lub.2 <| by
          intro s hs
          rcases hs with ⟨u, hu, rfl⟩
          have hu_ball : u ∈ Metric.closedBall (0 : H) β := hrange hu
          simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      -- The owner theorem may return the sharp radius `γ`; enlarge it to the requested radius `β`.
      exact hLipγ.weaken hγ_le_β
    · have hEmpty : IsEmpty H := not_nonempty_iff.mp hH
      -- In the empty space, every function is vacuously Lipschitz.
      exact by
        classical
        refine LipschitzWith.of_dist_le_mul ?_
        intro x y
        exact (hEmpty.false x).elim
  tfae_have 1 → 4 := by
    intro hLip
    -- A global Lipschitz bound controls every translated increment in the recession supremum.
    exact recessionFunction_toEReal_le_mul_norm_of_lipschitz f β hLip hf.2.nonempty
  tfae_have 4 → 2 := by
    intro hrec
    exact h42 hrec
  tfae_have 2 → 3 := by
    intro hrange
    have hLip : LipschitzWith β f := h21 hrange
    have hrec :
        ∀ y : H, (recessionFunction f.toEReal hf.2.nonempty y : EReal) ≤
          ((β : ℝ) * ‖y‖ : ℝ) :=
      recessionFunction_toEReal_le_mul_norm_of_lipschitz f β hLip hf.2.nonempty
    intro u hu
    exact
      mem_closedBall_of_recession_bound_of_mem_effectiveDomain_gammaZeroConjugate
        (f := f) (β := β) (hf := hf) hrec hu
  tfae_have 3 → 1 := by
    intro hdom
    refine h21 ?_
    intro u hu
    exact
      hdom <|
        mem_effectiveDomain_gammaZeroConjugate_of_mem_range_subdifferential
          (f := f) (hf := hf) hu
  tfae_have 4 → 3 := by
    intro hrec u hu
    exact
      mem_closedBall_of_recession_bound_of_mem_effectiveDomain_gammaZeroConjugate
        (f := f) (β := β) (hf := hf) hrec hu
  tfae_finish

end DirectionalDerivativesAndSubgradients

end

end ERealFunction
