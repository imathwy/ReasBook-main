/-
Lean version: leanprover/lean4:v4.29.1
Mathlib version: 5e932f97dd25535344f80f9dd8da3aab83df0fe6
-/

import Mathlib

noncomputable instance : SMul ℝ (WithTopBot ℝ) where
  smul := fun r x ↦ r * x

/-- Helper for import Mathlib: when all four inputs are finite, an inequality in `WithTopBot ℝ`
reduces to the corresponding real inequality. -/
lemma finite_weighted_sum_lt {a b d u v : ℝ}
    (h :
      ((a : WithTopBot ℝ) * (u : WithTopBot ℝ)) +
          ((b : WithTopBot ℝ) * (v : WithTopBot ℝ)) <
        (d : WithTopBot ℝ)) :
    a * u + b * v < d := by
  -- Push the inequality through the two coercions `ℝ → WithBot ℝ → WithTopBot ℝ`.
  have h' : ((((a * u + b * v : ℝ) : WithBot ℝ) : WithTopBot ℝ) < (d : WithTopBot ℝ)) := by
    simpa [WithTopBot, WithTop.coe_add, WithTop.coe_mul, WithBot.coe_add, WithBot.coe_mul,
      mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h
  exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp h')

/-- Helper for import Mathlib: multiplying by a nonnegative real is monotone on `WithTopBot ℝ`. -/
lemma mul_le_mul_left_coe_withTopBot {a : ℝ} (ha : 0 ≤ a) {u v : WithTopBot ℝ} (h : u ≤ v) :
    (a : WithTopBot ℝ) * u ≤ (a : WithTopBot ℝ) * v := by
  -- Split first on whether the upper bound is `⊤`; the finite branch reduces to `WithBot ℝ`.
  induction v using WithTop.recTopCoe with
  | top =>
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha0' : (a : WithTopBot ℝ) ≠ 0 := by
          exact_mod_cast ha0
        rw [WithTop.mul_top ha0']
        exact le_top
  | coe v =>
      induction u using WithTop.recTopCoe with
      | top =>
          -- `⊤ ≤ ↑v` is impossible.
          exfalso
          simp at h
      | coe u =>
          -- The finite branch is exactly the monotonicity statement on `WithBot ℝ`.
          have huv : u ≤ v := WithTop.coe_le_coe.mp h
          have ha' : (0 : WithBot ℝ) ≤ ((a : ℝ) : WithBot ℝ) := by
            exact WithBot.coe_le_coe.mpr ha
          exact WithTop.coe_le_coe.mpr (mul_le_mul_of_nonneg_left huv ha')

/-- Helper for import Mathlib: a strict finite upper bound on a weighted sum in `WithTopBot ℝ`
can be realized by finite real heights above the two inputs. -/
lemma exists_real_pair_above_of_weighted_sum_lt
    {u v : WithTopBot ℝ} {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h : (a : WithTopBot ℝ) * u + (b : WithTopBot ℝ) * v < d) :
    ∃ r t : ℝ, u < r ∧ v < t ∧ a * r + b * t ≤ d := by
  -- Peel off the outer `WithTop`; the `⊤` cases contradict the finite upper bound.
  induction u using WithTop.recTopCoe with
  | top =>
      exfalso
      simp [ha.ne'] at h
  | coe u =>
      -- Then peel off the inner `WithBot`; the remaining cases are elementary real algebra.
      induction u using WithBot.recBotCoe with
      | bot =>
          induction v using WithTop.recTopCoe with
          | top =>
              exfalso
              simp [hb.ne'] at h
          | coe v =>
              induction v using WithBot.recBotCoe with
              | bot =>
                  refine ⟨0, d / b, ?_, ?_, ?_⟩
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe 0)
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe (d / b))
                  · have hEq : a * 0 + b * (d / b) = d := by
                        field_simp [hb.ne']
                        ring
                    linarith
              | coe v =>
                  let t : ℝ := v + 1
                  let r : ℝ := (d - b * t) / a
                  refine ⟨r, t, ?_, ?_, ?_⟩
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe r)
                  · exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (by simp [t]))
                  · have hEq : a * r + b * t = d := by
                        dsimp [r, t]
                        field_simp [ha.ne']
                        ring
                    linarith
      | coe u =>
          induction v using WithTop.recTopCoe with
          | top =>
              exfalso
              simp [hb.ne'] at h
          | coe v =>
              induction v using WithBot.recBotCoe with
              | bot =>
                  let r : ℝ := u + 1
                  let t : ℝ := (d - a * r) / b
                  refine ⟨r, t, ?_, ?_, ?_⟩
                  · exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (by simp [r]))
                  · exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe t)
                  · have hEq : a * r + b * t = d := by
                        dsimp [r, t]
                        field_simp [hb.ne']
                        ring
                    linarith
              | coe v =>
                  -- In the fully finite case, use a symmetric real perturbation.
                  have hreal : a * u + b * v < d := by
                    exact finite_weighted_sum_lt h
                  let δ : ℝ := d - (a * u + b * v)
                  let r : ℝ := u + δ / (2 * a)
                  let t : ℝ := v + δ / (2 * b)
                  have hδ : 0 < δ := by
                    dsimp [δ]
                    linarith
                  refine ⟨r, t, ?_, ?_, ?_⟩
                  · have hr_aux : 0 < δ / (2 * a) := by
                      dsimp [δ]
                      positivity
                    exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (by dsimp [r]; linarith))
                  · have ht_aux : 0 < δ / (2 * b) := by
                      dsimp [δ]
                      positivity
                    exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (by dsimp [t]; linarith))
                  · dsimp [r, t, δ]
                    have hsum :
                        a * (u + (d - (a * u + b * v)) / (2 * a)) +
                            b * (v + (d - (a * u + b * v)) / (2 * b)) =
                          a * u + b * v + (d - (a * u + b * v)) / 2 +
                            (d - (a * u + b * v)) / 2 := by
                      field_simp [ha.ne', hb.ne']
                      ring
                    rw [hsum]
                    linarith

/-- Helper for import Mathlib: a `ConvexOn` map to `WithTopBot ℝ` has a convex real epigraph. -/
lemma ConvexOn.convex_real_epigraph {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    {f : E → WithTopBot ℝ} (hf : ConvexOn ℝ s f) :
    Convex ℝ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y} := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  -- Apply Jensen to the first coordinate, then enlarge the finite heights monotonically.
  calc
    f (a • x + b • y) ≤ (a : WithTopBot ℝ) * f x + (b : WithTopBot ℝ) * f y :=
      hf.2 hx hy ha hb hab
    _ ≤ (a : WithTopBot ℝ) * (r : WithTopBot ℝ) + (b : WithTopBot ℝ) * (t : WithTopBot ℝ) := by
      exact add_le_add (mul_le_mul_left_coe_withTopBot ha hr) (mul_le_mul_left_coe_withTopBot hb ht)
    _ = (a * r + b * t : ℝ) := by
      simp [WithTop.coe_add, WithTop.coe_mul, WithBot.coe_add, WithBot.coe_mul]

/-- Helper for import Mathlib: convexity of the real epigraph recovers `ConvexOn` on
`WithTopBot ℝ`. -/
lemma convexOn_of_convex_real_epigraph {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E}
    {f : E → WithTopBot ℝ}
    (h_epi : Convex ℝ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y}) (hs : Convex ℝ s) :
    ConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Route correction: work directly in `WithTopBot ℝ = WithTop (WithBot ℝ)`, not in `EReal`.
  change f (a • x + b • y) ≤ (a : WithTopBot ℝ) * f x + (b : WithTopBot ℝ) * f y
  by_cases ha0 : a = 0
  · -- The endpoint case is immediate once the coefficients are specialized.
    subst a
    have hb1 : b = 1 := by
      linarith
    subst b
    simp
  by_cases hb0 : b = 0
  · -- The symmetric endpoint case is equally immediate.
    subst b
    have ha1 : a = 1 := by
      linarith
    subst a
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let rhs : WithTopBot ℝ := (a : WithTopBot ℝ) * f x + (b : WithTopBot ℝ) * f y
  -- To show `f (...) ≤ rhs`, it suffices to dominate it by every finite value strictly above `rhs`.
  refine (WithTop.le_of_forall_lt_iff_le).1 ?_
  intro z hz
  induction z using WithBot.recBotCoe with
  | bot =>
      exact (not_lt_of_ge bot_le hz).elim
  | coe d =>
      -- Lift finite upper bounds on the weighted sum to finite epigraph heights at the endpoints.
      obtain ⟨r, t, hur, hvt, hsum⟩ := exists_real_pair_above_of_weighted_sum_lt ha_pos hb_pos hz
      have hx_epi : (x, r) ∈ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y} := ⟨hx, hur.le⟩
      have hy_epi : (y, t) ∈ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y} := ⟨hy, hvt.le⟩
      have hcombo := h_epi hx_epi hy_epi ha hb hab
      have hcombo' : f (a • x + b • y) ≤ (a * r + b * t : ℝ) := by
        simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
          add_assoc] using hcombo.2
      calc
        f (a • x + b • y) ≤ (a * r + b * t : ℝ) := hcombo'
        _ ≤ (d : WithTopBot ℝ) := by
          exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr hsum)

/-- import Mathlib: convexity on `WithTopBot ℝ` is equivalent to convexity of the real epigraph. -/
theorem main {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} (f : E → WithTopBot ℝ) :
    (Convex ℝ {(x, y) : E × ℝ | x ∈ s ∧ f x ≤ y} ∧ Convex ℝ s) ↔
        ConvexOn ℝ s f := by
  constructor
  · -- The reverse direction packages the finite-height approximation argument.
    intro h
    exact convexOn_of_convex_real_epigraph h.1 h.2
  · -- The forward direction is the direct epigraph Jensen argument.
    intro h
    exact ⟨h.convex_real_epigraph, h.1⟩
