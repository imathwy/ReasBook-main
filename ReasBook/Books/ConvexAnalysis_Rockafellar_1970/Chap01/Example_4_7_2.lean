import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

variable {𝕜 : Type*} [LinearOrder 𝕜]

section RingLayer

variable [Ring 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item gives an explicit `[-∞, +∞]`-valued function on a one-dimensional
  ordered scalar line.
- `core/canonical`: the owner abstractions are `indicator` for the `0/+∞` boundary term,
  `Function.IsConvex` from `Theorem_4_2`, with properness governed by `Function.IsProper` from
  Definition 4.6.
- `bridge/view`: the source-facing example keeps the genuinely new `-∞` interior branch explicit,
  while the boundary/outside behavior is expressed through the chapter owner
  `δ[𝕜](· | {x : 𝕜 | |x| = 1})`; convexity remains owner-level API, while improperness is
  expressed directly as failure of `Function.IsProper`.
- Primitive data vs derived API: the primitive datum is the source-facing interior `-∞` branch
  together with the owner-side boundary indicator. Regionwise evaluation on `|x| < 1`, `|x| = 1`,
  and `1 < |x|` is derived theorem-level API, and convexity/properness stay at the chapter owner
  level rather than being repackaged locally.

Domain-style sampling used here:
- the project declaration `indicator` from `Defintion_4_8_1`;
- the project declaration `Function.IsConvex` from `Theorem_4_2`;
- the project declaration `Function.IsProper` from `Definition_4_6`, whose negation gives the
  source meaning of improperness;
- the chapter codomain owner layer `WithBotTop 𝕜` for `[-∞, +∞]`-valued functions.
-/

/-- Example 4.7.2 in canonical owner form: the function on a one-dimensional ordered scalar line
that equals `-∞` on `|x| < 1`, equals `0` on `|x| = 1`, and equals `+∞` on `|x| > 1`.
Specializing `𝕜 = ℝ` recovers the textbook statement. -/
def example_4_7_2 : 𝕜 → WithBotTop 𝕜 :=
  fun x ↦
    if |x| < 1 then
      ⊥
    else
      δ[𝕜](x | {y : 𝕜 | |y| = 1})

/-- On the open interval `(-1, 1)`, `example_4_7_2` takes the value `-∞`. -/
@[simp] theorem example_4_7_2_apply_of_abs_lt_one {x : 𝕜} (hx : |x| < 1) :
    example_4_7_2 x = ⊥ := by
  simp [example_4_7_2, hx]

/-- On the boundary points `|x| = 1`, `example_4_7_2` takes the value `0`. -/
@[simp] theorem example_4_7_2_apply_of_abs_eq_one {x : 𝕜} (hx : |x| = 1) :
    example_4_7_2 x = 0 := by
  rw [example_4_7_2, if_neg (by simp [hx])]
  simp [hx]

/-- Outside the closed interval `[-1, 1]`, `example_4_7_2` takes the value `+∞`. -/
@[simp] theorem example_4_7_2_apply_of_one_lt_abs {x : 𝕜} (hx : 1 < |x|) :
    example_4_7_2 x = ⊤ := by
  have hlt : ¬ |x| < 1 := not_lt_of_ge hx.le
  have hne : |x| ≠ 1 := ne_of_gt hx
  rw [example_4_7_2, if_neg hlt]
  simp [hne]

private theorem abs_le_one_of_example_4_7_2_lt {x α : 𝕜} (hx : example_4_7_2 x < α) :
    |x| ≤ 1 := by
  by_contra h
  have h' : 1 < |x| := lt_of_not_ge h
  simp [example_4_7_2_apply_of_one_lt_abs h'] at hx

private theorem example_4_7_2_apply_one [IsOrderedRing 𝕜] :
    example_4_7_2 (1 : 𝕜) = (0 : WithBotTop 𝕜) := by
  exact example_4_7_2_apply_of_abs_eq_one (x := (1 : 𝕜)) (abs_one : |(1 : 𝕜)| = 1)

section Strict

variable [IsStrictOrderedRing 𝕜]

-- Proof sketch: use the explicit values of `example_4_7_2`. It takes the value `⊥` on every
-- `x` with `|x| < 1`, so it fails `Function.IsProper`.
/-- The function from Example 4.7.2 is improper. -/
theorem example_4_7_2_isImproper :
    ¬ (example_4_7_2 : 𝕜 → WithBotTop 𝕜).IsProper := by
  intro hproper
  have hzero : example_4_7_2 (0 : 𝕜) = ⊥ := by
    have hlt : |(0 : 𝕜)| < 1 := by simp
    exact example_4_7_2_apply_of_abs_lt_one hlt
  have hbot : (⊥ : WithBotTop 𝕜) < example_4_7_2 (0 : 𝕜) :=
    Function.IsProper.bot_lt hproper (0 : 𝕜)
  rw [hzero] at hbot
  exact lt_irrefl _ hbot

end Strict

-- Proof sketch: evaluate at `x = 1`, where the defining middle branch gives the finite value `0`,
-- so the function cannot coincide with the constant `⊤` function.
/-- The function from Example 4.7.2 is not identically `+∞`. -/
theorem example_4_7_2_ne_top [IsOrderedRing 𝕜] :
    example_4_7_2 ≠ (⊤ : 𝕜 → WithBotTop 𝕜) := by
  intro h
  have hval : example_4_7_2 (1 : 𝕜) = (0 : WithBotTop 𝕜) := example_4_7_2_apply_one
  have htop : (0 : WithBotTop 𝕜) = ⊤ := by
    simpa [hval] using congrFun h (1 : 𝕜)
  exact (WithBotTop.coe_ne_top (0 : 𝕜)) htop

-- Proof sketch: evaluate at `x = 1`, where the defining middle branch gives `0`, or at `x = 2`,
-- where the outer branch gives `⊤`; either value differs from `⊥`, so the function is not
-- constantly `⊥`.
/-- The function from Example 4.7.2 is not identically `-∞`. -/
theorem example_4_7_2_ne_bot [IsOrderedRing 𝕜] :
    example_4_7_2 ≠ (⊥ : 𝕜 → WithBotTop 𝕜) := by
  intro h
  have hval : example_4_7_2 (1 : 𝕜) = (0 : WithBotTop 𝕜) := example_4_7_2_apply_one
  have hbot : (0 : WithBotTop 𝕜) = ⊥ := by
    simpa [hval] using congrFun h (1 : 𝕜)
  exact (WithBotTop.coe_ne_bot (0 : 𝕜)) hbot

end RingLayer

section ConvexLayer

variable [CommRing 𝕜] [IsStrictOrderedRing 𝕜]

private theorem affine_upper_bound_pos_of_example_4_7_2_boundary
    {x y α β t : 𝕜} (hx : example_4_7_2 x < α) (hy : example_4_7_2 y < β)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hz : |(1 - t) * x + t * y| = 1) :
    0 < (1 - t) * α + t * β := by
  have hx_bounds : -1 ≤ x ∧ x ≤ 1 := abs_le.mp <| abs_le_one_of_example_4_7_2_lt hx
  have hy_bounds : -1 ≤ y ∧ y ≤ 1 := abs_le.mp <| abs_le_one_of_example_4_7_2_lt hy
  rcases (abs_eq (show 0 ≤ (1 : 𝕜) by positivity)).mp hz with hz1 | hz1
  · have hx_eq : x = 1 := by
      nlinarith [hx_bounds.2, hy_bounds.2, ht0, ht1, hz1]
    have hy_eq : y = 1 := by
      nlinarith [hx_bounds.2, hy_bounds.2, ht0, ht1, hz1]
    have hx_pos : 0 < α := by
      exact WithBotTop.coe_pos.mp (by simpa [hx_eq] using hx)
    have hy_pos : 0 < β := by
      exact WithBotTop.coe_pos.mp (by simpa [hy_eq] using hy)
    nlinarith
  · have hx_eq : x = -1 := by
      nlinarith [hx_bounds.1, hy_bounds.1, ht0, ht1, hz1]
    have hy_eq : y = -1 := by
      nlinarith [hx_bounds.1, hy_bounds.1, ht0, ht1, hz1]
    have hx_pos : 0 < α := by
      exact WithBotTop.coe_pos.mp (by simpa [hx_eq] using hx)
    have hy_pos : 0 < β := by
      exact WithBotTop.coe_pos.mp (by simpa [hy_eq] using hy)
    nlinarith

-- Proof sketch: apply the owner theorem `Function.isConvex_iff_lt_affine_upper_bound`. If the
-- interpolated point stays in `|x| < 1`, the value is `⊥`. If it lands on `|x| = 1`, positivity
-- of the affine upper bound forces both endpoints to lie at the same boundary point `±1`, so the
-- interpolated value is `0` and still lies strictly below the target real height.
/-- The function from Example 4.7.2 is convex. -/
theorem example_4_7_2_isConvex [DenselyOrdered 𝕜] :
    Function.IsConvex 𝕜 (example_4_7_2 : 𝕜 → WithBotTop 𝕜) := by
  rw [Function.isConvex_iff_lt_affine_upper_bound (f := (example_4_7_2 : 𝕜 → WithBotTop 𝕜))]
  intro x y α β t hx hy ht0 ht1
  let z : 𝕜 := (1 - t) • x + t • y
  have hz_le : |z| ≤ 1 := by
    have hx_le : |x| ≤ 1 := abs_le_one_of_example_4_7_2_lt hx
    have hy_le : |y| ≤ 1 := abs_le_one_of_example_4_7_2_lt hy
    have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
    dsimp [z]
    calc
      |(1 - t) * x + t * y| ≤ |(1 - t) * x| + |t * y| := abs_add_le _ _
      _ = (1 - t) * |x| + t * |y| := by
        rw [abs_mul, abs_of_nonneg ht_nonneg, abs_mul, abs_of_nonneg ht0.le]
      _ ≤ (1 - t) * 1 + t * 1 := by
        gcongr
      _ = 1 := by ring
  rcases lt_or_eq_of_le hz_le with hz_lt | hz_eq
  · rw [show example_4_7_2 z = ⊥ from example_4_7_2_apply_of_abs_lt_one hz_lt]
    simpa only [z, smul_eq_mul] using
      (show (⊥ : WithBotTop 𝕜) < (((1 - t) * α + t * β : 𝕜) : WithBotTop 𝕜) from
        WithBot.bot_lt_coe _)
  · have hpos : 0 < (1 - t) * α + t * β :=
      affine_upper_bound_pos_of_example_4_7_2_boundary hx hy ht0 ht1 <| by
        simpa [z, smul_eq_mul] using hz_eq
    rw [show example_4_7_2 z = 0 from example_4_7_2_apply_of_abs_eq_one hz_eq]
    simpa only using (WithBotTop.coe_pos.2 hpos)

end ConvexLayer

end
