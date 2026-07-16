import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_6
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_5_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.FirstOrderTaylorModel

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 1.5.9 is source-facing in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the converse implication from a global quadratic bound on the absolute affine
  first-order remainder with an explicit field `g` to the textbook Lipschitz conclusion
  `LipschitzWith L g`
* core/canonical: the explicit-data affine-model owner `affineModelAt f g x`
* bridge/view: under completeness, `HasGradientAt f (g x) x`, the identity `∇ f = g`, and the
  chapter owner pair `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)` from Definition 1.5.2

Primary domain:
* first-order smooth optimization on a real inner-product space, with complete-space companions
  only where the canonical gradient owner `∇ f` is used

Sampled owner-style declarations:
* `affineModelAt` in `FirstOrderTaylorModel`, the explicit-data affine approximation owner
* `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)` in `Definition_1_5_2`, the chapter owner for
  `C^{1,1}_L`
* `LipschitzWith L g` and `LipschitzWith.norm_sub_le`
* `HasGradientAt`
* `gradient_eq`

Owner abstraction:
* the explicit-data affine-model owner `affineModelAt f g x`
* under completeness, the canonical gradient specialization `firstOrderTaylorModelAt f x` and the
  Chapter 1 owner pair `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`

Primitive data:
* a Lipschitz constant `L`
* a candidate gradient field `g : E → E`
* the global quadratic remainder estimate against the owner affine model `affineModelAt f g x`

Derived API:
* the source-facing smoothness statement `LipschitzWith L g`
* under completeness, the local gradient statement `HasGradientAt f (g x) x`
* under completeness, the identification `∇ f = g`
* under completeness, the canonical `C^{1,1}_L` owner statement
  `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`

No extra wrapper is introduced here. The main proposition stays on the source-facing field `g`,
and the complete-space companions reuse the chapter owner directly instead of packaging a parallel
`... ∧ LipschitzWith L g` API. -/

variable {L : NNReal} {f : E → ℝ} {g : E → E}
variable (hquad :
  ∀ x y,
    |f y - affineModelAt f g x y| ≤
      (L : ℝ) / 2 * ‖y - x‖ ^ 2)

include hquad

/-- Helper for Proposition 1.5.9: adding the forward and reverse affine-model bounds along the
secant `y - x` yields the source-style pairing estimate
`|⟪g y - g x, y - x⟫| ≤ L ‖y - x‖²`. -/
lemma gradient_secant_inner_bound_of_sub_affineApproximation_norm_sq_bound
    (x y : E) :
    |inner ℝ (g y - g x) (y - x)| ≤ (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  have hxy := hquad x y
  have hyx := hquad y x
  have hxy_lower_raw :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f y - (f x + inner ℝ (g x) (y - x)) := by
    -- Expand the affine model at `x` before taking the lower half of the absolute-value bound.
    simpa [affineModelAt_apply] using (abs_le.mp hxy).1
  have hxy_lower :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f y - f x - inner ℝ (g x) (y - x) := by
    -- Reassociate the forward affine-model error into the subtraction form used below.
    linarith
  have hxy_upper_raw :
      f y - (f x + inner ℝ (g x) (y - x)) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The upper half of the forward remainder estimate has the same expanded affine model.
    simpa [affineModelAt_apply] using (abs_le.mp hxy).2
  have hxy_upper :
      f y - f x - inner ℝ (g x) (y - x) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- Reassociate the forward inequality into the same subtraction normal form.
    linarith
  have hyx_lower_raw :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f x - (f y + inner ℝ (g y) (x - y)) := by
    -- After swapping the endpoints, the secant length is unchanged because `‖x - y‖ = ‖y - x‖`.
    simpa [affineModelAt_apply, norm_sub_rev] using (abs_le.mp hyx).1
  have hyx_lower :
      -((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) ≤
        f x - f y + inner ℝ (g y) (y - x) := by
    -- Replace `x - y` by `-(y - x)` so the reversed affine term matches the forward secant vector.
    have hxyeq : inner ℝ (g y) (x - y) = -inner ℝ (g y) (y - x) := by
      rw [show x - y = -(y - x) by abel_nf, inner_neg_right]
    linarith
  have hyx_upper_raw :
      f x - (f y + inner ℝ (g y) (x - y)) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The reversed upper bound has the same normalization of the secant length.
    simpa [affineModelAt_apply, norm_sub_rev] using (abs_le.mp hyx).2
  have hyx_upper :
      f x - f y + inner ℝ (g y) (y - x) ≤
        (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- Again rewrite the inner product against `x - y` as the negated pairing against `y - x`.
    have hxyeq : inner ℝ (g y) (x - y) = -inner ℝ (g y) (y - x) := by
      rw [show x - y = -(y - x) by abel_nf, inner_neg_right]
    linarith
  have hupper :
      inner ℝ (g y - g x) (y - x) ≤ (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    -- Adding the two upper inequalities cancels the function values and leaves the secant pairing.
    rw [inner_sub_left]
    linarith
  have hlower :
      -((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) ≤ inner ℝ (g y - g x) (y - x) := by
    -- Adding the two lower inequalities gives the matching lower bound.
    rw [inner_sub_left]
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Proposition 1.5.9: translating both endpoints by `t • u` isolates the first-order
term `t * ⟪g y - g x, u⟫`, and the remaining error is still quadratic in the translation size. -/
lemma translated_endpoint_difference_linearization_error_bound
    (x y u : E) (t : ℝ) :
    |(f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u| ≤
      (L : ℝ) * ‖t • u‖ ^ (2 : ℕ) := by
  have hy :
      |f (y + t • u) - (f y + t * inner ℝ (g y) u)| ≤
        (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) := by
    -- Apply the quadratic remainder bound at base point `y` along the translated direction `t • u`.
    simpa [affineModelAt_apply, sub_eq_add_neg, inner_smul_right] using hquad y (y + t • u)
  have hx :
      |f (x + t • u) - (f x + t * inner ℝ (g x) u)| ≤
        (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) := by
    -- The same expansion at base point `x` gives the matching error term for the second endpoint.
    simpa [affineModelAt_apply, sub_eq_add_neg, inner_smul_right] using hquad x (x + t • u)
  let ry : ℝ := f (y + t • u) - (f y + t * inner ℝ (g y) u)
  let rx : ℝ := f (x + t • u) - (f x + t * inner ℝ (g x) u)
  have hremainder :
      (f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u =
        ry - rx := by
    -- Group the translated endpoint difference into the two one-point Taylor remainders.
    dsimp [ry, rx]
    rw [inner_sub_left]
    ring_nf
  calc
    |(f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u|
        = |ry - rx| := by rw [hremainder]
    _ ≤ |ry| + |rx| := by
      simpa [sub_eq_add_neg] using abs_add_le ry (-rx)
    _ ≤ (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) + ((L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ)) := by
      exact add_le_add (by simpa [ry] using hy) (by simpa [rx] using hx)
    _ = (L : ℝ) * ‖t • u‖ ^ (2 : ℕ) := by ring

/-- Helper for Proposition 1.5.9: the translated endpoint difference has derivative
`⟪g y - g x, u⟫` at `t = 0` because the solved remainder is quadratic in `t`. -/
lemma translated_endpoint_difference_hasDerivAt
    (x y u : E) :
    HasDerivAt
      (fun t : ℝ ↦ (f (y + t • u) - f (x + t • u)) - (f y - f x))
      (inner ℝ (g y - g x) u) 0 := by
  let R : ℝ → ℝ :=
    fun t ↦
      (f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u
  have hBigO : R =O[nhds (0 : ℝ)] fun t ↦ ‖t - 0‖ ^ (2 : ℕ) := by
    refine Asymptotics.IsBigO.of_bound ((L : ℝ) * ‖u‖ ^ (2 : ℕ)) ?_
    filter_upwards with t
    -- Rewrite the quadratic remainder bound into the standard `O(‖t‖²)` normal form.
    have hR :=
      translated_endpoint_difference_linearization_error_bound
        (hquad := hquad) x y u t
    calc
      ‖R t‖ = |(f (y + t • u) - f (x + t • u)) - (f y - f x) - t * inner ℝ (g y - g x) u| := by
        simp [R, Real.norm_eq_abs]
      _ ≤ (L : ℝ) * ‖t • u‖ ^ (2 : ℕ) := hR
      _ = (L : ℝ) * (|t| ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ)) := by
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ = (L : ℝ) * ‖u‖ ^ (2 : ℕ) * ‖‖t - 0‖ ^ (2 : ℕ)‖ := by
        simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hR' : HasDerivAt R 0 0 := by
    -- A quadratic remainder has zero derivative at the origin.
    simpa using (hBigO.hasFDerivAt (by norm_num : 1 < 2)).hasDerivAt
  have hlin :
      HasDerivAt
        (fun t : ℝ ↦ t * inner ℝ (g y - g x) u)
        (inner ℝ (g y - g x) u) 0 := by
    -- The linear term contributes exactly the desired pairing coefficient.
    simpa [one_mul] using (hasDerivAt_id 0).mul_const (inner ℝ (g y - g x) u)
  -- Reassemble the translated difference from the quadratic remainder and the linear part.
  convert hR'.add hlin using 1
  · ext t
    simp [R, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    abel_nf
  · ring

/-- Helper for Proposition 1.5.9: a direct decomposition against the affine model at `x` controls
the translated endpoint difference, but it leaves a quadratic tail in `‖y - x‖`. -/
lemma translated_endpoint_difference_bound_with_quadratic_tail
    (x y u : E) (t : ℝ) :
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)| ≤
      (L : ℝ) / 2 * ‖(y - x) + t • u‖ ^ (2 : ℕ) +
        ((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) + (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ)) := by
  let r₁ : ℝ := f (y + t • u) - affineModelAt f g x (y + t • u)
  let r₂ : ℝ := f y - affineModelAt f g x y
  let r₃ : ℝ := f (x + t • u) - affineModelAt f g x (x + t • u)
  have hr₁ :
      |r₁| ≤ (L : ℝ) / 2 * ‖(y - x) + t • u‖ ^ (2 : ℕ) := by
    -- Evaluate the remainder bound at the translated endpoint `y + t • u`.
    simpa [r₁, affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hquad x (y + t • u)
  have hr₂ : |r₂| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The same remainder bound at `y` provides the second tail term.
    simpa [r₂] using hquad x y
  have hr₃ : |r₃| ≤ (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ) := by
    -- At `x + t • u`, the affine displacement from `x` is exactly `t • u`.
    simpa [r₃, affineModelAt_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hquad x (x + t • u)
  have hdecomp :
      (f (y + t • u) - f (x + t • u)) - (f y - f x) = r₁ - r₂ - r₃ := by
    -- Isolate the translated difference as the alternating sum of the three affine-model errors.
    dsimp [r₁, r₂, r₃]
    simp [affineModelAt_apply, sub_eq_add_neg, inner_add_right, inner_sub_right,
      add_assoc, add_left_comm, add_comm]
    ring_nf
  calc
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)| = |r₁ - r₂ - r₃| := by rw [hdecomp]
    _ ≤ |r₁| + |r₂| + |r₃| := by
      have htri : |r₁ + (-r₂ + -r₃)| ≤ |r₁| + |-r₂ + -r₃| := abs_add_le _ _
      have htri' : |-r₂ + -r₃| ≤ |r₂| + |r₃| := by
        simpa using (abs_add_le (-r₂) (-r₃))
      have hmid : |r₁| + |-r₂ + -r₃| ≤ |r₁| + (|r₂| + |r₃|) := by
        simpa [add_assoc, add_left_comm, add_comm] using (add_le_add_right htri' |r₁|)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htri.trans hmid
    _ ≤ (L : ℝ) / 2 * ‖(y - x) + t • u‖ ^ (2 : ℕ) +
          ((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) + (L : ℝ) / 2 * ‖t • u‖ ^ (2 : ℕ)) := by
      linarith [hr₁, hr₂, hr₃]

/-- Helper for Proposition 1.5.9: the centered second difference at `c` is controlled by the same
quadratic modulus because the affine terms at `c` cancel between the two symmetric endpoints. -/
lemma centered_second_difference_bound_of_sub_affineApproximation_norm_sq_bound
    (c v : E) :
    |f (c + v) + f (c - v) - 2 * f c| ≤ (L : ℝ) * ‖v‖ ^ (2 : ℕ) := by
  have hplus :
      |f (c + v) - (f c + inner ℝ (g c) v)| ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- Apply the affine-model remainder bound at `c` to the forward symmetric endpoint.
    simpa [affineModelAt_apply] using hquad c (c + v)
  have hminus :
      |f (c - v) - (f c + inner ℝ (g c) (-v))| ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- Apply the same bound at the backward symmetric endpoint.
    simpa [affineModelAt_apply, norm_neg, sub_eq_add_neg] using hquad c (c - v)
  have hplus_lower :
      -((L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ)) ≤
        f (c + v) - f c - inner ℝ (g c) v := by
    -- Rewrite the lower half of the forward absolute-value bound into subtraction form.
    linarith [(abs_le.mp hplus).1]
  have hplus_upper :
      f (c + v) - f c - inner ℝ (g c) v ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- Rewrite the upper half of the forward absolute-value bound into subtraction form.
    linarith [(abs_le.mp hplus).2]
  have hminus_lower :
      -((L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ)) ≤
        f (c - v) - f c + inner ℝ (g c) v := by
    -- Replace the backward affine term by the negated pairing against `v`.
    have hneg : inner ℝ (g c) (-v) = -inner ℝ (g c) v := by
      rw [inner_neg_right]
    linarith [(abs_le.mp hminus).1]
  have hminus_upper :
      f (c - v) - f c + inner ℝ (g c) v ≤
        (L : ℝ) / 2 * ‖v‖ ^ (2 : ℕ) := by
    -- The same normalization works for the upper half of the backward bound.
    have hneg : inner ℝ (g c) (-v) = -inner ℝ (g c) v := by
      rw [inner_neg_right]
    linarith [(abs_le.mp hminus).2]
  have hupper :
      f (c + v) + f (c - v) - 2 * f c ≤ (L : ℝ) * ‖v‖ ^ (2 : ℕ) := by
    -- Adding the two upper inequalities cancels the affine terms at the center point.
    linarith
  have hlower :
      -((L : ℝ) * ‖v‖ ^ (2 : ℕ)) ≤ f (c + v) + f (c - v) - 2 * f c := by
    -- Adding the two lower inequalities gives the matching lower bound.
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Proposition 1.5.9: rewriting around the midpoint of the four translated endpoints
turns the translated endpoint difference into a difference of centered second differences. -/
lemma translated_endpoint_difference_eq_centered_second_difference_sub
    (x y u : E) (t : ℝ) :
    let d : E := y - x
    let h : E := t • u
    let c : E := x + (1 / 2 : ℝ) • (d + h)
    let a : E := (1 / 2 : ℝ) • (d + h)
    let b : E := (1 / 2 : ℝ) • (d - h)
    ((f (y + h) - f (x + h)) - (f y - f x)) =
      (f (c + a) + f (c - a) - 2 * f c) -
        (f (c + b) + f (c - b) - 2 * f c) := by
  dsimp
  have hca :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) + (1 / 2 : ℝ) • ((y - x) + t • u) = y + t • u := by
    -- The midpoint plus the forward half-displacement reaches the translated endpoint `y + t • u`.
    linear_combination (norm := module)
  have hcmA :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) - (1 / 2 : ℝ) • ((y - x) + t • u) = x := by
    -- The same midpoint minus that half-displacement returns to the original left endpoint.
    linear_combination (norm := module)
  have hcb :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) + (1 / 2 : ℝ) • ((y - x) - t • u) = y := by
    -- Replacing the forward half-step by the complementary one reaches the original right endpoint.
    linear_combination (norm := module)
  have hcmB :
      x + (1 / 2 : ℝ) • ((y - x) + t • u) - (1 / 2 : ℝ) • ((y - x) - t • u) = x + t • u := by
    -- The complementary reflected point is the translated left endpoint `x + t • u`.
    linear_combination (norm := module)
  rw [hca, hcmA, hcb, hcmB]
  ring

omit hquad in
/-- Helper for Proposition 1.5.9: the four-point centered difference can be rewritten exactly as
an alternating sum of three affine-model remainders based at the corner `c + a`. -/
lemma centered_second_difference_eq_corner_remainder_combination
    (c a b : E) :
    (f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c) =
      (f (c - a) - affineModelAt f g (c + a) (c - a)) -
        (f (c + b) - affineModelAt f g (c + a) (c + b)) -
        (f (c - b) - affineModelAt f g (c + a) (c - b)) := by
  -- Expand the three affine-model errors at the common corner `c + a`.
  simp [affineModelAt_apply, sub_eq_add_neg]
  -- Normalize the scalar algebra so that only the combined affine pairing remains.
  ring_nf
  have hinner :
      -inner ℝ (g (c + a)) (c + -a + (-a + -c)) +
          inner ℝ (g (c + a)) (c + b + (-a + -c)) +
        inner ℝ (g (c + a)) (c + -b + (-a + -c)) = 0 := by
    -- The three displacement vectors sum to zero, so their common affine contribution cancels.
    have hneg :
        -inner ℝ (g (c + a)) (c + -a + (-a + -c)) =
          inner ℝ (g (c + a)) (-(c + -a + (-a + -c))) := by
      rw [inner_neg_right]
    rw [hneg, ← inner_add_right, ← inner_add_right]
    have hsum :
        -(c + -a + (-a + -c)) + (c + b + (-a + -c)) + (c + -b + (-a + -c)) = 0 := by
      abel_nf
    rw [hsum, inner_zero_right]
  -- The remaining equality is the pure four-point identity.
  linarith [hinner]

/-- Helper for Proposition 1.5.9: for a fixed translation `h`, the increment map
`z ↦ f (z + h) - f z` still has a quadratic affine-model remainder, now with candidate field
`z ↦ g (z + h) - g z`. -/
lemma increment_difference_linearization_error_bound
    (x y h : E) :
    |((f (y + h) - f y) - (f (x + h) - f x)) -
        inner ℝ (g (x + h) - g x) (y - x)| ≤
      (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
  let A : ℝ := f (y + h) - affineModelAt f g (x + h) (y + h)
  let B : ℝ := f y - affineModelAt f g x y
  have hshift : (y + h) - (x + h) = y - x := by
    abel_nf
  have hA : |A| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- Translate both endpoints by `h`; the secant vector itself does not change.
    simpa [A, affineModelAt_apply, hshift] using hquad (x + h) (y + h)
  have hB : |B| ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    -- The original pair `(x, y)` contributes the matching quadratic remainder.
    simpa [B] using hquad x y
  have hdecomp :
      ((f (y + h) - f y) - (f (x + h) - f x)) -
          inner ℝ (g (x + h) - g x) (y - x) =
        A - B := by
    -- Expand both affine remainders and regroup the function values and pairings.
    dsimp [A, B]
    rw [hshift, inner_sub_left]
    ring
  calc
    |((f (y + h) - f y) - (f (x + h) - f x)) -
        inner ℝ (g (x + h) - g x) (y - x)| = |A - B| := by
          rw [hdecomp]
    _ ≤ |A| + |B| := by
      simpa [sub_eq_add_neg] using abs_add_le A (-B)
    _ ≤ (L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) + ((L : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ)) := by
      exact add_le_add hA hB
    _ = (L : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by ring

/-- Helper for Proposition 1.5.9: the centered-second-difference gap is a translated increment
whose linearization is the off-diagonal pairing `⟪g (c + a) - g (c - b), a - b⟫`. -/
lemma centered_second_difference_linearization_error_bound
    (c a b : E) :
    |((f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c)) -
        inner ℝ (g (c + a) - g (c - b)) (a - b)| ≤
      (L : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
  have hinc :=
    increment_difference_linearization_error_bound
      (hquad := hquad) (x := c - b) (y := c - a) (h := a + b)
  have hyh : c - a + (a + b) = c + b := by
    abel_nf
  have hxh : c - b + (a + b) = c + a := by
    abel_nf
  have hyx : (c - a) - (c - b) = -(a - b) := by
    abel_nf
  -- Rewrite the translated increment identity into the desired centered-difference form.
  have hinc' :
      |inner ℝ (g (c + a) - g (c - b)) (a - b) -
          ((f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c))| ≤
        (L : ℝ) * ‖a - b‖ ^ (2 : ℕ) := by
    convert hinc using 1
    · congr 1
      rw [hyh, hxh, hyx, inner_neg_right]
      ring
    · rw [hyx, norm_neg]
  simpa [abs_sub_comm] using hinc'

/-- Helper for Proposition 1.5.9: the difference of two centered second differences should obey
the sharp four-point polarization bound. -/
lemma centered_second_difference_polarization_bound
    (c a b : E) :
    |(f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c)| ≤
      (L : ℝ) * ‖a + b‖ * ‖a - b‖ := by
  -- Route correction: the previous direct absolute-value attack obscured the finite-difference
  -- cancellation. The proved corner identity reduces the frontier to one sharp signed estimate.
  have hcorner :
      (f (c + a) + f (c - a) - 2 * f c) - (f (c + b) + f (c - b) - 2 * f c) =
        (f (c - a) - affineModelAt f g (c + a) (c - a)) -
          (f (c + b) - affineModelAt f g (c + a) (c + b)) -
          (f (c - b) - affineModelAt f g (c + a) (c - b)) := by
    -- Rewrite the centered difference through the exact corner-based remainder decomposition.
    exact centered_second_difference_eq_corner_remainder_combination
      (f := f) (g := g) c a b
  have hdiag :=
    centered_second_difference_linearization_error_bound
      (hquad := hquad) c a b
  -- TODO: the current signed-corner subplan is structurally wrong. The proved diagonal
  -- linearization `hdiag` shows that the remaining blocker is now exactly the off-diagonal pairing
  -- estimate `|⟪g (c + a) - g (c - b), a - b⟫| ≤ (L : ℝ) * ‖a + b‖ * ‖a - b‖`, which must be
  -- obtained by a genuinely nonnegative mixed-increment argument rather than the false signed
  -- inequality `… ≤ L * inner ℝ (a + b) (a - b)`.
  have _ := hcorner
  have _ := hdiag
  sorry

/-- Helper for Proposition 1.5.9: the midpoint rewrite reduces the translated endpoint difference
to the centered-second-difference polarization bound, which is exactly the sharp mixed estimate
needed for the derivative-at-zero route. -/
lemma translated_endpoint_difference_le_mul_norm_mul
    (x y u : E) (t : ℝ) :
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)| ≤
      (L : ℝ) * ‖y - x‖ * ‖t • u‖ := by
  let d : E := y - x
  let h : E := t • u
  let c : E := x + (1 / 2 : ℝ) • (d + h)
  let a : E := (1 / 2 : ℝ) • (d + h)
  let b : E := (1 / 2 : ℝ) • (d - h)
  have hrewrite :
      ((f (y + h) - f (x + h)) - (f y - f x)) =
        (f (c + a) + f (c - a) - 2 * f c) -
          (f (c + b) + f (c - b) - 2 * f c) := by
    -- Rewrite the translated difference around the midpoint configuration from the new route.
    simpa [d, h, c, a, b] using
      translated_endpoint_difference_eq_centered_second_difference_sub
        (hquad := hquad) (f := f) x y u t
  have hab_sum : a + b = d := by
    -- The midpoint decomposition splits `d` into the sum of the two half-displacements.
    dsimp [a, b]
    linear_combination (norm := module)
  have hab_diff : a - b = h := by
    -- Their difference recovers the translation increment `h`.
    dsimp [a, b]
    linear_combination (norm := module)
  calc
    |(f (y + t • u) - f (x + t • u)) - (f y - f x)|
        = |(f (c + a) + f (c - a) - 2 * f c) -
            (f (c + b) + f (c - b) - 2 * f c)| := by
            rw [show t • u = h by rfl, hrewrite]
    _ ≤ (L : ℝ) * ‖a + b‖ * ‖a - b‖ := by
      -- Invoke the centered-second-difference polarization step at the midpoint configuration.
      exact centered_second_difference_polarization_bound (hquad := hquad) c a b
    _ = (L : ℝ) * ‖y - x‖ * ‖t • u‖ := by
      -- Simplify the midpoint variables back to the original displacement and translation size.
      simp [d, h, hab_sum, hab_diff]

/-- Helper for Proposition 1.5.9: a uniform pairing bound against every test direction implies the
desired norm bound by testing with `u = g y - g x`. -/
lemma norm_sub_le_of_inner_bound
    (x y : E)
    (hinner :
      ∀ u : E, |inner ℝ (g y - g x) u| ≤ (L : ℝ) * ‖y - x‖ * ‖u‖) :
    ‖g y - g x‖ ≤ (L : ℝ) * ‖y - x‖ := by
  let v : E := g y - g x
  have hpair : |inner ℝ v v| ≤ (L : ℝ) * ‖y - x‖ * ‖v‖ := by
    simpa [v] using hinner v
  have hsq : ‖v‖ ^ (2 : ℕ) ≤ (L : ℝ) * ‖y - x‖ * ‖v‖ := by
    -- The upper half of the absolute-value bound gives the quadratic norm inequality.
    simpa [v, real_inner_self_eq_norm_sq] using (abs_le.mp hpair).2
  have hnonneg : 0 ≤ (L : ℝ) * ‖y - x‖ := by
    positivity
  by_cases hv : ‖v‖ = 0
  · -- In the degenerate case the gradient difference vanishes, so the bound is immediate.
    simp [v, hv, hnonneg]
  · -- Otherwise divide the quadratic inequality by the positive norm.
    have hv' : ‖v‖ ≠ 0 := hv
    have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) hv'.symm
    have : ‖v‖ ≤ (L : ℝ) * ‖y - x‖ := by
      nlinarith [hsq]
    simpa [v] using this

/-- Helper for Proposition 1.5.9: a scalar function differentiable at `0` with increment bounded
by `C ‖t‖` near `0` has derivative at `0` bounded in absolute value by `C`. -/
lemma abs_derivAt_zero_le_of_bound
    {φ : ℝ → ℝ} {m C : ℝ}
    (hderiv : HasDerivAt φ m 0)
    (hC : 0 ≤ C)
    (hbound : ∀ t, |φ t - φ 0| ≤ C * ‖t - 0‖) :
    |m| ≤ C := by
  have hlip : ∀ᶠ t in nhds (0 : ℝ), ‖φ t - φ 0‖ ≤ C * ‖t - 0‖ := by
    -- Rewrite the pointwise absolute-value estimate as the norm bound needed by
    -- `HasFDerivAt.le_of_lip'`.
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [Real.norm_eq_abs] using hbound t
  -- The derivative norm cannot exceed any local Lipschitz constant at the base point.
  have hnorm := hderiv.hasFDerivAt.le_of_lip' hC hlip
  simpa [Real.norm_eq_abs] using hnorm

/-- Helper for Proposition 1.5.9: once the translated endpoint function is shown to be
`L ‖y - x‖ ‖u‖`-Lipschitz in `t`, its derivative at `0` gives the arbitrary-direction pairing
bound. -/
lemma gradient_sub_inner_le_mul_norm_mul
    (x y u : E) :
    |inner ℝ (g y - g x) u| ≤ (L : ℝ) * ‖y - x‖ * ‖u‖ := by
  let φ : ℝ → ℝ := fun t ↦ (f (y + t • u) - f (x + t • u)) - (f y - f x)
  have hderiv :
      HasDerivAt φ (inner ℝ (g y - g x) u) 0 := by
    -- The translated endpoint difference has the desired derivative at the origin.
    simpa [φ] using translated_endpoint_difference_hasDerivAt (hquad := hquad) x y u
  have hC_nonneg : 0 ≤ (L : ℝ) * ‖y - x‖ * ‖u‖ := by
    positivity
  have hbound :
      ∀ t, |φ t - φ 0| ≤ ((L : ℝ) * ‖y - x‖ * ‖u‖) * ‖t - 0‖ := by
    intro t
    -- The sharp mixed-increment estimate gives a linear bound in `‖t‖`.
    simpa [φ, norm_smul, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using
      translated_endpoint_difference_le_mul_norm_mul (hquad := hquad) x y u t
  -- Apply the general derivative-versus-local-Lipschitz comparison at `t = 0`.
  exact abs_derivAt_zero_le_of_bound (hquad := hquad) hderiv hC_nonneg hbound

/-- Proposition 1.5.9: if the affine-model remainder of `f` with respect to a field `g` is
globally bounded by `(L / 2) ‖y - x‖²`, then `g` is globally `L`-Lipschitz. This statement uses
only the intrinsic field `g`, so it does not assume ambient completeness. -/
theorem lipschitzGradient_of_sub_affineApproximation_norm_sq_bound :
    LipschitzWith L g := by
  -- Route correction: the source proof's secant estimate along `y - x` is not sufficient by
  -- itself to control `‖g y - g x‖`; the missing step is an arbitrary-direction pairing bound.
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  -- Once the arbitrary-direction pairing bound is available, test it against the gradient
  -- difference itself to recover the operator norm estimate.
  simpa [norm_sub_rev] using
    norm_sub_le_of_inner_bound (hquad := hquad) (L := L) (g := g) y x
      (fun u ↦ gradient_sub_inner_le_mul_norm_mul (hquad := hquad) y x u)

section CompleteSpace

variable [CompleteSpace E]

include hquad

/-- Helper for Proposition 1.5.9: the quadratic remainder bound upgrades the affine-model error at
`x` from `O(‖y - x‖²)` to `o(‖y - x‖)`. -/
lemma sub_affineApproximation_isLittleO_of_norm_sq_bound
    (x : E) :
    (fun y ↦ f y - affineModelAt f g x y) =o[nhds x] fun y ↦ ‖y - x‖ := by
  let r : E → ℝ := fun y ↦ f y - affineModelAt f g x y
  -- First record the global quadratic estimate as a local `O(‖y - x‖²)` bound near `x`.
  have hBigO :
      r =O[nhds x] fun y ↦ ‖y - x‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ((L : ℝ) / 2) ?_
    filter_upwards with y
    simpa [r, Real.norm_eq_abs] using hquad x y
  -- A quadratic bound forces zero derivative for the remainder term, which is exactly the desired
  -- little-o statement after simplifying the zero linear part and the vanishing base value.
  have hDeriv0 : HasFDerivAt r (0 : E →L[ℝ] ℝ) x :=
    hBigO.hasFDerivAt (by norm_num : 1 < 2)
  simpa [r] using (hasFDerivAt_iff_isLittleO).mp hDeriv0

/-- The quadratic affine-model remainder bound in Proposition 1.5.9 forces the prescribed field
`g` to be the genuine first-order gradient witness of `f` at every point. -/
theorem hasGradientAt_of_sub_affineApproximation_norm_sq_bound
    (x : E) :
    HasGradientAt f (g x) x := by
  -- Convert the quadratic remainder estimate to the textbook little-o affine-approximation form.
  have hLittle := sub_affineApproximation_isLittleO_of_norm_sq_bound hquad x
  -- The chapter bridge `Definition_1_4_6` then identifies the prescribed field as the gradient.
  simpa [affineModelAt] using
    (hasGradientAt_iff_sub_affineApproximation_isLittleO).mpr hLittle

/-- Helper for Proposition 1.5.9: a pointwise gradient field with a global Lipschitz bound gives a
continuous Fréchet derivative field, hence a `C¹` function. -/
lemma contDiffOne_of_hasGradientAt_and_lipschitzField
    (hgrad : ∀ x, HasGradientAt f (g x) x)
    (hLip : LipschitzWith L g) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun x ↦ (InnerProductSpace.toDual ℝ E) (g x), ?_, ?_⟩
  · -- Transport the Lipschitz field through the Riesz map to obtain a continuous derivative field.
    exact (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E)).comp hLip.continuous
  · -- Each pointwise gradient witness packages directly as the corresponding Fréchet derivative.
    intro x
    simpa using (hgrad x).hasFDerivAt

/-- The recovered affine-model field from Proposition 1.5.9 agrees with the totalized gradient. -/
theorem gradient_eq_of_sub_affineApproximation_norm_sq_bound :
    ∇ f = g := by
  exact gradient_eq (hasGradientAt_of_sub_affineApproximation_norm_sq_bound hquad)

/-- Complete-space owner strengthening of Proposition 1.5.9: under the same quadratic affine-model
remainder bound, the canonical gradient belongs to the chapter's `C^{1,1}_L` owner class from
Definition 1.5.2. -/
theorem mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound :
    ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f) := by
  -- Reuse the local affine-approximation bridge to recover the intended gradient field everywhere.
  have hgrad : ∀ x, HasGradientAt f (g x) x :=
    hasGradientAt_of_sub_affineApproximation_norm_sq_bound hquad
  -- The noncomplete-space theorem supplies the global Lipschitz estimate for the prescribed field.
  have hLip : LipschitzWith L g :=
    lipschitzGradient_of_sub_affineApproximation_norm_sq_bound hquad
  refine ⟨contDiffOne_of_hasGradientAt_and_lipschitzField (hquad := hquad) hgrad hLip, ?_⟩
  -- Finally rewrite the canonical totalized gradient to the recovered field `g`.
  simpa [gradient_eq_of_sub_affineApproximation_norm_sq_bound hquad] using hLip

end CompleteSpace

end
