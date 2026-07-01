import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic search note: `lean_leansearch` is unavailable in this runner, so the candidate API was
-- checked directly against mathlib's `Metric.sphere`, `Complex.normSq`, and
-- `EuclideanGeometry.inversion`.

open EuclideanGeometry

/-- The complex homographic map `z ↦ (α z + β) / (γ z + δ)`. -/
def homographic_map (α β γ δ z : ℂ) : ℂ :=
  (α * z + β) / (γ * z + δ)

/-- The point `-δ / γ`; when `γ ≠ 0`, this is the finite pole of the non-affine complex
homographic map. -/
def homographic_pole (γ δ : ℂ) : ℂ :=
  -δ / γ

/-- The relation saying that `z₁` and `z₂` correspond under inversion in the circle with center
`a` and radius `r`, expressed through the canonical inversion owner
`EuclideanGeometry.inversion`. -/
def inversion_pair (a : ℂ) (r : ℝ) (z₁ z₂ : ℂ) : Prop :=
  z₁ ≠ a ∧ z₂ ≠ a ∧ inversion a r z₁ = z₂

/-- Helper for Exercise 5: away from the center, the canonical inversion equation is equivalent to
the textbook product relation `(z₁ - a) * conj (z₂ - a) = r²`. -/
theorem complex_inversion_eq_iff_mul_star_eq_radius_sq {a z₁ z₂ : ℂ} {r : ℝ}
    (hz₁ : z₁ ≠ a) (_hz₂ : z₂ ≠ a) :
    inversion a r z₁ = z₂ ↔ (z₁ - a) * star (z₂ - a) = (r ^ 2 : ℂ) := by
  have hz₁sub : z₁ - a ≠ 0 := sub_ne_zero.mpr hz₁
  have hdist : dist z₁ a ≠ 0 := by
    rwa [dist_ne_zero]
  have hnorm_mul : (z₁ - a) * star (z₁ - a) = Complex.normSq (z₁ - a) := by
    simpa [mul_comm] using (Complex.normSq_eq_conj_mul_self (z := z₁ - a)).symm
  have hsq_real : ((r / dist z₁ a) ^ 2) * dist z₁ a ^ 2 = r ^ 2 := by
    field_simp [hdist]
  have hsq_norm : ((r / ‖z₁ - a‖) ^ 2) * ‖z₁ - a‖ ^ 2 = r ^ 2 := by
    simpa [dist_eq_norm] using hsq_real
  constructor
  · intro hz
    -- Rewrite the inversion image as the scalar multiple given by `inversion_vsub_center`.
    have hvsub : z₂ - a = (((r / dist z₁ a) ^ 2 : ℝ) : ℂ) * (z₁ - a) := by
      simpa [hz, smul_eq_mul] using inversion_vsub_center a r z₁
    calc
      (z₁ - a) * star (z₂ - a)
          = (z₁ - a) * star ((((r / dist z₁ a) ^ 2 : ℝ) : ℂ) * (z₁ - a)) := by
              rw [hvsub]
      _ = (((r / dist z₁ a) ^ 2 : ℂ) * ((z₁ - a) * star (z₁ - a))) := by
            simp [mul_left_comm, mul_comm]
      _ = (((r / dist z₁ a) ^ 2 : ℂ) * Complex.normSq (z₁ - a)) := by
            rw [hnorm_mul]
      _ = ((((r / dist z₁ a) ^ 2) * Complex.normSq (z₁ - a) : ℝ) : ℂ) := by
            norm_num
      _ = (r ^ 2 : ℂ) := by
            rw [Complex.normSq_eq_norm_sq, dist_eq_norm]
            exact_mod_cast hsq_norm
  · intro hz
    -- Compare the target point with the canonical inversion image through the same center-offset.
    have hstar :
        star (z₁ - a) * (z₂ - a) = (r ^ 2 : ℂ) := by
      simpa [mul_comm] using congrArg star hz
    have hvsub : z₂ - a = (((r / dist z₁ a) ^ 2 : ℝ) : ℂ) * (z₁ - a) := by
      have hstar_ne : star (z₁ - a) ≠ 0 := by
        intro hzero
        apply hz₁sub
        simpa using congrArg star hzero
      apply mul_left_cancel₀ hstar_ne
      calc
        star (z₁ - a) * (z₂ - a) = (r ^ 2 : ℂ) := hstar
        _ = (((r / dist z₁ a) ^ 2 : ℂ) * Complex.normSq (z₁ - a)) := by
              rw [Complex.normSq_eq_norm_sq, dist_eq_norm]
              exact_mod_cast hsq_norm.symm
        _ = star (z₁ - a) * ((((r / dist z₁ a) ^ 2 : ℝ) : ℂ) * (z₁ - a)) := by
              rw [← hnorm_mul]
              simp [mul_assoc, mul_left_comm, mul_comm]
    have hinv : inversion a r z₁ - a = z₂ - a := by
      calc
        inversion a r z₁ - a = (((r / dist z₁ a) ^ 2 : ℝ) : ℂ) * (z₁ - a) := by
          simpa [smul_eq_mul] using inversion_vsub_center a r z₁
        _ = z₂ - a := hvsub.symm
    have hinv' := congrArg (fun z : ℂ ↦ z + a) hinv
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hinv'

/-- For complex inversion, the source's equation `(z₁ - a) * conj (z₂ - a) = r²` is the explicit
coordinate form of the canonical inversion relation. -/
theorem inversion_pair_iff {a z₁ z₂ : ℂ} {r : ℝ} :
    inversion_pair a r z₁ z₂ ↔
      z₁ ≠ a ∧ z₂ ≠ a ∧ (z₁ - a) * star (z₂ - a) = (r ^ 2 : ℂ) := by
  constructor
  · rintro ⟨hz₁, hz₂, hz⟩
    -- Replace the geometric inversion relation by its normalized complex equation.
    exact ⟨hz₁, hz₂, (complex_inversion_eq_iff_mul_star_eq_radius_sq hz₁ hz₂).mp hz⟩
  · rintro ⟨hz₁, hz₂, hz⟩
    -- Feed the explicit complex equation back into the canonical inversion relation.
    exact ⟨hz₁, hz₂, (complex_inversion_eq_iff_mul_star_eq_radius_sq hz₁ hz₂).mpr hz⟩

/-- The denominator governing whether the image of a circle under a homography is again a circle. -/
def image_inversion_den (a : ℂ) (r : ℝ) (γ δ : ℂ) : ℝ :=
  Complex.normSq (δ + a * γ) - r ^ 2 * Complex.normSq γ

/-- The intrinsic circle-membership condition for the homographic pole is equivalent to the
explicit coordinate equation used in the image formulas. -/
theorem homographic_pole_mem_inversion_circle_iff {a γ δ : ℂ} {r : ℝ} :
    homographic_pole γ δ ∈ Metric.sphere a |r| ↔
      Complex.normSq (homographic_pole γ δ - a) = r ^ 2 := by
  constructor
  · intro hpole
    rw [Metric.mem_sphere, dist_eq_norm] at hpole
    calc
      Complex.normSq (homographic_pole γ δ - a) = ‖homographic_pole γ δ - a‖ ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
      _ = |r| ^ 2 := by rw [hpole]
      _ = r ^ 2 := by rw [sq_abs]
  · intro hpole
    have hsq : ‖homographic_pole γ δ - a‖ ^ 2 = |r| ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq, sq_abs] using hpole
    -- Both sides are nonnegative, so equality of squares gives equality of distances.
    rw [Metric.mem_sphere, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp hsq

/-- The pole lies off the inversion circle exactly when the coordinate equation fails. -/
theorem homographic_pole_not_mem_inversion_circle_iff {a γ δ : ℂ} {r : ℝ} :
    homographic_pole γ δ ∉ Metric.sphere a |r| ↔
      Complex.normSq (homographic_pole γ δ - a) ≠ r ^ 2 := by
  simpa using not_congr (homographic_pole_mem_inversion_circle_iff (a := a) (γ := γ) (δ := δ)
    (r := r))

/-- Helper for Exercise 5: the image-circle denominator is the pole-offset equation scaled by
`normSq γ`. -/
theorem image_inversion_den_eq_normSq_gamma_mul_pole_offset {a γ δ : ℂ} {r : ℝ} (hγ : γ ≠ 0) :
    image_inversion_den a r γ δ =
      Complex.normSq γ * (Complex.normSq (homographic_pole γ δ - a) - r ^ 2) := by
  have hγsq : Complex.normSq γ ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hγ
  have hpole_sub : homographic_pole γ δ - a = -(δ + a * γ) / γ := by
    -- Expand the pole offset into the single quotient used by the norm computation.
    rw [homographic_pole]
    field_simp [hγ]
    ring
  calc
    image_inversion_den a r γ δ
        = Complex.normSq (δ + a * γ) - r ^ 2 * Complex.normSq γ := rfl
    _ = Complex.normSq γ * (Complex.normSq (homographic_pole γ δ - a) - r ^ 2) := by
      rw [hpole_sub, Complex.normSq_div, Complex.normSq_neg]
      field_simp [hγsq]

/-- Helper for Exercise 5: an inversion pair for a genuine corresponding-point relation has
nonzero radius. -/
theorem inversion_pair_radius_ne_zero {a z₁ z₂ : ℂ} {r : ℝ} (hz : inversion_pair a r z₁ z₂) :
    r ≠ 0 := by
  rintro rfl
  rcases hz with ⟨_, hz₂, hz⟩
  have : inversion a 0 z₁ = a := inversion_zero_radius a z₁
  exact hz₂ (hz.symm.trans this)

/-- Helper for Exercise 5: when the pole is off the source circle, the image-circle denominator
cannot vanish. -/
theorem image_inversion_den_ne_zero_of_pole_off_circle {a γ δ : ℂ} {r : ℝ} (hγ : γ ≠ 0)
    (hpole : homographic_pole γ δ ∉ Metric.sphere a |r|) :
    image_inversion_den a r γ δ ≠ 0 := by
  rw [image_inversion_den_eq_normSq_gamma_mul_pole_offset hγ]
  refine mul_ne_zero ?_ ?_
  · simpa [Complex.normSq_eq_zero] using hγ
  · exact sub_ne_zero.mpr ((homographic_pole_not_mem_inversion_circle_iff (a := a) (γ := γ)
      (δ := δ) (r := r)).1 hpole)

/-- The center of the image circle when a homography sends an inversion circle to a circle. -/
def image_inversion_center (a : ℂ) (r : ℝ) (α β γ δ : ℂ) : ℂ :=
  ((β + a * α) * star (δ + a * γ) - ((r ^ 2 : ℝ) : ℂ) * α * star γ) /
    (image_inversion_den a r γ δ : ℂ)

/-- The radius of the image circle when a homography sends an inversion circle to a circle. -/
def image_inversion_radius (a : ℂ) (r : ℝ) (α β γ δ : ℂ) : ℝ :=
  |r| * ‖α * δ - β * γ‖ / |image_inversion_den a r γ δ|

/-- The linear coefficient of the image line when a homography sends a circle through its pole to a
line. -/
def image_reflection_coeff (a : ℂ) (r : ℝ) (α β γ δ : ℂ) : ℂ :=
  ((r ^ 2 : ℝ) : ℂ) * star α * γ - (δ + a * γ) * star (β + a * α)

/-- The real constant defining the image line when a homography sends a circle through its pole to
a line. -/
def image_reflection_const (a : ℂ) (r : ℝ) (α β : ℂ) : ℝ :=
  r ^ 2 * Complex.normSq α - Complex.normSq (β + a * α)

/-- Helper for Exercise 5: on the pole-on-circle branch, multiplying the image-line coefficient by
`conj γ` factors it through the pole shift and the homography determinant. -/
theorem star_mul_image_reflection_coeff_eq_pole_shift_mul_star_det
    {a α β γ δ : ℂ} {r : ℝ} (hden : image_inversion_den a r γ δ = 0) :
    star γ * image_reflection_coeff a r α β γ δ =
      (δ + a * γ) * star (α * δ - β * γ) := by
  let s : ℂ := δ + a * γ
  let b : ℂ := β + a * α
  have hnorm : Complex.normSq (δ + a * γ) = r ^ 2 * Complex.normSq γ := by
    rw [image_inversion_den] at hden
    linarith [hden]
  have hnorm_cast :
      (Complex.normSq (δ + a * γ) : ℂ) = ((r ^ 2 * Complex.normSq γ : ℝ) : ℂ) := by
    exact_mod_cast hnorm
  have hγnorm : star γ * γ = Complex.normSq γ := by
    simp [Complex.normSq_eq_conj_mul_self]
  have hsnorm : (Complex.normSq s : ℂ) = star s * s := by
    simp [s, Complex.normSq_eq_conj_mul_self]
  have hbracket : star α * star s - star γ * star b = star α * star δ - star β * star γ := by
    dsimp [s, b]
    simp only [map_add, map_mul]
    ring
  -- Route correction: isolate the pole-on-circle substitution before expanding the coefficient.
  calc
    star γ * image_reflection_coeff a r α β γ δ
        = star γ *
            ((((r ^ 2 : ℝ) : ℂ) * star α * γ) -
              (δ + a * γ) * star (β + a * α)) := by
              rfl
    _ = star γ * ((((r ^ 2 : ℝ) : ℂ) * star α * γ)) -
          star γ * ((δ + a * γ) * star (β + a * α)) := by
            ring
    _ = ((((r ^ 2 : ℝ) : ℂ) * star α) * (star γ * γ)) -
          s * (star γ * star b) := by
            simp [s, b]
            ring
    _ = (((r ^ 2 * Complex.normSq γ : ℝ) : ℂ) * star α) -
          s * (star γ * star b) := by
            rw [hγnorm]
            norm_num
            ring
    _ = ((Complex.normSq s : ℂ) * star α) - s * (star γ * star b) := by
          rw [← show (Complex.normSq s : ℂ) = ((r ^ 2 * Complex.normSq γ : ℝ) : ℂ) by
            simpa [s] using hnorm_cast]
    _ = s * star (α * δ - β * γ) := by
          rw [hsnorm]
          calc
            star s * s * star α - s * (star γ * star b)
                = s * (star α * star s - star γ * star b) := by
                    ring
            _ = s * (star α * star δ - star β * star γ) := by
                  rw [hbracket]
            _ = s * star (α * δ - β * γ) := by
                  simp

theorem image_reflection_coeff_ne_zero
    {a α β γ δ : ℂ} {r : ℝ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0)
    (hr : r ≠ 0) (hpole : homographic_pole γ δ ∈ Metric.sphere a |r|) :
    image_reflection_coeff a r α β γ δ ≠ 0 := by
  have hden : image_inversion_den a r γ δ = 0 := by
    -- The pole-on-circle hypothesis is exactly the vanishing condition for the image denominator.
    have hpole_eq :
        Complex.normSq (homographic_pole γ δ - a) = r ^ 2 :=
      (homographic_pole_mem_inversion_circle_iff (a := a) (γ := γ) (δ := δ) (r := r)).1 hpole
    rw [image_inversion_den_eq_normSq_gamma_mul_pole_offset hγ, hpole_eq, sub_self, mul_zero]
  have hfactor :
      star γ * image_reflection_coeff a r α β γ δ =
        (δ + a * γ) * star (α * δ - β * γ) :=
    star_mul_image_reflection_coeff_eq_pole_shift_mul_star_det (a := a) (α := α) (β := β)
      (γ := γ) (δ := δ) (r := r) hden
  intro hcoeff
  have hrhs_zero : (δ + a * γ) * star (α * δ - β * γ) = 0 := by
    simpa [hcoeff] using hfactor
  rcases mul_eq_zero.mp hrhs_zero with hshift | hdet_star
  · have hγnorm : Complex.normSq γ ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using hγ
    have hr_sq_mul : r ^ 2 * Complex.normSq γ = 0 := by
      rw [image_inversion_den, hshift, Complex.normSq_zero] at hden
      linarith
    have hr_sq : r ^ 2 = 0 := (mul_eq_zero.mp hr_sq_mul).resolve_right hγnorm
    have hr_zero : r = 0 := by nlinarith
    exact hr hr_zero
  · have hdet_zero : α * δ - β * γ = 0 := by
      simpa using congrArg star hdet_star
    exact hdet hdet_zero

/-- The affine line in `ℂ` with textbook equation `c * w + conj c * conj w = t`. It is presented
canonically as an affine line, while the explicit coefficient-constant equation is a bridge
description. The hypothesis `c ≠ 0` is exactly what makes the textbook equation define a line
rather than all of `ℂ` or the empty set. -/
def reflection_line (c : ℂ) (t : ℝ) (hc : c ≠ 0) : AffineSubspace ℝ ℂ :=
  let u : ℂˣ := Units.mk0 c hc
  line[ℝ, ((t / (2 * Complex.normSq (u : ℂ)) : ℝ) : ℂ) * star (u : ℂ),
    ((t / (2 * Complex.normSq (u : ℂ)) : ℝ) : ℂ) * star (u : ℂ) + Complex.I * star (u : ℂ)]

instance reflection_line_nonempty (c : ℂ) (t : ℝ) (hc : c ≠ 0) :
    Nonempty (reflection_line c t hc) := by
  refine ⟨⟨((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c, ?_⟩⟩
  exact left_mem_affineSpan_pair ℝ _ _

/-- The image line when a homography sends a circle through its pole to a line. -/
def image_reflection_line (a : ℂ) (r : ℝ) (α β γ δ : ℂ)
    (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0)
    (hpole : homographic_pole γ δ ∈ Metric.sphere a |r|) : AffineSubspace ℝ ℂ :=
  if hc : image_reflection_coeff a r α β γ δ ≠ 0 then
    reflection_line
      (image_reflection_coeff a r α β γ δ)
      (image_reflection_const a r α β)
      hc
  else
    ⊤

instance image_reflection_line_nonempty (a : ℂ) (r : ℝ) (α β γ δ : ℂ)
    (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0)
    (hpole : homographic_pole γ δ ∈ Metric.sphere a |r|) :
    Nonempty (image_reflection_line a r α β γ δ hdet hγ hpole) := by
  classical
  unfold image_reflection_line
  by_cases hc : image_reflection_coeff a r α β γ δ ≠ 0
  · simpa [hc] using
      (reflection_line_nonempty
        (image_reflection_coeff a r α β γ δ)
        (image_reflection_const a r α β)
        hc)
  · refine ⟨⟨0, ?_⟩⟩
    simp [hc]

/-- Helper for Exercise 5: once the nonzero-radius hypothesis is available, the total image-line
definition reduces to the intended reflection line. -/
theorem image_reflection_line_eq_reflection_line {a α β γ δ : ℂ} {r : ℝ}
    (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0) (hr : r ≠ 0)
    (hpole : homographic_pole γ δ ∈ Metric.sphere a |r|) :
    image_reflection_line a r α β γ δ hdet hγ hpole =
      reflection_line
        (image_reflection_coeff a r α β γ δ)
        (image_reflection_const a r α β)
        (image_reflection_coeff_ne_zero hdet hγ hr hpole) := by
  -- The repaired total definition collapses back to the geometric branch used in the theorem.
  unfold image_reflection_line
  simp [image_reflection_coeff_ne_zero hdet hγ hr hpole]

/-- Helper for Exercise 5: membership in `reflection_line c t hc` can be read using the
distinguished base point and direction chosen in its definition. -/
theorem reflection_line_vsub_basepoint_iff_real_smul_direction {c w : ℂ} {t : ℝ} (hc : c ≠ 0) :
    let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
    w ∈ reflection_line c t hc ↔ ∃ s : ℝ, w - u = s • (Complex.I * star c) := by
  dsimp
  -- Unfold the packaged reflection line back to the affine span of its chosen base point and
  -- direction point.
  rw [show reflection_line c t hc =
      line[ℝ, ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c,
        ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c + Complex.I * star c] by
      simp [reflection_line]]
  -- Translate membership to the vector condition relative to the left endpoint of the affine line.
  rw [← vsub_vadd w (((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c),
    vadd_left_mem_affineSpan_pair]
  -- On `ℂ`, the line direction is exactly `Complex.I * star c`.
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, by simpa using hs.symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, by simpa using hs.symm⟩

/-- Helper for Exercise 5: the kernel of the real line equation
`d ↦ c * d + conj c * conj d` is the real span of `I * conj c`. -/
theorem reflection_line_equation_zero_iff_real_smul_direction {c d : ℂ} (hc : c ≠ 0) :
    c * d + star c * star d = 0 ↔ ∃ s : ℝ, d = s • (Complex.I * star c) := by
  constructor
  · intro hzero
    let q : ℂ := d / (Complex.I * star c)
    have hstarc : star c ≠ 0 := by
      intro hstar
      apply hc
      simpa using congrArg star hstar
    have hden : Complex.I * star c ≠ 0 := mul_ne_zero Complex.I_ne_zero hstarc
    have hfactor :
        c * d + star c * star d = (Complex.I * (Complex.normSq c : ℂ)) * (q - star q) := by
      -- Rewrite the displacement through the chosen normalizing denominator.
      have hd : d = q * (Complex.I * star c) := by
        exact (div_mul_cancel₀ d hden).symm
      rw [hd]
      simp [q, Complex.normSq_eq_conj_mul_self]
      ring
    have hnorm : (Complex.normSq c : ℂ) ≠ 0 := by
      exact_mod_cast (show Complex.normSq c ≠ 0 by simpa [Complex.normSq_eq_zero] using hc)
    have hmulzero : (Complex.I * (Complex.normSq c : ℂ)) * (q - star q) = 0 := by
      rw [← hfactor]
      exact hzero
    have hq_eq : q = star q := by
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp hmulzero).resolve_left
        (mul_ne_zero Complex.I_ne_zero hnorm)
    have hq_real : q = (Complex.re q : ℂ) := by
      have him : Complex.im q = 0 := Complex.conj_eq_iff_im.mp hq_eq.symm
      calc
        q = (Complex.re q : ℂ) + (Complex.im q : ℂ) * Complex.I := by
          symm
          exact Complex.re_add_im q
        _ = (Complex.re q : ℂ) := by simp [him]
    refine ⟨Complex.re q, ?_⟩
    -- Replace the scalar by the real part of `q`, which equals `q` because `q` is self-adjoint.
    calc
      d = q * (Complex.I * star c) := by
        exact (div_mul_cancel₀ d hden).symm
      _ = (Complex.re q : ℂ) * (Complex.I * star c) := by
        exact congrArg (fun z : ℂ ↦ z * (Complex.I * star c)) hq_real
      _ = Complex.re q • (Complex.I * star c) := by simp
  · rintro ⟨s, rfl⟩
    -- A direction vector of the reflection line annihilates the defining linear equation.
    simp
    ring

/-- For `c ≠ 0`, membership in `reflection_line c t` is exactly the textbook complex equation
`c * w + conj c * conj w = t`. -/
theorem mem_reflection_line_iff {c w : ℂ} {t : ℝ} (hc : c ≠ 0) :
    w ∈ reflection_line c t hc ↔ c * w + star c * star w = (t : ℂ) := by
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  have hnorm : Complex.normSq c ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hc
  have hbase :
      c * u + star c * star u = (t : ℂ) := by
    -- Evaluate the defining equation at the distinguished base point of the affine line.
    dsimp [u]
    calc
      c * (((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c) +
            star c * star ((((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c))
          = (((t / (2 * Complex.normSq c)) * Complex.normSq c +
                (t / (2 * Complex.normSq c)) * Complex.normSq c : ℝ) : ℂ) := by
              simp [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm, mul_comm]
      _ = (t : ℂ) := by
        have hreal :
            (t / (2 * Complex.normSq c)) * Complex.normSq c +
              (t / (2 * Complex.normSq c)) * Complex.normSq c = t := by
          field_simp [hnorm]
          ring
        exact_mod_cast hreal
  have hshift :
      c * (w - u) + star c * star (w - u) =
        (c * w + star c * star w) - (c * u + star c * star u) := by
    -- Translate the textbook equation from `w` to the distinguished base point `u`.
    simp [sub_eq_add_neg, mul_add]
    ring
  constructor
  · intro hw
    have hdir :
        ∃ s : ℝ, w - u = s • (Complex.I * star c) :=
      (reflection_line_vsub_basepoint_iff_real_smul_direction (c := c) (w := w) (t := t) hc).1 hw
    have hzero :
        c * (w - u) + star c * star (w - u) = 0 :=
      (reflection_line_equation_zero_iff_real_smul_direction (c := c) (d := w - u) hc).2 hdir
    calc
      c * w + star c * star w
          = (c * (w - u) + star c * star (w - u)) + (c * u + star c * star u) := by
              rw [hshift]
              ring
      _ = (0 : ℂ) + (t : ℂ) := by rw [hzero, hbase]
      _ = (t : ℂ) := by simp
  · intro hw
    have hzero :
        c * (w - u) + star c * star (w - u) = 0 := by
      rw [hshift, hw, hbase]
      ring
    have hdir :
        ∃ s : ℝ, w - u = s • (Complex.I * star c) :=
      (reflection_line_equation_zero_iff_real_smul_direction (c := c) (d := w - u) hc).1 hzero
    exact (reflection_line_vsub_basepoint_iff_real_smul_direction (c := c) (w := w) (t := t) hc).2
      hdir

/-- Helper for Exercise 5: away from the source circle, the image inversion radius is nonzero. -/
theorem image_inversion_radius_ne_zero_of_pole_off_circle
    {a α β γ δ : ℂ} {r : ℝ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0) (hr : r ≠ 0)
    (hpole : homographic_pole γ δ ∉ Metric.sphere a |r|) :
    image_inversion_radius a r α β γ δ ≠ 0 := by
  -- The explicit radius formula is a quotient of three nonzero real factors.
  unfold image_inversion_radius
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (abs_ne_zero.mpr hr) (norm_ne_zero_iff.mpr hdet)
  · exact abs_ne_zero.mpr (image_inversion_den_ne_zero_of_pole_off_circle hγ hpole)

/-- Helper for Exercise 5: once the source pair satisfies the inversion equation, the shifted
source brackets multiply to the transformed denominator product. -/
theorem source_shifted_factor_product {a z₁ z₂ γ δ : ℂ} {r : ℝ}
    (hz : (z₁ - a) * star (z₂ - a) = (r ^ 2 : ℂ)) :
    (star (δ + a * γ) * (z₁ - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)) *
        star (star (δ + a * γ) * (z₂ - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)) =
      ((r ^ 2 : ℂ) * (γ * z₁ + δ) * star (γ * z₂ + δ)) := by
  let s : ℂ := δ + a * γ
  let x : ℂ := z₁ - a
  let y : ℂ := star (z₂ - a)
  let ρ : ℂ := (r ^ 2 : ℂ)
  have hzxy : x * y = ρ := by
    simpa [x, y, ρ] using hz
  have hγz₁ : γ * z₁ + δ = γ * x + s := by
    -- Recenter the first denominator around the inversion center `a`.
    dsimp [x, s]
    ring
  have hstar_γz₂ : star (γ * z₂ + δ) = star γ * y + star s := by
    have hγz₂ : γ * z₂ + δ = γ * (z₂ - a) + s := by
      -- Recenter the second denominator in the same source-faithful form.
      dsimp [s]
      ring
    rw [hγz₂]
    simp [y, s, mul_comm, mul_left_comm, mul_assoc]
  -- Route correction: isolate the pure source-side bracket identity before returning to the
  -- image-center denominator-clearing algebra.
  calc
    (star (δ + a * γ) * (z₁ - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)) *
        star (star (δ + a * γ) * (z₂ - a) + (((r ^ 2 : ℝ) : ℂ) * star γ))
        = (star s * x + ρ * star γ) * (s * y + ρ * γ) := by
            simp [x, y, s, ρ, mul_comm, mul_left_comm, mul_assoc]
    _ = ρ * (γ * x + s) * (star γ * y + star s) := by
          -- Replace the source product by `ρ` so the two sides become the same polynomial.
          rw [← hzxy]
          ring
    _ = ρ * (γ * z₁ + δ) * star (γ * z₂ + δ) := by
          rw [← hγz₁, ← hstar_γz₂]
    _ = ((r ^ 2 : ℂ) * (γ * z₁ + δ) * star (γ * z₂ + δ)) := by
          simp [ρ]

/-- Helper for Exercise 5: if the homographic pole lies on the source circle, then the shifted
pole offset satisfies the normalized denominator equation `star s * s = r² * star γ * γ`. -/
theorem pole_on_circle_denominator_eq {a γ δ : ℂ} {r : ℝ}
    (hden : image_inversion_den a r γ δ = 0) :
    star (δ + a * γ) * (δ + a * γ) = ((r ^ 2 : ℂ)) * (star γ * γ) := by
  have hnorm : Complex.normSq (δ + a * γ) = r ^ 2 * Complex.normSq γ := by
    rw [image_inversion_den] at hden
    linarith
  have hnorm_cast :
      (Complex.normSq (δ + a * γ) : ℂ) = ((r ^ 2 * Complex.normSq γ : ℝ) : ℂ) := by
    exact_mod_cast hnorm
  -- Rewrite the real norm-square equation into the complex conjugate-multiplication form.
  simpa [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm, mul_comm] using hnorm_cast

/-- Helper for Exercise 5: after substituting the pole-on-circle denominator relation, the cleared
reflection numerator factors through the source inversion relation `x * y = r²`. -/
theorem homographic_map_cross_reflection_equation_cleared_factor
    {x y s b α γ : ℂ} {r : ℝ}
    (hs : star s * s = ((r ^ 2 : ℂ)) * (star γ * γ)) :
    let ρ : ℂ := (r ^ 2 : ℂ)
    let c : ℂ := ρ * star α * γ - s * star b
    let Δ : ℂ := α * s - b * γ
    c * (α * x + b) * (y * star γ + star s) +
        star c * (star α * y + star b) * (γ * x + s) -
        (ρ * (Complex.normSq α : ℂ) - (Complex.normSq b : ℂ)) *
          ((γ * x + s) * (y * star γ + star s)) =
      (x * y - ρ) * (α * star γ * c - b * γ * star Δ) := by
  -- Route correction: rewrite the pole condition first so the remaining numerator factors only by
  -- the source relation `x * y - r²`.
  have hs' : s * star s = ((r ^ 2 : ℂ)) * (γ * star γ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hs
  have hs0 : ((r ^ 2 : ℂ)) * (γ * star γ) - s * star s = 0 := by
    rw [hs']
    ring
  dsimp
  simp [Complex.normSq_eq_conj_mul_self]
  calc
    (↑r ^ 2 * star α * γ - s * star b) * (α * x + b) * (y * star γ + star s) +
        (↑r ^ 2 * α * star γ - star s * b) * (star α * y + star b) * (γ * x + s) -
        (↑r ^ 2 * (star α * α) - star b * b) * ((γ * x + s) * (y * star γ + star s))
        =
      (x * y - ↑r ^ 2) *
          (α * star γ * (↑r ^ 2 * star α * γ - s * star b) -
            b * γ * (star α * star s - star b * star γ)) +
        ((((r ^ 2 : ℂ)) * (γ * star γ) - s * star s) *
          (α * star α * ((r ^ 2 : ℂ)) + α * star b * x + star α * b * y + b * star b)) := by
            ring
    _ = (x * y - ↑r ^ 2) *
          (α * star γ * (↑r ^ 2 * star α * γ - s * star b) -
            b * γ * (star α * star s - star b * star γ)) := by
          rw [hs0]
          ring

/-- Helper for Exercise 5: clearing the two explicit denominators isolates the centered-image
numerator before any use of the source inversion relation. -/
theorem homographic_map_sub_image_inversion_center_num
    {a α β γ δ z : ℂ} {r : ℝ} (hz_ne_pole : γ * z + δ ≠ 0)
    (hD : image_inversion_den a r γ δ ≠ 0) :
    ((γ * z + δ) * (image_inversion_den a r γ δ : ℂ)) *
        (homographic_map α β γ δ z - image_inversion_center a r α β γ δ) =
      (α * z + β) * (image_inversion_den a r γ δ : ℂ) -
        (γ * z + δ) *
          (((β + a * α) * star (δ + a * γ)) - (((r ^ 2 : ℝ) : ℂ) * α * star γ)) := by
  have hD_complex : (image_inversion_den a r γ δ : ℂ) ≠ 0 := by
    exact_mod_cast hD
  -- Route correction: first clear the homography and image-center denominators, then leave the
  -- remaining recentering/factorization to a separate pure polynomial lemma.
  unfold homographic_map image_inversion_center
  -- `field_simp` removes the two explicit divisions and leaves a polynomial identity.
  field_simp [hz_ne_pole, hD_complex]

/-- Helper for Exercise 5: after the denominators are cleared, the centered-image numerator
re-centers around `z - a` and factors through the homography determinant. -/
theorem homographic_map_sub_image_inversion_center_cleared
    {a α β γ δ z : ℂ} {r : ℝ} (hz_ne_pole : γ * z + δ ≠ 0)
    (hD : image_inversion_den a r γ δ ≠ 0) :
    ((γ * z + δ) * (image_inversion_den a r γ δ : ℂ)) *
        (homographic_map α β γ δ z - image_inversion_center a r α β γ δ) =
      (α * δ - β * γ) *
        (star (δ + a * γ) * (z - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)) := by
  let s : ℂ := δ + a * γ
  let ρ : ℂ := (r ^ 2 : ℂ)
  have hden_expand :
      (image_inversion_den a r γ δ : ℂ) = star s * s - ρ * (star γ * γ) := by
    -- Rewrite the real denominator into the complex norm-square polynomial used by Cartan's
    -- centered-image factorization.
    dsimp [s, ρ]
    simp [image_inversion_den, Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm, mul_comm]
  have hrecenter : γ * z + δ = γ * (z - a) + s := by
    -- Recenter the homographic denominator around the inversion center `a`.
    dsimp [s]
    ring
  calc
    ((γ * z + δ) * (image_inversion_den a r γ δ : ℂ)) *
        (homographic_map α β γ δ z - image_inversion_center a r α β γ δ)
        =
      (α * z + β) * (image_inversion_den a r γ δ : ℂ) -
        (γ * z + δ) *
          (((β + a * α) * star (δ + a * γ)) - (((r ^ 2 : ℝ) : ℂ) * α * star γ)) := by
            exact homographic_map_sub_image_inversion_center_num
              (a := a) (α := α) (β := β) (γ := γ) (δ := δ) (z := z) (r := r)
              hz_ne_pole hD
    _ = (α * δ - β * γ) * (star s * (z - a) + ρ * star γ) := by
          rw [hden_expand, hrecenter]
          dsimp [s, ρ]
          -- Normalize the two equivalent radius-square casts before expanding the polynomial.
          rw [show ((r : ℂ) ^ 2) = (((r ^ 2 : ℝ) : ℂ)) by norm_num]
          ring
    _ = (α * δ - β * γ) *
          (star (δ + a * γ) * (z - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)) := by
            simp [s, ρ]

/-- Helper for Exercise 5: once the homographic denominators are cleared, the transformed points
satisfy the inversion equation for the image circle. -/
theorem homographic_image_centered_mul_star_eq_image_radius_sq
    {a z₁ z₂ α β γ δ : ℂ} {r : ℝ}
    (hz : (z₁ - a) * star (z₂ - a) = (r ^ 2 : ℂ))
    (hz₁_ne_pole : γ * z₁ + δ ≠ 0) (hz₂_ne_pole : γ * z₂ + δ ≠ 0)
    (hD : image_inversion_den a r γ δ ≠ 0) :
    (homographic_map α β γ δ z₁ - image_inversion_center a r α β γ δ) *
        star (homographic_map α β γ δ z₂ - image_inversion_center a r α β γ δ) =
      ((image_inversion_radius a r α β γ δ) ^ 2 : ℂ) := by
  let D : ℝ := image_inversion_den a r γ δ
  let w₁ : ℂ := homographic_map α β γ δ z₁
  let w₂ : ℂ := homographic_map α β γ δ z₂
  let A : ℂ := image_inversion_center a r α β γ δ
  let Δ : ℂ := α * δ - β * γ
  let B₁ : ℂ := star (δ + a * γ) * (z₁ - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)
  let B₂ : ℂ := star (δ + a * γ) * (z₂ - a) + (((r ^ 2 : ℝ) : ℂ) * star γ)
  have h₁ :
      ((γ * z₁ + δ) * (D : ℂ)) * (w₁ - A) = Δ * B₁ := by
    simpa [D, w₁, A, Δ, B₁] using
      homographic_map_sub_image_inversion_center_cleared
        (a := a) (α := α) (β := β) (γ := γ) (δ := δ) (z := z₁) (r := r)
        hz₁_ne_pole hD
  have h₂ :
      ((γ * z₂ + δ) * (D : ℂ)) * (w₂ - A) = Δ * B₂ := by
    simpa [D, w₂, A, Δ, B₂] using
      homographic_map_sub_image_inversion_center_cleared
        (a := a) (α := α) (β := β) (γ := γ) (δ := δ) (z := z₂) (r := r)
        hz₂_ne_pole hD
  have h₂_star :
      star (((γ * z₂ + δ) * (D : ℂ)) * (w₂ - A)) = star (Δ * B₂) := by
    -- Conjugate the second cleared identity so the target centered factor becomes `star (w₂ - A)`.
    simpa [map_mul, D, w₂, A, Δ, B₂] using congrArg star h₂
  have hsource :
      B₁ * star B₂ = ((r ^ 2 : ℂ) * (γ * z₁ + δ) * star (γ * z₂ + δ)) := by
    -- Reuse the source-side factorization proved from the original inversion relation.
    simpa [B₁, B₂] using
      source_shifted_factor_product (a := a) (z₁ := z₁) (z₂ := z₂) (γ := γ) (δ := δ) (r := r) hz
  have hscaled_radius :
      (((D ^ 2) * (image_inversion_radius a r α β γ δ) ^ 2 : ℝ) : ℂ) =
        ((r ^ 2 : ℂ) * (Complex.normSq Δ : ℂ)) := by
    have hD_sq : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
    have hreal :
        D ^ 2 * (image_inversion_radius a r α β γ δ) ^ 2 =
          r ^ 2 * Complex.normSq Δ := by
      -- Square the explicit radius formula and clear the real denominator `|D|²`.
      unfold image_inversion_radius
      rw [pow_two, div_pow, mul_pow, sq_abs, sq_abs, Complex.normSq_eq_norm_sq]
      field_simp [hD_sq]
      ring
    exact_mod_cast hreal
  have hfactor_eq :
      (((γ * z₁ + δ) * star (γ * z₂ + δ)) * (((D ^ 2 : ℝ) : ℂ))) *
          ((w₁ - A) * star (w₂ - A)) =
        (((γ * z₁ + δ) * star (γ * z₂ + δ)) * (((D ^ 2 : ℝ) : ℂ))) *
          (((image_inversion_radius a r α β γ δ) ^ 2 : ℂ)) := by
    -- Both sides are the same scaled identity after substituting the source factorization and the
    -- explicit image-radius square.
    calc
      (((γ * z₁ + δ) * star (γ * z₂ + δ)) * (((D ^ 2 : ℝ) : ℂ))) *
          ((w₁ - A) * star (w₂ - A))
          =
        (((γ * z₁ + δ) * (D : ℂ)) * (w₁ - A)) *
          star (((γ * z₂ + δ) * (D : ℂ)) * (w₂ - A)) := by
            simp [D, mul_assoc, mul_left_comm, mul_comm]
            ring
      _ = (Δ * B₁) * star (Δ * B₂) := by rw [h₁, h₂_star]
      _ = ((Complex.normSq Δ : ℂ) * (B₁ * star B₂)) := by
            simp [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm, mul_comm]
      _ = ((Complex.normSq Δ : ℂ) *
            ((r ^ 2 : ℂ) * (γ * z₁ + δ) * star (γ * z₂ + δ))) := by
            rw [hsource]
      _ = (((γ * z₁ + δ) * star (γ * z₂ + δ)) *
            (((D ^ 2) * (image_inversion_radius a r α β γ δ) ^ 2 : ℝ) : ℂ)) := by
            rw [hscaled_radius]
            ring
      _ = (((γ * z₁ + δ) * star (γ * z₂ + δ)) * (((D ^ 2 : ℝ) : ℂ))) *
            (((image_inversion_radius a r α β γ δ) ^ 2 : ℂ)) := by
            norm_num
            ring
  have hcommon_ne :
      (((γ * z₁ + δ) * star (γ * z₂ + δ)) * (((D ^ 2 : ℝ) : ℂ))) ≠ 0 := by
    have hz₂_star_ne : star (γ * z₂ + δ) ≠ 0 := by
      intro hstar
      apply hz₂_ne_pole
      simpa using congrArg star hstar
    have hD_sq_complex : (((D ^ 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 hD)
    exact mul_ne_zero (mul_ne_zero hz₁_ne_pole hz₂_star_ne) hD_sq_complex
  -- Cancel the common nonzero factor to recover the normalized image-circle equation itself.
  exact mul_left_cancel₀ hcommon_ne hfactor_eq

/-- Helper for Exercise 5: on the pole-on-circle branch, the transformed points satisfy the
degenerate line equation describing the image reflection line. -/
theorem homographic_map_cross_reflection_equation
    {a z₁ z₂ α β γ δ : ℂ} {r : ℝ}
    (hz : (z₁ - a) * star (z₂ - a) = (r ^ 2 : ℂ))
    (hz₁_ne_pole : γ * z₁ + δ ≠ 0) (hz₂_ne_pole : γ * z₂ + δ ≠ 0)
    (hden : image_inversion_den a r γ δ = 0) :
    image_reflection_coeff a r α β γ δ * homographic_map α β γ δ z₁ +
        star (image_reflection_coeff a r α β γ δ) *
          star (homographic_map α β γ δ z₂) =
      (image_reflection_const a r α β : ℂ) := by
  let x : ℂ := z₁ - a
  let y : ℂ := star (z₂ - a)
  let s : ℂ := δ + a * γ
  let b : ℂ := β + a * α
  let ρ : ℂ := (r ^ 2 : ℂ)
  let c : ℂ := ρ * star α * γ - s * star b
  let t : ℂ := ρ * (Complex.normSq α : ℂ) - (Complex.normSq b : ℂ)
  have hs : star s * s = ρ * (star γ * γ) := by
    -- Replace the vanishing image denominator by the normalized pole-on-circle equation first.
    simpa [s, ρ] using pole_on_circle_denominator_eq (a := a) (γ := γ) (δ := δ) (r := r) hden
  have hzxy : x * y = ρ := by
    -- Recenter the source inversion relation in the shifted variables `x` and `y`.
    simpa [x, y, ρ] using hz
  have hαz₁ : α * z₁ + β = α * x + b := by
    -- Recenter the first transformed numerator around `a`.
    dsimp [x, b]
    ring
  have hγz₁ : γ * z₁ + δ = γ * x + s := by
    -- Recenter the first transformed denominator around `a`.
    dsimp [x, s]
    ring
  have hstar_αz₂ : star (α * z₂ + β) = star α * y + star b := by
    -- Express the conjugated second numerator using the shifted source coordinate `y`.
    dsimp [y, b]
    simp
    ring
  have hstar_γz₂ : star (γ * z₂ + δ) = y * star γ + star s := by
    -- Express the conjugated second denominator in the same shifted coordinates.
    dsimp [y, s]
    simp
    ring
  have hden₂ : y * star γ + star s ≠ 0 := by
    -- The second transformed denominator stays nonzero after conjugation.
    have hstar_ne : star (γ * z₂ + δ) ≠ 0 := by
      intro hzero
      apply hz₂_ne_pole
      simpa using congrArg star hzero
    simpa [hstar_γz₂] using hstar_ne
  have hden₁ : γ * x + s ≠ 0 := by
    -- The first transformed denominator is the original non-pole hypothesis in shifted form.
    simpa [hγz₁] using hz₁_ne_pole
  have hnumerator :
      c * (α * x + b) * (y * star γ + star s) +
          star c * (star α * y + star b) * (γ * x + s) =
        t * ((γ * x + s) * (y * star γ + star s)) := by
    -- The cleared numerator is exactly the source factor `(x * y - ρ)` times a residual factor.
    have hfactor :=
      homographic_map_cross_reflection_equation_cleared_factor
        (x := x) (y := y) (s := s) (b := b) (α := α) (γ := γ) (r := r) hs
    have hzero :
        c * (α * x + b) * (y * star γ + star s) +
            star c * (star α * y + star b) * (γ * x + s) -
            t * ((γ * x + s) * (y * star γ + star s)) = 0 := by
      simpa [c, t, ρ, Complex.normSq_eq_conj_mul_self, hzxy] using hfactor
    exact sub_eq_zero.mp hzero
  have hcommon_ne : ((γ * x + s) * (y * star γ + star s)) ≠ 0 := by
    exact mul_ne_zero hden₁ hden₂
  have hquotient :
      c * ((α * x + b) / (γ * x + s)) +
          star c * ((star α * y + star b) / (y * star γ + star s)) =
        t := by
    -- Cancel each homographic denominator separately before comparing with the cleared numerator.
    have hmul₁ :
        c * ((α * x + b) / (γ * x + s)) * ((γ * x + s) * (y * star γ + star s)) =
          c * (α * x + b) * (y * star γ + star s) := by
      calc
        c * ((α * x + b) / (γ * x + s)) * ((γ * x + s) * (y * star γ + star s))
            = c * ((((α * x + b) / (γ * x + s)) * (γ * x + s)) * (y * star γ + star s)) := by
                ring
        _ = c * ((α * x + b) * (y * star γ + star s)) := by
              rw [div_mul_cancel₀ _ hden₁]
        _ = c * (α * x + b) * (y * star γ + star s) := by
              ring
    have hmul₂ :
        star c * ((star α * y + star b) / (y * star γ + star s)) *
            ((γ * x + s) * (y * star γ + star s)) =
          star c * (star α * y + star b) * (γ * x + s) := by
      calc
        star c * ((star α * y + star b) / (y * star γ + star s)) *
            ((γ * x + s) * (y * star γ + star s))
            =
          star c * ((((star α * y + star b) / (y * star γ + star s)) *
            (y * star γ + star s)) * (γ * x + s)) := by
              ring
        _ = star c * ((star α * y + star b) * (γ * x + s)) := by
              rw [div_mul_cancel₀ _ hden₂]
        _ = star c * (star α * y + star b) * (γ * x + s) := by
              ring
    apply mul_right_cancel₀ hcommon_ne
    calc
      (c * ((α * x + b) / (γ * x + s)) +
            star c * ((star α * y + star b) / (y * star γ + star s))) *
          ((γ * x + s) * (y * star γ + star s))
          =
        c * ((α * x + b) / (γ * x + s)) * ((γ * x + s) * (y * star γ + star s)) +
          star c * ((star α * y + star b) / (y * star γ + star s)) *
            ((γ * x + s) * (y * star γ + star s)) := by
              ring
      _ = c * (α * x + b) * (y * star γ + star s) +
            star c * (star α * y + star b) * (γ * x + s) := by
              rw [hmul₁, hmul₂]
      _ = t * ((γ * x + s) * (y * star γ + star s)) := hnumerator
  have hstar_map₂ :
      star (homographic_map α β γ δ z₂) = (star α * y + star b) / (y * star γ + star s) := by
    -- Conjugating the second transformed point converts its rational form to the shifted data.
    rw [homographic_map]
    calc
      star ((α * z₂ + β) / (γ * z₂ + δ))
          = star (α * z₂ + β) / star (γ * z₂ + δ) := by simp
      _ = (star α * y + star b) / (y * star γ + star s) := by
            rw [hstar_αz₂, hstar_γz₂]
  -- Return from the shifted coordinates to the original image-line equation.
  calc
    image_reflection_coeff a r α β γ δ * homographic_map α β γ δ z₁ +
        star (image_reflection_coeff a r α β γ δ) *
          star (homographic_map α β γ δ z₂)
        =
      c * ((α * x + b) / (γ * x + s)) +
        star c * ((star α * y + star b) / (y * star γ + star s)) := by
          rw [homographic_map, hαz₁, hγz₁, hstar_map₂]
          simp [c, image_reflection_coeff, b, s, ρ]
    _ = t := hquotient
    _ = (image_reflection_const a r α β : ℂ) := by
          simp [t, image_reflection_const, b, ρ, Complex.normSq_eq_conj_mul_self]

/-- Helper for Exercise 5: the normal vector `conj c` is orthogonal to the direction of the
reflection line `reflection_line c t hc`. -/
theorem reflection_line_star_mem_direction_orthogonal {c : ℂ} {t : ℝ} (hc : c ≠ 0) :
    star c ∈ (reflection_line c t hc).directionᗮ := by
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  let v : ℂ := u + Complex.I * star c
  have hvsub : v - u = Complex.I * star c := by
    -- The explicit line direction is the tangent vector `I * conj c`.
    simp [u, v]
  have hline : reflection_line c t hc = line[ℝ, u, v] := by
    -- Unfold the packaged line back to the affine span of its two chosen points.
    simp [reflection_line, u, v]
  -- Reduce orthogonality to the single generator of the affine line direction.
  simpa [hline] using
    (by
      rw [direction_affineSpan, vectorSpan_pair_rev,
        Submodule.mem_orthogonal_singleton_iff_inner_left]
      simpa [hvsub, smul_eq_mul, mul_comm] using
        (real_inner_I_smul_self (𝕜 := ℂ) (E := ℂ) (x := star c)) :
      star c ∈ (line[ℝ, u, v] : AffineSubspace ℝ ℂ).directionᗮ)

/-- Helper for Exercise 5: the antisymmetric line equation
`c * d - conj c * conj d = 0` cuts out the real span of `conj c`. -/
theorem mul_sub_star_eq_zero_iff_real_smul_star {c d : ℂ} (hc : c ≠ 0) :
    c * d - star c * star d = 0 ↔ ∃ s : ℝ, d = s • star c := by
  constructor
  · intro hzero
    let q : ℂ := d / star c
    have hstarc : star c ≠ 0 := by
      intro hstar
      apply hc
      simpa using congrArg star hstar
    have hd : d = q * star c := by
      dsimp [q]
      exact (div_mul_cancel₀ d hstarc).symm
    have hfactor :
        c * d - star c * star d = (Complex.normSq c : ℂ) * (q - star q) := by
      -- Rewrite `d` through the normalized quotient `q`, so the line equation becomes
      -- self-adjointness of `q`.
      rw [hd]
      simp [q, Complex.normSq_eq_conj_mul_self]
      ring
    have hnorm : (Complex.normSq c : ℂ) ≠ 0 := by
      exact_mod_cast (show Complex.normSq c ≠ 0 by simpa [Complex.normSq_eq_zero] using hc)
    have hq_eq : q = star q := by
      have hmulzero : (Complex.normSq c : ℂ) * (q - star q) = 0 := by
        rwa [hfactor] at hzero
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp hmulzero).resolve_left hnorm
    have hq_real : q = (Complex.re q : ℂ) := by
      have him : Complex.im q = 0 := Complex.conj_eq_iff_im.mp hq_eq.symm
      calc
        q = (Complex.re q : ℂ) + (Complex.im q : ℂ) * Complex.I := by
          symm
          exact Complex.re_add_im q
        _ = (Complex.re q : ℂ) := by simp [him]
    refine ⟨Complex.re q, ?_⟩
    -- Replace `q` by its real part to recover the desired real multiple of `conj c`.
    calc
      d = q * star c := hd
      _ = (Complex.re q : ℂ) * star c := by
            exact congrArg (fun z : ℂ ↦ z * star c) hq_real
      _ = Complex.re q • star c := by simp
  · rintro ⟨s, rfl⟩
    -- A real multiple of the normal vector makes the antisymmetric line equation vanish.
    simp [sub_eq_add_neg, Complex.mul_re, mul_assoc, mul_left_comm, mul_comm]

/-- Exercise 5 (1). A homographic transformation whose pole does not lie on the inversion circle
sends finite corresponding inverse points to corresponding points for the inversion in the image
circle, with the explicit center and radius given below. -/
theorem homographic_maps_inversion_pair_to_inversion_pair
    {a z₁ z₂ α β γ δ : ℂ} {r : ℝ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0)
    (hz : inversion_pair a r z₁ z₂)
    (hz₁_ne_pole : γ * z₁ + δ ≠ 0) (hz₂_ne_pole : γ * z₂ + δ ≠ 0)
    (hpole : homographic_pole γ δ ∉ Metric.sphere a |r|) :
    inversion_pair
      (image_inversion_center a r α β γ δ)
      (image_inversion_radius a r α β γ δ)
      (homographic_map α β γ δ z₁)
      (homographic_map α β γ δ z₂) := by
  rcases (inversion_pair_iff (a := a) (z₁ := z₁) (z₂ := z₂) (r := r)).1 hz with
    ⟨_, _, hz_prod⟩
  have hr : r ≠ 0 := inversion_pair_radius_ne_zero hz
  have hD : image_inversion_den a r γ δ ≠ 0 :=
    image_inversion_den_ne_zero_of_pole_off_circle hγ hpole
  have hprod :
      (homographic_map α β γ δ z₁ - image_inversion_center a r α β γ δ) *
          star (homographic_map α β γ δ z₂ - image_inversion_center a r α β γ δ) =
        ((image_inversion_radius a r α β γ δ) ^ 2 : ℂ) :=
    homographic_image_centered_mul_star_eq_image_radius_sq
      (a := a) (z₁ := z₁) (z₂ := z₂) (α := α) (β := β) (γ := γ) (δ := δ) (r := r)
      hz_prod hz₁_ne_pole hz₂_ne_pole hD
  have hR_ne : image_inversion_radius a r α β γ δ ≠ 0 :=
    image_inversion_radius_ne_zero_of_pole_off_circle hdet hγ hr hpole
  have hw₁_ne :
      homographic_map α β γ δ z₁ ≠ image_inversion_center a r α β γ δ := by
    intro hw₁
    have hR_sq_ne : (((image_inversion_radius a r α β γ δ) ^ 2 : ℂ)) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 hR_ne)
    have hsq_zero :
        ((image_inversion_radius a r α β γ δ) ^ 2 : ℂ) = 0 := by
      simpa [hw₁] using hprod.symm
    exact hR_sq_ne hsq_zero
  have hw₂_ne :
      homographic_map α β γ δ z₂ ≠ image_inversion_center a r α β γ δ := by
    intro hw₂
    have hR_sq_ne : (((image_inversion_radius a r α β γ δ) ^ 2 : ℂ)) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 hR_ne)
    have hsq_zero :
        ((image_inversion_radius a r α β γ δ) ^ 2 : ℂ) = 0 := by
      simpa [hw₂] using hprod.symm
    exact hR_sq_ne hsq_zero
  -- Feed the normalized image-circle equation back into the canonical inversion-pair criterion.
  exact (inversion_pair_iff
    (a := image_inversion_center a r α β γ δ)
    (z₁ := homographic_map α β γ δ z₁)
    (z₂ := homographic_map α β γ δ z₂)
    (r := image_inversion_radius a r α β γ δ)).2 ⟨hw₁_ne, hw₂_ne, hprod⟩

/-- Exercise 5 (2). If the pole of the homographic transformation lies on the inversion circle,
then finite transformed points are corresponding points of the reflection in the image line. -/
theorem homographic_maps_inversion_pair_to_reflection_line
    {a z₁ z₂ α β γ δ : ℂ} {r : ℝ} (hdet : α * δ - β * γ ≠ 0) (hγ : γ ≠ 0)
    (hz : inversion_pair a r z₁ z₂)
    (hz₁_ne_pole : γ * z₁ + δ ≠ 0) (hz₂_ne_pole : γ * z₂ + δ ≠ 0)
    (hpole : homographic_pole γ δ ∈ Metric.sphere a |r|) :
    reflection (image_reflection_line a r α β γ δ hdet hγ hpole)
        (homographic_map α β γ δ z₁) =
      homographic_map α β γ δ z₂ := by
  rcases (inversion_pair_iff (a := a) (z₁ := z₁) (z₂ := z₂) (r := r)).1 hz with
    ⟨_, _, hz_prod⟩
  have hr : r ≠ 0 := inversion_pair_radius_ne_zero hz
  let c : ℂ := image_reflection_coeff a r α β γ δ
  let t : ℝ := image_reflection_const a r α β
  let w₁ : ℂ := homographic_map α β γ δ z₁
  let w₂ : ℂ := homographic_map α β γ δ z₂
  have hc : c ≠ 0 := by
    simpa [c] using image_reflection_coeff_ne_zero hdet hγ hr hpole
  have hcross₁₂ :
      c * w₁ + star c * star w₂ = (t : ℂ) := by
    simpa [c, t, w₁, w₂] using
      homographic_map_cross_reflection_equation
        (a := a) (z₁ := z₁) (z₂ := z₂) (α := α) (β := β) (γ := γ) (δ := δ) (r := r)
        hz_prod hz₁_ne_pole hz₂_ne_pole
        (by
          have hpole_eq :
              Complex.normSq (homographic_pole γ δ - a) = r ^ 2 :=
            (homographic_pole_mem_inversion_circle_iff (a := a) (γ := γ) (δ := δ) (r := r)).1 hpole
          rw [image_inversion_den_eq_normSq_gamma_mul_pole_offset hγ, hpole_eq, sub_self, mul_zero])
  have hz_prod_swap : (z₂ - a) * star (z₁ - a) = (r ^ 2 : ℂ) := by
    -- Conjugating the source equation gives the same inversion relation with the two points
    -- swapped.
    simpa [mul_comm] using congrArg star hz_prod
  have hcross₂₁ :
      c * w₂ + star c * star w₁ = (t : ℂ) := by
    simpa [c, t, w₁, w₂] using
      homographic_map_cross_reflection_equation
        (a := a) (z₁ := z₂) (z₂ := z₁) (α := α) (β := β) (γ := γ) (δ := δ) (r := r)
        hz_prod_swap hz₂_ne_pole hz₁_ne_pole
        (by
          have hpole_eq :
              Complex.normSq (homographic_pole γ δ - a) = r ^ 2 :=
            (homographic_pole_mem_inversion_circle_iff (a := a) (γ := γ) (δ := δ) (r := r)).1 hpole
          rw [image_inversion_den_eq_normSq_gamma_mul_pole_offset hγ, hpole_eq, sub_self, mul_zero])
  let m : ℂ := (w₁ + w₂) / 2
  let v : ℂ := w₁ - m
  have hmid_eq : c * m + star c * star m = (t : ℂ) := by
    -- Averaging the two cross-equations shows that the midpoint lies on the image reflection line.
    calc
      c * m + star c * star m
          = ((1 / 2 : ℂ)) *
              ((c * w₁ + star c * star w₂) + (c * w₂ + star c * star w₁)) := by
                simp [m, div_eq_mul_inv, mul_add, map_add, mul_assoc, mul_left_comm, mul_comm]
                ring
      _ = ((1 / 2 : ℂ)) * ((t : ℂ) + (t : ℂ)) := by rw [hcross₁₂, hcross₂₁]
      _ = (t : ℂ) := by ring
  have hmid_mem : m ∈ reflection_line c t hc := by
    exact (mem_reflection_line_iff (c := c) (w := m) (t := t) hc).2 hmid_eq
  have hdiff_zero : c * (w₁ - w₂) - star c * star (w₁ - w₂) = 0 := by
    -- Subtracting the two cross-equations isolates the normal component of the displacement.
    calc
      c * (w₁ - w₂) - star c * star (w₁ - w₂)
          = (c * w₁ + star c * star w₂) - (c * w₂ + star c * star w₁) := by
                simp [sub_eq_add_neg, mul_add, map_add]
                ring
      _ = (t : ℂ) - (t : ℂ) := by rw [hcross₁₂, hcross₂₁]
      _ = 0 := by ring
  rcases (mul_sub_star_eq_zero_iff_real_smul_star (c := c) (d := w₁ - w₂) hc).1 hdiff_zero with
    ⟨s, hs⟩
  have hv_eq : v = (s / 2) • star c := by
    -- The half-difference from the midpoint is the expected real multiple of the line normal.
    calc
      v = (w₁ - w₂) / 2 := by
            dsimp [v, m]
            ring
      _ = (((s : ℂ) * star c) / 2) := by
            simpa [smul_eq_mul] using congrArg (fun z : ℂ ↦ z / 2) hs
      _ = (((s / 2 : ℝ) : ℂ) * star c) := by
            norm_num
            ring
      _ = (s / 2) • star c := by simp
  have hv_orth : v ∈ (reflection_line c t hc).directionᗮ := by
    rw [hv_eq]
    exact Submodule.smul_mem _ _ (reflection_line_star_mem_direction_orthogonal (c := c) (t := t) hc)
  have hw₁_split : v +ᵥ m = w₁ := by
    -- The first image point is the midpoint translated by the normal half-difference.
    dsimp [v]
    simp
  have hw₂_split : -v +ᵥ m = w₂ := by
    -- The second image point is obtained by flipping the same normal vector.
    dsimp [v, m]
    ring
  -- Reflect across the concrete line by fixing the midpoint and negating the orthogonal component.
  have hreflect :
      reflection (reflection_line c t hc) w₁ = w₂ := by
    calc
    reflection (reflection_line c t hc) w₁
        = reflection (reflection_line c t hc) (v +ᵥ m) := by rw [hw₁_split]
    _ = -v +ᵥ m := reflection_orthogonal_vadd hmid_mem hv_orth
    _ = w₂ := hw₂_split
  simpa [c, t, w₁, w₂, image_reflection_line_eq_reflection_line hdet hγ hr hpole] using hreflect
