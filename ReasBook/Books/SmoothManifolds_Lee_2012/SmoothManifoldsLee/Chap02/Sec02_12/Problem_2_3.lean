import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff RealInnerProductSpace
open Complex Metric ComplexConjugate

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Local API note: semantic `lean_leansearch` was unavailable in this session; the sphere-valued
-- smoothness statements below use mathlib's `Instances.Sphere` API directly.

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C2" => WithLp 2 (ℂ × ℂ)
local notation "unitSphere3" => sphere (0 : C2) 1
local notation "unitSphere2" => sphere (0 : R3) 1

/-- Problem 2-3 (1): the nth power map `p_n(z) = z^n` on `S¹ ⊆ ℂ` is smooth for every integer
`n`. -/
theorem circle_zpow_map_smooth (n : ℤ) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle ↦ z ^ n) := by
  -- Split the integer exponent into the natural-power and inverse-of-natural-power cases.
  cases n with
  | ofNat m =>
      simpa using
        (contMDiff_pow (I := 𝓡 1) (n := ∞) (i := m) :
          ContMDiff (𝓡 1) (𝓡 1) ∞ fun z : Circle ↦ z ^ m)
  | negSucc m =>
      -- Negative powers are smooth because inversion is smooth on the Lie group `Circle`.
      simpa [zpow_negSucc] using
        (ContMDiff.inv
          (I := 𝓡 1)
          (I' := 𝓡 1)
          (n := ∞)
          (f := fun z : Circle ↦ z ^ (m + 1))
          (contMDiff_pow (I := 𝓡 1) (n := ∞) (i := m + 1)))

/- Problem 2-3 (2): the antipodal map `x ↦ -x` on the unit sphere `Sⁿ` is smooth. -/
recall contMDiff_neg_sphere {m : ℕ∞ω} {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] :
    CMDiff m fun x : sphere (0 : E) 1 ↦ -x

/-- The real vector space `ℂ × ℂ` has dimension `4`. -/
theorem finrank_real_complex_prod_fact : Fact (Module.finrank ℝ C2 = 3 + 1) := by
  refine ⟨?_⟩
  calc
    Module.finrank ℝ C2 = Module.finrank ℝ (ℂ × ℂ) :=
      (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).finrank_eq
    _ = Module.finrank ℝ ℂ + Module.finrank ℝ ℂ := by rw [Module.finrank_prod]
    _ = 3 + 1 := by norm_num [Complex.finrank_real_complex]

/-- The standard sphere in `ℂ²` uses the real-dimension-four sphere manifold structure. -/
local instance complex_pair_finrank_fact : Fact (Module.finrank ℝ C2 = 3 + 1) :=
  finrank_real_complex_prod_fact

/-- The Euclidean space `ℝ³` has real dimension `3`. -/
theorem finrank_real_r3_fact : Fact (Module.finrank ℝ R3 = 2 + 1) := by
  refine ⟨?_⟩
  simpa using (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))

/-- The standard sphere in `ℝ³` uses the real-dimension-three sphere manifold structure. -/
local instance r3_finrank_fact : Fact (Module.finrank ℝ R3 = 2 + 1) :=
  finrank_real_r3_fact

/-- The ambient quadratic formula defining the map `S^3 → S^2` in Problem 2-3(c). -/
def hopf_map_aux : C2 → R3 :=
  fun p ↦
    let w := p.fst
    let z := p.snd
    WithLp.toLp 2
      ![Complex.re (z * conj w + w * conj z),
        Complex.re (Complex.I * w * conj z - Complex.I * z * conj w),
        Complex.re (z * conj z - w * conj w)]

/-- Helper for Problem 2-3: the first real coordinate of the Hopf map formula. -/
def hopf_first (p : C2) : ℝ :=
  let w := p.fst
  let z := p.snd
  Complex.re (z * conj w + w * conj z)

/-- Helper for Problem 2-3: the second real coordinate of the Hopf map formula. -/
def hopf_second (p : C2) : ℝ :=
  let w := p.fst
  let z := p.snd
  Complex.re (Complex.I * w * conj z - Complex.I * z * conj w)

/-- Helper for Problem 2-3: the third real coordinate of the Hopf map formula. -/
def hopf_third (p : C2) : ℝ :=
  let w := p.fst
  let z := p.snd
  Complex.re (z * conj z - w * conj w)

/-- Helper for Problem 2-3: the ambient Hopf-coordinate vector before it is packed into `ℝ³`. -/
def hopf_coords (p : C2) : Fin 3 → ℝ :=
  fun i ↦
    match i with
    | 0 => hopf_first p
    | 1 => hopf_second p
    | 2 => hopf_third p

/-- Helper for Problem 2-3: the first coordinate is the compact complex expression from the
textbook formula. -/
lemma hopf_first_eq (p : C2) :
    hopf_first p = Complex.re (p.snd * conj p.fst + p.fst * conj p.snd) := rfl

/-- Helper for Problem 2-3: the second coordinate is the compact complex expression from the
textbook formula. -/
lemma hopf_second_eq (p : C2) :
    hopf_second p = Complex.re (Complex.I * p.fst * conj p.snd - Complex.I * p.snd * conj p.fst) :=
  rfl

/-- Helper for Problem 2-3: the third coordinate is the compact complex expression from the
textbook formula. -/
lemma hopf_third_eq (p : C2) :
    hopf_third p = Complex.re (p.snd * conj p.snd - p.fst * conj p.fst) := rfl

/-- Helper for Problem 2-3: `hopf_map_aux` is the `toLp` packaging of the coordinate vector. -/
lemma hopf_map_aux_eq_coords (p : C2) :
    hopf_map_aux p = WithLp.toLp 2 (hopf_coords p) := by
  ext i
  fin_cases i <;> rfl

/-- Helper for Problem 2-3: the first Hopf coordinate is smooth as a real-valued map on `ℂ²`. -/
lemma hopf_first_contDiff : ContDiff ℝ ∞ hopf_first := by
  -- This coordinate is the real part of a quadratic complex polynomial.
  have hfst : ContDiff ℝ ∞ fun x : C2 ↦ x.fst := by
    simpa using (WithLp.fstL 2 ℝ ℂ ℂ).contDiff
  have hsnd : ContDiff ℝ ∞ fun x : C2 ↦ x.snd := by
    simpa using (WithLp.sndL 2 ℝ ℂ ℂ).contDiff
  have hfirst :
      hopf_first = (Complex.reCLM : ℂ → ℝ) ∘
        (fun x : C2 ↦ x.snd * conj x.fst + x.fst * conj x.snd) := by
    rfl
  rw [hfirst]
  exact
    (Complex.reCLM.contDiff.comp
      ((hsnd.mul ((Complex.conjCLE).contDiff.comp hfst)).add
        (hfst.mul ((Complex.conjCLE).contDiff.comp hsnd))))

/-- Helper for Problem 2-3: the second Hopf coordinate is smooth as a real-valued map on `ℂ²`. -/
lemma hopf_second_contDiff : ContDiff ℝ ∞ hopf_second := by
  -- This coordinate has the same quadratic form, with the constant factor `I`.
  have hfst : ContDiff ℝ ∞ fun x : C2 ↦ x.fst := by
    simpa using (WithLp.fstL 2 ℝ ℂ ℂ).contDiff
  have hsnd : ContDiff ℝ ∞ fun x : C2 ↦ x.snd := by
    simpa using (WithLp.sndL 2 ℝ ℂ ℂ).contDiff
  have hsecond :
      hopf_second = (Complex.reCLM : ℂ → ℝ) ∘
        (fun x : C2 ↦ Complex.I * x.fst * conj x.snd - Complex.I * x.snd * conj x.fst) := by
    rfl
  rw [hsecond]
  exact
    (Complex.reCLM.contDiff.comp
      ((((contDiff_const.mul hfst).mul ((Complex.conjCLE).contDiff.comp hsnd)).sub
        ((contDiff_const.mul hsnd).mul ((Complex.conjCLE).contDiff.comp hfst)))))

/-- Helper for Problem 2-3: the third Hopf coordinate is smooth as a real-valued map on `ℂ²`. -/
lemma hopf_third_contDiff : ContDiff ℝ ∞ hopf_third := by
  -- This coordinate is the difference of two norm-square expressions.
  have hfst : ContDiff ℝ ∞ fun x : C2 ↦ x.fst := by
    simpa using (WithLp.fstL 2 ℝ ℂ ℂ).contDiff
  have hsnd : ContDiff ℝ ∞ fun x : C2 ↦ x.snd := by
    simpa using (WithLp.sndL 2 ℝ ℂ ℂ).contDiff
  have hthird :
      hopf_third = (Complex.reCLM : ℂ → ℝ) ∘
        (fun x : C2 ↦ x.snd * conj x.snd - x.fst * conj x.fst) := by
    rfl
  rw [hthird]
  exact
    (Complex.reCLM.contDiff.comp
      ((hsnd.mul ((Complex.conjCLE).contDiff.comp hsnd)).sub
        (hfst.mul ((Complex.conjCLE).contDiff.comp hfst))))

/-- Helper for Problem 2-3: the ambient quadratic map `ℂ² → ℝ³` is smooth. -/
lemma hopf_map_aux_contMDiff :
    ContMDiff 𝓘(ℝ, C2) 𝓘(ℝ, R3) ∞ hopf_map_aux := by
  -- First prove smoothness of the coordinate vector before applying `WithLp.toLp`.
  have hcoords : ContDiff ℝ ∞ hopf_coords := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · -- The first coordinate is the real part of a quadratic complex polynomial.
      simpa [hopf_coords] using hopf_first_contDiff
    · -- The second coordinate has the same quadratic structure, with a fixed factor of `I`.
      simpa [hopf_coords] using hopf_second_contDiff
    · -- The third coordinate is the difference of two complex norm-square expressions.
      simpa [hopf_coords] using hopf_third_contDiff
  -- Then move from the coordinate vector to `EuclideanSpace ℝ (Fin 3)` via `toLp`.
  have haux : ContDiff ℝ ∞ hopf_map_aux := by
    have haux_eq : hopf_map_aux = fun p : C2 ↦ WithLp.toLp 2 (hopf_coords p) := by
      funext p
      exact hopf_map_aux_eq_coords p
    rw [haux_eq]
    exact (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 ↦ ℝ)).comp hcoords
  exact haux.contMDiff

/-- Helper for Problem 2-3: the squared Euclidean norm of the Hopf coordinates is the square of
the ambient `ℂ²` norm-square. -/
lemma hopf_map_aux_norm_sq_formula (p : C2) :
    ‖hopf_map_aux p‖ ^ 2 = (Complex.normSq p.fst + Complex.normSq p.snd) ^ 2 := by
  -- Rewrite `hopf_map_aux` using the explicit coordinate vector.
  rw [hopf_map_aux_eq_coords]
  -- Rewrite the `ℝ³` norm as a sum of coordinate squares.
  rw [EuclideanSpace.real_norm_sq_eq]
  -- Expand the three coordinates into a polynomial identity in the real and imaginary parts.
  simp [hopf_coords, hopf_first_eq, hopf_second_eq, hopf_third_eq,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, pow_two]
  rw [Fin.sum_univ_three]
  rw [show Complex.normSq p.fst = p.fst.re * p.fst.re + p.fst.im * p.fst.im by
      simpa using (RCLike.normSq_apply p.fst)]
  rw [show Complex.normSq p.snd = p.snd.re * p.snd.re + p.snd.im * p.snd.im by
      simpa using (RCLike.normSq_apply p.snd)]
  ring_nf

/-- The quadratic coordinate formula in Problem 2-3(c) sends `S^3 ⊆ ℂ²` into `S^2 ⊆ ℝ³`. -/
theorem hopf_map_aux_mem_unit_sphere2 (p : unitSphere3) :
    hopf_map_aux p ∈ unitSphere2 := by
  -- Rewrite membership in the sphere as the norm condition `‖x‖ = 1`.
  rw [mem_sphere_iff_norm, sub_zero]
  have hp_norm : ‖(p : C2)‖ = 1 := by
    simpa [mem_sphere_iff_norm, sub_zero] using p.property
  have hnorm_sq : ‖hopf_map_aux p‖ ^ 2 = 1 := by
    -- The Hopf norm identity reduces the target to the defining unit-sphere equation on `p`.
    calc
      ‖hopf_map_aux p‖ ^ 2
          = (Complex.normSq ((p : C2).fst) + Complex.normSq ((p : C2).snd)) ^ 2 :=
        hopf_map_aux_norm_sq_formula p
      _ = (‖((p : C2).fst)‖ ^ 2 + ‖((p : C2).snd)‖ ^ 2) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = (‖(p : C2)‖ ^ 2) ^ 2 := by
        rw [WithLp.prod_norm_sq_eq_of_L2 (p : C2)]
      _ = 1 := by
        simp [hp_norm]
  -- A nonnegative real with square `1` must equal `1`.
  have hnorm_sq' : ‖hopf_map_aux p‖ ^ 2 = 1 ^ 2 := by simpa using hnorm_sq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hnorm_sq' with hnorm | hnorm
  · exact hnorm
  · linarith [norm_nonneg (hopf_map_aux p)]

/-- The sphere-valued map `F : S^3 → S^2` from Problem 2-3(c). -/
def hopf_map : unitSphere3 → unitSphere2 :=
  fun p ↦ ⟨hopf_map_aux p, hopf_map_aux_mem_unit_sphere2 p⟩

/-- Problem 2-3 (3): the map `F : S^3 → S^2` with coordinates
`(z\bar{w} + w\bar{z}, iw\bar{z} - iz\bar{w}, z\bar{z} - w\bar{w})` is smooth. -/
theorem hopf_map_smooth :
    ContMDiff (𝓡 3) (𝓡 2) ∞ hopf_map := by
  -- View the sphere-valued map as a codomain restriction of the ambient smooth map.
  have hambient : ContMDiff (𝓡 3) 𝓘(ℝ, R3) ∞ fun p : unitSphere3 ↦ hopf_map_aux p := by
    exact hopf_map_aux_contMDiff.comp contMDiff_coe_sphere
  -- The codomain restriction is smooth because the ambient formula lands in `S²`.
  simpa [hopf_map] using
    (ContMDiff.codRestrict_sphere
      (n := 2)
      (f := fun p : unitSphere3 ↦ hopf_map_aux p)
      hambient
      hopf_map_aux_mem_unit_sphere2)
