import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Exercise_4_10
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Proposition_4_22
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Example_4_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Manifold
open scoped Manifold Matrix ContDiff Torus

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)

/-- Helper for Problem 4-12: the transition map between finite product charts is the product of
the factorwise transition maps. -/
lemma open_partial_homeomorph_pi_symm_trans_pi
    (e e' : Fin 2 → OpenPartialHomeomorph Circle (EuclideanSpace ℝ (Fin 1))) :
    (OpenPartialHomeomorph.pi e).symm.trans (OpenPartialHomeomorph.pi e') =
      OpenPartialHomeomorph.pi (fun i ↦ (e i).symm.trans (e' i)) := by
  -- Compare the transition maps coordinatewise.
  apply OpenPartialHomeomorph.ext
  · intro x
    funext i
    rfl
  · intro x
    funext i
    rfl
  · ext x
    simp [Set.mem_pi]

/-- Helper for Problem 4-12: membership in the source condition for the torus product model is
equivalent to the corresponding coordinatewise source conditions. -/
lemma mem_torus_model_source_iff
    {e : Fin 2 → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))}
    {x : Fin 2 → EuclideanSpace ℝ (Fin 1)} :
    x ∈ ((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm) ⁻¹'
        (OpenPartialHomeomorph.pi e).source ∩
      Set.range (ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)) ↔
      ∀ i, x i ∈ (𝓡 1).symm ⁻¹' (e i).source ∩ Set.range (𝓡 1) := by
  have hrange :
      Set.range (ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)) =
        Set.pi Set.univ (fun i ↦ Set.range (𝓡 1)) := by
    change Set.range (Pi.map fun _ : Fin 2 ↦ (𝓡 1)) = _
    simp
  rw [hrange]
  constructor
  · intro hx i
    have hx_source_mem :
        ((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm x) ∈
          Set.pi Set.univ (fun i ↦ (e i).source) := by
      simpa [OpenPartialHomeomorph.pi] using hx.1
    have hx_source_mem' :
        ∀ i ∈ Set.univ, ((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm x) i ∈ (e i).source := by
      dsimp [ModelPi] at hx_source_mem ⊢
      rw [Set.mem_pi] at hx_source_mem
      exact hx_source_mem
    have hx_source : ∀ i, ((𝓡 1).symm (x i)) ∈ (e i).source := by
      simpa [ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using
        fun i ↦ hx_source_mem' i (by simp)
    have hx_range_mem : x ∈ Set.pi Set.univ (fun i ↦ Set.range (𝓡 1)) := hx.2
    have hx_range : ∀ i, x i ∈ Set.range (𝓡 1) := by
      rw [Set.mem_pi] at hx_range_mem
      exact fun i ↦ hx_range_mem i (by simp)
    exact ⟨hx_source i, hx_range i⟩
  · intro hx
    constructor
    · have hx_source :
          ∀ i, ((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm x) i ∈ (e i).source := by
        simpa [ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using fun i ↦ (hx i).1
      have hx_source_mem' :
          ∀ i ∈ Set.univ,
            ((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm x) i ∈ (e i).source := by
        exact fun i _ ↦ hx_source i
      have hx_source_mem :
          ((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm x) ∈
            Set.pi Set.univ (fun i ↦ (e i).source) := by
        dsimp [ModelPi] at ⊢
        rw [Set.mem_pi]
        exact hx_source_mem'
      simpa [OpenPartialHomeomorph.pi] using hx_source_mem
    · rw [Set.mem_pi]
      exact fun i _ ↦ (hx i).2

/-- Helper for Problem 4-12: each coordinate projection on the torus model space is smooth. -/
lemma contDiffOn_torus_model_proj (i : Fin 2) (s : Set (Fin 2 → EuclideanSpace ℝ (Fin 1))) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (fun x : Fin 2 → EuclideanSpace ℝ (Fin 1) ↦ x i) s := by
  simpa using
    ((((ContinuousLinearMap.proj (R := ℝ) i) :
      (Fin 2 → EuclideanSpace ℝ (Fin 1)) →L[ℝ] EuclideanSpace ℝ (Fin 1)).contDiff).contDiffOn :
      ContDiffOn ℝ (∞ : ℕ∞ω)
        ((ContinuousLinearMap.proj (R := ℝ) i) :
          (Fin 2 → EuclideanSpace ℝ (Fin 1)) → EuclideanSpace ℝ (Fin 1)) s)

/-- Helper for Problem 4-12: a finite product of circle chart transitions is smooth for the torus
product model. -/
lemma torus_contDiffGroupoid_pi
    {e : Fin 2 → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))}
    (he : ∀ i, e i ∈ contDiffGroupoid (∞ : ℕ∞ω) (𝓡 1)) :
    OpenPartialHomeomorph.pi e ∈ contDiffGroupoid (∞ : ℕ∞ω) T2Model := by
  refine (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid (∞ : ℕ∞ω) T2Model)).2 ?_
  constructor
  · refine contDiffOn_pi.2 ?_
    intro i
    have hi :=
      (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid (∞ : ℕ∞ω) (𝓡 1))).1 (he i)
    simpa [Function.comp] using
      (show ContDiffOn ℝ (∞ : ℕ∞ω) ((𝓡 1) ∘ e i ∘ (𝓡 1).symm)
          ((𝓡 1).symm ⁻¹' (e i).source ∩ Set.range (𝓡 1)) from by
            simpa [contDiffPregroupoid] using hi.1).comp
          (contDiffOn_torus_model_proj i _)
          (fun x hx ↦ (mem_torus_model_source_iff (e := e) (x := x)).1 hx i)
  · refine contDiffOn_pi.2 ?_
    intro i
    have hi :=
      (mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid (∞ : ℕ∞ω) (𝓡 1))).1 (he i)
    simpa [Function.comp] using
      (show ContDiffOn ℝ (∞ : ℕ∞ω) ((𝓡 1) ∘ (e i).symm ∘ (𝓡 1).symm)
          ((𝓡 1).symm ⁻¹' ((e i).symm).source ∩ Set.range (𝓡 1)) from by
            simpa [contDiffPregroupoid] using hi.2).comp
          (contDiffOn_torus_model_proj i _)
          (fun x hx ↦
            (mem_torus_model_source_iff (e := fun i ↦ (e i).symm) (x := x)).1
              (by simpa [OpenPartialHomeomorph.pi] using hx) i)

/-- Helper for Problem 4-12: the product of two circles carries the canonical product manifold
structure modeled on the product of two copies of `ℝ`. -/
local instance torus_product_isManifold :
    IsManifold T2Model (∞ : ℕ∞ω) (𝕋^{2}) := by
  refine isManifold_of_contDiffOn (I := T2Model) (n := (∞ : ℕ∞ω)) (M := 𝕋^{2}) ?_
  intro f g hf hg
  rcases hf with ⟨f', hf', rfl⟩
  rcases hg with ⟨g', hg', rfl⟩
  have hf_atlas : ∀ i, f' i ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle := by
    simpa [Set.mem_pi] using hf'
  have hg_atlas : ∀ i, g' i ∈ atlas (EuclideanSpace ℝ (Fin 1)) Circle := by
    simpa [Set.mem_pi] using hg'
  have hpi :=
    ((mem_groupoid_of_pregroupoid (PG := contDiffPregroupoid (∞ : ℕ∞ω) T2Model)).1 <|
    torus_contDiffGroupoid_pi fun i =>
      (contDiffGroupoid (∞ : ℕ∞ω) (𝓡 1)).compatible (hf_atlas i) (hg_atlas i)).1
  change
    ContDiffOn ℝ (∞ : ℕ∞ω)
      (↑(ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)) ∘
        ↑((OpenPartialHomeomorph.pi f').symm.trans (OpenPartialHomeomorph.pi g')) ∘
        ↑((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm))
      (↑((ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)).symm) ⁻¹'
          ((OpenPartialHomeomorph.pi f').symm.trans (OpenPartialHomeomorph.pi g')).source ∩
        Set.range ↑(ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)))
  rw [open_partial_homeomorph_pi_symm_trans_pi]
  simpa using hpi

/-- The standard torus map on `𝕋² = S¹ × S¹`, written in circle coordinates. -/
def torus_of_revolution_map : 𝕋^{2} → R3 :=
  fun z ↦
    WithLp.toLp 2
      ![
        ((2 : ℝ) + (z 1 : ℂ).re) * (z 0 : ℂ).re,
        ((2 : ℝ) + (z 1 : ℂ).re) * (z 0 : ℂ).im,
        (z 1 : ℂ).im
      ]

/-- The ambient torus immersion `X : ℝ² → ℝ³` from the standard surface-of-revolution
parametrization. -/
def torus_of_revolution_immersion : R2 → R3 :=
  fun p ↦
    WithLp.toLp 2
      ![
        ((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0),
        ((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0),
        Real.sin (p 1)
      ]

/-- The standard torus in `ℝ³`, written as the algebraic surface of revolution with major radius
`2` and minor radius `1`. -/
def torus_of_revolution_surface : Set R3 :=
  { p | ((p 0) ^ (2 : ℕ) + (p 1) ^ (2 : ℕ) + (p 2) ^ (2 : ℕ) + 3) ^ (2 : ℕ) =
      16 * ((p 0) ^ (2 : ℕ) + (p 1) ^ (2 : ℕ)) }

/-- Problem 4-12 (1): the torus immersion `X : ℝ² → ℝ³` factors through the covering map
`ε² : ℝ² → 𝕋²`, so it descends to the quotient as `torus_of_revolution_map : 𝕋² → ℝ³`. -/
theorem torus_of_revolution_map_comp_standardTorusCovering :
    torus_of_revolution_map ∘ standardTorusCovering 2 = torus_of_revolution_immersion := by
  -- Evaluate the quotient formula coordinatewise after expanding `Circle.exp`.
  funext p
  ext i
  fin_cases i
  · simp [torus_of_revolution_map, torus_of_revolution_immersion, standardTorusCovering,
      Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re]
  · simp [torus_of_revolution_map, torus_of_revolution_immersion, standardTorusCovering,
      Circle.coe_exp, Complex.exp_mul_I, Complex.sin_ofReal_re, Complex.cos_ofReal_re]
  · simp [torus_of_revolution_map, torus_of_revolution_immersion, standardTorusCovering,
      Circle.coe_exp, Complex.exp_mul_I, Complex.sin_ofReal_re]

/-- Helper for Problem 4-12: a circle point has real and imaginary parts with squared sum `1`. -/
lemma circle_re_sq_add_im_sq (z : Circle) :
    (z : ℂ).re ^ (2 : ℕ) + (z : ℂ).im ^ (2 : ℕ) = 1 := by
  -- `Circle.normSq_coe` is exactly the Pythagorean identity on the unit circle.
  simpa [Complex.normSq, pow_two, sq] using Circle.normSq_coe z

/-- Helper for Problem 4-12: equality of real and imaginary parts determines a circle point. -/
lemma circle_eq_of_re_eq_im_eq {z w : Circle}
    (hre : (z : ℂ).re = (w : ℂ).re) (him : (z : ℂ).im = (w : ℂ).im) :
    z = w := by
  -- A circle point is determined by its underlying complex number.
  apply Subtype.ext
  exact Complex.ext hre him

/-- Helper for Problem 4-12: the scalar factor `2 + cos θ` in the ambient torus parametrization is
strictly positive. -/
lemma torus_revolution_factor_cos_pos (θ : ℝ) : 0 < (2 : ℝ) + Real.cos θ := by
  -- The cosine term stays in `[-1, 1]`, so adding `2` keeps the factor positive.
  nlinarith [Real.neg_one_le_cos θ]

/-- Helper for Problem 4-12: the scalar factor `2 + Re z` in the descended torus map is strictly
positive for every circle point `z`. -/
lemma torus_revolution_factor_circle_pos (z : Circle) : 0 < (2 : ℝ) + (z : ℂ).re := by
  -- The real part of a unit complex number also lies in `[-1, 1]`.
  have him_nonneg : 0 ≤ (z : ℂ).im ^ (2 : ℕ) := sq_nonneg _
  have hz := circle_re_sq_add_im_sq z
  nlinarith

/-- Helper for Problem 4-12: injectivity of a composition descends across a surjective right
factor. -/
lemma injective_of_comp_right {α β γ : Type*} {f : β → γ} {g : α → β}
    (hcomp : Function.Injective (f ∘ g)) (hg : Function.Surjective g) :
    Function.Injective f := by
  -- Pull two target points back along the surjective right factor and compare upstairs.
  intro x y hxy
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  exact congrArg g (hcomp hxy)

/-- Helper for Problem 4-12: the ambient torus parametrization is smooth on `ℝ²`. -/
theorem torus_of_revolution_immersion_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞ torus_of_revolution_immersion := by
  rw [contMDiff_iff_contDiff]
  -- Keep the argument on the Euclidean side and repackage the coordinates with `WithLp.toLp`.
  have hExplicit :
      ContDiff ℝ ∞
        (fun p : R2 ↦
          WithLp.toLp 2
            ![
              ((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0),
              ((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0),
              Real.sin (p 1)
            ]) := by
    refine (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 ↦ ℝ)).comp ?_
    rw [contDiff_pi]
    intro i
    fin_cases i
    · -- The first coordinate is a product of smooth trigonometric factors.
      have h0 :
          ContDiff ℝ ∞ (fun p : R2 ↦ Real.cos (p 0)) :=
        Real.contDiff_cos.comp
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0))
      have h1 :
          ContDiff ℝ ∞ (fun p : R2 ↦ (2 : ℝ) + Real.cos (p 1)) := by
        simpa using contDiff_const.add
          (Real.contDiff_cos.comp
            (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)))
      simpa using h1.mul h0
    · -- The second coordinate differs only by replacing `cos` with `sin` in the last factor.
      have h0 :
          ContDiff ℝ ∞ (fun p : R2 ↦ Real.sin (p 0)) :=
        Real.contDiff_sin.comp
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 0))
      have h1 :
          ContDiff ℝ ∞ (fun p : R2 ↦ (2 : ℝ) + Real.cos (p 1)) := by
        simpa using contDiff_const.add
          (Real.contDiff_cos.comp
            (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1)))
      simpa using h1.mul h0
    · -- The third coordinate is the smooth sine of the second Euclidean coordinate.
      simpa using Real.contDiff_sin.comp
        (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (i := 1))
  simpa [torus_of_revolution_immersion] using hExplicit

/-- Helper for Problem 4-12: the first coordinate of the ambient torus parametrization has the
expected derivative. -/
lemma torus_of_revolution_first_coord_hasFDerivAt (p : R2) :
    HasFDerivAt
      (fun q : R2 ↦ Real.cos (q 0) * ((2 : ℝ) + Real.cos (q 1)))
      (-((Real.sin (p 0) * ((2 : ℝ) + Real.cos (p 1))) •
            (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) +
        -((Real.cos (p 0) * Real.sin (p 1)) •
            (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ))) p := by
  have h0 :
      HasFDerivAt (fun q : R2 ↦ Real.cos (q 0))
        (-(Real.sin (p 0) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ))) p := by
    -- Differentiate the first angular coordinate through the Euclidean projection.
    simpa using
      (Real.hasDerivAt_cos (p 0)).comp_hasFDerivAt p
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 0)
  have h1 :
      HasFDerivAt (fun q : R2 ↦ (2 : ℝ) + Real.cos (q 1))
        (-(Real.sin (p 1) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ))) p := by
    -- The scalar factor depends only on the second angular coordinate.
    simpa using
      ((Real.hasDerivAt_cos (p 1)).comp_hasFDerivAt p
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1)).const_add
        (2 : ℝ)
  -- Apply the product rule and normalize the scalar factors into the advertised order.
  simpa [smul_add, smul_smul, neg_smul, add_comm, add_left_comm, add_assoc, mul_comm,
    mul_left_comm, mul_assoc] using h0.mul h1

/-- Helper for Problem 4-12: the second coordinate of the ambient torus parametrization has the
expected derivative. -/
lemma torus_of_revolution_second_coord_hasFDerivAt (p : R2) :
    HasFDerivAt
      (fun q : R2 ↦ Real.sin (q 0) * ((2 : ℝ) + Real.cos (q 1)))
      (((Real.cos (p 0) * ((2 : ℝ) + Real.cos (p 1))) •
            (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) +
        -((Real.sin (p 0) * Real.sin (p 1)) •
            (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ))) p := by
  have h0 :
      HasFDerivAt (fun q : R2 ↦ Real.sin (q 0))
        (Real.cos (p 0) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) p := by
    -- Differentiate the first angular coordinate through the Euclidean projection.
    simpa using
      (Real.hasDerivAt_sin (p 0)).comp_hasFDerivAt p
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 0)
  have h1 :
      HasFDerivAt (fun q : R2 ↦ (2 : ℝ) + Real.cos (q 1))
        (-(Real.sin (p 1) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ))) p := by
    -- The same scalar factor as above carries through unchanged.
    simpa using
      ((Real.hasDerivAt_cos (p 1)).comp_hasFDerivAt p
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1)).const_add
        (2 : ℝ)
  -- Apply the product rule and reorder the two summands to match the statement.
  simpa [smul_add, smul_smul, neg_smul, add_comm, add_left_comm, add_assoc, mul_comm,
    mul_left_comm, mul_assoc] using h0.mul h1

/-- Helper for Problem 4-12: the third coordinate of the ambient torus parametrization has the
expected derivative. -/
lemma torus_of_revolution_third_coord_hasFDerivAt (p : R2) :
    HasFDerivAt
      (fun q : R2 ↦ Real.sin (q 1))
      (Real.cos (p 1) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ)) p := by
  -- This is the one-variable sine derivative composed with the second coordinate projection.
  simpa using
    (Real.hasDerivAt_sin (p 1)).comp_hasFDerivAt p
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) p 1)

/-- Helper for Problem 4-12: the derivative of the ambient torus parametrization has the expected
coordinate formula. -/
theorem torus_of_revolution_immersion_fderiv_apply (p v : R2) :
    fderiv ℝ torus_of_revolution_immersion p v =
      WithLp.toLp 2
        ![
          -(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * v 0 -
            (Real.sin (p 1) * Real.cos (p 0)) * v 1,
          (((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * v 0 -
            (Real.sin (p 1) * Real.sin (p 0)) * v 1,
          Real.cos (p 1) * v 1
        ] := by
  let L0 : R2 →L[ℝ] ℝ :=
    -((Real.sin (p 0) * ((2 : ℝ) + Real.cos (p 1))) •
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) +
      -((Real.cos (p 0) * Real.sin (p 1)) •
        (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ))
  let L1 : R2 →L[ℝ] ℝ :=
    (Real.cos (p 0) * ((2 : ℝ) + Real.cos (p 1))) •
      (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ) +
    -((Real.sin (p 0) * Real.sin (p 1)) •
      (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ))
  let L2 : R2 →L[ℝ] ℝ :=
    Real.cos (p 1) • (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ)
  have hpi :
      HasFDerivAt
        (fun q : R2 ↦
          ![
            ((2 : ℝ) + Real.cos (q 1)) * Real.cos (q 0),
            ((2 : ℝ) + Real.cos (q 1)) * Real.sin (q 0),
            Real.sin (q 1)
          ])
        (ContinuousLinearMap.pi ![L0, L1, L2]) p := by
    -- Assemble the three scalar derivatives into the derivative of the coordinate tuple.
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa [L0, mul_comm, mul_left_comm, mul_assoc] using
        torus_of_revolution_first_coord_hasFDerivAt p
    · simpa [L1, mul_comm, mul_left_comm, mul_assoc] using
        torus_of_revolution_second_coord_hasFDerivAt p
    · simpa [L2] using torus_of_revolution_third_coord_hasFDerivAt p
  have htoLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin 3 → ℝ) → R3)
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap)
        ![
          ((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0),
          ((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0),
          Real.sin (p 1)
        ] :=
    PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ)
      ![
        ((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0),
        ((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0),
        Real.sin (p 1)
      ]
  have hImm :
      HasFDerivAt torus_of_revolution_immersion
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.pi ![L0, L1, L2])) p := by
    -- Compose the tuple derivative with the fixed linear equivalence `WithLp.toLp`.
    simpa [torus_of_revolution_immersion] using htoLp.comp p hpi
  rw [hImm.fderiv]
  -- Compare the coordinate tuple first, then transport it back with `WithLp.toLp`.
  have htuple :
      ![L0 v, L1 v, L2 v] =
        ![
          -(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * v 0 -
            (Real.sin (p 1) * Real.cos (p 0)) * v 1,
          (((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * v 0 -
            (Real.sin (p 1) * Real.sin (p 0)) * v 1,
          Real.cos (p 1) * v 1
        ] := by
    ext i
    fin_cases i
    · simp [L0, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
        smul_eq_mul]
      ring
    · simp [L1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
        smul_eq_mul]
      ring
    · simp [L2, ContinuousLinearMap.smul_apply, PiLp.proj_apply, smul_eq_mul]
  convert congrArg (WithLp.toLp 2) htuple using 1
  ext i
  fin_cases i <;> rfl

/-- Helper for Problem 4-12: the derivative of the ambient torus parametrization is injective at
every point. -/
theorem torus_of_revolution_immersion_fderiv_injective (p : R2) :
    Function.Injective (fderiv ℝ torus_of_revolution_immersion p) := by
  intro v w hvw
  have hcoord0 :
      -(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * v 0 -
          (Real.sin (p 1) * Real.cos (p 0)) * v 1 =
        -(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * w 0 -
          (Real.sin (p 1) * Real.cos (p 0)) * w 1 := by
    simpa [torus_of_revolution_immersion_fderiv_apply] using congrArg (fun y : R3 ↦ y 0) hvw
  have hcoord1 :
      (((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * v 0 -
          (Real.sin (p 1) * Real.sin (p 0)) * v 1 =
        (((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * w 0 -
          (Real.sin (p 1) * Real.sin (p 0)) * w 1 := by
    simpa [torus_of_revolution_immersion_fderiv_apply] using congrArg (fun y : R3 ↦ y 1) hvw
  -- Compare two fixed linear combinations of the first two coordinates and the third coordinate.
  have h_v1_sin :
      -(Real.sin (p 1) * v 1) = -(Real.sin (p 1) * w 1) := by
    have hcoord0' := congrArg (fun t : ℝ ↦ Real.cos (p 0) * t) hcoord0
    have hcoord1' := congrArg (fun t : ℝ ↦ Real.sin (p 0) * t) hcoord1
    have hcomb :
        Real.cos (p 0) *
            (-(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * v 0 -
              (Real.sin (p 1) * Real.cos (p 0)) * v 1) +
          Real.sin (p 0) *
            ((((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * v 0 -
              (Real.sin (p 1) * Real.sin (p 0)) * v 1) =
        Real.cos (p 0) *
            (-(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * w 0 -
              (Real.sin (p 1) * Real.cos (p 0)) * w 1) +
          Real.sin (p 0) *
            ((((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * w 0 -
              (Real.sin (p 1) * Real.sin (p 0)) * w 1) := by
      linarith
    ring_nf at hcomb
    nlinarith [hcomb, Real.sin_sq_add_cos_sq (p 0)]
  have h_v1_cos :
      Real.cos (p 1) * v 1 = Real.cos (p 1) * w 1 := by
    have hcoord := congrArg (fun y : R3 ↦ y 2) hvw
    simpa [torus_of_revolution_immersion_fderiv_apply] using hcoord
  have h_v1 : v 1 = w 1 := by
    have hsin_zero : Real.sin (p 1) * (v 1 - w 1) = 0 := by
      linarith
    have hcos_zero : Real.cos (p 1) * (v 1 - w 1) = 0 := by
      linarith
    have hsq : (v 1 - w 1) ^ (2 : ℕ) = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq (p 1), hsin_zero, hcos_zero]
    nlinarith
  have h_v0_scaled :
      ((2 : ℝ) + Real.cos (p 1)) * v 0 = ((2 : ℝ) + Real.cos (p 1)) * w 0 := by
    have hcoord0' := congrArg (fun t : ℝ ↦ (-Real.sin (p 0)) * t) hcoord0
    have hcoord1' := congrArg (fun t : ℝ ↦ Real.cos (p 0) * t) hcoord1
    have hcomb :
        (-Real.sin (p 0)) *
            (-(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * v 0 -
              (Real.sin (p 1) * Real.cos (p 0)) * v 1) +
          Real.cos (p 0) *
            ((((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * v 0 -
              (Real.sin (p 1) * Real.sin (p 0)) * v 1) =
        (-Real.sin (p 0)) *
            (-(((2 : ℝ) + Real.cos (p 1)) * Real.sin (p 0)) * w 0 -
              (Real.sin (p 1) * Real.cos (p 0)) * w 1) +
          Real.cos (p 0) *
            ((((2 : ℝ) + Real.cos (p 1)) * Real.cos (p 0)) * w 0 -
              (Real.sin (p 1) * Real.sin (p 0)) * w 1) := by
      linarith
    ring_nf at hcomb
    nlinarith [hcomb, h_v1, Real.sin_sq_add_cos_sq (p 0)]
  have h_v0 : v 0 = w 0 := by
    have hfactor : 0 < (2 : ℝ) + Real.cos (p 1) := torus_revolution_factor_cos_pos (p 1)
    nlinarith
  ext i
  fin_cases i
  · exact h_v0
  · exact h_v1

/-- Helper for Problem 4-12: the ambient torus parametrization is an immersion. -/
theorem torus_of_revolution_immersion_isImmersion :
    IsImmersion (𝓡 2) (𝓡 3) ∞ torus_of_revolution_immersion := by
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    torus_of_revolution_immersion_contMDiff).2 ?_
  intro p
  -- In Euclidean models, the manifold derivative agrees with the ordinary Fréchet derivative.
  rw [mfderiv_eq_fderiv]
  exact torus_of_revolution_immersion_fderiv_injective p

/-- Problem 4-12 (2): the descended map `X̃ : 𝕋² → ℝ³` is smooth. -/
theorem torus_of_revolution_map_contMDiff :
    ContMDiff T2Model (𝓡 3) ∞ torus_of_revolution_map := by
  let hcov := standard_torus_covering_isSmoothCoveringMap 2
  -- Route correction: descend smoothness through the surjective local diffeomorphism `ε²`
  -- instead of proving the torus coordinate projections directly on the product model.
  refine
    (smooth_iff_comp_right_of_surjective_isLocalDiffeomorph hcov.isLocalDiffeomorph
      hcov.surjective).2 ?_
  -- The lifted map is exactly the ambient smooth immersion `X : ℝ² → ℝ³`.
  simpa [torus_of_revolution_map_comp_standardTorusCovering] using
    torus_of_revolution_immersion_contMDiff

/-- Helper for Problem 4-12: at a cover point, the manifold derivative of the ambient immersion
factors through the derivative of the descended torus map and the covering derivative. -/
lemma torus_of_revolution_map_mfderiv_comp_cover (x : R2) :
    mfderiv (𝓡 2) (𝓡 3) torus_of_revolution_immersion x =
      (mfderiv T2Model (𝓡 3) torus_of_revolution_map (standardTorusCovering 2 x)).comp
        (mfderiv (𝓡 2) T2Model (standardTorusCovering 2) x) := by
  let hcov := standard_torus_covering_isSmoothCoveringMap 2
  have hmap :
      MDifferentiableAt T2Model (𝓡 3) torus_of_revolution_map (standardTorusCovering 2 x) :=
    torus_of_revolution_map_contMDiff.mdifferentiableAt (by simp)
  have hcover :
      MDifferentiableAt (𝓡 2) T2Model (standardTorusCovering 2) x :=
    hcov.isLocalDiffeomorph.contMDiff.mdifferentiableAt (by simp)
  -- Differentiate the factorization `X = X̃ ∘ ε²` and apply the manifold chain rule once.
  simpa [torus_of_revolution_map_comp_standardTorusCovering] using
    mfderiv_comp x hmap hcover

/-- Helper for Problem 4-12: the manifold derivative of the standard torus covering is surjective
at every point. -/
lemma standard_torus_covering_mfderiv_surjective (x : R2) :
    Function.Surjective (mfderiv (𝓡 2) T2Model (standardTorusCovering 2) x) := by
  let hcov := standard_torus_covering_isSmoothCoveringMap 2
  -- The covering derivative is the underlying map of the tangent-space equivalence supplied by
  -- the local diffeomorphism structure.
  rw [← hcov.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe (by simp) x]
  exact (hcov.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).surjective

/-- Helper for Problem 4-12: the descended torus map has injective manifold derivative at each
point coming from the covering coordinates. -/
lemma torus_of_revolution_map_mfderiv_injective_at_cover (x : R2) :
    Function.Injective
      (mfderiv T2Model (𝓡 3) torus_of_revolution_map (standardTorusCovering 2 x)) := by
  have himm :
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) torus_of_revolution_immersion x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv
      torus_of_revolution_immersion_contMDiff).mp torus_of_revolution_immersion_isImmersion x
  have hcomp :
      Function.Injective
        ((mfderiv T2Model (𝓡 3) torus_of_revolution_map (standardTorusCovering 2 x)).comp
          (mfderiv (𝓡 2) T2Model (standardTorusCovering 2) x)) := by
    simpa [torus_of_revolution_map_mfderiv_comp_cover x] using himm
  -- Surjectivity of the covering derivative lets injectivity descend to the torus derivative.
  exact injective_of_comp_right hcomp (standard_torus_covering_mfderiv_surjective x)

/-- Helper for Problem 4-12: the descended torus map is an immersion because every torus point
comes from a cover point where the derivative is already known to be injective. -/
theorem torus_of_revolution_map_isImmersion :
    IsImmersion T2Model (𝓡 3) ∞ torus_of_revolution_map := by
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    torus_of_revolution_map_contMDiff).2 ?_
  intro z
  let hcov := standard_torus_covering_isSmoothCoveringMap 2
  rcases hcov.surjective z with ⟨x, rfl⟩
  -- Lift the torus point to `ℝ²` and reuse the injectivity established upstairs.
  exact torus_of_revolution_map_mfderiv_injective_at_cover x

/-- Helper for Problem 4-12: the first two coordinates of the descended torus map have squared
radius `(2 + Re z₁)²`. -/
theorem torus_of_revolution_map_xy_sq (z : 𝕋^{2}) :
    (torus_of_revolution_map z 0) ^ (2 : ℕ) + (torus_of_revolution_map z 1) ^ (2 : ℕ) =
      ((2 : ℝ) + (z 1 : ℂ).re) ^ (2 : ℕ) := by
  -- Expand the two Cartesian coordinates and factor out the common radius.
  have hz0 := circle_re_sq_add_im_sq (z 0)
  calc
    (torus_of_revolution_map z 0) ^ (2 : ℕ) + (torus_of_revolution_map z 1) ^ (2 : ℕ)
        = (((2 : ℝ) + (z 1 : ℂ).re) * (z 0 : ℂ).re) ^ (2 : ℕ) +
            (((2 : ℝ) + (z 1 : ℂ).re) * (z 0 : ℂ).im) ^ (2 : ℕ) := by
              simp [torus_of_revolution_map]
    _ = ((2 : ℝ) + (z 1 : ℂ).re) ^ (2 : ℕ) *
          ((z 0 : ℂ).re ^ (2 : ℕ) + (z 0 : ℂ).im ^ (2 : ℕ)) := by ring
    _ = ((2 : ℝ) + (z 1 : ℂ).re) ^ (2 : ℕ) := by simp [hz0]

/-- Helper for Problem 4-12: the descended torus map is injective. -/
theorem torus_of_revolution_map_injective :
    Function.Injective torus_of_revolution_map := by
  intro z w hzw
  have hxy :
      ((2 : ℝ) + (z 1 : ℂ).re) ^ (2 : ℕ) = ((2 : ℝ) + (w 1 : ℂ).re) ^ (2 : ℕ) := by
    -- The first two coordinates determine the common radial factor.
    rw [← torus_of_revolution_map_xy_sq z, ← torus_of_revolution_map_xy_sq w]
    simp [hzw]
  have hre1 : (z 1 : ℂ).re = (w 1 : ℂ).re := by
    have hzpos := torus_revolution_factor_circle_pos (z 1)
    have hwpos := torus_revolution_factor_circle_pos (w 1)
    nlinarith
  have him1 : (z 1 : ℂ).im = (w 1 : ℂ).im := by
    -- The third coordinate is exactly the imaginary part of the second circle factor.
    have hcoord := congrArg (fun y : R3 ↦ y 2) hzw
    simpa [torus_of_revolution_map] using hcoord
  have hz1w1 : z 1 = w 1 := circle_eq_of_re_eq_im_eq hre1 him1
  have hfactor_ne : ((2 : ℝ) + (z 1 : ℂ).re) ≠ 0 :=
    ne_of_gt (torus_revolution_factor_circle_pos (z 1))
  have hre0 : (z 0 : ℂ).re = (w 0 : ℂ).re := by
    -- Once the common radial factor matches, the first Cartesian coordinate recovers `Re z₀`.
    have hcoord := congrArg (fun y : R3 ↦ y 0) hzw
    have hcoord' :
        ((2 : ℝ) + (z 1 : ℂ).re) * (z 0 : ℂ).re =
          ((2 : ℝ) + (z 1 : ℂ).re) * (w 0 : ℂ).re := by
      simpa [torus_of_revolution_map, hz1w1] using hcoord
    exact mul_left_cancel₀ hfactor_ne hcoord'
  have him0 : (z 0 : ℂ).im = (w 0 : ℂ).im := by
    -- The second Cartesian coordinate similarly recovers `Im z₀`.
    have hcoord := congrArg (fun y : R3 ↦ y 1) hzw
    have hcoord' :
        ((2 : ℝ) + (z 1 : ℂ).re) * (z 0 : ℂ).im =
          ((2 : ℝ) + (z 1 : ℂ).re) * (w 0 : ℂ).im := by
      simpa [torus_of_revolution_map, hz1w1] using hcoord
    exact mul_left_cancel₀ hfactor_ne hcoord'
  ext i
  fin_cases i
  · simpa using congrArg (fun u : Circle ↦ (u : ℂ)) (circle_eq_of_re_eq_im_eq hre0 him0)
  · simpa using congrArg (fun u : Circle ↦ (u : ℂ)) hz1w1

/-- Problem 4-12 (3): the descended map `X̃ : 𝕋² → ℝ³` is a smooth embedding. -/
theorem torus_of_revolution_map_isSmoothEmbedding :
    IsSmoothEmbedding T2Model (𝓡 3) ∞ torus_of_revolution_map := by
  -- Compactness of `𝕋²` upgrades the injective immersion to a smooth embedding.
  exact smooth_embedding_of_compact_source_injective_isImmersion
    torus_of_revolution_map_injective torus_of_revolution_map_isImmersion

/-- Helper for Problem 4-12: every point in the image of the descended torus map satisfies the
quartic surface equation. -/
theorem torus_of_revolution_map_mem_surface (z : 𝕋^{2}) :
    torus_of_revolution_map z ∈ torus_of_revolution_surface := by
  -- Expand the quartic equation using the radial identity from `torus_of_revolution_map_xy_sq`.
  have hxy := torus_of_revolution_map_xy_sq z
  have hz1 := circle_re_sq_add_im_sq (z 1)
  change
    ((torus_of_revolution_map z 0) ^ (2 : ℕ) + (torus_of_revolution_map z 1) ^ (2 : ℕ) +
        (torus_of_revolution_map z 2) ^ (2 : ℕ) + 3) ^ (2 : ℕ) =
      16 * ((torus_of_revolution_map z 0) ^ (2 : ℕ) + (torus_of_revolution_map z 1) ^ (2 : ℕ))
  rw [hxy]
  simp [torus_of_revolution_map]
  nlinarith [hz1]

/-- Helper for Problem 4-12: a point on the quartic torus surface has the expected radial data. -/
lemma torus_of_revolution_surface_radial_data (p : R3) (hp : p ∈ torus_of_revolution_surface) :
    let r := Real.sqrt (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ))
    r ^ (2 : ℕ) = p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) ∧
      (r - 2) ^ (2 : ℕ) + p 2 ^ (2 : ℕ) = 1 ∧
      1 ≤ r := by
  let r := Real.sqrt (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ))
  have hs_nonneg : 0 ≤ p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) := by
    positivity
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ (2 : ℕ) = p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) := by
    simpa [r] using Real.sq_sqrt hs_nonneg
  have hquartic :
      (r ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + 3) ^ (2 : ℕ) = (4 * r) ^ (2 : ℕ) := by
    calc
      (r ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + 3) ^ (2 : ℕ)
          = ((p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ)) + p 2 ^ (2 : ℕ) + 3) ^ (2 : ℕ) := by
              rw [hr_sq]
      _ = 16 * (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ)) := hp
      _ = 16 * r ^ (2 : ℕ) := by rw [hr_sq]
      _ = (4 * r) ^ (2 : ℕ) := by ring
  have hleft_nonneg : 0 ≤ r ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + 3 := by
    positivity
  have hlinear : r ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + 3 = 4 * r := by
    exact (sq_eq_sq₀ hleft_nonneg (by positivity)).mp hquartic
  have hcircle : (r - 2) ^ (2 : ℕ) + p 2 ^ (2 : ℕ) = 1 := by
    nlinarith
  have hr_ge_one : 1 ≤ r := by
    nlinarith [sq_nonneg (r - 2), sq_nonneg (p 2), hcircle]
  -- The quartic equation becomes the standard unit-circle equation for the minor radius.
  exact ⟨hr_sq, hcircle, hr_ge_one⟩

/-- Helper for Problem 4-12: a point on the quartic torus surface determines the two circle
factors of its torus preimage. -/
lemma torus_of_revolution_surface_circle_factors (p : R3)
    (hp : p ∈ torus_of_revolution_surface) :
    let r := Real.sqrt (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ))
    ∃ z0 z1 : Circle,
      (z0 : ℂ).re = p 0 / r ∧
      (z0 : ℂ).im = p 1 / r ∧
        (z1 : ℂ).re = r - 2 ∧
        (z1 : ℂ).im = p 2 ∧
        (2 : ℝ) + (z1 : ℂ).re = r := by
  let r := Real.sqrt (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ))
  rcases torus_of_revolution_surface_radial_data p hp with ⟨hr_sq, hminor, hr_ge_one⟩
  have hr_ne : r ≠ 0 := by
    linarith
  let w0 : ℂ := (p 0 / r : ℝ) + (p 1 / r : ℝ) * Complex.I
  let w1 : ℂ := (r - 2 : ℝ) + (p 2 : ℝ) * Complex.I
  have hr_sq' : r ^ (2 : ℕ) = p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) := by
    simpa [r] using hr_sq
  have hminor' : (r - 2) ^ (2 : ℕ) + p 2 ^ (2 : ℕ) = 1 := by
    simpa [r] using hminor
  have hw0_normSq : Complex.normSq w0 = 1 := by
    -- Normalize the radial coordinates by the nonzero radius `r`.
    have hcalc :
        (p 0 / r) ^ (2 : ℕ) + (p 1 / r) ^ (2 : ℕ) =
          (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ)) / r ^ (2 : ℕ) := by
      field_simp [hr_ne]
    calc
      Complex.normSq w0 = (p 0 / r) ^ (2 : ℕ) + (p 1 / r) ^ (2 : ℕ) := by
        simp [w0, Complex.normSq_apply]
        ring
      _ = (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ)) / r ^ (2 : ℕ) := hcalc
      _ = 1 := by
        rw [← hr_sq']
        field_simp [hr_ne]
  have hw1_normSq : Complex.normSq w1 = 1 := by
    -- The quartic equation already gave the second circle factor.
    simpa [w1, Complex.normSq_apply, pow_two] using hminor'
  have hw0_mem : w0 ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by
      simpa [Complex.normSq_eq_norm_sq] using hw0_normSq)
  have hw1_mem : w1 ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by
      simpa [Complex.normSq_eq_norm_sq] using hw1_normSq)
  let z0 : Circle := ⟨w0, hw0_mem⟩
  let z1 : Circle := ⟨w1, hw1_mem⟩
  have hz0_re : (z0 : ℂ).re = p 0 / r := by
    simp [z0, w0]
  have hz0_im : (z0 : ℂ).im = p 1 / r := by
    simp [z0, w0]
  have hz1_re : (z1 : ℂ).re = r - 2 := by
    simp [z1, w1]
  have hz1_im : (z1 : ℂ).im = p 2 := by
    simp [z1, w1]
  have hz1_shift : (2 : ℝ) + (z1 : ℂ).re = r := by
    rw [hz1_re]
    ring
  -- Package the two unit complex numbers as the torus coordinates.
  exact ⟨z0, z1, hz0_re, hz0_im, hz1_re, hz1_im, hz1_shift⟩

/-- Helper for Problem 4-12: every point on the quartic torus surface has an explicit preimage in
`𝕋²`. -/
lemma torus_of_revolution_surface_has_preimage (p : R3)
    (hp : p ∈ torus_of_revolution_surface) :
    ∃ z : 𝕋^{2}, torus_of_revolution_map z = p := by
  let r := Real.sqrt (p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ))
  rcases torus_of_revolution_surface_circle_factors p hp with
    ⟨z0, z1, hz0_re, hz0_im, hz1_re, hz1_im, hz1_shift⟩
  have hr_ge_one :
      1 ≤ r := (torus_of_revolution_surface_radial_data p hp).2.2
  have hr_ne : r ≠ 0 := by
    linarith
  let z : 𝕋^{2} := ![z0, z1]
  refine ⟨z, ?_⟩
  -- Read off the three coordinates of `X̃(z)` from the chosen circle factors.
  ext i
  fin_cases i
  · have hcoord : r * (p 0 / r) = p 0 := by
      field_simp [hr_ne]
    simpa [torus_of_revolution_map, z, hz0_re, hz1_shift] using hcoord
  · have hcoord : r * (p 1 / r) = p 1 := by
      field_simp [hr_ne]
    simpa [torus_of_revolution_map, z, hz0_im, hz1_shift] using hcoord
  · simp [torus_of_revolution_map, z, hz1_im]

/-- Problem 4-12 (4): the image of the descended torus embedding is exactly the standard torus
surface of revolution in `ℝ³`. -/
theorem range_torus_of_revolution_map :
    Set.range torus_of_revolution_map = torus_of_revolution_surface := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    -- Every torus point satisfies the quartic equation by direct expansion.
    exact torus_of_revolution_map_mem_surface z
  · intro hp
    -- Conversely, the explicit circle-factor reconstruction provides a torus preimage.
    exact torus_of_revolution_surface_has_preimage p hp
