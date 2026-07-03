import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_2_1 (from Chap02/Sec02_08) -/
noncomputable section

open scoped Manifold ContDiff

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/- Exercise 2.1: building on the bundled smooth-function space recalled in
`Notation_2_8_extra_3`, the canonical mathlib ring structure makes the smooth real-valued
functions on a smooth manifold into a commutative ring under pointwise multiplication. -/
#check (inferInstance : CommRing C^∞⟮I, M; ℝ⟯)

/- Exercise 2.1, pointwise multiplication: this is the canonical owner theorem
`ContMDiffMap.coe_mul`, specialized to smooth real-valued functions on `M`. -/
#check (ContMDiffMap.coe_mul : ∀ f g : C^∞⟮I, M; ℝ⟯, ⇑(f * g) = f * g)

/- The same space of smooth real-valued functions carries its canonical `ℝ`-algebra structure. -/
#check (inferInstance : Algebra ℝ C^∞⟮I, M; ℝ⟯)

/- Exercise 2.1, scalar multiplication: this is the canonical owner theorem
`ContMDiffMap.coe_smul`, specialized to the canonical `ℝ`-algebra structure on
`C^∞⟮I, M; ℝ⟯`. -/
#check (ContMDiffMap.coe_smul : ∀ r : ℝ, ∀ f : C^∞⟮I, M; ℝ⟯, ⇑(r • f) = r • ⇑f)

/-! ### Problem_2_1 (from Chap02/Sec02_12) -/
open Set
open scoped Manifold ContDiff

/-- The real Heaviside step function, equal to `1` on `[0, ∞)` and `0` on `(-∞, 0)`. -/
noncomputable def realHeavisideStep : ℝ → ℝ :=
  fun x ↦ if 0 ≤ x then 1 else 0

-- Proof sketch: unfold `realHeavisideStep` and simplify the defining `if` using `hx`.
/-- The real Heaviside step function takes the value `1` at every nonnegative real number. -/
theorem realHeavisideStep_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    realHeavisideStep x = 1 := by
  simp [realHeavisideStep, hx]

/-- The real Heaviside step function takes the value `0` at every negative real number. -/
theorem realHeavisideStep_of_neg {x : ℝ} (hx : x < 0) :
    realHeavisideStep x = 0 := by
  simp [realHeavisideStep, show ¬ 0 ≤ x by linarith]

-- Proof sketch: if `x < 0`, choose an open neighborhood `U` on which `realHeavisideStep` is
-- constantly `0`; if `x ≥ 0`, choose an open neighborhood `V` of `1` and take `U = univ`, so the
-- relevant restriction is constantly `1` on `U ∩ realHeavisideStep ⁻¹' V`. For the identity
-- charts on open subsets of `ℝ`, this is exactly a `ContDiffOn` statement for the restricted map.
/-- Problem 2-1 (1): this records only the chartwise `ContDiffOn` clause appearing in the canonical
smoothness criterion `contMDiff_iff`; it is a local bridge theorem rather than a second smoothness
owner. With identity charts on open subsets of `ℝ`, this is the existence of open neighborhoods
`U` of `x` and `V` of `realHeavisideStep x` such that `realHeavisideStep` is `ContDiffOn` on
`U ∩ realHeavisideStep ⁻¹' V`. -/
theorem realHeavisideStep_has_local_smooth_coordinate_representatives (x : ℝ) :
    ∃ U V : Set ℝ,
      IsOpen U ∧ x ∈ U ∧
      IsOpen V ∧ realHeavisideStep x ∈ V ∧
      ContDiffOn ℝ ∞ realHeavisideStep (U ∩ realHeavisideStep ⁻¹' V) := by
  by_cases hx : x < 0
  · refine ⟨Iio 0, univ, isOpen_Iio, hx, isOpen_univ, mem_univ _, ?_⟩
    simpa [preimage_univ, inter_univ] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) (Iio 0)).congr
        (fun y hy ↦ realHeavisideStep_of_neg hy)
  · have hx_nonneg : 0 ≤ x := le_of_not_gt hx
    refine ⟨univ, Ioi (1 / 2 : ℝ), isOpen_univ, mem_univ _, isOpen_Ioi, ?_, ?_⟩
    · simpa [realHeavisideStep_of_nonneg hx_nonneg] using
        (show (1 : ℝ) ∈ Ioi (1 / 2 : ℝ) by norm_num)
    · simpa [inter_univ] using
        (contDiffOn_const :
            ContDiffOn ℝ ∞ (fun _ : ℝ ↦ (1 : ℝ)) (realHeavisideStep ⁻¹' Ioi (1 / 2 : ℝ))).congr
          (fun y hy ↦
            have hyV : realHeavisideStep y ∈ Ioi (1 / 2 : ℝ) := by
              simpa [Set.mem_preimage] using hy
            have hy_nonneg : 0 ≤ y := by
              by_contra hy_nonneg
              have hzero : realHeavisideStep y = 0 := by
                exact realHeavisideStep_of_neg (lt_of_not_ge hy_nonneg)
              exact (by simp : ¬ (0 : ℝ) ∈ Ioi (1 / 2 : ℝ)) (by simpa [hzero] using hyV)
            realHeavisideStep_of_nonneg hy_nonneg)

/-- The real Heaviside step function has a jump discontinuity at `0`. -/
theorem realHeavisideStep_not_continuousAt_zero :
    ¬ ContinuousAt realHeavisideStep 0 := by
  intro hcont
  have hpre : realHeavisideStep ⁻¹' Ioi (1 / 2 : ℝ) ∈ nhds (0 : ℝ) := by
    have hV : Ioi (1 / 2 : ℝ) ∈ nhds (realHeavisideStep 0) := by
      simpa [realHeavisideStep_of_nonneg (show (0 : ℝ) ≤ 0 by rfl)] using
        Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
    exact hcont.preimage_mem_nhds hV
  rcases Metric.mem_nhds_iff.1 hpre with ⟨ε, hε_pos, hε_subset⟩
  have hε_half_pos : 0 < ε / 2 := by
    linarith
  have hball : -(ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hε_half_pos]
    linarith
  have hmem : -(ε / 2) ∈ realHeavisideStep ⁻¹' Ioi (1 / 2 : ℝ) := hε_subset hball
  have hzero : realHeavisideStep (-(ε / 2)) = 0 := by
    apply realHeavisideStep_of_neg
    linarith
  exact (by simp : ¬ (0 : ℝ) ∈ Ioi (1 / 2 : ℝ)) (by simpa [Set.mem_preimage, hzero] using hmem)

-- Problem 2-1 (2) is a derived `ContMDiff` consequence of the jump discontinuity above via the
-- canonical owner theorem `ContMDiff.continuous`.
/-- Problem 2-1 (2): the real Heaviside step function is not smooth as a map `ℝ → ℝ` in the
sense of this chapter; smoothness would force continuity. -/
theorem realHeavisideStep_not_smooth :
    ¬ ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ realHeavisideStep := by
  intro hsmooth
  exact realHeavisideStep_not_continuousAt_zero hsmooth.continuous.continuousAt
