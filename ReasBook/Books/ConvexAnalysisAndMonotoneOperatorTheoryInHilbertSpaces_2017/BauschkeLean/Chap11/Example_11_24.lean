import Mathlib
import BauschkeLean.Chap01.Definition_1_8
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.
-- `lean_leansearch` was unavailable in this session, so the statement shape was checked against
-- local Chapter 11 precedent and direct file-level type-checking.

noncomputable section

namespace ERealFunction

open Filter

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [-instance] Prod.nonUnitalSeminormedRing Prod.seminormedRing
attribute [-instance] Prod.nonUnitalNormedRing Prod.normedRing Prod.normedCommRing
attribute [-instance] Prod.nonUnitalSeminormedCommRing Prod.nonUnitalNormedCommRing
attribute [-instance] Prod.seminormedCommRing

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- The real-valued function `(ξ₁, ξ₂) ↦ ξ₁ + ‖(ξ₁, ξ₂)‖` from Example 11.24, viewed on `ℝ²`
with the local `ℓ²` product geometry. -/
noncomputable def example11_24Function : ℝ × ℝ → ℝ
  | (ξ₁, ξ₂) => ξ₁ + ‖(ξ₁, ξ₂)‖

local notation "f" => example11_24Function.toEReal.asEReal

/-- The sequence `xₙ = (-n, 1)` from Example 11.24. -/
def example11_24Sequence : ℕ → ℝ × ℝ
  | n => (-((n : ℝ)), 1)

/-- Helper for Example 11.24: the local `ℓ²` norm on `ℝ²` is the usual Euclidean norm in
coordinates. -/
private theorem example11_24_prod_norm_eq (ξ : ℝ × ℝ) :
    ‖ξ‖ = Real.sqrt (ξ.1 ^ 2 + ξ.2 ^ 2) := by
  -- Translate the raw-product norm to `WithLp 2`, where the Euclidean coordinate formula is
  -- already available.
  calc
    ‖ξ‖ = ‖WithLp.toLp 2 ξ‖ := by
      simpa using
        (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := ℝ) (β := ℝ) ξ)
    _ = Real.sqrt (‖(WithLp.toLp 2 ξ).fst‖ ^ 2 + ‖(WithLp.toLp 2 ξ).snd‖ ^ 2) := by
      simpa using (WithLp.prod_norm_eq_of_L2 (x := WithLp.toLp 2 ξ))
    _ = Real.sqrt (ξ.1 ^ 2 + ξ.2 ^ 2) := by
      simp

/-- Helper for Example 11.24: the function `ξ₁ + ‖ξ‖` is bounded below by `0` on `ℝ²`. -/
private theorem example11_24Function_nonneg (ξ : ℝ × ℝ) :
    0 ≤ example11_24Function ξ := by
  have hcoord : |ξ.1| ≤ ‖ξ‖ := by
    -- The first coordinate is dominated by the transported `ℓ²` product norm.
    simpa [Real.norm_eq_abs] using
      (WithLp.norm_fst_le (p := 2) (x := WithLp.toLp 2 ξ))
  have hneg : -ξ.1 ≤ ‖ξ‖ := by
    exact (neg_le_abs ξ.1).trans hcoord
  -- Rearranging the coordinate estimate gives the nonnegativity of the objective.
  rw [example11_24Function]
  linarith

/-- Helper for Example 11.24: the zero set of `ξ₁ + ‖ξ‖` is the nonpositive horizontal axis. -/
private theorem example11_24Function_eq_zero_iff (ξ : ℝ × ℝ) :
    example11_24Function ξ = 0 ↔ ξ.1 ≤ 0 ∧ ξ.2 = 0 := by
  constructor
  · intro hzero
    have hnorm_eq : ‖ξ‖ = -ξ.1 := by
      rw [example11_24Function] at hzero
      linarith
    have hξ1_nonpos : ξ.1 ≤ 0 := by
      have hnorm_nonneg : 0 ≤ ‖ξ‖ := by
        rw [example11_24_prod_norm_eq]
        exact Real.sqrt_nonneg _
      linarith
    have hsqrt_eq : Real.sqrt (ξ.1 ^ 2 + ξ.2 ^ 2) = -ξ.1 := by
      simpa [example11_24_prod_norm_eq] using hnorm_eq
    have hsq : ξ.1 ^ 2 + ξ.2 ^ 2 = (-ξ.1) ^ 2 := by
      -- Squaring the norm identity isolates the vanished second coordinate.
      have hsq' := congrArg (fun t : ℝ ↦ t ^ 2) hsqrt_eq
      change (Real.sqrt (ξ.1 ^ 2 + ξ.2 ^ 2)) ^ 2 = (-ξ.1) ^ 2 at hsq'
      rw [Real.sq_sqrt (by positivity : 0 ≤ ξ.1 ^ 2 + ξ.2 ^ 2)] at hsq'
      exact hsq'
    have hξ2_sq : ξ.2 ^ 2 = 0 := by
      nlinarith
    exact ⟨hξ1_nonpos, sq_eq_zero_iff.mp hξ2_sq⟩
  · rintro ⟨hξ1_nonpos, hξ2_zero⟩
    -- On the horizontal axis, the norm reduces to `|ξ₁| = -ξ₁`.
    rw [example11_24Function, example11_24_prod_norm_eq, hξ2_zero]
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_nonpos hξ1_nonpos]
    ring

/-- Helper for Example 11.24: the infimum of the range is attained at the origin and equals `0`.
-/
private theorem example11_24_sInf_eq_zero_aux :
    sInf (Set.range f) = 0 := by
  have hzero_lb : ∀ y ∈ Set.range f, (0 : EReal) ≤ y := by
    rintro y ⟨ξ, rfl⟩
    change (0 : EReal) ≤ ((example11_24Function ξ : ℝ) : EReal)
    exact_mod_cast example11_24Function_nonneg ξ
  have horigin_real : example11_24Function ((0 : ℝ), (0 : ℝ)) = 0 := by
    -- At the origin both the linear term and the Euclidean norm vanish.
    rw [example11_24Function, example11_24_prod_norm_eq]
    norm_num
  have horigin : f ((0 : ℝ), (0 : ℝ)) = 0 := by
    change ((example11_24Function ((0 : ℝ), (0 : ℝ)) : ℝ) : EReal) = 0
    exact_mod_cast horigin_real
  have hsInf_le : sInf (Set.range f) ≤ 0 := by
    exact (isGLB_sInf (Set.range f)).1 ⟨((0 : ℝ), (0 : ℝ)), horigin⟩
  have hzero_le : (0 : EReal) ≤ sInf (Set.range f) := by
    exact (isGLB_sInf (Set.range f)).2 hzero_lb
  exact le_antisymm hsInf_le hzero_le

/-- Helper for Example 11.24: rationalizing `-n + √(n²+1)` gives the reciprocal form used in the
limit argument. -/
private theorem example11_24_sequence_value_eq_inv (n : ℕ) :
    -((n : ℝ)) + Real.sqrt (((n : ℝ) ^ 2) + 1) =
      1 / (Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ)) := by
  have hinside_pos : 0 < ((n : ℝ) ^ 2) + 1 := by
    positivity
  have hdenom_pos : 0 < Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ) := by
    have hsqrt_pos : 0 < Real.sqrt (((n : ℝ) ^ 2) + 1) := Real.sqrt_pos.2 hinside_pos
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      positivity
    exact add_pos_of_pos_of_nonneg hsqrt_pos hn_nonneg
  have hdenom_ne : Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ) ≠ 0 := ne_of_gt hdenom_pos
  -- Multiplying by the conjugate reduces the numerator to `(n² + 1) - n² = 1`.
  field_simp [hdenom_ne]
  have hsqrt_sq : (Real.sqrt (((n : ℝ) ^ 2) + 1)) ^ 2 = ((n : ℝ) ^ 2) + 1 := by
    exact Real.sq_sqrt (by positivity : 0 ≤ ((n : ℝ) ^ 2) + 1)
  nlinarith

/-- Helper for Example 11.24: every point on the horizontal axis stays at least unit distance
from `xₙ = (-n, 1)`. -/
private theorem example11_24_one_le_dist_sequence_to_horizontal_axis_point
    (n : ℕ) (a : ℝ) :
    1 ≤ dist (example11_24Sequence n) (a, 0) := by
  have hroot : 1 ≤ Real.sqrt (((-((n : ℝ)) - a) ^ 2) + 1) := by
    -- The quantity under the square root is at least `1`.
    refine (Real.one_le_sqrt).2 ?_
    nlinarith
  simpa [dist_eq_norm, example11_24Sequence, example11_24_prod_norm_eq] using hroot

/-- Example 11.24 (1): the function `(ξ₁, ξ₂) ↦ ξ₁ + ‖(ξ₁, ξ₂)‖` is convex on `ℝ²`. -/
theorem example11_24Function_convexOn :
    _root_.ConvexOn ℝ Set.univ example11_24Function := by
  have hfst : _root_.ConvexOn ℝ Set.univ (fun ξ : ℝ × ℝ ↦ ξ.1) := by
    -- The first coordinate is a linear map, hence convex on the whole space.
    simpa using
      (((LinearMap.fst ℝ ℝ ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ).convexOn
        (convex_univ : Convex ℝ Set.univ))
  -- The objective is the sum of the first-coordinate linear functional and the norm.
  simpa [example11_24Function] using hfst.add (convexOn_norm (s := Set.univ) convex_univ)

/-- Example 11.24 (2): the minimizers of `f` are exactly the nonpositive horizontal axis
`ℝ₋ × {0}`. -/
theorem example11_24_argmin_eq :
    Argmin f = Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
  ext ξ
  -- The argmin set is the zero set because the global infimum is `0`.
  rw [mem_argmin_iff_eq_sInf, example11_24_sInf_eq_zero_aux]
  change ((example11_24Function ξ : ℝ) : EReal) = 0 ↔ ξ ∈ Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ)
  constructor
  · intro hzero
    have hzero_real : example11_24Function ξ = 0 := by
      exact_mod_cast hzero
    simpa [Set.mem_Iic, Set.mem_singleton_iff] using
      (example11_24Function_eq_zero_iff ξ).1 hzero_real
  · intro hmem
    have hzero_real : example11_24Function ξ = 0 := by
      simpa [Set.mem_Iic, Set.mem_singleton_iff] using
        (example11_24Function_eq_zero_iff ξ).2 hmem
    exact_mod_cast hzero_real

/-- Example 11.24 (3): along `xₙ = (-n, 1)`, the function values satisfy
`f(xₙ) = -n + √(n² + 1)`. -/
theorem example11_24Function_value_sequence (n : ℕ) :
    example11_24Function (example11_24Sequence n) =
      -((n : ℝ)) + Real.sqrt (((n : ℝ) ^ 2) + 1) := by
  -- Substituting the explicit sequence coordinates reduces the norm to the Euclidean formula.
  rw [example11_24Function, example11_24_prod_norm_eq]
  simp [example11_24Sequence]

/-- The infimum of the range of the Example 11.24 function is `0`. -/
theorem example11_24_sInf_eq_zero :
    sInf (Set.range f) = 0 := by
  -- The auxiliary infimum computation is exactly the main scalar statement here.
  exact example11_24_sInf_eq_zero_aux

/-- Example 11.24 (4): the sequence `xₙ = (-n, 1)` is a minimizing sequence for `f`. -/
theorem example11_24Sequence_isMinimizing :
    IsMinimizingSequence f example11_24Sequence := by
  rw [isMinimizingSequence_iff_lt_top]
  refine ⟨?_, ?_⟩
  · intro n
    -- Each term has a finite real value, so it lies strictly below `⊤`.
    change ((example11_24Function (example11_24Sequence n) : ℝ) : EReal) < ⊤
    rw [example11_24Function_value_sequence]
    exact EReal.coe_lt_top _
  · have hdenom :
        Tendsto
          (fun n : ℕ ↦ Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ))
          atTop atTop := by
      -- The denominator dominates `n`, so it also tends to `+∞`.
      refine Filter.tendsto_atTop_mono ?_ tendsto_natCast_atTop_atTop
      intro n
      have hsqrt_nonneg : 0 ≤ Real.sqrt (((n : ℝ) ^ 2) + 1) := Real.sqrt_nonneg _
      linarith
    have hinv :
        Tendsto
          (fun n : ℕ ↦ (1 / (Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ)) : ℝ))
          atTop (nhds (0 : ℝ)) := by
      simpa [one_div] using hdenom.inv_tendsto_atTop
    have hcoe :
        Tendsto
          (fun n : ℕ ↦
            (((1 / (Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ)) : ℝ) : EReal)))
          atTop (nhds (0 : EReal)) :=
      EReal.tendsto_coe.2 hinv
    have hvalues :
        f ∘ example11_24Sequence =
          fun n : ℕ ↦
            (((1 / (Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ)) : ℝ) : EReal)) := by
      funext n
      change ((example11_24Function (example11_24Sequence n) : ℝ) : EReal) =
        (((1 / (Real.sqrt (((n : ℝ) ^ 2) + 1) + (n : ℝ)) : ℝ) : EReal))
      rw [example11_24Function_value_sequence, example11_24_sequence_value_eq_inv]
    -- The rationalized value formula reduces the minimizing-sequence limit to a reciprocal that
    -- tends to `0`.
    rw [hvalues, example11_24_sInf_eq_zero]
    exact hcoe

/-- Example 11.24 (5): every term of `xₙ = (-n, 1)` stays at distance `1` from `Argmin f`. -/
theorem example11_24Sequence_infDist_argmin (n : ℕ) :
    Metric.infDist (example11_24Sequence n) (Argmin f) = 1 := by
  -- Replacing `Argmin f` by the explicit horizontal ray leaves a direct distance computation.
  rw [example11_24_argmin_eq]
  have hwitness : (-((n : ℝ)), (0 : ℝ)) ∈ Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ) := by
    refine ⟨?_, by simp⟩
    change -((n : ℝ)) ≤ 0
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      positivity
    linarith
  have hupper :
      Metric.infDist (example11_24Sequence n) (Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ)) ≤ 1 := by
    -- The point `(-n, 0)` lies on the minimizing ray and realizes distance `1`.
    simpa [example11_24Sequence, dist_eq_norm, example11_24_prod_norm_eq] using
      (Metric.infDist_le_dist_of_mem (x := example11_24Sequence n) hwitness)
  have hlower :
      1 ≤ Metric.infDist (example11_24Sequence n) (Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ)) := by
    -- Every point on the ray has second coordinate `0`, so the vertical gap enforces a unit
    -- lower bound on the infimum distance.
    rw [Metric.le_infDist
      (x := example11_24Sequence n)
      (s := Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ)) ⟨(-((n : ℝ)), 0), hwitness⟩]
    rintro ⟨a, b⟩ ha
    have hb : b = 0 := by
      simpa using ha.2
    simpa [hb] using example11_24_one_le_dist_sequence_to_horizontal_axis_point n a
  exact le_antisymm hupper hlower

end ERealFunction
