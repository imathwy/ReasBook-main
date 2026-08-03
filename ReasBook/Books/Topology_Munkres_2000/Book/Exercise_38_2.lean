module

public import Topology_Munkres_2000.Book.Example_38_3.Compactification
public import Topology_Munkres_2000.Book.Example_38_4.Extension
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

@[expose] public section

open Set

namespace TopologistsSineCurve

/-- Helper for Exercise 38.2: the formula `x ↦ cos (1 / x)` is continuous on `(0, 1)`. -/
lemma continuous_cosOscillationFormula :
    Continuous (fun x : Ioo (0 : ℝ) 1 ↦ Real.cos (1 / x.1)) := by
  -- The reciprocal is continuous away from zero, and cosine preserves continuity.
  have hreciprocal : Continuous (fun x : Ioo (0 : ℝ) 1 ↦ 1 / (x.1 : ℝ)) :=
    continuous_const.div continuous_subtype_val fun x ↦ ne_of_gt x.2.1
  exact Real.continuous_cos.comp hreciprocal

/-- Helper for Exercise 38.2: the cosine formula has uniformly bounded pairwise distance. -/
lemma cosOscillationFormula_bounded :
    ∃ C : ℝ, ∀ x y : Ioo (0 : ℝ) 1,
      dist (Real.cos (1 / x.1)) (Real.cos (1 / y.1)) ≤ C := by
  -- Both cosine values lie in `[-1, 1]`, so their distance is at most two.
  refine ⟨2, fun x y ↦ ?_⟩
  rw [Real.dist_eq]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [Real.neg_one_le_cos (1 / x.1), Real.cos_le_one (1 / y.1)]
  · linarith [Real.cos_le_one (1 / x.1), Real.neg_one_le_cos (1 / y.1)]

/-- The bounded continuous function `x ↦ cos (1 / x)` on `(0, 1)`. -/
noncomputable def cosOscillation : BoundedContinuousFunction (Ioo (0 : ℝ) 1) ℝ where
  -- Package the formula using the named continuity and boundedness facts above.
  toFun := fun x ↦ Real.cos (1 / x.1)
  continuous_toFun := continuous_cosOscillationFormula
  map_bounded' := cosOscillationFormula_bounded

/-- The bounded cosine oscillation has its prescribed pointwise formula. -/
@[simp]
theorem cosOscillation_apply (x : Ioo (0 : ℝ) 1) :
    cosOscillation x = Real.cos (1 / x.1) := rfl

/-- Helper for Exercise 38.2: the positive cosine phases are positive full turns. -/
private noncomputable def positiveCosinePhase (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (2 * Real.pi)

/-- Helper for Exercise 38.2: the negative cosine phases are odd half-turns after full turns. -/
private noncomputable def negativeCosinePhase (n : ℕ) : ℝ :=
  positiveCosinePhase n + Real.pi

/-- Helper for Exercise 38.2: every positive cosine phase is larger than one. -/
private lemma one_lt_positiveCosinePhase (n : ℕ) : 1 < positiveCosinePhase n := by
  -- A phase contains at least one full turn, and `π ≥ 2`.
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hpi : (2 : ℝ) ≤ Real.pi := by
    linarith [Real.one_le_pi_div_two]
  dsimp only [positiveCosinePhase]
  nlinarith

/-- Helper for Exercise 38.2: every negative cosine phase is larger than one. -/
private lemma one_lt_negativeCosinePhase (n : ℕ) : 1 < negativeCosinePhase n := by
  -- Adding the positive number `π` preserves the preceding lower bound.
  dsimp only [negativeCosinePhase]
  linarith [one_lt_positiveCosinePhase n, Real.pi_pos]

/-- Helper for Exercise 38.2: positive cosine phases tend to infinity. -/
private lemma positiveCosinePhase_tendsto_atTop :
    Filter.Tendsto positiveCosinePhase Filter.atTop Filter.atTop := by
  -- Natural numbers shifted by one diverge, as does their positive scalar multiple.
  have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop (b - 1)] with n hn
    linarith
  have hscale : (0 : ℝ) < 2 * Real.pi := by positivity
  refine (hnat.atTop_mul_const hscale).congr fun n ↦ ?_
  simp only [positiveCosinePhase, Nat.cast_add, Nat.cast_one]

/-- Helper for Exercise 38.2: negative cosine phases tend to infinity. -/
private lemma negativeCosinePhase_tendsto_atTop :
    Filter.Tendsto negativeCosinePhase Filter.atTop Filter.atTop := by
  -- A fixed translation of a divergent phase sequence still diverges.
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.tendsto_atTop.1 positiveCosinePhase_tendsto_atTop
    (b - Real.pi)] with n hn
  dsimp only [negativeCosinePhase]
  linarith

/-- Helper for Exercise 38.2: reciprocals of positive cosine phases lie in `(0, 1)`. -/
private lemma positiveCosineParameter_mem (n : ℕ) :
    1 / positiveCosinePhase n ∈ Ioo (0 : ℝ) 1 := by
  -- Positivity and the strict lower bound on the denominator give both inequalities.
  have hpositive : 0 < positiveCosinePhase n :=
    lt_trans zero_lt_one (one_lt_positiveCosinePhase n)
  have hdenominator : 1 < 1 * positiveCosinePhase n := by
    simpa only [one_mul] using one_lt_positiveCosinePhase n
  constructor
  · exact one_div_pos.mpr hpositive
  · exact (div_lt_iff₀ hpositive).mpr hdenominator

/-- Helper for Exercise 38.2: reciprocals of negative cosine phases lie in `(0, 1)`. -/
private lemma negativeCosineParameter_mem (n : ℕ) :
    1 / negativeCosinePhase n ∈ Ioo (0 : ℝ) 1 := by
  -- Positivity and the strict lower bound on the denominator give both inequalities.
  have hpositive : 0 < negativeCosinePhase n :=
    lt_trans zero_lt_one (one_lt_negativeCosinePhase n)
  have hdenominator : 1 < 1 * negativeCosinePhase n := by
    simpa only [one_mul] using one_lt_negativeCosinePhase n
  constructor
  · exact one_div_pos.mpr hpositive
  · exact (div_lt_iff₀ hpositive).mpr hdenominator

/-- Helper for Exercise 38.2: source points with cosine value one. -/
private noncomputable def positiveCosineParameter (n : ℕ) : Ioo (0 : ℝ) 1 :=
  ⟨1 / positiveCosinePhase n, positiveCosineParameter_mem n⟩

/-- Helper for Exercise 38.2: source points with cosine value negative one. -/
private noncomputable def negativeCosineParameter (n : ℕ) : Ioo (0 : ℝ) 1 :=
  ⟨1 / negativeCosinePhase n, negativeCosineParameter_mem n⟩

/-- Helper for Exercise 38.2: positive cosine parameters tend to zero in `ℝ`. -/
private lemma positiveCosineParameter_tendsto_zero :
    Filter.Tendsto (fun n ↦ (positiveCosineParameter n).1)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Taking reciprocals turns phase divergence into convergence to zero.
  refine (tendsto_inv_atTop_zero.comp positiveCosinePhase_tendsto_atTop).congr
    fun n ↦ ?_
  simp only [Function.comp_apply, positiveCosineParameter, one_div]

/-- Helper for Exercise 38.2: negative cosine parameters tend to zero in `ℝ`. -/
private lemma negativeCosineParameter_tendsto_zero :
    Filter.Tendsto (fun n ↦ (negativeCosineParameter n).1)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Taking reciprocals turns phase divergence into convergence to zero.
  refine (tendsto_inv_atTop_zero.comp negativeCosinePhase_tendsto_atTop).congr
    fun n ↦ ?_
  simp only [Function.comp_apply, negativeCosineParameter, one_div]

/-- Helper for Exercise 38.2: sine vanishes at every positive cosine phase. -/
private lemma sin_positiveCosinePhase (n : ℕ) :
    Real.sin (positiveCosinePhase n) = 0 := by
  -- Full turns do not change the sine of zero.
  simpa only [positiveCosinePhase, zero_add, Real.sin_zero] using
    Real.sin_add_nat_mul_two_pi 0 (n + 1)

/-- Helper for Exercise 38.2: sine vanishes at every negative cosine phase. -/
private lemma sin_negativeCosinePhase (n : ℕ) :
    Real.sin (negativeCosinePhase n) = 0 := by
  -- Adding `π` negates sine, which is already zero at the full-turn phase.
  rw [negativeCosinePhase, Real.sin_add_pi, sin_positiveCosinePhase]
  norm_num

/-- Helper for Exercise 38.2: cosine is one at every positive cosine phase. -/
private lemma cos_positiveCosinePhase (n : ℕ) :
    Real.cos (positiveCosinePhase n) = 1 := by
  -- Evaluate cosine at an integral number of full turns.
  simpa only [positiveCosinePhase] using Real.cos_nat_mul_two_pi (n + 1)

/-- Helper for Exercise 38.2: cosine is negative one at every negative cosine phase. -/
private lemma cos_negativeCosinePhase (n : ℕ) :
    Real.cos (negativeCosinePhase n) = -1 := by
  -- Evaluate cosine one half-turn after an integral number of full turns.
  simpa only [negativeCosinePhase, positiveCosinePhase] using
    Real.cos_nat_mul_two_pi_add_pi (n + 1)

/-- Helper for Exercise 38.2: zero belongs to the signed unit interval. -/
private lemma zero_mem_signedUnitInterval : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by
  -- Both endpoint inequalities are numerical.
  norm_num

/-- Helper for Exercise 38.2: the origin regarded as a point of the signed unit interval. -/
private def signedUnitOrigin : Icc (-1 : ℝ) 1 :=
  ⟨0, zero_mem_signedUnitInterval⟩

/-- Helper for Exercise 38.2: the origin of the square containing the sine curve. -/
private def squareOrigin : Square :=
  (signedUnitOrigin, signedUnitOrigin)

/-- Helper for Exercise 38.2: the first square-embedding coordinate is the source value. -/
private lemma squareEmbedding_firstCoordinate (x : Ioo (0 : ℝ) 1) :
    (squareEmbedding x).1.1 = x.1 := by
  -- Project the first coordinate from the public planar computation rule.
  have hcoordinates := congrArg Prod.fst (squareInclusion_squareEmbedding x)
  simpa only [squareInclusion_apply] using hcoordinates

/-- Helper for Exercise 38.2: the second square-embedding coordinate is the sine value. -/
private lemma squareEmbedding_secondCoordinate (x : Ioo (0 : ℝ) 1) :
    (squareEmbedding x).2.1 = Real.sin (1 / x.1) := by
  -- Project the second coordinate from the public planar computation rule.
  have hcoordinates := congrArg Prod.snd (squareInclusion_squareEmbedding x)
  simpa only [squareInclusion_apply] using hcoordinates

/-- Helper for Exercise 38.2: positive cosine parameters approach the square origin. -/
private lemma squareEmbedding_positiveCosineParameter_tendsto :
    Filter.Tendsto (fun n ↦ squareEmbedding (positiveCosineParameter n))
      Filter.atTop (nhds squareOrigin) := by
  -- The first coordinate tends to zero and the sine coordinate is constantly zero.
  have hfirst : Filter.Tendsto
      (fun n ↦ (squareEmbedding (positiveCosineParameter n)).1)
      Filter.atTop (nhds signedUnitOrigin) := by
    rw [tendsto_subtype_rng]
    refine positiveCosineParameter_tendsto_zero.congr fun n ↦ ?_
    exact (squareEmbedding_firstCoordinate (positiveCosineParameter n)).symm
  have hsecond : Filter.Tendsto
      (fun n ↦ (squareEmbedding (positiveCosineParameter n)).2)
      Filter.atTop (nhds signedUnitOrigin) := by
    rw [tendsto_subtype_rng]
    refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ))
      Filter.atTop (nhds 0)).congr fun n ↦ ?_
    rw [squareEmbedding_secondCoordinate]
    simpa only [positiveCosineParameter, one_div, inv_inv] using
      (sin_positiveCosinePhase n).symm
  simpa only [squareOrigin] using hfirst.prodMk_nhds hsecond

/-- Helper for Exercise 38.2: negative cosine parameters approach the square origin. -/
private lemma squareEmbedding_negativeCosineParameter_tendsto :
    Filter.Tendsto (fun n ↦ squareEmbedding (negativeCosineParameter n))
      Filter.atTop (nhds squareOrigin) := by
  -- The first coordinate tends to zero and the sine coordinate is constantly zero.
  have hfirst : Filter.Tendsto
      (fun n ↦ (squareEmbedding (negativeCosineParameter n)).1)
      Filter.atTop (nhds signedUnitOrigin) := by
    rw [tendsto_subtype_rng]
    refine negativeCosineParameter_tendsto_zero.congr fun n ↦ ?_
    exact (squareEmbedding_firstCoordinate (negativeCosineParameter n)).symm
  have hsecond : Filter.Tendsto
      (fun n ↦ (squareEmbedding (negativeCosineParameter n)).2)
      Filter.atTop (nhds signedUnitOrigin) := by
    rw [tendsto_subtype_rng]
    refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ))
      Filter.atTop (nhds 0)).congr fun n ↦ ?_
    rw [squareEmbedding_secondCoordinate]
    simpa only [negativeCosineParameter, one_div, inv_inv] using
      (sin_negativeCosinePhase n).symm
  simpa only [squareOrigin] using hfirst.prodMk_nhds hsecond

/-- Helper for Exercise 38.2: the square origin lies in the induced compactification. -/
private lemma squareOrigin_mem_closure_range :
    squareOrigin ∈ closure (Set.range squareEmbedding) := by
  -- The positive cosine parameters provide an explicit sequence in the range.
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n ↦ squareEmbedding (positiveCosineParameter n), ?_,
    squareEmbedding_positiveCosineParameter_tendsto⟩
  intro n
  exact Set.mem_range_self (positiveCosineParameter n)

/-- Helper for Exercise 38.2: the common boundary point represented by the square origin. -/
private def squareBoundaryOrigin : InducedCompactification squareEmbedding :=
  ⟨squareOrigin, squareOrigin_mem_closure_range⟩

/-- Helper for Exercise 38.2: the packaged compactification map is the canonical closure map. -/
private lemma compactification_apply_ofMap (x : Ioo (0 : ℝ) 1) :
    compactification x = InducedCompactification.ofMap squareEmbedding x := by
  -- Unfold only the named compactification wrapper and use its computation rule.
  exact InducedCompactification.compactification_apply
    squareEmbedding isEmbedding_squareEmbedding x

/-- Helper for Exercise 38.2: two approaches to the same square boundary point have
cosine values one and negative one. -/
private lemma cosineCollisionAtSquareBoundary :
    ∃ p : InducedCompactification squareEmbedding,
      ∃ u v : ℕ → Ioo (0 : ℝ) 1,
        Filter.Tendsto (fun n ↦ InducedCompactification.ofMap squareEmbedding (u n))
            Filter.atTop (nhds p) ∧
          Filter.Tendsto (fun n ↦ InducedCompactification.ofMap squareEmbedding (v n))
            Filter.atTop (nhds p) ∧
          (∀ n, cosOscillation (u n) = 1) ∧
          (∀ n, cosOscillation (v n) = -1) := by
  -- Use reciprocal full-turn and half-turn phases, both converging to the square origin.
  refine ⟨squareBoundaryOrigin, positiveCosineParameter, negativeCosineParameter,
    ?_, ?_, ?_, ?_⟩
  · rw [tendsto_subtype_rng]
    simpa only [InducedCompactification.ofMap, squareBoundaryOrigin] using
      squareEmbedding_positiveCosineParameter_tendsto
  · rw [tendsto_subtype_rng]
    simpa only [InducedCompactification.ofMap, squareBoundaryOrigin] using
      squareEmbedding_negativeCosineParameter_tendsto
  · intro n
    rw [cosOscillation_apply]
    simpa only [positiveCosineParameter, one_div, inv_inv] using
      cos_positiveCosinePhase n
  · intro n
    rw [cosOscillation_apply]
    simpa only [negativeCosineParameter, one_div, inv_inv] using
      cos_negativeCosinePhase n

/-- Exercise 38.2 (1): The bounded function `x ↦ cos (1 / x)` does not extend
continuously to the compactification from Example 38.3. -/
theorem cosOscillation_not_extendable :
    ¬ compactification.Extends cosOscillation := by
  -- An extension would have incompatible limits along the two collision sequences.
  intro hextends
  rw [Compactification.extends_iff] at hextends
  obtain ⟨G, hG⟩ := hextends
  obtain ⟨p, u, v, hu, hv, hcosu, hcosv⟩ := cosineCollisionAtSquareBoundary
  have hGu : Filter.Tendsto
      (fun n ↦ G (InducedCompactification.ofMap squareEmbedding (u n)))
      Filter.atTop (nhds (G p)) :=
    G.continuous.continuousAt.tendsto.comp hu
  have hGu_one : Filter.Tendsto
      (fun n ↦ G (InducedCompactification.ofMap squareEmbedding (u n)))
      Filter.atTop (nhds (1 : ℝ)) := by
    refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      Filter.atTop (nhds 1)).congr fun n ↦ ?_
    calc
      (1 : ℝ) = cosOscillation (u n) := (hcosu n).symm
      _ = G (compactification (u n)) := (hG (u n)).symm
      _ = G (InducedCompactification.ofMap squareEmbedding (u n)) :=
        congrArg G (compactification_apply_ofMap (u n))
  have hGv : Filter.Tendsto
      (fun n ↦ G (InducedCompactification.ofMap squareEmbedding (v n)))
      Filter.atTop (nhds (G p)) :=
    G.continuous.continuousAt.tendsto.comp hv
  have hGv_negOne : Filter.Tendsto
      (fun n ↦ G (InducedCompactification.ofMap squareEmbedding (v n)))
      Filter.atTop (nhds (-1 : ℝ)) := by
    refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (-1 : ℝ))
      Filter.atTop (nhds (-1))).congr fun n ↦ ?_
    calc
      (-1 : ℝ) = cosOscillation (v n) := (hcosv n).symm
      _ = G (compactification (v n)) := (hG (v n)).symm
      _ = G (InducedCompactification.ofMap squareEmbedding (v n)) :=
        congrArg G (compactification_apply_ofMap (v n))
  have hpositive : G p = 1 := tendsto_nhds_unique hGu hGu_one
  have hnegative : G p = -1 := tendsto_nhds_unique hGv hGv_negOne
  -- Uniqueness would identify the distinct real numbers `1` and `-1`.
  have hone_eq_negOne : (1 : ℝ) = -1 := hpositive.symm.trans hnegative
  norm_num at hone_eq_negOne

/-- Helper for Exercise 38.2: all three raw cube coordinates lie in `[0, 1]`. -/
lemma cubeEmbeddingCoordinates_mem (x : Ioo (0 : ℝ) 1) :
    x.1 ∈ Icc (0 : ℝ) 1 ∧
      (Real.sin (1 / x.1) + 1) / 2 ∈ Icc (0 : ℝ) 1 ∧
      (Real.cos (1 / x.1) + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
  -- Rescale the standard sine and cosine bounds from `[-1, 1]` to `[0, 1]`.
  constructor
  · exact ⟨x.2.1.le, x.2.2.le⟩
  constructor
  · constructor
    · linarith [Real.neg_one_le_sin (1 / x.1)]
    · linarith [Real.sin_le_one (1 / x.1)]
  · constructor
    · linarith [Real.neg_one_le_cos (1 / x.1)]
    · linarith [Real.cos_le_one (1 / x.1)]

/-- Exercise 38.2 (2): The embedding into `[0, 1]³`, with coordinates ordered as
`x`, `(sin (1 / x) + 1) / 2`, and `(cos (1 / x) + 1) / 2`. -/
noncomputable def cubeEmbedding : Ioo (0 : ℝ) 1 → (Fin 3 → Icc (0 : ℝ) 1) :=
  -- Assemble the three coordinates using their named interval-membership proofs.
  fun x ↦ ![⟨x.1, (cubeEmbeddingCoordinates_mem x).1⟩,
    ⟨(Real.sin (1 / x.1) + 1) / 2, (cubeEmbeddingCoordinates_mem x).2.1⟩,
    ⟨(Real.cos (1 / x.1) + 1) / 2, (cubeEmbeddingCoordinates_mem x).2.2⟩]

/-- The first cube coordinate is the original point of `(0, 1)`. -/
@[simp]
theorem cubeEmbedding_apply_zero (x : Ioo (0 : ℝ) 1) :
    (cubeEmbedding x 0).1 = x.1 := rfl

/-- The second cube coordinate is the rescaled sine oscillation. -/
@[simp]
theorem cubeEmbedding_apply_one (x : Ioo (0 : ℝ) 1) :
    (cubeEmbedding x 1).1 = (Real.sin (1 / x.1) + 1) / 2 := rfl

/-- The third cube coordinate is the rescaled cosine oscillation. -/
@[simp]
theorem cubeEmbedding_apply_two (x : Ioo (0 : ℝ) 1) :
    (cubeEmbedding x 2).1 = (Real.cos (1 / x.1) + 1) / 2 := rfl

/-- Exercise 38.2 (3): The explicit map into `[0, 1]³` is an embedding. -/
theorem isEmbedding_cubeEmbedding : Topology.IsEmbedding cubeEmbedding := by
  -- Establish continuity coordinatewise, using the same reciprocal for sine and cosine.
  have hreciprocal : Continuous (fun x : Ioo (0 : ℝ) 1 ↦ 1 / (x.1 : ℝ)) :=
    continuous_const.div continuous_subtype_val fun x ↦ ne_of_gt x.2.1
  have hsine : Continuous (fun x : Ioo (0 : ℝ) 1 ↦ Real.sin (1 / x.1)) :=
    Real.continuous_sin.comp hreciprocal
  have hcosine : Continuous (fun x : Ioo (0 : ℝ) 1 ↦ Real.cos (1 / x.1)) :=
    Real.continuous_cos.comp hreciprocal
  have hcontinuous : Continuous cubeEmbedding := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Continuous.subtype_mk continuous_subtype_val
        fun x ↦ (cubeEmbeddingCoordinates_mem x).1
    · exact Continuous.subtype_mk ((hsine.add continuous_const).div_const 2)
        fun x ↦ (cubeEmbeddingCoordinates_mem x).2.1
    · exact Continuous.subtype_mk ((hcosine.add continuous_const).div_const 2)
        fun x ↦ (cubeEmbeddingCoordinates_mem x).2.2
  have hprojection : Continuous
      (fun y : Fin 3 → Icc (0 : ℝ) 1 ↦ (y 0).1) :=
    continuous_subtype_val.comp (continuous_apply 0)
  have hcomp :
      (fun y : Fin 3 → Icc (0 : ℝ) 1 ↦ (y 0).1) ∘ cubeEmbedding =
        fun x : Ioo (0 : ℝ) 1 ↦ x.1 := by
    funext x
    exact cubeEmbedding_apply_zero x
  -- Projection to coordinate zero recovers the standard subtype embedding.
  refine Topology.IsEmbedding.of_comp hcontinuous hprojection ?_
  rw [hcomp]
  exact Topology.IsEmbedding.subtypeVal

/-- The compactification of `(0, 1)` induced by the cube embedding. -/
noncomputable def cubeCompactification : Compactification (Ioo (0 : ℝ) 1) :=
  InducedCompactification.compactification cubeEmbedding isEmbedding_cubeEmbedding

/-- The cube compactification stores the canonical map into the closure of the range. -/
@[simp]
theorem cubeCompactification_apply (x : Ioo (0 : ℝ) 1) :
    cubeCompactification x = InducedCompactification.ofMap cubeEmbedding x :=
  InducedCompactification.compactification_apply cubeEmbedding isEmbedding_cubeEmbedding x

/-- Helper for Exercise 38.2: every ambient cube coordinate restricts continuously to the
induced compactification. -/
lemma continuous_coordinateExtensionFormula (i : Fin 3) :
    Continuous (fun y : InducedCompactification cubeEmbedding ↦
      ((InducedCompactification.inclusion cubeEmbedding y) i).1) := by
  -- Compose the ambient inclusion, coordinate evaluation, and subtype projection.
  exact continuous_subtype_val.comp
    ((continuous_apply i).comp
      (InducedCompactification.isEmbedding_inclusion cubeEmbedding).continuous)

/-- An ambient cube coordinate restricted to the induced compactification. -/
noncomputable def coordinateExtension (i : Fin 3) :
    ContinuousMap (InducedCompactification cubeEmbedding) ℝ where
  -- Package the ambient coordinate with the named continuity lemma.
  toFun := fun y ↦ ((InducedCompactification.inclusion cubeEmbedding y) i).1
  continuous_toFun := continuous_coordinateExtensionFormula i

/-- A restricted ambient cube coordinate is evaluated by the ambient inclusion. -/
@[simp]
theorem coordinateExtension_apply (i : Fin 3) (y : InducedCompactification cubeEmbedding) :
    coordinateExtension i y = ((InducedCompactification.inclusion cubeEmbedding y) i).1 := rfl

/-- The continuous extension of the coordinate function `x ↦ x`. -/
noncomputable def firstExtension :
    ContinuousMap (InducedCompactification cubeEmbedding) ℝ :=
  coordinateExtension 0

/-- The continuous extension of the sine oscillation. -/
noncomputable def sineExtension :
    ContinuousMap (InducedCompactification cubeEmbedding) ℝ :=
  2 * coordinateExtension 1 - 1

/-- The continuous extension of the cosine oscillation. -/
noncomputable def cosineExtension :
    ContinuousMap (InducedCompactification cubeEmbedding) ℝ :=
  2 * coordinateExtension 2 - 1

/-- Exercise 38.2 (4): The first-coordinate extension agrees with `x ↦ x`. -/
theorem firstExtension_ofMap (x : Ioo (0 : ℝ) 1) :
    firstExtension (InducedCompactification.ofMap cubeEmbedding x) = x.1 := by
  -- Evaluate the restricted ambient coordinate on the original embedded point.
  simp only [firstExtension, coordinateExtension_apply,
    InducedCompactification.inclusion_ofMap, cubeEmbedding_apply_zero]

/-- Exercise 38.2 (5): The recovered sine coordinate extends `x ↦ sin (1 / x)`. -/
theorem sineExtension_ofMap (x : Ioo (0 : ℝ) 1) :
    sineExtension (InducedCompactification.ofMap cubeEmbedding x) =
      Real.sin (1 / x.1) := by
  -- Evaluate coordinate one and undo its affine rescaling.
  have htwo :
      (2 : ContinuousMap (InducedCompactification cubeEmbedding) ℝ)
          (InducedCompactification.ofMap cubeEmbedding x) = (2 : ℝ) :=
    ContinuousMap.natCast_apply 2 _
  have hone :
      (1 : ContinuousMap (InducedCompactification cubeEmbedding) ℝ)
          (InducedCompactification.ofMap cubeEmbedding x) = (1 : ℝ) :=
    ContinuousMap.one_apply _
  simp only [sineExtension, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    htwo, hone, coordinateExtension_apply,
    InducedCompactification.inclusion_ofMap,
    cubeEmbedding_apply_one]
  ring

/-- Exercise 38.2 (6): The recovered cosine coordinate extends `x ↦ cos (1 / x)`. -/
theorem cosineExtension_ofMap (x : Ioo (0 : ℝ) 1) :
    cosineExtension (InducedCompactification.ofMap cubeEmbedding x) =
      Real.cos (1 / x.1) := by
  -- Evaluate coordinate two and undo its affine rescaling.
  have htwo :
      (2 : ContinuousMap (InducedCompactification cubeEmbedding) ℝ)
          (InducedCompactification.ofMap cubeEmbedding x) = (2 : ℝ) :=
    ContinuousMap.natCast_apply 2 _
  have hone :
      (1 : ContinuousMap (InducedCompactification cubeEmbedding) ℝ)
          (InducedCompactification.ofMap cubeEmbedding x) = (1 : ℝ) :=
    ContinuousMap.one_apply _
  simp only [cosineExtension, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    htwo, hone, coordinateExtension_apply,
    InducedCompactification.inclusion_ofMap,
    cubeEmbedding_apply_two]
  ring


end TopologistsSineCurve

end
