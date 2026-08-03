module

public import Topology_Munkres_2000.Book.Example_51_2.Paths
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

noncomputable section

namespace PuncturedPlane

/- Example 51.2 (1): The upper semicircle and upper semiellipse admit an affine path
homotopy in the punctured plane. -/
#check upperHomotopy

/-- The straight-line obstruction in Example 51.2: the affine interpolation from the
upper to the lower semicircle passes through the origin. -/
theorem affineUpperLowerHitsOrigin :
    (0 : ℝ × ℝ) ∈ Set.range
      (Path.Homotopy.affine upperSemicircleAmbient lowerSemicircleAmbient) := by
  -- Evaluate the straight-line homotopy halfway along both its parameters.
  have midpoint_mem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
    norm_num
  have pi_mul_half : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by
    ring
  let midpoint : unitInterval := ⟨1 / 2, midpoint_mem⟩
  refine ⟨(midpoint, midpoint), ?_⟩
  -- At this point the two semicircles have opposite vertical coordinates.
  rw [Path.Homotopy.affine_apply]
  have upperAmbient_apply : upperSemicircleAmbient midpoint =
      (upperSemicircle midpoint).1 := by
    exact congrFun (Path.map_coe upperSemicircle inclusion.continuous) midpoint
  have lowerAmbient_apply : lowerSemicircleAmbient midpoint =
      (lowerSemicircle midpoint).1 := by
    exact congrFun (Path.map_coe lowerSemicircle inclusion.continuous) midpoint
  rw [upperAmbient_apply, lowerAmbient_apply, upperSemicircle_apply,
    lowerSemicircle_apply]
  simp only [upperSemicirclePoint, lowerSemicirclePoint, midpoint,
    AffineMap.lineMap_apply_module]
  norm_num [pi_mul_half, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Helper for Example 51.2: the exponential has nonzero image after identifying
`ℂ` with `ℝ × ℝ`. -/
lemma complexExpPair_ne_zero (z : ℂ) :
    Complex.equivRealProdCLM (Complex.exp z) ≠ 0 := by
  -- Injectivity of the real-coordinate equivalence reduces this to `exp_ne_zero`.
  rw [← map_zero Complex.equivRealProdCLM]
  exact fun h ↦ Complex.exp_ne_zero z (Complex.equivRealProdCLM.injective h)

/-- Helper for Example 51.2: the complex-to-real-pair equivalence preserves
nonzeroness. -/
lemma equivRealProdCLM_ne_zero_iff (z : ℂ) :
    z ≠ 0 ↔ Complex.equivRealProdCLM z ≠ 0 := by
  -- An equivalence maps an element to zero exactly when that element is zero.
  constructor
  · intro hz hmap
    apply hz
    exact Complex.equivRealProdCLM.injective
      (hmap.trans (map_zero Complex.equivRealProdCLM).symm)
  · intro hmap hz
    apply hmap
    rw [hz, map_zero]

/-- Helper for Example 51.2: the complex exponential regarded as a map to the
punctured real plane. -/
def puncturedPlaneExp : ℂ → PuncturedPlane := fun z ↦
  ⟨Complex.equivRealProdCLM (Complex.exp z), complexExpPair_ne_zero z⟩

/-- Helper for Example 51.2: the coordinate equivalence restricts to the two
punctured planes. -/
def complexNonzeroHomeomorph : {z : ℂ // z ≠ 0} ≃ₜ PuncturedPlane :=
  Complex.equivRealProdCLM.toHomeomorph.subtype equivRealProdCLM_ne_zero_iff

/-- Helper for Example 51.2: the restricted coordinate homeomorphism has the
expected underlying real pair. -/
lemma complexNonzeroHomeomorph_coe (z : {z : ℂ // z ≠ 0}) :
    (complexNonzeroHomeomorph z).1 = Complex.equivRealProdCLM z.1 := by
  -- The restriction changes only the proof that the image is nonzero.
  rfl

/-- Helper for Example 51.2: `puncturedPlaneExp` is a covering map. -/
lemma isCoveringMap_puncturedPlaneExp : IsCoveringMap puncturedPlaneExp := by
  -- Transport the standard exponential covering across the coordinate homeomorphism.
  have transported :=
    Complex.isCoveringMap_exp.homeomorph_comp complexNonzeroHomeomorph
  have map_eq : complexNonzeroHomeomorph ∘
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) =
      puncturedPlaneExp := by
    funext z
    apply Subtype.ext
    exact complexNonzeroHomeomorph_coe
      (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})
  rwa [map_eq] at transported

/-- Helper for Example 51.2: on the imaginary axis, `puncturedPlaneExp` has the
usual sine-and-cosine coordinates. -/
lemma puncturedPlaneExp_mul_I (θ : ℝ) :
    (puncturedPlaneExp ((θ : ℂ) * Complex.I)).1 = (Real.cos θ, Real.sin θ) := by
  -- Compute the exponential and then read off its real and imaginary parts.
  simp only [puncturedPlaneExp, Complex.exp_mul_I, Complex.equivRealProdCLM_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  norm_num

/-- Example 51.2 (3): The upper and lower semicircles are not path homotopic in the
punctured plane. -/
theorem upperLowerNotHomotopic :
    ¬ upperSemicircle.Homotopic lowerSemicircle := by
  -- The upper and lower paths lift to the positive and negative imaginary axes.
  intro h
  have upperArgument_continuous : Continuous fun s : unitInterval ↦
      (↑(Real.pi * (s : ℝ)) : ℂ) * Complex.I := by
    fun_prop
  have lowerArgument_continuous : Continuous fun s : unitInterval ↦
      (↑(-(Real.pi * (s : ℝ))) : ℂ) * Complex.I := by
    fun_prop
  let upperArgument : C(unitInterval, ℂ) :=
    ⟨fun s ↦ (↑(Real.pi * (s : ℝ)) : ℂ) * Complex.I, upperArgument_continuous⟩
  let lowerArgument : C(unitInterval, ℂ) :=
    ⟨fun s ↦ (↑(-(Real.pi * (s : ℝ))) : ℂ) * Complex.I, lowerArgument_continuous⟩
  let projection : C(ℂ, PuncturedPlane) :=
    ⟨puncturedPlaneExp, isCoveringMap_puncturedPlaneExp.continuous⟩
  have upper_comp : ContinuousMap.comp projection upperArgument =
      upperSemicircle.toContinuousMap := by
    -- The exponential coordinate formula identifies the positive lift with the upper path.
    apply ContinuousMap.coe_injective
    funext s
    apply Subtype.ext
    simpa only [ContinuousMap.comp_apply, projection, upperArgument,
      ContinuousMap.coe_mk, Path.coe_toContinuousMap, upperSemicircle_apply,
      upperSemicirclePoint] using
      puncturedPlaneExp_mul_I (Real.pi * (s : ℝ))
  have lower_comp : ContinuousMap.comp projection lowerArgument =
      lowerSemicircle.toContinuousMap := by
    -- Negating the argument changes only the sine coordinate.
    apply ContinuousMap.coe_injective
    funext s
    apply Subtype.ext
    simpa only [ContinuousMap.comp_apply, projection, lowerArgument,
      ContinuousMap.coe_mk, Path.coe_toContinuousMap, lowerSemicircle_apply,
      lowerSemicirclePoint, Real.cos_neg, Real.sin_neg] using
      puncturedPlaneExp_mul_I (-(Real.pi * (s : ℝ)))
  have zero_mem : (0 : unitInterval) ∈ ({0, 1} : Set unitInterval) := Or.inl rfl
  have arguments_zero : upperArgument 0 = lowerArgument 0 := by
    -- Both explicit lifts start at the zero argument.
    norm_num [upperArgument, lowerArgument]
  have common_start : ∃ s ∈ ({0, 1} : Set unitInterval),
      upperArgument s = lowerArgument s :=
    ⟨0, zero_mem, arguments_zero⟩
  have base_homotopy :
      (ContinuousMap.comp projection upperArgument).HomotopicRel
        (ContinuousMap.comp projection lowerArgument) ({0, 1} : Set unitInterval) := by
    -- Rewrite the assumed path homotopy as a homotopy of the projected lifts.
    rw [upper_comp, lower_comp]
    exact h
  have lifted_homotopy : upperArgument.HomotopicRel lowerArgument
      ({0, 1} : Set unitInterval) := by
    -- Uniqueness of covering lifts transports the relative homotopy upstairs.
    exact (isCoveringMap_puncturedPlaneExp.homotopicRel_iff_comp common_start).mpr
      base_homotopy
  have one_mem : (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) := Or.inr rfl
  have arguments_one : upperArgument 1 = lowerArgument 1 :=
    lifted_homotopy.fst_eq_snd one_mem
  have imaginary_parts := congrArg Complex.im arguments_one
  -- The alleged equality says `π = -π`, contradicting positivity of `π`.
  norm_num [upperArgument, lowerArgument, Complex.mul_im] at imaginary_parts
  linarith [Real.pi_pos]

/- Example 51.2 (4): The upper and lower semicircles admit an affine path homotopy in
the full plane. -/
#check Path.Homotopy.affine upperSemicircleAmbient lowerSemicircleAmbient

end PuncturedPlane
