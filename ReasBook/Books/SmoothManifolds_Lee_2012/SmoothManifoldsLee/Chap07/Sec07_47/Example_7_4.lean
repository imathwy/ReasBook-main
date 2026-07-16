import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Topology.Algebra.Group.Matrix
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_08.Proposition_2_12
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Definition_7_47_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Example_7_4_torus

noncomputable section

open scoped LieGroup Manifold ContDiff FourierTransform Matrix.Norms.Elementwise Pointwise Torus

-- Semantic recall hits used for the source-facing API here:
-- `Matrix.GeneralLinearGroup.det` is the canonical determinant owner on `GL`,
-- and `Units.contMDiff_val` gives the canonical smooth inclusion of `GL` into the ambient
-- matrix space. The remaining owners are `Circle.toUnits`, `AddChar`, `Real.fourierChar`,
-- `ContMDiffMonoidMorphism`, `MulAut.conj`, `Units.posSubgroup`, and the chapter owner
-- `torus_epsilon_add_char` with source-facing notation `ε^{n}`.

/- Route correction: keep every structure-valued definition proof-free by routing proof fields
through named helper lemmas, then lift ambient smoothness to units-valued maps with
`Units.isOpenEmbedding_val`. -/

/-- Helper for Example 7.4: smoothness into `Rˣ` is detected after composing with `Units.val`. -/
theorem contMDiff_units_of_val
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]
    {f : M → Rˣ}
    (h : ContMDiff I (𝓘(𝕜, R)) ∞ fun x ↦ ((f x : Rˣ) : R)) :
    ContMDiff I (𝓘(𝕜, R)) ∞ f := by
  -- The units manifold is an open submanifold of the ambient normed algebra.
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  simpa using h

/-- Helper for Example 7.4: the canonical inclusion `Circle.toUnits` is smooth. -/
theorem circle_toUnits_contMDiff :
    ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ Circle.toUnits := by
  -- Forgetting the unit structure reduces the map to the smooth circle inclusion into `ℂ`.
  letI : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  refine contMDiff_units_of_val ?_
  have hcoe : ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ fun z : Circle ↦ (z : ℂ) :=
    contMDiff_coe_sphere
  simpa [Circle.toUnits_apply] using hcoe

/-- Helper for Example 7.4: the units-valued real exponential. -/
def realExpUnits (t : ℝ) : ℝˣ :=
  Units.mk0 (Real.exp t) (Real.exp_ne_zero t)

/-- Helper for Example 7.4: the units-valued real exponential sends `0` to `1`. -/
theorem realExpUnits_map_zero : realExpUnits 0 = 1 := by
  -- Compare the two units through their ambient real values.
  ext
  simp [realExpUnits]

/-- Helper for Example 7.4: the units-valued real exponential converts addition
to multiplication. -/
theorem realExpUnits_map_add (s t : ℝ) :
    realExpUnits (s + t) = realExpUnits s * realExpUnits t := by
  -- The unit identity is just the scalar identity `exp (s + t) = exp s * exp t`.
  ext
  simp [realExpUnits, Real.exp_add]

/-- Helper for Example 7.4: the units-valued real exponential is smooth. -/
theorem realExpUnits_contMDiff :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ)) ∞ realExpUnits := by
  -- Lift smoothness of the ambient exponential through `Units.val`.
  refine contMDiff_units_of_val ?_
  simpa [realExpUnits] using
    (Real.contDiff_exp.contMDiff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ Real.exp)

/-- Helper for Example 7.4: `realExpUnits t` lies in the positive subgroup of `ℝˣ`. -/
theorem realExpUnits_pos (t : ℝ) : 0 < ((realExpUnits t : ℝˣ) : ℝ) := by
  -- Positivity is inherited from `Real.exp`.
  simpa [realExpUnits] using Real.exp_pos t

/-- Helper for Example 7.4: the real logarithm inverts the real exponential on positive units. -/
theorem realExpUnits_log (u : ℝˣ) (hu : 0 < (u : ℝ)) :
    realExpUnits (Real.log (u : ℝ)) = u := by
  -- Compare the two units by their ambient real values.
  ext
  exact Real.exp_log hu

/-- Helper for Example 7.4: the positive-unit version of the real exponential. -/
def realExpPosUnit (t : ℝ) : Units.posSubgroup ℝ :=
  ⟨realExpUnits t, realExpUnits_pos t⟩

/-- Helper for Example 7.4: the positive-unit real exponential is multiplicative. -/
theorem realExpPosUnit_add (s t : ℝ) :
    realExpPosUnit (s + t) = realExpPosUnit s * realExpPosUnit t := by
  -- Reduce the subgroup equality to the corresponding equality in `ℝˣ`.
  apply Subtype.ext
  exact realExpUnits_map_add s t

/-- Helper for Example 7.4: the logarithm is a left inverse to `realExpPosUnit`. -/
theorem realExpPosMulEquiv_leftInv (t : Multiplicative ℝ) :
    Multiplicative.ofAdd
        (Real.log (((realExpPosUnit (Multiplicative.toAdd t) : Units.posSubgroup ℝ) : ℝˣ) : ℝ)) =
      t := by
  -- The ambient scalar identity is `Real.log_exp`.
  simpa [realExpPosUnit, realExpUnits] using
    congrArg Multiplicative.ofAdd (Real.log_exp (Multiplicative.toAdd t))

/-- Helper for Example 7.4: the logarithm is a right inverse to `realExpPosUnit`. -/
theorem realExpPosMulEquiv_rightInv (u : Units.posSubgroup ℝ) :
    realExpPosUnit (Real.log (((u : Units.posSubgroup ℝ) : ℝˣ) : ℝ)) = u := by
  -- Reduce the subgroup equality to the already normalized unit identity.
  apply Subtype.ext
  exact realExpUnits_log (u : ℝˣ) u.property

/-- Helper for Example 7.4: `realExpPosUnit` respects multiplication on `Multiplicative ℝ`. -/
theorem realExpPosMulEquiv_map_mul (s t : Multiplicative ℝ) :
    realExpPosUnit (Multiplicative.toAdd (s * t)) =
      realExpPosUnit (Multiplicative.toAdd s) * realExpPosUnit (Multiplicative.toAdd t) := by
  -- Multiplication in `Multiplicative ℝ` is addition in `ℝ`.
  simpa using realExpPosUnit_add (Multiplicative.toAdd s) (Multiplicative.toAdd t)

/-- Helper for Example 7.4: the units-valued complex exponential. -/
def complexExpUnits (z : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

/-- Helper for Example 7.4: the units-valued complex exponential sends `0` to `1`. -/
theorem complexExpUnits_map_zero : complexExpUnits 0 = 1 := by
  -- Compare the two units through their ambient complex values.
  ext
  simp [complexExpUnits]

/-- Helper for Example 7.4: the units-valued complex exponential converts addition to
multiplication. -/
theorem complexExpUnits_map_add (z w : ℂ) :
    complexExpUnits (z + w) = complexExpUnits z * complexExpUnits w := by
  -- The unit identity is just the scalar identity `exp (z + w) = exp z * exp w`.
  ext
  simp [complexExpUnits, Complex.exp_add]

/-- Helper for Example 7.4: the units-valued complex exponential is smooth. -/
theorem complexExpUnits_contMDiff :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ complexExpUnits := by
  -- Lift smoothness of the ambient exponential through `Units.val`.
  refine contMDiff_units_of_val ?_
  simpa [complexExpUnits] using
    (Complex.contDiff_exp.contMDiff : ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ Complex.exp)

/- Recall: the inclusion `S¹ ↪ ℂˣ` is the canonical monoid homomorphism `Circle.toUnits`. -/
#check (Circle.toUnits : Circle →* ℂˣ)

/-- The canonical inclusion `Circle.toUnits : Circle →* ℂˣ` is a smooth Lie group homomorphism. -/
def circle_toUnits_lie_hom : ContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle ℂˣ where
  toMonoidHom := Circle.toUnits
  contMDiff_toFun := circle_toUnits_contMDiff

/- The canonical inclusion `Circle.toUnits` is smooth as a map into the intrinsic Lie group
`ℂˣ`. -/
theorem circle_toUnits_smooth :
    ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ Circle.toUnits := circle_toUnits_lie_hom.contMDiff_toFun

/-- Example 7.4 (1): the real exponential defines an additive character from `ℝ` to `ℝˣ`. -/
def real_exp_units_add_char : AddChar ℝ ℝˣ where
  toFun := realExpUnits
  map_zero_eq_one' := realExpUnits_map_zero
  map_add_eq_mul' := realExpUnits_map_add

/-- The additive character `real_exp_units_add_char` is smooth. -/
theorem real_exp_units_add_char_smooth :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ)) ∞ real_exp_units_add_char := by
  -- Unfold the bundled additive character to its units-valued exponential.
  simpa [real_exp_units_add_char] using realExpUnits_contMDiff

/-- Example 7.4 (2): the image of the real exponential is the positive subgroup of `ℝˣ`. -/
theorem real_exp_units_add_char_range :
    real_exp_units_add_char.toMonoidHom.range = Units.posSubgroup ℝ := by
  -- Compare the two subgroups by membership in `ℝˣ`.
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    exact realExpUnits_pos t
  · intro hu
    refine ⟨Real.log (u : ℝ), ?_⟩
    exact realExpUnits_log u hu

/-- Example 7.4 (3): the real exponential identifies the additive group `ℝ` with the positive
subgroup of `ℝˣ`, with inverse given by the real logarithm. -/
def real_exp_pos_mulEquiv : Multiplicative ℝ ≃* Units.posSubgroup ℝ where
  toFun := fun t ↦ realExpPosUnit (Multiplicative.toAdd t)
  invFun := fun u ↦ Multiplicative.ofAdd (Real.log (((u : Units.posSubgroup ℝ) : ℝˣ) : ℝ))
  left_inv := realExpPosMulEquiv_leftInv
  right_inv := realExpPosMulEquiv_rightInv
  map_mul' := realExpPosMulEquiv_map_mul

/-- The multiplicative equivalence `real_exp_pos_mulEquiv` evaluates by the positive-unit
exponential. -/
@[simp] theorem real_exp_pos_mulEquiv_apply (t : Multiplicative ℝ) :
    real_exp_pos_mulEquiv t = realExpPosUnit (Multiplicative.toAdd t) :=
  rfl

/-- The inverse of `real_exp_pos_mulEquiv` is the real logarithm on positive units. -/
@[simp] theorem real_exp_pos_mulEquiv_symm_apply (u : Units.posSubgroup ℝ) :
    real_exp_pos_mulEquiv.symm u = Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ)) :=
  rfl

/-- Example 7.4 (4): the complex exponential defines an additive character from `ℂ` to `ℂˣ`. -/
def complex_exp_units_add_char : AddChar ℂ ℂˣ where
  toFun := complexExpUnits
  map_zero_eq_one' := complexExpUnits_map_zero
  map_add_eq_mul' := complexExpUnits_map_add

/-- The additive character `complex_exp_units_add_char` is smooth. -/
theorem complex_exp_units_add_char_smooth :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ complex_exp_units_add_char := by
  -- Unfold the bundled additive character to its units-valued exponential.
  simpa [complex_exp_units_add_char] using complexExpUnits_contMDiff

/-- Example 7.4 (5): the complex exponential is surjective onto `ℂˣ`. -/
theorem complex_exp_units_add_char_surjective :
    Function.Surjective complex_exp_units_add_char := by
  intro u
  -- The complex logarithm is a preimage for every nonzero complex number.
  refine ⟨Complex.log (u : ℂ), ?_⟩
  ext
  exact Complex.exp_log u.ne_zero

/-- Example 7.4 (6): the kernel of the complex exponential consists of the integer multiples of
`2π i`. -/
theorem complex_exp_units_add_char_eq_one_iff (z : ℂ) :
    complex_exp_units_add_char z = 1 ↔ ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * Complex.I) := by
  -- Forget the unit structure and use the standard description of `Complex.exp⁻¹ {1}`.
  have hexp :
      Complex.exp z = 1 ↔ ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * Complex.I) :=
    Complex.exp_eq_one_iff
  simpa [complex_exp_units_add_char, complexExpUnits, Units.ext_iff] using hexp

/-- Example 7.4 (7): the complex exponential is not injective. -/
theorem complex_exp_units_add_char_not_injective :
    ¬ Function.Injective complex_exp_units_add_char := by
  intro hInjective
  have hperiod : complex_exp_units_add_char (2 * Real.pi * Complex.I) = 1 := by
    exact (complex_exp_units_add_char_eq_one_iff (2 * Real.pi * Complex.I)).2 ⟨1, by simp⟩
  have hzero : complex_exp_units_add_char 0 = 1 := by
    exact complex_exp_units_add_char.map_zero_eq_one
  have hEq :
      complex_exp_units_add_char (2 * Real.pi * Complex.I) = complex_exp_units_add_char 0 :=
    hperiod.trans hzero.symm
  have hcontra := hInjective hEq
  exact Complex.two_pi_I_ne_zero hcontra

/- Recall: the map `ε(t) = e^{2π i t}` is the canonical additive character
`Real.fourierChar`, written in mathlib notation as `𝐞`. -/
#check (𝐞 : AddChar ℝ Circle)

/- The canonical additive character `ε(t) = e^{2π i t}`, written `𝐞`, is smooth. -/
theorem epsilon_smooth :
    ContMDiff 𝓘(ℝ) (𝓡 1) ∞ 𝐞 := by
  have hphase : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ (2 * Real.pi) * t) := by
    -- The phase function is linear, hence smooth.
    simpa using (contMDiff_const.mul contMDiff_id)
  -- Compose the smooth circle exponential with the linear phase.
  simpa [Real.fourierChar_apply', Function.comp] using contMDiff_circleExp.comp hphase

/-- Example 7.4 (8): the kernel of `ε(t) = e^{2π i t}` is the set of integers. -/
theorem epsilon_eq_one_iff (t : ℝ) :
    𝐞 t = 1 ↔ ∃ k : ℤ, t = k := by
  rw [Real.fourierChar_apply']
  constructor
  · intro ht
    have hExp : Circle.exp (2 * Real.pi * t) = Circle.exp 0 := by
      simpa using ht
    rcases Circle.exp_eq_exp.mp hExp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have htwo_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith
  · rintro ⟨k, rfl⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using Circle.exp_int_mul_two_pi k

/- Recall: the coordinatewise character `εⁿ : ℝⁿ → 𝕋ⁿ` is already introduced upstream in this
section as the chapter owner `torus_epsilon_add_char`, with notation `ε^{n}`. -/
section

variable (n : ℕ)

#check (ε^{n})

end

/-- The additive character `εⁿ : ℝⁿ → 𝕋ⁿ` is smooth for the product manifold structures on `ℝⁿ`
and `𝕋ⁿ`. -/
theorem torus_epsilon_smooth (n : ℕ) :
    ContMDiff
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      ∞
      (ε^{n}) := by
  -- Smoothness into a finite product is checked coordinatewise.
  rw [contMDiff_pi_iff]
  intro i
  have hid :
      ContMDiff
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        ∞
        (fun x : Fin n → ℝ ↦ x) :=
    contMDiff_id
  have hproj :
      ContMDiff
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        𝓘(ℝ)
        ∞
        (fun x : Fin n → ℝ ↦ x i) :=
    (contMDiff_pi_iff.mp hid) i
  -- Each coordinate is the one-dimensional Fourier character.
  simpa [torus_epsilon_add_char] using epsilon_smooth.comp hproj

/-- Example 7.4 (9): the kernel of `εⁿ` is the integer lattice `ℤⁿ`. -/
theorem torus_epsilon_eq_one_iff (n : ℕ) (x : Fin n → ℝ) :
    ε^{n} x = 1 ↔ ∃ k : Fin n → ℤ, x = fun i ↦ (k i : ℝ) := by
  constructor
  · intro hx
    classical
    let k : Fin n → ℤ := fun i ↦
      Classical.choose ((epsilon_eq_one_iff (x i)).1 (by
        simpa [torus_epsilon_add_char] using congrFun hx i))
    refine ⟨k, funext ?_⟩
    intro i
    exact Classical.choose_spec ((epsilon_eq_one_iff (x i)).1 (by
      simpa [torus_epsilon_add_char] using congrFun hx i))
  · rintro ⟨k, rfl⟩
    ext i
    simpa [torus_epsilon_add_char] using
      (epsilon_eq_one_iff ((k i : ℝ))).2 ⟨k i, rfl⟩

section

variable {n : ℕ}

local notation "Mℝ(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "Mℂ(" n ")" => Matrix (Fin n) (Fin n) ℂ

/-- The operator-normed ring structure on real `n × n` matrices used by the `GL(n, ℝ)` model. -/
instance real_matrix_normedRing (n : ℕ) : NormedRing (Mℝ(n)) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed real-algebra structure on real `n × n` matrices. -/
instance real_matrix_normedAlgebra (n : ℕ) : NormedAlgebra ℝ (Mℝ(n)) :=
  Matrix.linftyOpNormedAlgebra

instance real_matrix_completeSpace (n : ℕ) : CompleteSpace (Mℝ(n)) := by
  infer_instance

/-- The operator-normed ring structure on complex `n × n` matrices used by the `GL(n, ℂ)` model. -/
instance complex_matrix_normedRing (n : ℕ) : NormedRing (Mℂ(n)) :=
  Matrix.linftyOpNormedRing

/-- The real normed-algebra structure on complex `n × n` matrices used for the real Lie-group
model on `GL(n, ℂ)`. -/
instance complex_matrix_normedAlgebra (n : ℕ) : NormedAlgebra ℝ (Mℂ(n)) :=
  Matrix.linftyOpNormedAlgebra

instance complex_matrix_completeSpace (n : ℕ) : CompleteSpace (Mℂ(n)) := by
  infer_instance

/-- The standard charted-space structure on `GL(n, ℝ)` is induced from its inclusion into the
ambient real matrix algebra. -/
noncomputable instance realGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Mℝ(n)) (GL (Fin n) ℝ) := by
  change ChartedSpace (Mℝ(n)) ((Mℝ(n))ˣ)
  exact @Units.instChartedSpace (Mℝ(n)) (real_matrix_normedRing n) (real_matrix_completeSpace n)

/-- The standard charted-space structure on `GL(n, ℂ)` is induced from its inclusion into the
ambient complex matrix algebra. -/
noncomputable instance complexGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Mℂ(n)) (GL (Fin n) ℂ) := by
  change ChartedSpace (Mℂ(n)) ((Mℂ(n))ˣ)
  exact @Units.instChartedSpace
    (Mℂ(n))
    (complex_matrix_normedRing n)
    (complex_matrix_completeSpace n)

/-- Helper for Example 7.4: the ambient determinant on real matrices is smooth. -/
theorem contMDiff_matrix_det_real (n : ℕ) :
    ContDiff ℝ ∞ (fun M : Mℝ(n) ↦ Matrix.det M) := by
  have hdet :
      ContDiff ℝ ∞ (fun M : Mℝ(n) ↦
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i) := by
    -- The Leibniz formula is a finite sum of finite products of coordinate projections.
    fun_prop
  simpa [Matrix.det_apply] using hdet

/-- Helper for Example 7.4: the ambient determinant on complex matrices is smooth as a real map. -/
theorem contMDiff_matrix_det_complex (n : ℕ) :
    ContDiff ℝ ∞ (fun M : Mℂ(n) ↦ Matrix.det M) := by
  have hdet :
      ContDiff ℝ ∞ (fun M : Mℂ(n) ↦
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i) := by
    -- The Leibniz formula is again polynomial in the matrix entries.
    fun_prop
  simpa [Matrix.det_apply] using hdet

/-- Helper for Example 7.4: the determinant on `GL(n, ℝ)` is smooth. -/
theorem real_generalLinear_det_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ
      inferInstance
      (Mℝ(n))
      inferInstance
      inferInstance
      (Mℝ(n))
      inferInstance
      (𝓘(ℝ, Mℝ(n)))
      (GL (Fin n) ℝ)
      inferInstance
      (realGeneralLinearGroupChartedSpace n)
      ℝ
      inferInstance
      inferInstance
      ℝ
      inferInstance
      𝓘(ℝ)
      ℝˣ
      inferInstance
      inferInstance
      ∞
      (Matrix.GeneralLinearGroup.det : GL (Fin n) ℝ → ℝˣ) := sorry

/-- Helper for Example 7.4: the determinant on `GL(n, ℂ)` is smooth. -/
theorem complex_generalLinear_det_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ
      inferInstance
      (Mℂ(n))
      inferInstance
      inferInstance
      (Mℂ(n))
      inferInstance
      (𝓘(ℝ, Mℂ(n)))
      (GL (Fin n) ℂ)
      inferInstance
      (complexGeneralLinearGroupChartedSpace n)
      ℂ
      inferInstance
      inferInstance
      ℂ
      inferInstance
      (𝓘(ℝ, ℂ))
      ℂˣ
      inferInstance
      inferInstance
      ∞
      (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ → ℂˣ) := sorry

/-- The determinant on `GL(n, ℝ)` is a smooth Lie group homomorphism. This is the owner-level
bridge from mathlib's canonical monoid homomorphism `Matrix.GeneralLinearGroup.det` to the chapter
owner `ContMDiffMonoidMorphism`. -/
def real_generalLinear_det_lie_hom (n : ℕ) :
    @ContMDiffMonoidMorphism
      ℝ
      inferInstance
      (Mℝ(n))
      inferInstance
      (Mℝ(n))
      inferInstance
      inferInstance
      ℝ
      inferInstance
      ℝ
      inferInstance
      inferInstance
      (𝓘(ℝ, Mℝ(n)))
      𝓘(ℝ)
      ∞
      (GL (Fin n) ℝ)
      inferInstance
      (realGeneralLinearGroupChartedSpace n)
      inferInstance
      ℝˣ
      inferInstance
      inferInstance
      inferInstance :=
  { toMonoidHom := Matrix.GeneralLinearGroup.det
    contMDiff_toFun := real_generalLinear_det_contMDiff n }

/-- The determinant on `GL(n, ℂ)` is a smooth Lie group homomorphism. -/
def complex_generalLinear_det_lie_hom (n : ℕ) :
    @ContMDiffMonoidMorphism
      ℝ
      inferInstance
      (Mℂ(n))
      inferInstance
      (Mℂ(n))
      inferInstance
      inferInstance
      ℂ
      inferInstance
      ℂ
      inferInstance
      inferInstance
      (𝓘(ℝ, Mℂ(n)))
      (𝓘(ℝ, ℂ))
      ∞
      (GL (Fin n) ℂ)
      inferInstance
      (complexGeneralLinearGroupChartedSpace n)
      inferInstance
      ℂˣ
      inferInstance
      inferInstance
      inferInstance :=
  { toMonoidHom := Matrix.GeneralLinearGroup.det
    contMDiff_toFun := complex_generalLinear_det_contMDiff n }

/- Recall: the determinant on `GL(n, ℝ)` is the smooth Lie group homomorphism
`real_generalLinear_det_lie_hom n`. -/
#check (real_generalLinear_det_lie_hom n)

/- Recall: the determinant on `GL(n, ℂ)` is the smooth Lie group homomorphism
`complex_generalLinear_det_lie_hom n`. -/
#check (complex_generalLinear_det_lie_hom n)

end

section Conjugation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {H : Type*} [TopologicalSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]

/-- Helper for Example 7.4: conjugation by a fixed element is smooth. -/
theorem contMDiff_conjugationMap (g : G) :
    ContMDiff I I ∞ (fun h : G ↦ g * h * g⁻¹) := by
  -- Compose left multiplication by `g` with right multiplication by `g⁻¹`.
  have hleft : ContMDiff I I ∞ (fun h : G ↦ g * h) :=
    contMDiff_mul_left
  have hright : ContMDiff I I ∞ (fun h : G ↦ h * g⁻¹) :=
    contMDiff_mul_right
  simpa [Function.comp, ← mul_assoc] using
    hright.comp hleft

/-- Helper for Example 7.4: the automorphism `MulAut.conj g` is smooth. -/
theorem contMDiff_conjugationMulAut (g : G) :
    ContMDiff I I ∞ (MulAut.conj g : G → G) := by
  -- Rewrite the automorphism to the explicit conjugation formula.
  simpa [MulAut.conj_apply] using contMDiff_conjugationMap g

/-- Helper for Example 7.4: the inverse automorphism of `MulAut.conj g` is smooth. -/
theorem contMDiff_conjugationMulAut_symm (g : G) :
    ContMDiff I I ∞ ((MulAut.conj g).symm : G → G) := by
  -- The inverse automorphism is conjugation by `g⁻¹`.
  simpa [MulAut.conj_symm_apply] using contMDiff_conjugationMap g⁻¹

/-- Example 7.4 (10): for `g ∈ G`, conjugation by `g` is a Lie group homomorphism. -/
def conjugation_lie_hom (I : ModelWithCorners 𝕜 E H) [LieGroup I ∞ G] (g : G) :
    ContMDiffMonoidMorphism I I ∞ G G where
  toMonoidHom := (MulAut.conj g).toMonoidHom
  -- Route correction: attach the smooth-structure instance to the explicit `I` parameter.
  contMDiff_toFun := contMDiff_conjugationMulAut g

/- The Lie-group homomorphism `conjugation_lie_hom g` has underlying monoid homomorphism
`(MulAut.conj g).toMonoidHom`. -/
theorem conjugation_lie_hom_toMonoidHom (g : G) :
    (conjugation_lie_hom I g).toMonoidHom = (MulAut.conj g).toMonoidHom := by
  -- The structure field was chosen to be exactly the conjugation monoid homomorphism.
  rfl

/-- Example 7.4 (11): conjugation by `g` is a Lie group isomorphism, with inverse given by
conjugation by `g⁻¹`. -/
def conjugation_lie_iso (I : ModelWithCorners 𝕜 E H) [LieGroup I ∞ G] (g : G) :
    LieGroupIsomorphism I I G G where
  toDiffeomorph :=
    { toEquiv := (MulAut.conj g).toEquiv
      contMDiff_toFun := contMDiff_conjugationMulAut g
      contMDiff_invFun := contMDiff_conjugationMulAut_symm g }
  map_mul' := (MulAut.conj g).map_mul

/-- The inverse of `conjugation_lie_iso g` is conjugation by `g⁻¹`. -/
theorem conjugation_lie_iso_symm (I : ModelWithCorners 𝕜 E H) [LieGroup I ∞ G] (g : G) :
    (conjugation_lie_iso I g).symm.toMulEquiv = MulAut.conj g⁻¹ := by
  -- Two multiplicative equivalences are equal once their underlying functions agree.
  ext h
  simp [conjugation_lie_iso, LieGroupIsomorphism.symm, LieGroupIsomorphism.toMulEquiv]

end Conjugation

section

variable {G : Type*} [Group G]

/-- Example 7.4 (12): a subgroup is normal exactly when it is fixed by all conjugation maps. -/
theorem subgroup_normal_iff_conjugation_eq_self (K : Subgroup G) :
    K.Normal ↔ ∀ g : G, MulAut.conj g • K = K := by
  constructor
  · intro hK g
    let _ : K.Normal := hK
    exact Subgroup.Normal.conj_smul_eq_self g K
  · intro hK
    exact Subgroup.Normal.of_conjugate_fixed hK

end
