import Mathlib
import BauschkeLean.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace ComplexConjugate ComplexOrder

universe u v

namespace ContinuousLinearMap

section RealPositive

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Fact 20.18: the `L²` pair model is continuously equivalent to the raw product, so
all concrete calculations can be done in coordinates. -/
noncomputable abbrev pairSpaceEquiv : WithLp 2 (H × H) ≃L[ℝ] H × H :=
  WithLp.prodContinuousLinearEquiv 2 ℝ H H

/-- Helper for Fact 20.18: embed a real vector on the diagonal copy `(x, 0)` inside the pair
model. -/
noncomputable def ofRealVec : H →L[ℝ] WithLp 2 (H × H) :=
  (pairSpaceEquiv (H := H)).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ H H

/-- Helper for Fact 20.18: lift a real bounded operator diagonally to the pair model. -/
noncomputable def pairLift (T : H →L[ℝ] H) : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  (pairSpaceEquiv (H := H)).symm.toContinuousLinearMap ∘L (T.prodMap T) ∘L
    (pairSpaceEquiv (H := H)).toContinuousLinearMap

/-- Helper for Fact 20.18: the diagonal embedding is concretely `(x, 0)` in pair coordinates. -/
lemma ofRealVec_apply (x : H) : ofRealVec x = WithLp.toLp 2 (x, 0) := by
  -- Unfold the embedding and simplify through the `WithLp` product equivalence.
  simp [ofRealVec, pairSpaceEquiv]

/-- Helper for Fact 20.18: the diagonal lift acts coordinatewise on the concrete pair model. -/
lemma pairLift_apply (T : H →L[ℝ] H) (z : WithLp 2 (H × H)) :
    pairLift T z = WithLp.toLp 2 (T z.fst, T z.snd) := by
  -- Transport to raw product coordinates, apply `T` on both entries, and transport back.
  simp [pairLift, pairSpaceEquiv]
  rfl

/-- Helper for Fact 20.18: the diagonal lift preserves multiplication. -/
lemma pairLift_mul (S T : H →L[ℝ] H) :
    pairLift (S * T) = pairLift S * pairLift T := by
  -- Once the lift is expanded coordinatewise, the claim is pointwise composition on each factor.
  refine ContinuousLinearMap.ext fun z => ?_
  simp [pairLift_apply, ContinuousLinearMap.mul_apply]

/-- Helper for Fact 20.18: the diagonal lift preserves commutation. -/
lemma pairLift_commute {A B : H →L[ℝ] H} (hcomm : Commute A B) :
    Commute (pairLift A) (pairLift B) := by
  -- The diagonal lift is multiplicative, so it carries the commutator equation unchanged.
  change pairLift A * pairLift B = pairLift B * pairLift A
  rw [← pairLift_mul, ← pairLift_mul, hcomm.eq]

/-- Helper for Fact 20.18: the diagonal lift preserves self-adjointness on the real `L²` pair
model. -/
lemma pairLift_isSelfAdjoint_of_isSelfAdjoint {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (pairLift T) := by
  -- Reduce the symmetry check to the two coordinates of the pair model.
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hT
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hfst : ⟪T x.fst, y.fst⟫_ℝ = ⟪x.fst, T y.fst⟫_ℝ := by
    simpa using hT x.fst y.fst
  have hsnd : ⟪T x.snd, y.snd⟫_ℝ = ⟪x.snd, T y.snd⟫_ℝ := by
    simpa using hT x.snd y.snd
  calc
    ⟪pairLift T x, y⟫_ℝ = ⟪T x.fst, y.fst⟫_ℝ + ⟪T x.snd, y.snd⟫_ℝ := by
      simp [pairLift_apply, WithLp.prod_inner_apply]
    _ = ⟪x.fst, T y.fst⟫_ℝ + ⟪T x.snd, y.snd⟫_ℝ := by
      rw [hfst]
    _ = ⟪x.fst, T y.fst⟫_ℝ + ⟪x.snd, T y.snd⟫_ℝ := by
      rw [hsnd]
    _ = ⟪x, pairLift T y⟫_ℝ := by
      simp [pairLift_apply, WithLp.prod_inner_apply]

/-- Helper for Fact 20.18: positive real operators stay positive after the diagonal lift to the
real `L²` pair model. -/
lemma pairLift_isPositive_of_isPositive {T : H →L[ℝ] H} (hT : T.IsPositive) :
    (pairLift T).IsPositive := by
  -- The lifted quadratic form is the sum of the two original quadratic forms.
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨pairLift_isSelfAdjoint_of_isSelfAdjoint hT.isSelfAdjoint, ?_⟩
  intro z
  simpa [pairLift_apply, WithLp.prod_inner_apply] using
    add_nonneg (hT.inner_nonneg_left z.fst) (hT.inner_nonneg_left z.snd)

/-- Helper for Fact 20.18: the lifted operator sends the embedded real copy back to the embedded
real copy. -/
lemma pairLift_ofRealVec (T : H →L[ℝ] H) (x : H) :
    pairLift T (ofRealVec x) = ofRealVec (T x) := by
  -- Evaluate the diagonal lift on a vector whose second coordinate vanishes.
  simp [pairLift_apply, ofRealVec_apply]

/-- Helper for Fact 20.18: on the embedded real copy, the lifted quadratic form is exactly the
original real quadratic form. -/
lemma pairLiftInner_ofRealVec (T : H →L[ℝ] H) (x : H) :
    ⟪pairLift T (ofRealVec x), ofRealVec x⟫_ℝ = ⟪T x, x⟫_ℝ := by
  -- The second coordinate vanishes on the embedded real copy, so only the original quadratic form
  -- remains.
  rw [pairLift_ofRealVec]
  simp [ofRealVec_apply, WithLp.prod_inner_apply]

/-- Helper for Fact 20.18: `WithLp 2 (H × H)` is the theorem-local complexification carrier used
to transport the real operator problem to a complex Hilbert-space operator problem. -/
abbrev PairComplex := WithLp 2 (H × H)

/-- Helper for Fact 20.18: multiplication by `i` on the raw real pair carrier is the quarter-turn
`(x, y) ↦ (-y, x)`. -/
noncomputable def pairComplexIProd : Module.End ℝ (H × H) where
  toFun xy := (-xy.2, xy.1)
  map_add' x y := by
    -- The quarter-turn acts coordinatewise, so additivity is immediate on each component.
    ext <;> simp [add_comm]
  map_smul' r x := by
    -- The quarter-turn is real linear because each coordinate is built from real scalar
    -- multiplication and negation.
    ext <;> simp [smul_neg]

/-- Helper for Fact 20.18: the quarter-turn squares to `-1` on the raw real pair carrier. -/
lemma pairComplexIProd_sq_apply (x : H × H) :
    pairComplexIProd (H := H) (pairComplexIProd (H := H) x) = -x := by
  -- Evaluating the quarter-turn twice sends `(x, y)` to `(-x, -y)`.
  ext <;> simp [pairComplexIProd]

/-- Helper for Fact 20.18: the quarter-turn endomorphism is a square root of `-1`. -/
lemma pairComplexIProd_sq :
    pairComplexIProd (H := H) * pairComplexIProd (H := H) = -1 := by
  -- Equality of endomorphisms is pointwise, and the pointwise computation is the previous lemma.
  ext x <;> simp [pairComplexIProd_sq_apply]

/-- Helper for Fact 20.18: the universal property of `ℂ` upgrades the quarter-turn to a scalar
action of `ℂ` on the raw real pair carrier. -/
noncomputable def pairComplexScalarHom : ℂ →ₐ[ℝ] Module.End ℝ (H × H) :=
  Complex.lift
    ⟨pairComplexIProd (H := H), by
      -- Route correction: instead of packaging a bespoke complex structure by repeated coordinate
      -- rewrites, use `Complex.lift` from the already-proved square-root-of-`-1` endomorphism.
      simpa using
        congrArg (fun T : Module.End ℝ (H × H) => T) (pairComplexIProd_sq (H := H))⟩

/-- Helper for Fact 20.18: the raw real pair carrier is now a complex vector space. -/
noncomputable instance pairComplexModule : Module ℂ (H × H) :=
  Module.compHom (H × H) (pairComplexScalarHom (H := H)).toRingHom

/-- Helper for Fact 20.18: the induced complex scalar action on the raw real pair carrier is the
standard coordinate formula `(a + bi) • (x, y) = (ax - by, bx + ay)`. -/
lemma pairComplex_smul_apply (c : ℂ) (x : H × H) :
    c • x = ((c.re : ℝ) • x.1 - (c.im : ℝ) • x.2,
      (c.im : ℝ) • x.1 + (c.re : ℝ) • x.2) := by
  let hI : pairComplexIProd (H := H) * pairComplexIProd (H := H) = -1 :=
    pairComplexIProd_sq (H := H)
  -- Evaluate the universal `Complex.lift` formula on the pair carrier and expand the quarter-turn.
  change ((Complex.liftAux (pairComplexIProd (H := H)) hI) c) x = _
  rw [Complex.liftAux_apply]
  ext <;> simp [pairComplexIProd, sub_eq_add_neg, smul_neg, add_comm]

/-- Helper for Fact 20.18: multiplication by `i` on the `WithLp` pair carrier is the coordinate
quarter-turn `(-snd, fst)`. -/
lemma pairComplex_i_smul_apply (z : PairComplex (H := H)) :
    (Complex.I : ℂ) • z = WithLp.toLp 2 (-z.snd, z.fst) := by
  -- Transport the complex scalar action back through `WithLp.ofLp` and use the raw coordinate
  -- formula already established above.
  apply WithLp.ofLp_injective
  simp [pairComplex_smul_apply]

/-- Helper for Fact 20.18: the real `L²` inner product of `iz` with `z` vanishes. -/
lemma pairComplex_i_real_inner (z : PairComplex (H := H)) :
    ⟪(Complex.I : ℂ) • z, z⟫_ℝ = 0 := by
  -- In coordinates the cross terms cancel by symmetry of the real inner product.
  rw [pairComplex_i_smul_apply]
  simp [WithLp.prod_inner_apply, real_inner_comm]

/-- Helper for Fact 20.18: the quarter-turn is an isometry for the `L²` norm on the pair carrier. -/
lemma pairComplex_norm_i_smul (z : PairComplex (H := H)) : ‖(Complex.I : ℂ) • z‖ = ‖z‖ := by
  -- Compare squared norms and use that the quarter-turn only swaps coordinates up to sign.
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, pairComplex_i_smul_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp [add_comm]

/-- Helper for Fact 20.18: complex multiplication splits into the real part plus the imaginary
part times the quarter-turn. -/
lemma pairComplex_smul_decompose (c : ℂ) (z : PairComplex (H := H)) :
    c • z = (c.re : ℝ) • z + (c.im : ℝ) • ((Complex.I : ℂ) • z) := by
  -- After forgetting the `WithLp` wrapper, this is exactly the coordinate formula for complex
  -- scalar multiplication proved above.
  apply WithLp.ofLp_injective
  ext <;> simp [pairComplex_smul_apply, sub_eq_add_neg, add_comm]

/-- Helper for Fact 20.18: the `L²` norm on the pair carrier is compatible with the theorem-local
complex scalar action. -/
lemma pairComplex_norm_smul (c : ℂ) (z : PairComplex (H := H)) : ‖c • z‖ = ‖c‖ * ‖z‖ := by
  have horth : ⟪(c.re : ℝ) • z, (c.im : ℝ) • ((Complex.I : ℂ) • z)⟫_ℝ = 0 := by
    -- The real and imaginary directions are orthogonal because `iz` is orthogonal to `z`.
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm, pairComplex_i_real_inner]
    ring
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [← pairComplex_smul_decompose] at hsq
  have hmul : ‖c • z‖ * ‖c • z‖ = (‖c‖ * ‖z‖) * (‖c‖ * ‖z‖) := by
    calc
      ‖c • z‖ * ‖c • z‖ =
          ‖(c.re : ℝ) • z‖ * ‖(c.re : ℝ) • z‖ +
            ‖(c.im : ℝ) • ((Complex.I : ℂ) • z)‖ *
              ‖(c.im : ℝ) • ((Complex.I : ℂ) • z)‖ := by
          simpa using hsq
      _ = (|c.re| * ‖z‖) * (|c.re| * ‖z‖) +
            (|c.im| * ‖(Complex.I : ℂ) • z‖) * (|c.im| * ‖(Complex.I : ℂ) • z‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = (|c.re| * ‖z‖) * (|c.re| * ‖z‖) + (|c.im| * ‖z‖) * (|c.im| * ‖z‖) := by
          rw [pairComplex_norm_i_smul]
      _ = ((|c.re| * |c.re|) + (|c.im| * |c.im|)) * (‖z‖ * ‖z‖) := by
          ring
      _ = (c.re * c.re + c.im * c.im) * (‖z‖ * ‖z‖) := by
          rw [abs_mul_abs_self, abs_mul_abs_self]
      _ = (‖c‖ * ‖c‖) * (‖z‖ * ‖z‖) := by
          simpa [pow_two] using
            congrArg (fun t : ℝ => t * (‖z‖ * ‖z‖)) ((Complex.sq_norm c).symm)
      _ = (‖c‖ * ‖z‖) * (‖c‖ * ‖z‖) := by
          ring
  have hsq' : ‖c • z‖ ^ 2 = (‖c‖ * ‖z‖) ^ 2 := by
    simpa [pow_two] using hmul
  exact
    (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq'

/-- Helper for Fact 20.18: the theorem-local complex scalar action is compatible with the
existing `L²` norm on the pair carrier. -/
noncomputable instance pairComplexNormedSpace : NormedSpace ℂ (PairComplex (H := H)) where
  norm_smul_le c z := by
    -- The previous lemma proves the exact norm formula, so the norm inequality is immediate.
    simp [pairComplex_norm_smul]

/-- Helper for Fact 20.18: the theorem-local complex inner product on the pair carrier is the
standard complexification formula in real coordinates. -/
noncomputable def pairComplexInner (x y : PairComplex (H := H)) : ℂ :=
  ((⟪x.fst, y.fst⟫_ℝ + ⟪x.snd, y.snd⟫_ℝ : ℝ) : ℂ) +
    Complex.I * ((⟪x.fst, y.snd⟫_ℝ - ⟪x.snd, y.fst⟫_ℝ : ℝ) : ℂ)

/-- Helper for Fact 20.18: the theorem-local complex scalar action on the pair carrier has the
expected coordinate formula. -/
lemma pairComplex_smul_toLp (c : ℂ) (z : PairComplex (H := H)) :
    c • z = WithLp.toLp 2 ((c.re : ℝ) • z.fst - (c.im : ℝ) • z.snd,
      (c.im : ℝ) • z.fst + (c.re : ℝ) • z.snd) := by
  -- Forget the `WithLp` wrapper, use the raw coordinate formula, and transport back.
  apply WithLp.ofLp_injective
  simp [pairComplex_smul_apply]

/-- Helper for Fact 20.18: the real part of the theorem-local complex inner product is the
original `L²` norm square on the pair carrier. -/
lemma pairComplexInner_norm_sq_eq_re (x : PairComplex (H := H)) :
    ‖x‖ ^ 2 = Complex.re (pairComplexInner (H := H) x x) := by
  -- The imaginary part vanishes on the diagonal, so only the two squared norms remain.
  have hdiag : pairComplexInner (H := H) x x =
      (((⟪x.fst, x.fst⟫_ℝ + ⟪x.snd, x.snd⟫_ℝ : ℝ) : ℂ)) := by
    simp [pairComplexInner, real_inner_comm]
  calc
    ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 x
    _ = Complex.re (((⟪x.fst, x.fst⟫_ℝ + ⟪x.snd, x.snd⟫_ℝ : ℝ) : ℂ)) := by
      rw [show ⟪x.fst, x.fst⟫_ℝ = ‖x.fst‖ ^ 2 by simp,
        show ⟪x.snd, x.snd⟫_ℝ = ‖x.snd‖ ^ 2 by simp]
      exact (Complex.ofReal_re _).symm
    _ = Complex.re (pairComplexInner (H := H) x x) := by
      rw [hdiag]

/-- Helper for Fact 20.18: swapping the arguments of the theorem-local complex inner product
conjugates it. -/
lemma pairComplexInner_conj_symm (x y : PairComplex (H := H)) :
    conj (pairComplexInner (H := H) y x) = pairComplexInner (H := H) x y := by
  -- Swapping the arguments preserves the real part and flips the sign of the imaginary part.
  apply Complex.ext <;> simp [pairComplexInner, real_inner_comm, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc]

/-- Helper for Fact 20.18: the theorem-local complex inner product is additive in the left
argument. -/
lemma pairComplexInner_add_left (x y z : PairComplex (H := H)) :
    pairComplexInner (H := H) (x + y) z =
      pairComplexInner (H := H) x z + pairComplexInner (H := H) y z := by
  -- Each coordinate contribution is additive in the left variable.
  simp [pairComplexInner, inner_add_left, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  ring

/-- Helper for Fact 20.18: real scalar multiplication on the left pulls out of the theorem-local
complex inner product as expected. -/
lemma pairComplexInner_real_smul_left (r : ℝ) (x y : PairComplex (H := H)) :
    pairComplexInner (H := H) (r • x) y = conj (r : ℂ) * pairComplexInner (H := H) x y := by
  -- This is just real linearity of each coordinate inner product.
  simp [pairComplexInner, real_inner_smul_left, sub_eq_add_neg, mul_add]
  ring

/-- Helper for Fact 20.18: multiplication by `i` on the left pulls out as conjugate scalar in the
theorem-local complex inner product. -/
lemma pairComplexInner_i_smul_left (x y : PairComplex (H := H)) :
    pairComplexInner (H := H) ((Complex.I : ℂ) • x) y =
      conj (Complex.I : ℂ) * pairComplexInner (H := H) x y := by
  -- The quarter-turn coordinate formula matches multiplication by `-i` on the inner product.
  rw [pairComplex_i_smul_apply]
  apply Complex.ext <;> simp [pairComplexInner, real_inner_comm, sub_eq_add_neg, Complex.mul_re,
    Complex.mul_im]
  ring

/-- Helper for Fact 20.18: complex scalar multiplication on the left pulls out as conjugate scalar
in the theorem-local complex inner product. -/
lemma pairComplexInner_smul_left (c : ℂ) (x y : PairComplex (H := H)) :
    pairComplexInner (H := H) (c • x) y = conj c * pairComplexInner (H := H) x y := by
  -- Decompose a complex scalar into its real and imaginary parts and use the `i`-case separately.
  rw [pairComplex_smul_decompose c x, pairComplexInner_add_left, pairComplexInner_real_smul_left,
    pairComplexInner_real_smul_left, pairComplexInner_i_smul_left]
  have hc : conj c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hc]
  simp [sub_eq_add_neg, mul_add, mul_left_comm, mul_comm]

/-- Helper for Fact 20.18: the pair carrier becomes a complex Hilbert space with the standard
complexification inner product. -/
noncomputable instance pairComplexInnerProductSpace :
    InnerProductSpace ℂ (PairComplex (H := H)) where
  inner := pairComplexInner (H := H)
  norm_sq_eq_re_inner := pairComplexInner_norm_sq_eq_re (H := H)
  conj_inner_symm := pairComplexInner_conj_symm (H := H)
  add_left := pairComplexInner_add_left (H := H)
  smul_left x y c := pairComplexInner_smul_left (H := H) c x y

/-- Helper for Fact 20.18: after installing the theorem-local complex inner product, the complex
inner product notation unfolds to the explicit coordinate formula above. -/
@[simp] lemma pairComplex_inner_apply (x y : PairComplex (H := H)) :
    ⟪x, y⟫_ℂ = pairComplexInner (H := H) x y := rfl

/-- Helper for Fact 20.18: the diagonal real lift is compatible with the theorem-local complex
scalar action on the pair carrier. -/
lemma pairLift_smul (T : H →L[ℝ] H) (c : ℂ) (z : PairComplex (H := H)) :
    pairLift T (c • z) = c • pairLift T z := by
  -- Expand both sides in raw coordinates and use real linearity of `T`.
  rw [pairComplex_smul_toLp, pairLift_apply, pairLift_apply, pairComplex_smul_toLp]
  simp [sub_eq_add_neg, map_add, map_neg, map_smul]

/-- Helper for Fact 20.18: the real diagonal lift is automatically complex linear on the
theorem-local complexification carrier. -/
noncomputable def pairLiftComplex (T : H →L[ℝ] H) :
    PairComplex (H := H) →L[ℂ] PairComplex (H := H) where
  toLinearMap :=
    { toFun := pairLift T
      map_add' := pairLift T |>.map_add
      map_smul' := pairLift_smul T }
  cont := (pairLift T).continuous

/-- Helper for Fact 20.18: the complex lift still acts coordinatewise on the pair carrier. -/
lemma pairLiftComplex_apply (T : H →L[ℝ] H) (z : PairComplex (H := H)) :
    pairLiftComplex T z = WithLp.toLp 2 (T z.fst, T z.snd) := by
  -- The complex lift has the same underlying function as the real diagonal lift.
  simpa [pairLiftComplex] using pairLift_apply T z

/-- Helper for Fact 20.18: the complex lift preserves multiplication. -/
lemma pairLiftComplex_mul (S T : H →L[ℝ] H) :
    pairLiftComplex (S * T) = pairLiftComplex S * pairLiftComplex T := by
  -- Equality of complex lifts is pointwise composition on the same underlying pair carrier.
  refine ContinuousLinearMap.ext fun z => ?_
  simp [pairLiftComplex_apply, ContinuousLinearMap.mul_apply]

/-- Helper for Fact 20.18: the complex lift preserves commutation. -/
lemma pairLiftComplex_commute {A B : H →L[ℝ] H} (hcomm : Commute A B) :
    Commute (pairLiftComplex A) (pairLiftComplex B) := by
  -- The complex lift is multiplicative, so it carries the commutator equation unchanged.
  change pairLiftComplex A * pairLiftComplex B = pairLiftComplex B * pairLiftComplex A
  rw [← pairLiftComplex_mul, ← pairLiftComplex_mul, hcomm.eq]

/-- Helper for Fact 20.18: positive real operators stay positive after the diagonal lift to the
theorem-local complexification carrier. -/
lemma pairLiftComplex_isPositive_of_isPositive {T : H →L[ℝ] H} (hT : T.IsPositive) :
    (pairLiftComplex T).IsPositive := by
  -- The lifted quadratic form is a real nonnegative sum of the two original quadratic forms.
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hcross : ⟪T z.fst, z.snd⟫_ℝ = ⟪T z.snd, z.fst⟫_ℝ := by
    simpa [real_inner_comm] using hT.isSymmetric z.fst z.snd
  have hinner :
      ⟪pairLiftComplex T z, z⟫_ℂ =
        (((⟪T z.fst, z.fst⟫_ℝ + ⟪T z.snd, z.snd⟫_ℝ : ℝ) : ℂ)) := by
    simp [pairLiftComplex_apply, pairComplexInner, hcross]
  constructor
  · -- The cross term vanishes because the real operator is symmetric.
    rw [hinner]
    simp
  · -- The remaining real part is the sum of two nonnegative real quadratic forms.
    rw [hinner]
    exact add_nonneg (hT.inner_nonneg_left z.fst) (hT.inner_nonneg_left z.snd)

/-- Helper for Fact 20.18: the complex lift still sends the embedded real copy back to the
embedded real copy. -/
lemma pairLiftComplex_ofRealVec (T : H →L[ℝ] H) (x : H) :
    pairLiftComplex T (ofRealVec x) = ofRealVec (T x) := by
  -- The complex lift has the same underlying function as the real diagonal lift.
  simpa [pairLiftComplex] using pairLift_ofRealVec T x

/-- Helper for Fact 20.18: on the embedded real copy, the complexified lifted quadratic form is
exactly the original real quadratic form. -/
lemma pairLiftComplexInner_ofRealVec (T : H →L[ℝ] H) (x : H) :
    ⟪pairLiftComplex T (ofRealVec x), ofRealVec x⟫_ℂ = (⟪T x, x⟫_ℝ : ℂ) := by
  -- The second coordinate vanishes on the embedded real copy, so the imaginary part disappears.
  rw [pairLiftComplex_ofRealVec]
  simp [pairComplexInner, ofRealVec_apply]

/-- Helper for Fact 20.18: the complexified lifted product computes the original quadratic form on
the embedded real copy. -/
lemma pairLiftComplexMulInner_ofRealVec {A B : H →L[ℝ] H} (x : H) :
    ⟪(pairLiftComplex A * pairLiftComplex B) (ofRealVec x), ofRealVec x⟫_ℂ =
      (⟪(A * B) x, x⟫_ℝ : ℂ) := by
  -- Collapse the lifted product back to the lift of `A * B`, then evaluate on the real copy.
  rw [← pairLiftComplex_mul]
  simpa using pairLiftComplexInner_ofRealVec (T := A * B) x

/-- Helper for Fact 20.18: an adjoint factorization `B = S.adjoint * S` reduces positivity of
`A * B` to the quadratic-form positivity of `A` evaluated at `S x`. -/
lemma isPositive_mul_of_adjointFactor {A B S : H →L[ℝ] H}
    (hA : A.IsPositive) (hfactor : B = S.adjoint * S) (hAS : Commute A S) :
    (A * B).IsPositive := by
  -- Keep the commutation with the adjoint factor available for both the self-adjoint and
  -- quadratic-form parts of the proof.
  have hSAS : Commute A S.adjoint := by
    have hstar : Commute (star A) S := by
      simpa [hA.isSelfAdjoint.star_eq] using hAS
    simpa [ContinuousLinearMap.star_eq_adjoint] using hstar.star_right
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, ?_⟩
  · -- Positive operators are self-adjoint, so commuting factors give a self-adjoint product.
    have hAB : Commute A B := by
      rw [hfactor]
      exact hSAS.mul_right hAS
    have hBpos : B.IsPositive := by
      rw [hfactor]
      simpa [ContinuousLinearMap.mul_def] using (ContinuousLinearMap.isPositive_adjoint_comp_self S)
    exact (IsSelfAdjoint.commute_iff hA.isSelfAdjoint hBpos.isSelfAdjoint).mp hAB
  · intro x
    have hcommAdj : A * S.adjoint = S.adjoint * A := hSAS
    -- Rewrite the quadratic form of `A * B` through the adjoint factorization of `B`.
    calc
      ⟪(A * B) x, x⟫_ℝ = ⟪A (S.adjoint (S x)), x⟫_ℝ := by
        simp [hfactor]
      _ = ⟪S.adjoint (A (S x)), x⟫_ℝ := by
        congr 1
        simpa [Module.End.mul_apply] using congrArg (fun T => T (S x)) hcommAdj
      _ = ⟪A (S x), S x⟫_ℝ := by
        simpa using (ContinuousLinearMap.adjoint_inner_left S x (A (S x)))
      _ ≥ 0 := hA.inner_nonneg_left (S x)

/-- Helper for Fact 20.18: once the quadratic form of `A * B` is known to be nonnegative,
commuting positivity of the factors supplies the self-adjointness needed to conclude positivity
of the product. -/
lemma isPositive_mul_of_commute_of_inner_nonneg {A B : H →L[ℝ] H}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B)
    (hinner : ∀ x, 0 ≤ ⟪(A * B) x, x⟫_ℝ) :
    (A * B).IsPositive := by
  -- Once the quadratic form is nonnegative everywhere, only self-adjointness of the product
  -- remains, and commuting symmetric factors provide it directly.
  have hcommLinear : Commute (A : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H) := by
    change (A : H →ₗ[ℝ] H) * (B : H →ₗ[ℝ] H) = (B : H →ₗ[ℝ] H) * (A : H →ₗ[ℝ] H)
    exact congrArg (fun T : H →L[ℝ] H => (T : H →ₗ[ℝ] H)) hcomm.eq
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, hinner⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact LinearMap.IsSymmetric.mul_of_commute hA.isSymmetric hB.isSymmetric hcommLinear

/-- Helper for Fact 20.18: the diagonal pair lift computes the quadratic form of `A * B`
correctly on the embedded real copy `(x, 0)`. -/
lemma pairLiftMulInner_ofRealVec {A B : H →L[ℝ] H} (x : H) :
    ⟪(pairLift A * pairLift B) (ofRealVec x), ofRealVec x⟫_ℝ = ⟪(A * B) x, x⟫_ℝ := by
  -- Collapse the lifted product back to the lift of `A * B`, then use the coordinate formula
  -- already established in the theorem-local pair model.
  rw [← pairLift_mul]
  simpa using pairLiftInner_ofRealVec (T := A * B) x

/-- Helper for Fact 20.18: positivity of the lifted product implies the required nonnegativity of
the original real quadratic form. -/
lemma inner_nonneg_of_pairLiftMul_isPositive {A B : H →L[ℝ] H}
    (hpair : (pairLift A * pairLift B).IsPositive) :
    ∀ x, 0 ≤ ⟪(A * B) x, x⟫_ℝ := by
  intro x
  -- Test the lifted positive operator on the embedded real vector and rewrite back to `H`.
  have hinner : 0 ≤ ⟪(pairLift A * pairLift B) (ofRealVec x), ofRealVec x⟫_ℝ :=
    hpair.inner_nonneg_left (ofRealVec x)
  rwa [pairLiftMulInner_ofRealVec (A := A) (B := B) x] at hinner

/-- Helper for Fact 20.18: once the pair-model product is known to be positive, the original real
product is positive by reflecting the quadratic form and reusing the self-adjointness lemma. -/
lemma isPositive_of_pairLiftMul_isPositive {A B : H →L[ℝ] H}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B)
    (hpair : (pairLift A * pairLift B).IsPositive) :
    (A * B).IsPositive := by
  -- The local work is now reduced to a single pair-model positivity input.
  refine isPositive_mul_of_commute_of_inner_nonneg hA hB hcomm ?_
  exact inner_nonneg_of_pairLiftMul_isPositive hpair

/-- Helper for Fact 20.18: the remaining proof obligation is now reduced to the complex
inner-product and positivity bridge on the theorem-local pair carrier. -/
lemma isPositiveMulOfCommuteViaPairComplexification {A B : H →L[ℝ] H}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B) :
    (A * B).IsPositive := by
  -- Route correction: abandon the unfinished theorem-local CFC packaging on the real operator
  -- algebra and instead use the explicit complex Hilbert structure on `PairComplex`.
  have hA_pair : (pairLiftComplex A).IsPositive := pairLiftComplex_isPositive_of_isPositive hA
  have hB_pair : (pairLiftComplex B).IsPositive := pairLiftComplex_isPositive_of_isPositive hB
  have hpair_nonneg : (0 : PairComplex (H := H) →L[ℂ] PairComplex (H := H)) ≤
      pairLiftComplex A * pairLiftComplex B := by
    -- On the complex lift, the standard ordered-operator product theorem applies directly.
    letI : Module ℝ (PairComplex (H := H) →L[ℂ] PairComplex (H := H)) :=
      Module.complexToReal _
    letI : IsScalarTower ℝ ℂ (PairComplex (H := H) →L[ℂ] PairComplex (H := H)) :=
      IsScalarTower.complexToReal
    letI : NonnegSpectrumClass ℝ
        (PairComplex (H := H) →L[ℂ] PairComplex (H := H)) :=
      { quasispectrum_nonneg_of_nonneg := fun f hf ↦
          QuasispectrumRestricts.nnreal_iff.mp <| sub_zero f ▸ hf.spectrumRestricts }
    have hA_nonneg : (0 : PairComplex (H := H) →L[ℂ] PairComplex (H := H)) ≤ pairLiftComplex A :=
      (ContinuousLinearMap.nonneg_iff_isPositive (pairLiftComplex A)).2 hA_pair
    have hB_nonneg : (0 : PairComplex (H := H) →L[ℂ] PairComplex (H := H)) ≤ pairLiftComplex B :=
      (ContinuousLinearMap.nonneg_iff_isPositive (pairLiftComplex B)).2 hB_pair
    exact (pairLiftComplex_commute hcomm).mul_nonneg hA_nonneg hB_nonneg
  refine isPositive_mul_of_commute_of_inner_nonneg hA hB hcomm ?_
  intro x
  have hpair_pos : (pairLiftComplex A * pairLiftComplex B).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive (pairLiftComplex A * pairLiftComplex B)).1
      hpair_nonneg
  have hinner : (0 : ℂ) ≤
      ⟪(pairLiftComplex A * pairLiftComplex B) (ofRealVec x), ofRealVec x⟫_ℂ := by
    -- Test the positive lifted product on the embedded real vector.
    simpa using hpair_pos.inner_nonneg_left (ofRealVec x)
  rw [pairLiftComplexMulInner_ofRealVec (A := A) (B := B) x] at hinner
  simpa using hinner

/-- Helper for Fact 20.18: the theorem-local complexification route is now reduced to a single
remaining bridge theorem on `PairComplex`. -/
lemma isPositiveMulOfCommuteViaComplex {A B : H →L[ℝ] H}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B) :
    (A * B).IsPositive := by
  -- The pair-complexification route is now localized to one remaining bridge theorem.
  exact isPositiveMulOfCommuteViaPairComplexification hA hB hcomm

/-- A product of commuting positive bounded operators is positive. -/
theorem IsPositive.mul_of_commute {A B : H →L[ℝ] H}
    (hA : A.IsPositive) (hB : B.IsPositive) (hcomm : Commute A B) :
    (A * B).IsPositive := by
  -- The final theorem now delegates to the single complex-transport frontier above.
  exact isPositiveMulOfCommuteViaComplex hA hB hcomm

end RealPositive

section Real

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: turn the textbook hypotheses into positivity via
-- `ContinuousLinearMap.isPositive_iff'`, apply the owner-level positivity lemma
-- `ContinuousLinearMap.IsPositive.mul_of_commute`, and then forget positivity back to monotonicity.
/-- Fact 20.18: if `A` and `B` are self-adjoint monotone bounded linear operators on a real
Hilbert space and commute, then the product `AB` is monotone. -/
theorem isMonotone_mul_of_isSelfAdjoint_of_commute
    {A B : H →L[ℝ] H}
    (hA_self : IsSelfAdjoint A) (hB_self : IsSelfAdjoint B)
    (hA_mono : A.toLinearMap.IsMonotone) (hB_mono : B.toLinearMap.IsMonotone)
    (hcomm : Commute A B) :
    (A * B).toLinearMap.IsMonotone := by
  have hA_pos : A.IsPositive := (isPositive_iff' A).2 ⟨hA_self, hA_mono⟩
  have hB_pos : B.IsPositive := (isPositive_iff' B).2 ⟨hB_self, hB_mono⟩
  exact (hA_pos.mul_of_commute hB_pos hcomm).toLinearMap.isMonotone

end Real

end ContinuousLinearMap
