import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_1_5_1 (from Chap01) -/
noncomputable section

/-- Lemma 1.5.1: the fundamental group of `ℝ` based at `0` is trivial. -/
-- Proof sketch: contract `ℝ` to `0` by the straight-line homotopy `(s, t) ↦ (1 - t) * s`,
-- obtain that `ℝ` is contractible and hence simply connected, and then identify the
-- fundamental group at `0` as a subsingleton loop-class group.
theorem fundamental_group_real_zero_subsingleton :
    Subsingleton (FundamentalGroup ℝ 0) := by
  let _ : SimplyConnectedSpace ℝ := inferInstance
  change Subsingleton (Path.Homotopic.Quotient (0 : ℝ) (0 : ℝ))
  infer_instance

/-- Every element of the fundamental group of `ℝ` at `0` is the identity. -/
-- Proof sketch: apply the subsingleton statement for `FundamentalGroup ℝ 0` and compare any
-- element with the unit element.
theorem fundamental_group_real_zero_eq_one (γ : FundamentalGroup ℝ 0) :
    γ = 1 :=
  fundamental_group_real_zero_subsingleton.elim γ 1

/-! ### Definition_1_5_2 (from Chap01) -/
/- Definition 1.5.2: the circle `S^1` is the unit circle in `ℂ`, represented in mathlib by
`Circle`; it is used with its multiplicative topological group structure and with chosen
basepoint `1`. -/
recall Circle : Type

/- Elements of `Circle` are complex numbers of norm `1`. -/
recall Circle.norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1

/- The circle has its canonical multiplicative commutative group structure. -/
#check (inferInstance : CommGroup Circle)

/- The circle has its canonical topological group structure under multiplication. -/
#check (inferInstance : IsTopologicalGroup Circle)

/- The chosen basepoint on the circle is the unit complex number `1`. -/
#check (1 : Circle)

/-! ### Construction_1_5_3 (from Chap01) -/
noncomputable section

/-- The exponential line underlying the standard loop is continuous on the unit interval. -/
-- Proof sketch: `Circle.exp` is continuous on `ℝ`, and composing it with the affine map
-- `s ↦ 2 * π * n * s` preserves continuity; then restrict to `unitInterval`.
theorem standardLoop_continuousOn (n : ℤ) :
    ContinuousOn
      (fun s : ℝ ↦ Circle.exp (2 * Real.pi * (n : ℝ) * s))
      unitInterval := by
  -- The loop comes from composing `Circle.exp` with the affine line `s ↦ 2 * π * n * s`.
  have hline : Continuous (fun s : ℝ ↦ 2 * Real.pi * (n : ℝ) * s) := by
    fun_prop
  exact (Circle.exp.continuous.comp hline).continuousOn

/-- The exponential line defining the standard loop starts at the circle basepoint `1`. -/
-- Proof sketch: evaluate at `s = 0` and simplify the exponent to `0`, then use
-- `Circle.exp_zero`.
theorem standardLoop_zero (n : ℤ) :
    Circle.exp (2 * Real.pi * (n : ℝ) * 0) = (1 : Circle) := by
  -- At `s = 0`, the exponent is `0`, so the exponential hits the basepoint.
  simp

/-- The exponential line defining the standard loop ends at the circle basepoint `1`. -/
-- Proof sketch: evaluate at `s = 1`, rewrite the exponent as `2 * π * n`, and apply
-- `Circle.exp_two_pi_mul_int`.
theorem standardLoop_one (n : ℤ) :
    Circle.exp (2 * Real.pi * (n : ℝ) * 1) = (1 : Circle) := by
  -- At `s = 1`, the exponent is `2 * π * n`, which is a full integer number of turns.
  simpa [mul_assoc] using Circle.exp_two_pi_mul_int n

/-- Construction 1.5.3: for each integer `n`, the standard loop on `S^1` based at `1` is the
path `s ↦ e^{2πins}`, represented in mathlib by `s ↦ Circle.exp (2 * π * n * s)`. -/
def standardLoop (n : ℤ) : Path (1 : Circle) 1 :=
  Path.ofLine (standardLoop_continuousOn n) (standardLoop_zero n) (standardLoop_one n)

/-- Evaluating the standard loop gives the expected exponential formula on the unit interval. -/
@[simp] theorem standardLoop_apply (n : ℤ) (s : unitInterval) :
    standardLoop n s = Circle.exp (2 * Real.pi * (n : ℝ) * (s : ℝ)) :=
  rfl

/-! ### Lemma_1_5_4 (from Chap01) -/
noncomputable section

open FundamentalGroup

/-- The homotopy class of the standard loop with winding number `n` in `π₁(S¹, 1)`. -/
abbrev standardLoopClass (n : ℤ) : FundamentalGroup Circle 1 :=
  fromPath ⟦standardLoop n⟧

/-- Helper for Lemma 1.5.4: the Fourier character sends `0` to the circle basepoint. -/
lemma fourierChar_zero_eq_one : Real.fourierChar (0 : ℝ) = (1 : Circle) := by
  simp

/-- Helper for Lemma 1.5.4: the Fourier character sends every integer to the circle basepoint. -/
lemma fourierChar_int_eq_one (n : ℤ) : Real.fourierChar (n : ℝ) = (1 : Circle) := by
  simpa [Real.fourierChar_apply', mul_assoc] using Circle.exp_two_pi_mul_int n

/-- Helper for Lemma 1.5.4: the standard loop is the Fourier character of the lifted line
`s ↦ ns`. -/
lemma standardLoop_eq_fourierChar_mul (n : ℤ) (s : unitInterval) :
    standardLoop n s = Real.fourierChar ((n : ℝ) * (s : ℝ)) := by
  -- Rewrite the loop into the textbook exponential and simplify the scalar arithmetic.
  rw [standardLoop_apply, Real.fourierChar_apply']
  congr 1
  ring

/-- Helper for Lemma 1.5.4: the image of the straight segment from `0` to `n` under
`Real.fourierChar` is the standard loop of degree `n`. -/
lemma segment_zero_map_cast_eq_standardLoop (n : ℤ) :
    ((Path.segment (0 : ℝ) n).map Real.continuous_fourierChar).cast
      fourierChar_zero_eq_one.symm (fourierChar_int_eq_one n).symm = standardLoop n := by
  ext s
  -- Compare both paths pointwise after rewriting the segment and the standard loop formula.
  rw [standardLoop_eq_fourierChar_mul]
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    SetLike.coe_eq_coe]
  rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  congr 1
  ring

/-- Helper for Lemma 1.5.4: after translating the lift by an integer, the mapped segment still
represents the same standard loop. -/
lemma segment_translate_map_cast_eq_standardLoop (m n : ℤ) :
    ((Path.segment (n : ℝ) ((n + m : ℤ) : ℝ)).map Real.continuous_fourierChar).cast
      (fourierChar_int_eq_one n).symm
      (fourierChar_int_eq_one (n + m)).symm = standardLoop m := by
  ext s
  -- Rewrite the translated segment as `n + ms`, then use the additivity of `fourierChar`.
  rw [standardLoop_eq_fourierChar_mul]
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    Int.cast_add, SetLike.coe_eq_coe]
  rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  have hline : (1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * ((n : ℝ) + (m : ℝ)) =
      (n : ℝ) + (m : ℝ) * (s : ℝ) := by
    ring
  rw [hline]
  calc
    Real.fourierChar ((n : ℝ) + (m : ℝ) * (s : ℝ)) =
        Real.fourierChar (n : ℝ) * Real.fourierChar ((m : ℝ) * (s : ℝ)) := by
          simpa using (Real.fourierChar.map_add_eq_mul' (n : ℝ) ((m : ℝ) * (s : ℝ)))
    _ = Real.fourierChar ((m : ℝ) * (s : ℝ)) := by
          simp [fourierChar_int_eq_one]

/-- Helper for Lemma 1.5.4: concatenating the standard loops of degrees `n` and `m` is homotopic
to the standard loop of degree `m + n`. -/
lemma concat_standardLoop_homotopic_standardLoop_add (m n : ℤ) :
    ((standardLoop n).trans (standardLoop m)).Homotopic (standardLoop (m + n)) := by
  let expMap : C(ℝ, Circle) := ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  let liftedConcat : Path (0 : ℝ) (((n + m : ℤ) : ℝ)) :=
    (Path.segment (0 : ℝ) n).trans (Path.segment (n : ℝ) (((n + m : ℤ) : ℝ)))
  let liftedSingle : Path (0 : ℝ) (((n + m : ℤ) : ℝ)) :=
    Path.segment (0 : ℝ) (((n + m : ℤ) : ℝ))
  -- In `ℝ`, any two paths with the same endpoints are homotopic.
  have hlifted : liftedConcat.Homotopic liftedSingle :=
    SimplyConnectedSpace.paths_homotopic liftedConcat liftedSingle
  have hstart : Real.fourierChar (0 : ℝ) = (1 : Circle) := fourierChar_zero_eq_one
  have hmid : Real.fourierChar (n : ℝ) = (1 : Circle) := fourierChar_int_eq_one n
  have hend : Real.fourierChar (((n + m : ℤ) : ℝ)) = (1 : Circle) :=
    fourierChar_int_eq_one (n + m)
  have hmapped :
      ((liftedConcat.map expMap.continuous).cast hstart.symm hend.symm).Homotopic
        ((liftedSingle.map expMap.continuous).cast hstart.symm hend.symm) := by
    -- Map the lifted homotopy down to the circle, then recast both endpoints to `1`.
    simpa [hstart, hend] using Path.Homotopic.map hlifted expMap
  have hconcat :
      ((liftedConcat.map expMap.continuous).cast hstart.symm hend.symm) =
        (standardLoop n).trans (standardLoop m) := by
    -- The concatenated lifted path maps to the two standard loops in sequence.
    dsimp [liftedConcat, expMap]
    rw [Path.map_trans, Path.cast_trans _ _ hstart.symm hmid.symm hend.symm]
    rw [segment_zero_map_cast_eq_standardLoop, segment_translate_map_cast_eq_standardLoop]
  have hsingle :
      ((liftedSingle.map expMap.continuous).cast hstart.symm hend.symm) =
        standardLoop (m + n) := by
    -- The straight lifted segment is exactly the degree-`m+n` standard loop.
    dsimp [liftedSingle, expMap]
    simpa [add_comm] using segment_zero_map_cast_eq_standardLoop (n + m)
  exact hconcat.symm ▸ hsingle.symm ▸ hmapped

/-- Lemma 1.5.4: the standard loop classes multiply by adding winding numbers, so
`[f_m] [f_n] = [f_{m+n}]` in `π₁(S¹, 1)`. -/
-- Proof sketch: compare the concatenation of `standardLoop m` and `standardLoop n`
-- with `standardLoop (m + n)` pointwise using multiplication of exponentials on `Circle`,
-- then pass to homotopy classes and transport the result into `FundamentalGroup Circle 1`.
theorem standardLoopClass_add (m n : ℤ) :
    standardLoopClass m * standardLoopClass n = standardLoopClass (m + n) := by
  -- Multiplication in `π₁` is concatenation of loop classes, with the usual order reversal.
  change FundamentalGroup.fromPath ⟦(standardLoop n).trans (standardLoop m)⟧ =
      FundamentalGroup.fromPath ⟦standardLoop (m + n)⟧
  -- The lifted real-line argument supplies the required homotopy of loops.
  exact congrArg FundamentalGroup.fromPath
    (Quotient.sound (concat_standardLoop_homotopic_standardLoop_add m n))

/-- Helper for Lemma 1.5.4: the degree-zero standard loop is the constant loop at `1`. -/
lemma standardLoop_zero_eq_refl : standardLoop 0 = Path.refl (1 : Circle) := by
  ext s
  -- The exponent vanishes identically, so the loop is constant.
  simp [standardLoop_apply]

/-- Helper for Lemma 1.5.4: the degree-zero standard loop class is the identity element. -/
lemma standardLoopClass_zero : standardLoopClass 0 = 1 := by
  -- Rewrite both sides as classes of explicit loops and simplify the zero loop.
  change FundamentalGroup.fromPath ⟦standardLoop 0⟧ =
      FundamentalGroup.fromPath ⟦Path.refl (1 : Circle)⟧
  simp [standardLoop_zero_eq_refl]

/-- Helper for Lemma 1.5.4: the standard loop classes define a homomorphism
`Multiplicative ℤ → π₁(S¹, 1)`. -/
def standardLoopClass_hom : Multiplicative ℤ →* FundamentalGroup Circle 1 :=
  { toFun := fun a ↦ standardLoopClass (Multiplicative.toAdd a)
    map_one' := standardLoopClass_zero
    map_mul' := fun a b ↦
      (standardLoopClass_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)).symm }

/-- The class of the once-around loop generates the standard loop classes by integer powers. -/
-- Proof sketch: identify `(standardLoopClass 1) ^ n` with the value at `ofAdd n` of the
-- canonical `zpowersHom` out of `Multiplicative ℤ`, then compare with `standardLoopClass n`
-- using `standardLoopClass_add`.
theorem standardLoopClass_one_zpow (n : ℤ) :
    standardLoopClass 1 ^ n = standardLoopClass n := by
  -- Evaluate the homomorphism at `ofAdd n`; its value is the `n`th power of the generator.
  have happly := MonoidHom.apply_mint (α := FundamentalGroup Circle 1)
    standardLoopClass_hom (Multiplicative.ofAdd n)
  simpa [standardLoopClass_hom] using happly.symm

/-! ### Construction_1_5_5 (from Chap01) -/
noncomputable section

/-- The linear lift `\tilde f_n` of the standard loop is the path `s ↦ ns` from `0` to `n` in
`ℝ`. This is the canonical straight-line path `Path.segment 0 n`. -/
def standardLoopLift (n : ℤ) : Path (0 : ℝ) n :=
  Path.segment (0 : ℝ) n

/-- Evaluating the lifted standard loop gives the formula `\tilde f_n(s) = ns`. -/
-- Proof sketch: `Path.segment` is given by the affine line map; for endpoints `0` and `n`, this
-- simplifies to multiplication by `n`.
theorem standardLoopLift_apply (n : ℤ) (s : Set.Icc (0 : ℝ) 1) :
    standardLoopLift n s = (n : ℝ) * (s : ℝ) := by
  rw [standardLoopLift, Path.segment_apply, AffineMap.lineMap_apply_module]
  simp
  ring

/-- Construction 1.5.5: the standard loop `f_n` factors through the canonical covering map
`Real.fourierChar : ℝ → S¹` by the lift `\tilde f_n(s) = ns`. -/
-- Proof sketch: combine `standardLoop_apply` from Construction 1.5.3 with
-- `standardLoopLift_apply`, then identify the resulting expression with `Real.fourierChar`.
theorem standardLoop_factors_through_fourierChar (n : ℤ) (s : Set.Icc (0 : ℝ) 1) :
    standardLoop n s = Real.fourierChar (standardLoopLift n s) := by
  rw [standardLoop_apply, standardLoopLift_apply, Real.fourierChar_apply']
  ring_nf

/-- In textbook notation, the factorization of `f_n` through the covering map reads
`f_n(s) = e^{2πi\tilde f_n(s)}`. -/
theorem standardLoop_factors_through_circle_exp (n : ℤ) (s : Set.Icc (0 : ℝ) 1) :
    standardLoop n s = Circle.exp (2 * Real.pi * standardLoopLift n s) := by
  rw [standardLoop_factors_through_fourierChar]
  simp [Real.fourierChar_apply']

/-! ### Lemma_1_5_6 (from Chap01) -/
open scoped unitInterval

/-- The map `x ↦ e^{2πix}` from `ℝ` to `S¹`, represented by `Real.fourierChar`, is a covering
map. -/
-- Proof sketch: identify `Real.fourierChar` with the textbook map `x ↦ Circle.exp (2 * π * x)`
-- and obtain the covering-map property from `Circle.isCoveringMap_exp` by composing with the
-- homeomorphism of `ℝ` given by multiplication by `2 * π`.
theorem real_fourierChar_isCoveringMap : IsCoveringMap Real.fourierChar := by
  -- The scaling factor `2 * π` is nonzero, so multiplication by it is a homeomorphism of `ℝ`.
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  -- Transfer the covering-map property of `Circle.exp` along this homeomorphism.
  simpa [Real.fourierChar_apply', Function.comp_def, smul_eq_mul] using
    Circle.isCoveringMap_exp.comp_homeomorph (Homeomorph.smulOfNeZero (2 * Real.pi) h2pi)

/-- A path in `S¹` starting at `1` starts at the same point as the canonical base lift `0 : ℝ`
through `Real.fourierChar`. -/
-- Proof sketch: use the source condition `γ.source : γ 0 = 1` and identify
-- `Real.fourierChar 0` with `1 : Circle`.
theorem circle_path_start_eq_fourierChar_zero {y : Circle} (γ : Path (1 : Circle) y) :
    γ.toContinuousMap 0 = Real.fourierChar 0 := by
  simp [γ.source]

/-- Lemma 1.5.6: every path in `S^1` starting at `1` has a unique lift to `ℝ` starting at `0`
through the covering map `Real.fourierChar x = e^{2πix}`. -/
-- Proof sketch: apply the unique lifting theorem for the covering map
-- `real_fourierChar_isCoveringMap` to the path `f`, with the prescribed initial lift `0`.
theorem existsUnique_fourierChar_lift_of_circle_path {y : Circle} (f : Path (1 : Circle) y) :
    ∃! g : C(I, ℝ), (Real.fourierChar ∘ g : I → Circle) = f ∧ g 0 = 0 := by
  have hf0 := circle_path_start_eq_fourierChar_zero f
  refine
    ⟨real_fourierChar_isCoveringMap.liftPath f.toContinuousMap 0 hf0, ?_, ?_⟩
  · constructor
    · change
        Real.fourierChar ∘ ⇑(real_fourierChar_isCoveringMap.liftPath f.toContinuousMap 0 hf0) =
          ⇑f.toContinuousMap
      exact real_fourierChar_isCoveringMap.liftPath_lifts f.toContinuousMap 0 hf0
    · exact real_fourierChar_isCoveringMap.liftPath_zero f.toContinuousMap 0 hf0
  · intro g hg
    refine (real_fourierChar_isCoveringMap.eq_liftPath_iff' hf0).2 ?_
    refine ⟨?_, hg.2⟩
    change Real.fourierChar ∘ ⇑g = ⇑f.toContinuousMap
    simpa using hg.1

/-! ### Lemma_1_5_7 (from Chap01) -/
noncomputable section

open scoped unitInterval

/-- Lemma 1.5.7: homotopic loops in `S¹` based at `1` have canonical lifts through
`Real.fourierChar : ℝ → S¹` starting at `0`, and these lifts end at the same point of `ℝ`. -/
-- Proof sketch: unpack `γ₀.Homotopic γ₁` as an endpoint-fixed homotopy of continuous maps and
-- apply `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` to the covering map
-- `real_fourierChar_isCoveringMap` with initial lift `0`.
theorem fourierChar_lift_endpoint_eq_of_homotopic_loops
    (γ₀ γ₁ : Path (1 : Circle) 1) (h : γ₀.Homotopic γ₁) :
    real_fourierChar_isCoveringMap.liftPath γ₀.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ₀) 1 =
      real_fourierChar_isCoveringMap.liftPath γ₁.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ₁) 1 := by
  obtain ⟨H⟩ := h
  exact real_fourierChar_isCoveringMap.liftPath_apply_one_eq_of_homotopicRel ⟨H⟩ 0
    (circle_path_start_eq_fourierChar_zero γ₀) (circle_path_start_eq_fourierChar_zero γ₁)

/-! ### Definition_1_5_8 (from Chap01) -/
noncomputable section

open scoped unitInterval

/-- The basepoint `0 : ℝ` lies in the fiber of `Real.fourierChar` over `1 : Circle`. -/
-- Proof sketch: evaluate `Real.fourierChar` at `0` and simplify to `1`.
theorem mem_fourierChar_unit_fiber_zero :
    (0 : ℝ) ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) := by
  -- Evaluating `Real.fourierChar` at `0` lands at the basepoint of the circle.
  simp

/-- The canonical endpoint of the lift of a based loop class in `S¹` through
`Real.fourierChar : ℝ → S¹`, starting at `0`. -/
def circleFundamentalGroupLiftEndpoint
    (γ : FundamentalGroup Circle (1 : Circle)) :
    Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) :=
  real_fourierChar_isCoveringMap.monodromy (FundamentalGroup.toPath γ)
    ⟨0, mem_fourierChar_unit_fiber_zero⟩

/-- Definition 1.5.8: the map `j : π₁(S^1, 1) → ℤ` sends a loop class to the integer endpoint of
the unique lift through `Real.fourierChar : ℝ → S¹` starting at `0`. -/
def circleFundamentalGroupLiftIndex
    (γ : FundamentalGroup Circle (1 : Circle)) : ℤ :=
  Int.floor (circleFundamentalGroupLiftEndpoint γ : ℝ)

/-- Helper for Definition 1.5.8: a point of the fiber of `Real.fourierChar` over `1` is an
integer, so taking its floor recovers it exactly. -/
lemma floor_eq_self_of_mem_fourierChar_unit_fiber (x : ℝ)
    (hx : x ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle)) :
    ((Int.floor x : ℤ) : ℝ) = x := by
  -- Rewrite fiber membership as an equation in `Circle.exp`.
  exact (Int.floor_eq_self_iff_mem x).2 <| by
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [Real.fourierChar_apply'] at hx
    rcases (Circle.exp_eq_one).1 hx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Cancel the nonzero factor `2 * π` to identify the endpoint with the integer `n`.
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
      positivity
    have hx_eq := congrArg (fun t : ℝ => t / (2 * Real.pi)) hn
    simp [h2pi] at hx_eq
    simpa using hx_eq.symm

/-- The canonical lifted endpoint is the endpoint of the lifted representative loop starting
at `0`. -/
-- Proof sketch: unfold `circleFundamentalGroupLiftEndpoint`, evaluate monodromy on the path class
-- of `γ`, and identify the result with the endpoint of `real_fourierChar_isCoveringMap.liftPath`.
theorem circleFundamentalGroupLiftEndpoint_spec (γ : Path (1 : Circle) 1) :
    (circleFundamentalGroupLiftEndpoint (FundamentalGroup.fromPath ⟦γ⟧) : ℝ) =
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ) 1 := by
  -- Monodromy on the path class is definitionally the endpoint of the lifted path.
  rfl

/-- The lift index of a loop class is the endpoint of the lifted representative loop starting
at `0`. -/
-- Proof sketch: combine `circleFundamentalGroupLiftEndpoint_spec` with the fact that the lifted
-- endpoint lies in the unit fiber of `Real.fourierChar`, hence is an integer.
theorem circleFundamentalGroupLiftIndex_spec (γ : Path (1 : Circle) 1) :
    ((circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ⟧) : ℤ) : ℝ) =
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ) 1 := by
  -- Rewrite the index through the concrete lifted endpoint supplied by monodromy.
  rw [circleFundamentalGroupLiftIndex, circleFundamentalGroupLiftEndpoint_spec]
  -- The endpoint remains in the unit fiber, so the floor lemma recovers it exactly.
  exact floor_eq_self_of_mem_fourierChar_unit_fiber _
    (circleFundamentalGroupLiftEndpoint (FundamentalGroup.fromPath ⟦γ⟧)).2

/-! ### Lemma_1_5_9 (from Chap01) -/
noncomputable section

open FundamentalGroup
open scoped unitInterval

/-- Helper for Lemma 1.5.9: the lift-index map on `π₁(S¹, 1)` depends only on the homotopy
class of the chosen loop. -/
-- Proof sketch: use `FundamentalGroup.fromPath_eq_iff_homotopic` to identify the two loop
-- classes, then apply `circleFundamentalGroupLiftIndex` to that equality.
theorem circleFundamentalGroupLiftIndex_eq_of_homotopic_loops
    (γ₀ γ₁ : Path (1 : Circle) 1) (h : γ₀.Homotopic γ₁) :
    circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ₀⟧) =
      circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ₁⟧) := by
  apply congrArg circleFundamentalGroupLiftIndex
  exact (FundamentalGroupoid.fromPath_eq_iff_homotopic γ₀ γ₁).2 h

/-- Lemma 1.5.9: the lift-index map `j` is well defined on loop classes in `π₁(S¹, 1)`, and on
the standard loop `f_n` it returns the integer `n`. -/
-- Proof sketch: identify `j([f_n])` with the endpoint of the canonical lift of `f_n` via
-- `circleFundamentalGroupLiftIndex_spec`, then evaluate that lift using `standardLoopLift_apply`
-- at `1` to obtain the endpoint `n`.
theorem circleFundamentalGroupLiftIndex_standardLoop (n : ℤ) :
    circleFundamentalGroupLiftIndex (standardLoopClass n) = n := by
  have hlift :
      standardLoopLift n =
        real_fourierChar_isCoveringMap.liftPath (standardLoop n).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (standardLoop n)) := by
    apply (real_fourierChar_isCoveringMap.eq_liftPath_iff'
      (circle_path_start_eq_fourierChar_zero (standardLoop n))).2
    constructor
    · ext s
      exact congrArg Subtype.val (standardLoop_factors_through_fourierChar n s).symm
    · simp [standardLoopLift]
  have hlift_apply :
      real_fourierChar_isCoveringMap.liftPath (standardLoop n).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (standardLoop n)) 1 =
        standardLoopLift n 1 := by
    simpa using DFunLike.congr_fun hlift.symm 1
  have hspec :
      ((circleFundamentalGroupLiftIndex (standardLoopClass n) : ℤ) : ℝ) =
        standardLoopLift n 1 := by
    simpa [standardLoopClass] using
      (circleFundamentalGroupLiftIndex_spec (standardLoop n)).trans hlift_apply
  have hendpoint : standardLoopLift n 1 = (n : ℝ) := by
    rw [standardLoopLift_apply n 1]
    norm_num
  exact Int.cast_injective <| hspec.trans hendpoint

/-! ### Lemma_1_5_10 (from Chap01) -/
noncomputable section

open Path.Homotopic.Quotient

/-- Lemma 1.5.10: the lift-index map `j : π₁(S¹, 1) → ℤ`, represented by
`circleFundamentalGroupLiftIndex`, is injective. -/
-- Proof sketch: represent loop classes by actual loops, lift both loops through the covering map
-- `Real.fourierChar : ℝ → S¹` starting at `0`, and use equality of lift indices to identify their
-- endpoints. Since `ℝ` is simply connected, the two lifted paths are homotopic; mapping that
-- homotopy down to `S¹` shows the original loops are homotopic.
theorem circleFundamentalGroupLiftIndex_injective :
    Function.Injective circleFundamentalGroupLiftIndex := by
  change Function.Injective
    (fun γ : Path.Homotopic.Quotient (1 : Circle) (1 : Circle) ↦
      circleFundamentalGroupLiftIndex γ)
  intro γ₀ γ₁ hγ
  revert hγ
  refine Quotient.inductionOn₂ γ₀ γ₁ ?_
  intro p₀ p₁ h
  let expMap : C(ℝ, Circle) := ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  let g₀ : Path (0 : ℝ) ((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ) :=
    { toContinuousMap :=
        real_fourierChar_isCoveringMap.liftPath p₀.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₀)
      source' := by
        simpa using real_fourierChar_isCoveringMap.liftPath_zero p₀.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₀)
      target' := by
        symm
        simpa using circleFundamentalGroupLiftIndex_spec p₀ }
  let g₁ : Path (0 : ℝ) ((circleFundamentalGroupLiftIndex ⟦p₁⟧ : ℤ) : ℝ) :=
    { toContinuousMap :=
        real_fourierChar_isCoveringMap.liftPath p₁.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₁)
      source' := by
        simpa using real_fourierChar_isCoveringMap.liftPath_zero p₁.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₁)
      target' := by
        symm
        simpa using circleFundamentalGroupLiftIndex_spec p₁ }
  have hcast :
      (((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ)) =
        (((circleFundamentalGroupLiftIndex ⟦p₁⟧ : ℤ) : ℝ)) := by
    exact congrArg (fun n : ℤ ↦ (n : ℝ)) h
  let g₁' : Path (0 : ℝ) ((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ) :=
    Path.cast g₁ rfl hcast
  have hhom : g₀.Homotopic g₁' := SimplyConnectedSpace.paths_homotopic g₀ g₁'
  have hstart : expMap 0 = (1 : Circle) := by
    simp [expMap]
  have hend : expMap (((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ)) = (1 : Circle) := by
    change Real.fourierChar (((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ)) = (1 : Circle)
    simpa [Real.fourierChar_apply', mul_assoc, mul_comm, mul_left_comm] using
      Circle.exp_two_pi_mul_int (circleFundamentalGroupLiftIndex ⟦p₀⟧)
  have hmap :
      (Path.cast (g₀.map expMap.continuous) hstart.symm hend.symm).Homotopic
        (Path.cast (g₁'.map expMap.continuous) hstart.symm hend.symm) := by
    simpa [hstart, hend] using Path.Homotopic.map hhom expMap
  have hg₀ : Path.cast (g₀.map expMap.continuous) hstart.symm hend.symm = p₀ := by
    apply Path.ext
    funext s
    exact congrFun (real_fourierChar_isCoveringMap.liftPath_lifts p₀.toContinuousMap 0
      (circle_path_start_eq_fourierChar_zero p₀)) s
  have hg₁ : Path.cast (g₁'.map expMap.continuous) hstart.symm hend.symm = p₁ := by
    apply Path.ext
    funext s
    change Real.fourierChar (g₁ s) = p₁ s
    exact congrFun (real_fourierChar_isCoveringMap.liftPath_lifts p₁.toContinuousMap 0
      (circle_path_start_eq_fourierChar_zero p₁)) s
  rw [← hg₀, ← hg₁]
  exact eq.2 hmap

/-! ### Theorem_1_5_11 (from Chap01) -/
noncomputable section

open FundamentalGroup

/-- The standard loop class `standardLoopClass 1` generates `π₁(S¹, 1)`. -/
theorem standardLoopClass_one_zpowers_eq_top :
    Subgroup.zpowers (standardLoopClass 1 : FundamentalGroup Circle 1) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun γ ↦ ?_
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨circleFundamentalGroupLiftIndex γ, ?_⟩
  apply circleFundamentalGroupLiftIndex_injective
  rw [standardLoopClass_one_zpow, circleFundamentalGroupLiftIndex_standardLoop]

instance : Infinite (FundamentalGroup Circle 1) := by
  have hstandardLoopClass : Function.Injective standardLoopClass := by
    intro m n h
    have hindex := congrArg circleFundamentalGroupLiftIndex h
    change
      circleFundamentalGroupLiftIndex (standardLoopClass m) =
        circleFundamentalGroupLiftIndex (standardLoopClass n) at hindex
    rwa [circleFundamentalGroupLiftIndex_standardLoop, circleFundamentalGroupLiftIndex_standardLoop]
      at hindex
  exact Infinite.of_injective standardLoopClass hstandardLoopClass

/- Theorem 1.5.11: the canonical infinite-cyclic owner `intEquivOfZPowersEqTop` specializes the
generator theorem above to identify `π₁(S¹, 1)` with `Multiplicative ℤ`. -/
#check
  (intEquivOfZPowersEqTop (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top :
    Multiplicative ℤ ≃* FundamentalGroup Circle (1 : Circle))

/- Evaluation of the canonical equivalence is already the owner theorem
`intEquivOfZPowersEqTop_apply`; combined with `standardLoopClass_one_zpow`, it sends
`Multiplicative.ofAdd n` to `standardLoopClass n`. -/
#check
  (intEquivOfZPowersEqTop_apply (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top :
    ∀ a : Multiplicative ℤ,
      intEquivOfZPowersEqTop (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top a =
        standardLoopClass 1 ^ Multiplicative.toAdd a)

#print standardLoopClass_one_zpowers_eq_top
