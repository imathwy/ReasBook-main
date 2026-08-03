import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap17.Proposition_17_7

-- Semantic search tooling was unavailable in this session; the statement surface follows the
-- local differentiability API already used in Proposition 17.7.

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfStrictlyConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The strict first-order lower-support inequality on the effective domain associated to a
Gâteaux derivative field `DT`. -/
def StrictGateauxSupportInequalityOn
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ) : Prop :=
  ∀ x ∈ effectiveDomain f, ∀ y ∈ effectiveDomain f, x ≠ y →
    DT y (x - y) + (f y : EReal).toReal < (f x : EReal).toReal

/-- The derivative field `DT` is strictly monotone on `U` when every distinct pair of points of
`U` has strictly positive monotonicity pairing. -/
def StrictGateauxDerivativeMonotoneOn
    (DT : H → H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x ≠ y → 0 < (DT x - DT y) (x - y)

/-- The second derivative field `A₂` is positive on `U` when each of its quadratic forms is
strictly positive on every nonzero direction at every point of `U`. -/
def GateauxSecondDerivativePositiveOn
    (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ z : H, z ≠ 0 → 0 < A₂ x z z

/-- Helper for Proposition 17.10: subtracting two points on the same affine segment factors
through the segment direction. -/
private lemma lineMap_sub_lineMap_eq_smul_sub
    (x y : H) (s t : ℝ) :
    AffineMap.lineMap y x s - AffineMap.lineMap y x t = (s - t) • (x - y) := by
  -- Expand both affine-segment points around the same base point and collect the scalar factor.
  calc
    AffineMap.lineMap y x s - AffineMap.lineMap y x t
        = (s • (x - y) + y) - (t • (x - y) + y) := by
            rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    _ = s • (x - y) - t • (x - y) := by
          simp
    _ = (s - t) • (x - y) := by
          rw [sub_smul]

/-- Helper for Proposition 17.10: distinct parameters on a nondegenerate affine segment give
distinct points. -/
private lemma lineMap_apply_ne_of_ne
    {x y : H} (hxy : x ≠ y) {s t : ℝ} (hst : s ≠ t) :
    AffineMap.lineMap y x s ≠ AffineMap.lineMap y x t := by
  intro hEq
  have hsmul : (s - t) • (x - y) = 0 := by
    calc
      (s - t) • (x - y)
          = AffineMap.lineMap y x s - AffineMap.lineMap y x t := by
              symm
              simpa using lineMap_sub_lineMap_eq_smul_sub x y s t
      _ = 0 := by simpa [hEq]
  have hsub : x - y = 0 := by
    exact (smul_eq_zero.mp hsmul).resolve_left (sub_ne_zero.mpr hst)
  exact hxy (sub_eq_zero.mp hsub)

/-- Helper for Proposition 17.10: a Gâteaux derivative field differentiates every translated
segment trace at an arbitrary parameter. -/
private lemma segment_curve_hasDerivAt
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x h : H} {t : ℝ}
    (hGateaux : HasGateauxDerivativeOn T DT U) (ht : x + t • h ∈ U) :
    HasDerivAt (fun s : ℝ ↦ T (x + s • h)) (DT (x + t • h) h) t := by
  let path : ℝ → K := fun s ↦ T ((x + t • h) + s • h)
  have hline : HasDerivAt path (DT (x + t • h) h) 0 := by
    -- Recenter the line derivative at time `t` and invoke the Gâteaux hypothesis there.
    simpa [HasLineDerivAt, path] using
      (HasGateauxDerivativeWithinAt.hasLineDerivAt (hGateaux (x + t • h) ht) h)
  have hline_shift : HasDerivAt path (DT (x + t • h) h) (-t + t) := by
    simpa using hline
  -- Shift the recentered derivative statement back to the original parameter `t`.
  simpa [path, add_assoc, add_left_comm, add_comm, add_smul, smul_add, mul_comm,
    mul_left_comm, mul_assoc, one_smul] using
    HasDerivAt.comp_const_add (-t) t hline_shift

/-- Helper for Proposition 17.10: the scalar trace of the derivative field along a segment has the
expected second-derivative formula. -/
private lemma line_derivative_trace_hasDerivAt
    (DT : H → H →L[ℝ] ℝ) (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ)
    {U : Set H} (hA₂ : HasGateauxDerivativeOn DT A₂ U)
    {x y : H} {t : ℝ} (ht : AffineMap.lineMap y x t ∈ U) :
    HasDerivAt (fun s : ℝ ↦ DT (AffineMap.lineMap y x s) (x - y))
      (A₂ (AffineMap.lineMap y x t) (x - y) (x - y)) t := by
  have ht' : y + t • (x - y) ∈ U := by
    simpa [AffineMap.lineMap_apply_module', add_comm] using ht
  have hop :
      HasDerivAt (fun s : ℝ ↦ DT (AffineMap.lineMap y x s))
        (A₂ (AffineMap.lineMap y x t) (x - y)) t := by
    -- Differentiate the operator-valued segment trace before evaluating it at the fixed chord.
    simpa [AffineMap.lineMap_apply_module', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using (segment_curve_hasDerivAt (T := DT) (DT := A₂) (U := U)
        (x := y) (h := x - y) hA₂ ht')
  -- Apply the differentiated operator trace to the fixed segment direction.
  simpa using hop.clm_apply (hasDerivAt_const t (x - y))

/-- Helper for Proposition 17.10: strict convexity implies ordinary convexity on the effective
domain. -/
private lemma convexOn_effectiveDomain_of_strictlyConvex
    (f : H → Set.Ioi (⊥ : EReal)) (hproper : IsProper f.asEReal) (hstrict : StrictlyConvex f) :
    ConvexOn f (effectiveDomain f) := by
  refine ⟨by simpa [effectiveDomain, dom] using hproper.2, subset_rfl, ?_⟩
  intro x hx y hy α hα0 hα1
  by_cases hxy : x = y
  · -- Equal endpoints collapse the strict Jensen expression to equality.
    subst y
    have hcombo : α • x + (1 - α) • x = x := by
      calc
        α • x + (1 - α) • x = (α + (1 - α)) • x := by rw [add_smul]
        _ = x := by simp
    have hα_nonneg : 0 ≤ (α : EReal) := by
      exact_mod_cast hα0.le
    have hβ_nonneg : 0 ≤ ((1 - α : ℝ) : EReal) := by
      exact_mod_cast (sub_nonneg.mpr hα1.le)
    have hsum : (α : EReal) + (1 - α : EReal) = 1 := by
      have hsum_real : α + (1 - α : ℝ) = 1 := by
        ring
      exact_mod_cast hsum_real
    have hweight :
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f x : EReal) = (f x : EReal) := by
      calc
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f x : EReal)
            = ((α : EReal) + (1 - α : EReal)) * (f x : EReal) := by
                symm
                exact EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg
        _ = (f x : EReal) := by rw [hsum, one_mul]
    have hvalue : (f (α • x + (1 - α) • x) : EReal) = (f x : EReal) := by
      exact congrArg (fun t : H ↦ (f t : EReal)) hcombo
    calc
      (f (α • x + (1 - α) • x) : EReal) = (f x : EReal) := hvalue
      _ ≤ (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f x : EReal) := by
        rw [hweight]
  · -- Distinct points satisfy the stronger strict Jensen inequality.
    exact le_of_lt (hstrict.ineq hx hy hxy hα0 hα1)

/-- Helper for Proposition 17.10: a weighted sum of finite endpoint values is the corresponding
real cast after applying `toReal`. -/
private lemma weighted_value_sum_eq_coe_toReal
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (α : ℝ) :
    (((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) =
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsub_cast : (((1 - α : ℝ) : EReal)) = 1 - (α : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  calc
    (((α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal : ℝ)) : EReal)
        = (α : EReal) * (((f x : EReal).toReal : ℝ) : EReal) +
            (((1 - α : ℝ) : EReal)) * (((f y : EReal).toReal : ℝ) : EReal) := by
              rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ = (α : EReal) * (((f x : EReal).toReal : ℝ) : EReal) +
          (1 - α : EReal) * (((f y : EReal).toReal : ℝ) : EReal) := by
            rw [hsub_cast]
    _ = (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
          rw [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot]

/-- Proposition 17.10 (1): on an open convex effective domain, strict convexity of `f` is
equivalent to the strict first-order lower-support inequality for a Gâteaux derivative field
`DT` of `x ↦ (f x : EReal).toReal` on `effectiveDomain f`. -/
theorem strictlyConvex_iff_strictGateauxSupportInequalityOn_of_open_convex_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hproper : IsProper f.asEReal)
    (hopen : IsOpen (effectiveDomain f))
    (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f)) :
    StrictlyConvex f ↔ StrictGateauxSupportInequalityOn f DT := by
  constructor
  · intro hstrict
    have hdom : (effectiveDomain f).Nonempty := by
      simpa [effectiveDomain, dom] using hproper.2
    have htfae :=
      convex_tfae_of_open_convex_effectiveDomain f DT hdom hopen hconv hDT
    have hconvf : ConvexOn f (effectiveDomain f) :=
      convexOn_effectiveDomain_of_strictlyConvex f hproper hstrict
    have hsupport : GateauxSupportInequalityOn f DT :=
      (List.TFAE.out htfae.1 0 1).mp hconvf
    intro x hx y hy hxy
    have hweak := hsupport x hx y hy
    by_contra hnot
    have hEq : DT y (x - y) + (f y : EReal).toReal = (f x : EReal).toReal := by
      exact le_antisymm hweak (le_of_not_gt hnot)
    let z : H := AffineMap.lineMap y x (1 / 2 : ℝ)
    have hz : z ∈ effectiveDomain f := by
      -- The midpoint stays in the convex effective domain.
      simpa [z] using hconv.lineMap_mem hy hx (by constructor <;> norm_num)
    have hz_support : DT y (z - y) + (f y : EReal).toReal ≤ (f z : EReal).toReal :=
      hsupport z hz y hy
    have hz_sub : z - y = (1 / 2 : ℝ) • (x - y) := by
      -- The midpoint displacement from `y` is half of the full chord.
      simpa [z] using lineMap_sub_lineMap_eq_smul_sub x y (1 / 2 : ℝ) 0
    have hz_real :
        (1 / 2 : ℝ) * (f x : EReal).toReal +
            (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal ≤
          (f z : EReal).toReal := by
      have hz_dir : DT y (z - y) = (1 / 2 : ℝ) * DT y (x - y) := by
        -- Linearity turns the midpoint displacement into a scalar multiple of the endpoint chord.
        simpa [hz_sub, smul_eq_mul] using congrArg (fun v : H ↦ DT y v) hz_sub
      linarith
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hz_ereal :
        (((1 / 2 : ℝ) * (f x : EReal).toReal +
            (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal : ℝ) : EReal) ≤
          (f z : EReal) := by
      have hz_cast :
          (((1 / 2 : ℝ) * (f x : EReal).toReal +
              (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal : ℝ) : EReal) ≤
            (((f z : EReal).toReal : ℝ) : EReal) := by
        exact_mod_cast hz_real
      simpa [EReal.coe_toReal hz_top hz_bot] using hz_cast
    have hstrict_mid0 :
        (f z : EReal) <
          (1 / 2 : EReal) * (f x : EReal) + (1 - (1 / 2 : ℝ) : EReal) * (f y : EReal) := by
      -- First state strict convexity in the native `EReal` weighted-sum form.
      simpa [z, AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
        (hstrict.ineq (x := x) (y := y) (α := (1 / 2 : ℝ)) hx hy hxy
          (by norm_num) (by norm_num))
    have hstrict_mid :
        (f z : EReal) <
          (((1 / 2 : ℝ) * (f x : EReal).toReal +
              (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal : ℝ) : EReal) := by
      -- Then rewrite the weighted `EReal` sum as a cast of the real midpoint average.
      exact hstrict_mid0.trans_eq
        (weighted_value_sum_eq_coe_toReal (f := f) hx hy (1 / 2 : ℝ)).symm
    exact (not_lt_of_ge hz_ereal) hstrict_mid
  · intro hsupport
    intro x hx y hy hxy α hα0 hα1
    let z : H := AffineMap.lineMap y x α
    have hz : z ∈ effectiveDomain f := by
      -- Convexity keeps the Jensen point inside the effective domain.
      simpa [z] using hconv.lineMap_mem hy hx ⟨hα0.le, hα1.le⟩
    have hxz : x ≠ z := by
      -- Distinct segment parameters stay distinct because the chord is nonzero.
      simpa [z] using
        (lineMap_apply_ne_of_ne (x := x) (y := y) hxy (show α ≠ 1 from hα1.ne)).symm
    have hyz : y ≠ z := by
      -- The same injectivity argument rules out `y = z`.
      simpa [z] using
        lineMap_apply_ne_of_ne (x := x) (y := y) hxy (show (0 : ℝ) ≠ α from ne_of_lt hα0)
    have hx_support : DT z (x - z) + (f z : EReal).toReal < (f x : EReal).toReal :=
      hsupport x hx z hz hxz
    have hy_support : DT z (y - z) + (f z : EReal).toReal < (f y : EReal).toReal :=
      hsupport y hy z hz hyz
    have hx_scaled :
        α * (DT z (x - z) + (f z : EReal).toReal) < α * (f x : EReal).toReal :=
      mul_lt_mul_of_pos_left hx_support hα0
    have hy_scaled :
        (1 - α) * (DT z (y - z) + (f z : EReal).toReal) <
          (1 - α) * (f y : EReal).toReal :=
      mul_lt_mul_of_pos_left hy_support (sub_pos.mpr hα1)
    have hxz_sub : x - z = (1 - α) • (x - y) := by
      -- The displacement from `z` to `x` is the remaining segment weight times the chord.
      simpa [z] using lineMap_sub_lineMap_eq_smul_sub x y 1 α
    have hyz_sub : y - z = (0 - α) • (x - y) := by
      -- The displacement from `z` to `y` points in the opposite chord direction.
      simpa [z] using lineMap_sub_lineMap_eq_smul_sub x y 0 α
    have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
      -- The two weighted displacements from the Jensen point cancel exactly.
      calc
        α • (x - z) + (1 - α) • (y - z)
            = α • ((1 - α) • (x - y)) + (1 - α) • ((0 - α) • (x - y)) := by
                rw [hxz_sub, hyz_sub]
        _ = (α * (1 - α) + (1 - α) * (0 - α)) • (x - y) := by
              rw [smul_smul, smul_smul, add_smul]
        _ = 0 := by
              ring_nf
              simp
    have hcancel :
        α * DT z (x - z) + (1 - α) * DT z (y - z) = 0 := by
      -- Apply the linear derivative functional to the cancelling vector identity.
      have := congrArg (fun v : H ↦ DT z v) hcancel_vec
      simpa [map_add, smul_eq_mul] using this
    have hstrict_real :
        (f z : EReal).toReal <
          α * (f x : EReal).toReal + (1 - α) * (f y : EReal).toReal := by
      linarith
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hstrict_ereal :
        (f z : EReal) <
          (((α * (f x : EReal).toReal +
              (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) := by
      have hstrict_cast :
          (((f z : EReal).toReal : ℝ) : EReal) <
            (((α * (f x : EReal).toReal +
                (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) := by
        exact_mod_cast hstrict_real
      simpa [EReal.coe_toReal hz_top hz_bot] using hstrict_cast
    -- Convert the strict real inequality back to the `EReal` Jensen inequality.
    have hz_eq : α • x + (1 - α) • y = z := by
      simpa [z, AffineMap.lineMap_apply_module, add_comm] using
        (AffineMap.lineMap_apply_module (p := y) (q := x) (c := α)).symm
    calc
      (f (α • x + (1 - α) • y) : EReal) = (f z : EReal) := by rw [hz_eq]
      _ < (((α * (f x : EReal).toReal +
            (1 - α) * (f y : EReal).toReal : ℝ)) : EReal) := hstrict_ereal
      _ = (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
            exact weighted_value_sum_eq_coe_toReal (f := f) hx hy α

/-- Proposition 17.10 (2): on an open convex effective domain, the strict first-order
lower-support inequality for `DT` is equivalent to strict monotonicity of `DT` on
`effectiveDomain f`. -/
theorem strict_support_iff_strict_monotone_of_open_convex_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hproper : IsProper f.asEReal)
    (hopen : IsOpen (effectiveDomain f))
    (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f)) :
    StrictGateauxSupportInequalityOn f DT ↔
      StrictGateauxDerivativeMonotoneOn DT (effectiveDomain f) := by
  constructor
  · intro hsupport
    intro x hx y hy hxy
    have hxy_support := hsupport x hx y hy hxy
    have hyx_support := hsupport y hy x hx hxy.symm
    have hsum : DT y (x - y) + DT x (y - x) < 0 := by
      linarith
    have hpair_real : 0 < DT x (x - y) - DT y (x - y) := by
      have hneg : DT y (x - y) - DT x (x - y) < 0 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
      linarith
    -- Adding the two strict support inequalities cancels the function values and leaves the
    -- strict monotonicity pairing.
    simpa [ContinuousLinearMap.sub_apply, sub_eq_add_neg] using hpair_real
  · intro hstrictMono
    have hdom : (effectiveDomain f).Nonempty := by
      simpa [effectiveDomain, dom] using hproper.2
    have htfae :=
      convex_tfae_of_open_convex_effectiveDomain f DT hdom hopen hconv hDT
    have hmono : GateauxDerivativeMonotoneOn DT (effectiveDomain f) := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst y
        simp [ContinuousLinearMap.sub_apply, sub_eq_add_neg]
      · exact (hstrictMono x hx y hy hxy).le
    have hconvf : ConvexOn f (effectiveDomain f) :=
      (List.TFAE.out htfae.1 2 0).mp hmono
    have hsupport : GateauxSupportInequalityOn f DT :=
      (List.TFAE.out htfae.1 2 1).mp hmono
    intro x hx y hy hxy
    have hweak := hsupport x hx y hy
    by_contra hnot
    have hEq : DT y (x - y) + (f y : EReal).toReal = (f x : EReal).toReal := by
      exact le_antisymm hweak (le_of_not_gt hnot)
    let z : H := AffineMap.lineMap y x (1 / 2 : ℝ)
    have hz : z ∈ effectiveDomain f := by
      -- The midpoint remains in the convex effective domain.
      simpa [z] using hconv.lineMap_mem hy hx (by constructor <;> norm_num)
    have hyz : y ≠ z := by
      -- The midpoint differs from the left endpoint because the segment is nondegenerate.
      simpa [z] using
        lineMap_apply_ne_of_ne (x := x) (y := y) hxy (show (0 : ℝ) ≠ (1 / 2 : ℝ) by norm_num)
    have hz_support_from_y : DT y (z - y) + (f y : EReal).toReal ≤ (f z : EReal).toReal :=
      hsupport z hz y hy
    have hz_support_from_z : DT z (x - z) + (f z : EReal).toReal ≤ (f x : EReal).toReal :=
      hsupport x hx z hz
    have hz_sub : z - y = (1 / 2 : ℝ) • (x - y) := by
      -- The midpoint displacement from `y` is half the full chord.
      simpa [z] using lineMap_sub_lineMap_eq_smul_sub x y (1 / 2 : ℝ) 0
    have hxz_sub : x - z = (1 / 2 : ℝ) • (x - y) := by
      -- The displacement from the midpoint to `x` is the same half-chord.
      have hxz_sub' : x - z = (1 - (1 / 2 : ℝ)) • (x - y) := by
        simpa [z] using lineMap_sub_lineMap_eq_smul_sub x y 1 (1 / 2 : ℝ)
      rw [hxz_sub']
      congr 1
      norm_num
    have hconv_real :
        _root_.ConvexOn ℝ (effectiveDomain f) (fun u ↦ (f u : EReal).toReal) :=
      ConvexOn.toReal_convexOn_effectiveDomain hconvf
    have hz_upper :
        (f z : EReal).toReal ≤
          (1 / 2 : ℝ) * (f x : EReal).toReal + (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal := by
      -- Ordinary convexity gives the midpoint upper bound.
      have hz_eq : z = (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y := by
        simpa [z, AffineMap.lineMap_apply_module, add_comm] using
          (AffineMap.lineMap_apply_module (p := y) (q := x) (c := (1 / 2 : ℝ)))
      rw [hz_eq]
      simpa [smul_eq_mul] using
        (hconv_real.2 hx hy (by norm_num : 0 ≤ (1 / 2 : ℝ))
          (by norm_num : 0 ≤ (1 - (1 / 2 : ℝ))) (by ring))
    have hz_lower :
        (1 / 2 : ℝ) * (f x : EReal).toReal + (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal ≤
          (f z : EReal).toReal := by
      -- Equality at `x` turns the support lower bound from `y` into the midpoint lower bound.
      have hz_dir : DT y (z - y) = (1 / 2 : ℝ) * DT y (x - y) := by
        simpa [hz_sub, smul_eq_mul] using congrArg (fun v : H ↦ DT y v) hz_sub
      linarith
    have hz_eq :
        (f z : EReal).toReal =
          (1 / 2 : ℝ) * (f x : EReal).toReal + (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal := by
      linarith
    have hmid_compare : DT z (x - y) ≤ DT y (x - y) := by
      -- The support inequality at `x` with base point `z` forces the midpoint derivative to be
      -- no larger than the endpoint derivative under the equality hypothesis.
      have hz_dir : DT z (x - z) = (1 / 2 : ℝ) * DT z (x - y) := by
        simpa [hxz_sub, smul_eq_mul] using congrArg (fun v : H ↦ DT z v) hxz_sub
      linarith
    have hstrict_mid :
        DT y (x - y) < DT z (x - y) := by
      -- Strict monotonicity between `y` and the midpoint gives the opposite strict inequality.
      have hpair :
          0 < (DT z - DT y) (z - y) := hstrictMono z hz y hy hyz.symm
      have hpair_real : 0 < DT z (x - y) - DT y (x - y) := by
        have hpair_half : 0 < (1 / 2 : ℝ) * (DT z (x - y) - DT y (x - y)) := by
          simpa [hz_sub, ContinuousLinearMap.sub_apply, smul_eq_mul] using hpair
        nlinarith
      linarith
    exact (not_lt_of_ge hmid_compare) hstrict_mid

/-- Proposition 17.10 (3): if `A₂` is a second Gâteaux derivative field for `DT` on the open
convex effective domain and its quadratic form is strictly positive on every nonzero direction,
then `DT` is strictly monotone there; together with (1) and (2), this yields clause (iv) implies
each of clauses (i), (ii), and (iii). -/
theorem strict_monotone_of_second_derivative_positive_of_open_convex_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hproper : IsProper f.asEReal)
    (hopen : IsOpen (effectiveDomain f))
    (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f))
    {A₂ : H → H →L[ℝ] H →L[ℝ] ℝ}
    (hA₂ : HasGateauxDerivativeOn DT A₂ (effectiveDomain f))
    (hpositive : GateauxSecondDerivativePositiveOn A₂ (effectiveDomain f)) :
    StrictGateauxDerivativeMonotoneOn DT (effectiveDomain f) := by
  intro x hx y hy hxy
  let k : ℝ → ℝ := fun t ↦ DT (AffineMap.lineMap y x t) (x - y)
  have hk_cont : ContinuousOn k (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- The derivative formula gives continuity of the one-dimensional trace on the whole segment.
    exact
      (HasDerivAt.continuousAt
        (line_derivative_trace_hasDerivAt (DT := DT) (A₂ := A₂) hA₂
          (x := x) (y := y) (t := t) (hconv.lineMap_mem hy hx ht))).continuousWithinAt
  have hk_pos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), 0 < deriv k t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    have hk_deriv :
        deriv k t = A₂ (AffineMap.lineMap y x t) (x - y) (x - y) := by
      -- Differentiate the scalar pairing trace and identify its derivative with the quadratic
      -- form of the second derivative field on the chord direction.
      simpa [k] using
        (line_derivative_trace_hasDerivAt (DT := DT) (A₂ := A₂) hA₂
          (x := x) (y := y) (t := t) (hconv.lineMap_mem hy hx ht')).deriv
    rw [hk_deriv]
    exact hpositive _ (hconv.lineMap_mem hy hx ht') _ (sub_ne_zero.mpr hxy)
  have hk_strict :
      StrictMonoOn k (Set.Icc (0 : ℝ) 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) hk_cont hk_pos
  have h01 : k 0 < k 1 := hk_strict (by simp) (by simp) zero_lt_one
  have hpair_real : 0 < DT x (x - y) - DT y (x - y) := by
    simpa [k, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using sub_pos.mpr h01
  -- Endpoint comparison of the strictly increasing pairing trace is exactly the desired
  -- strict monotonicity pairing.
  simpa [ContinuousLinearMap.sub_apply, sub_eq_add_neg] using hpair_real

end DifferentiabilityOfStrictlyConvexFunctions

end ERealFunction
