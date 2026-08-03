import Mathlib
import BauschkeLean.Chap16.Corollary_16_72
import BauschkeLean.Chap16.Example_16_62
import BauschkeLean.Chap11.Proposition_11_7
import BauschkeLean.Chap17.Proposition_17_21
import BauschkeLean.Chap17.Proposition_17_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

noncomputable section

section DifferentiabilityOfDistanceCompositions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- Classical decidability of membership in `C`, used to state the piecewise subdifferential
formula for compositions with the distance to `C`. -/
local instance instDecidablePredCompInfDistSet :
    DecidablePred (fun x : H ↦ x ∈ C) := Classical.decPred _

/-- Classical decidability of membership in `frontier C`, used to state the boundary branch of the
subdifferential formula for compositions with the distance to `C`. -/
local instance instDecidablePredCompInfDistFrontier :
    DecidablePred (fun x : H ↦ x ∈ frontier C) := Classical.decPred _

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

local notation "P" => P[C, hC_cheb]

-- Route correction: use the stable directional-derivative owner from Proposition 17.21 and
-- restore the one-sided scalar notation locally, avoiding the broken direct import of
-- Proposition 17.2 while keeping the source-facing theorem statement unchanged.
local notation:arg f "′₊(" x ")" => ERealFunction.directionalDerivative f x 1
local notation:arg f "′₋(" x ")" => -ERealFunction.directionalDerivative f x (-1)

/-- Helper for Example 17 33: the distance-to-set map is convex on the ambient Hilbert space for a
nonempty closed convex set. -/
lemma convexOn_univ_infDist_of_nonempty_isClosed_convex :
    (hC_nonempty' : C.Nonempty) → (hC_closed' : IsClosed C) → (hC_convex' : Convex ℝ C) →
    _root_.ConvexOn ℝ Set.univ (fun y : H ↦ Metric.infDist y C) := by
  intro hC_nonempty' hC_closed' hC_convex'
  let hC_cheb' := isChebyshev_of_nonempty_isClosed_convex hC_nonempty' hC_closed' hC_convex'
  let P' : H → H := P[C, hC_cheb']
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hPx : P' x ∈ C := projectionPoint_mem C hC_cheb' x
  have hPy : P' y ∈ C := projectionPoint_mem C hC_cheb' y
  have hcombo_mem : a • P' x + b • P' y ∈ C := hC_convex' hPx hPy ha hb hab
  have hdistx : Metric.infDist x C = ‖x - P' x‖ := by
    simpa [P', dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb' x).2.symm
  have hdisty : Metric.infDist y C = ‖y - P' y‖ := by
    simpa [P', dist_eq_norm] using (projectionPoint_isBestApproximation C hC_cheb' y).2.symm
  calc
    Metric.infDist (a • x + b • y) C
        ≤ dist (a • x + b • y) (a • P' x + b • P' y) := by
            exact Metric.infDist_le_dist_of_mem hcombo_mem
    _ = ‖a • (x - P' x) + b • (y - P' y)‖ := by
          simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ ‖a • (x - P' x)‖ + ‖b • (y - P' y)‖ := norm_add_le _ _
    _ = a * ‖x - P' x‖ + b * ‖y - P' y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a * Metric.infDist x C + b * Metric.infDist y C := by
          rw [hdistx, hdisty]

/-- Helper for Example 17 33: a real-valued convex function on all of `ℝ` remains convex after
coercion to the chapter's canonical `EReal`-valued owner. -/
lemma comp_distance_convexOn_toEReal_of_convexOn_univ
    (φ : ℝ → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    ConvexOn φ.toEReal (effectiveDomain φ.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Function.effectiveDomain_toEReal]
  · simp [Function.effectiveDomain_toEReal]
  · intro s hs t ht a ha0 ha1
    have hreal :
        φ (a • s + (1 - a) • t) ≤ a * φ s + (1 - a) * φ t := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by ring)
    change ((φ (a • s + (1 - a) • t) : ℝ) : EReal) ≤
      ((a * φ s + (1 - a) * φ t : ℝ) : EReal)
    exact_mod_cast hreal

/-- Helper for Example 17 33: a continuous convex real-valued function packages canonically
as a member of `Γ₀`. -/
lemma real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : ℝ → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Lower semicontinuity follows from continuity after coercing to `EReal`.
    simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · -- Convexity is the `toEReal` transport established above.
    exact comp_distance_convexOn_toEReal_of_convexOn_univ φ hconv

omit [CompleteSpace H] in
/-- Helper for Example 17 33: membership in the subdifferential of
`x ↦ φ (Metric.infDist x C)` is equivalent to the corresponding real-valued affine minorant
inequality. -/
lemma comp_distanceToSet_mem_subdifferential_iff_real
    (φ : ℝ → ℝ) {x u : H} :
    u ∈ (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u + φ (Metric.infDist x C) ≤ φ (Metric.infDist y C) := by
  rw [ERealFunction.mem_subdifferential_iff]
  constructor
  · intro hu y
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [Function.toEReal_apply, EReal.coe_add] using hu y
  · intro hu y
    exact EReal.coe_le_coe_iff.mpr <| by
      simpa [Function.toEReal_apply, EReal.coe_add] using hu y

/-- Helper for Example 17 33: the scalar hypothesis can be normalized to monotonicity on the
nonnegative ray. -/
lemma monotoneOn_nonnegative_of_monotoneOn_or_even
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ) :
    MonotoneOn φ (Set.Ici (0 : ℝ)) := by
  rcases hφ_mono_or_even with hφmono | hφeven
  · -- The given monotonicity branch already has the required shape.
    exact hφmono
  · have hconv_toEReal : ConvexOn φ.toEReal (effectiveDomain φ.toEReal) :=
      comp_distance_convexOn_toEReal_of_convexOn_univ φ hφconv
    have hEven_toEReal : Function.Even φ.toEReal.asEReal := by
      -- The `toEReal` and `asEReal` coercions preserve the source evenness pointwise.
      intro t
      simp [Function.asEReal_apply, Function.toEReal_apply, hφeven t]
    have hmono_toEReal :
        MonotoneOn φ.toEReal.asEReal (Set.Ici (0 : ℝ)) :=
      ERealFunction.monotoneOn_nonnegative_of_even_convexOn
        φ.toEReal hconv_toEReal hEven_toEReal
    intro s hs t ht hst
    -- Descend the `EReal` inequality back to the finite real branch.
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [Function.asEReal_apply, Function.toEReal_apply] using hmono_toEReal hs ht hst

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 17 33: monotonicity on the nonnegative ray restricts directly to the range
of the distance-to-set map because `Metric.infDist` is everywhere nonnegative. -/
lemma monotoneOn_infDist_range_of_monotoneOn_nonnegative
    (φ : ℝ → ℝ) (hφmono : MonotoneOn φ (Set.Ici (0 : ℝ))) :
    MonotoneOn φ (Set.range (fun y : H ↦ Metric.infDist y C)) := by
  intro a ha b hb hab
  rcases ha with ⟨ya, rfl⟩
  rcases hb with ⟨yb, rfl⟩
  exact hφmono
    (Metric.infDist_nonneg (x := ya) (s := C))
    (Metric.infDist_nonneg (x := yb) (s := C))
    hab

/-- Helper for Example 17 33: for a convex scalar function, differentiability identifies the
canonical right derivative with the ordinary derivative. -/
lemma scalar_right_derivative_eq_deriv_of_differentiableAt
    {φ : ℝ → ℝ} (hconv : ConvexOn φ.toEReal (effectiveDomain φ.toEReal)) {r : ℝ}
    (hφdiff : DifferentiableAt ℝ φ r) :
    (φ.toEReal)′₊(r) = (((deriv φ r : ℝ)) : EReal) := by
  have hline : HasLineDerivAt ℝ φ (deriv φ r) r (1 : ℝ) := by
    -- The one-dimensional Fréchet derivative gives the line derivative in direction `1`.
    simpa using hφdiff.hasDerivAt.hasFDerivAt.hasLineDerivAt (1 : ℝ)
  have hreal :
      Filter.Tendsto
        (fun t : ℝ ↦ ((((φ (r + t * 1) - φ r) / t : ℝ)) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((deriv φ r : ℝ)) : EReal)) := by
    -- Cast the real right-slope limit to `EReal`.
    exact EReal.tendsto_coe.2 <| by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hline.tendsto_slope_zero_right
  have hright : HasRightDerivativeAt φ.toEReal r (((deriv φ r : ℝ)) : EReal) := by
    refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
    -- Replace the `toEReal` quotient by the cast of the ordinary real quotient.
    refine Filter.Tendsto.congr' ?_ hreal
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro t _
    simp only [Function.toEReal_apply, smul_eq_mul]
    rw [← EReal.coe_sub, ← EReal.coe_div]
  -- Convexity upgrades the source derivative limit to the canonical right derivative owner.
  simpa [HasRightDerivativeAt] using
    (directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := φ.toEReal) hconv hright)

/-- Helper for Example 17 33: for a convex scalar function, differentiability identifies the
canonical left derivative with the ordinary derivative. -/
lemma scalar_left_derivative_eq_deriv_of_differentiableAt
    {φ : ℝ → ℝ} (hconv : ConvexOn φ.toEReal (effectiveDomain φ.toEReal)) {r : ℝ}
    (hφdiff : DifferentiableAt ℝ φ r) :
    (φ.toEReal)′₋(r) = (((deriv φ r : ℝ)) : EReal) := by
  have hline : HasLineDerivAt ℝ φ (-(deriv φ r)) r (-1 : ℝ) := by
    -- The same Fréchet derivative gives the line derivative in direction `-1`.
    simpa using hφdiff.hasDerivAt.hasFDerivAt.hasLineDerivAt (-1 : ℝ)
  have hreal :
      Filter.Tendsto
        (fun t : ℝ ↦ ((((φ (r + t * (-1)) - φ r) / t : ℝ)) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-(((deriv φ r : ℝ)) : EReal))) := by
    -- Cast the real line-derivative limit in direction `-1` to `EReal`.
    exact EReal.tendsto_coe.2 <| by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hline.tendsto_slope_zero_right
  have hleft : HasLeftDerivativeAt φ.toEReal r (((deriv φ r : ℝ)) : EReal) := by
    refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
    -- Match the source `toEReal` quotient with the cast real quotient along direction `-1`.
    refine Filter.Tendsto.congr' ?_ hreal
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro t _
    simp only [Function.toEReal_apply, smul_eq_mul]
    rw [← EReal.coe_sub, ← EReal.coe_div]
  have hdir :
      (φ.toEReal)′(r; -1) = -((((deriv φ r : ℝ)) : EReal)) :=
    directionalDerivative_eq_of_hasDirectionalDerivativeAt (f := φ.toEReal) hconv hleft
  -- The left derivative is the negated directional derivative in direction `-1`.
  simpa using congrArg Neg.neg hdir

/-- Helper for Example 17 33: at a scalar differentiability point, the subdifferential of
`φ.toEReal` is the singleton generated by the ordinary derivative. -/
lemma scalar_subdifferential_toEReal_eq_singleton_deriv
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ) {r : ℝ}
    (hφdiff : DifferentiableAt ℝ φ r) :
    (∂ φ.toEReal) r = ({deriv φ r} : Set ℝ) := by
  have hφconv_toEReal : ConvexOn φ.toEReal (effectiveDomain φ.toEReal) :=
    comp_distance_convexOn_toEReal_of_convexOn_univ φ hφconv
  have hr_mem : r ∈ effectiveDomain φ.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  -- Rewrite the scalar subdifferential as the interval between the one-sided derivatives.
  rw [subdifferential_eq_Icc_oneSidedDerivatives (f := φ.toEReal) (hconv := hφconv_toEReal) hr_mem]
  change Real.toEReal ⁻¹' Set.Icc ((φ.toEReal)′₋(r)) ((φ.toEReal)′₊(r)) =
    ({deriv φ r} : Set ℝ)
  rw [scalar_left_derivative_eq_deriv_of_differentiableAt hφconv_toEReal hφdiff]
  rw [scalar_right_derivative_eq_deriv_of_differentiableAt hφconv_toEReal hφdiff]
  ext a
  -- A degenerate interval with equal endpoints is exactly a singleton.
  simp [Set.mem_preimage]

/-- Helper for Example 17 33: once the scalar index set is a singleton, the indexed union of
scaled sets collapses to the corresponding scalar multiple. -/
lemma iUnion_smul_singleton_eq
    {E : Type*} [SMul ℝ E] (a : ℝ) (S : Set E) :
    (⋃ α ∈ ({a} : Set ℝ), α • S) = a • S := by
  ext x
  constructor
  · intro hx
    -- Membership in the double union forces the unique scalar index to be `a`.
    rcases Set.mem_iUnion.mp hx with ⟨α, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hα, hx⟩
    rcases Set.mem_singleton_iff.mp hα with hαeq
    simpa [hαeq] using hx
  · intro hx
    -- Conversely, the singleton index `a` witnesses membership in the union.
    exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨by simp, hx⟩⟩

omit [CompleteSpace H] in
/-- Helper for Example 17 33: on `interior C`, the distance vanishes on a neighborhood, so the
composition `x ↦ φ (Metric.infDist x C)` is locally constant and has subdifferential `{0}`. -/
lemma subdifferential_comp_distanceToSet_eq_singleton_zero_of_mem_interior
    (φ : ℝ → ℝ) (hφmono : MonotoneOn φ (Set.Ici (0 : ℝ)))
    {x : H} (hx : x ∈ interior C) :
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x = ({0} : Set H) := by
  have hxC : x ∈ C := interior_subset hx
  ext u
  constructor
  · intro hu
    rw [Set.mem_singleton_iff]
    by_cases hu0 : u = 0
    · exact hu0
    have hu_affine := (comp_distanceToSet_mem_subdifferential_iff_real (C := C) (φ := φ)
      (x := x) (u := u)).1 hu
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ε, hε_pos, hball⟩
    let t : ℝ := ε / (2 * ‖u‖)
    have ht_pos : 0 < t := by
      -- Choose the same symmetric perturbation used in the distance-only interior proof.
      dsimp [t]
      exact div_pos hε_pos (by positivity)
    have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have ht_mul_norm : t * ‖u‖ = ε / 2 := by
      calc
        t * ‖u‖ = ε / (2 * ‖u‖) * ‖u‖ := by rfl
        _ = ε / 2 := by
          field_simp [hu_norm_ne]
    have hplus_dist : dist (x + t • u) x < ε := by
      -- The forward perturbation stays inside the interior ball.
      rw [dist_eq_norm]
      have hplus_shift : x + t • u - x = t • u := by abel
      rw [hplus_shift, norm_smul, Real.norm_of_nonneg ht_pos.le, ht_mul_norm]
      linarith
    have hplus_mem : x + t • u ∈ C := by
      exact hball (by simpa [Metric.mem_ball] using hplus_dist)
    have hminus_dist : dist (x - t • u) x < ε := by
      -- The backward perturbation stays in the same interior ball.
      rw [dist_eq_norm]
      have hminus_shift : x - t • u - x = -(t • u) := by abel
      rw [hminus_shift, norm_neg, norm_smul, Real.norm_of_nonneg ht_pos.le, ht_mul_norm]
      linarith
    have hminus_mem : x - t • u ∈ C := by
      exact hball (by simpa [Metric.mem_ball] using hminus_dist)
    have hplus_nonpos : t * ‖u‖ ^ 2 ≤ 0 := by
      -- On `C`, the composition has the constant value `φ 0`, so the inner-product estimate
      -- collapses exactly as in Example 16.62.
      have htest := hu_affine (x + t • u)
      have hplus_shift : (x + t • u) - x = t • u := by abel
      rw [Metric.infDist_zero_of_mem hxC, Metric.infDist_zero_of_mem hplus_mem] at htest
      rw [hplus_shift, real_inner_smul_left, real_inner_self_eq_norm_sq] at htest
      linarith
    have hminus_nonpos : -(t * ‖u‖ ^ 2) ≤ 0 := by
      -- Testing the opposite perturbation yields the reverse sign.
      have htest := hu_affine (x - t • u)
      have hminus_shift : (x - t • u) - x = -(t • u) := by abel
      rw [Metric.infDist_zero_of_mem hxC, Metric.infDist_zero_of_mem hminus_mem] at htest
      rw [hminus_shift, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at htest
      linarith
    have hsq_zero : ‖u‖ ^ 2 = 0 := by
      nlinarith [hplus_nonpos, hminus_nonpos, ht_pos]
    have hnorm_zero : ‖u‖ = 0 := sq_eq_zero_iff.mp hsq_zero
    exact norm_eq_zero.mp hnorm_zero
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    -- The zero vector is a subgradient because `Metric.infDist y C ≥ 0` and `φ` is monotone on
    -- the nonnegative ray.
    rw [comp_distanceToSet_mem_subdifferential_iff_real (C := C) (φ := φ) (x := x) (u := (0 : H))]
    intro y
    have hφ_ge : φ 0 ≤ φ (Metric.infDist y C) := by
      exact hφmono
        (by simp)
        (by simpa using Metric.infDist_nonneg (x := y) (s := C))
        (Metric.infDist_nonneg (x := y) (s := C))
    simpa [Metric.infDist_zero_of_mem hxC] using hφ_ge

/-- Helper for Example 17 33: every real number lies in the relative interior of `Set.univ`. -/
lemma mem_relativeInterior_univ_real (z : ℝ) :
    z ∈ Set.relativeInterior (Set.univ : Set ℝ) := by
  rw [Set.mem_relativeInterior_iff]
  refine ⟨by simp, ?_⟩
  have huniv_sub : (Set.univ : Set ℝ) - ({z} : Set ℝ) = Set.univ := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      refine Set.mem_sub.2 ?_
      exact ⟨y + z, by simp, z, by simp, by ring⟩
  have hcone_univ : Set.cone (Set.univ : Set ℝ) = Set.univ := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rw [Set.cone_def]
      exact
        (ConvexCone.mem_hull_of_convex
          (𝕜 := ℝ) (M := ℝ) (s := (Set.univ : Set ℝ)) (x := y) convex_univ).2 <| by
            refine ⟨1, by norm_num, ?_⟩
            simp
  have hspan_univ : (Submodule.span ℝ (Set.univ : Set ℝ) : Set ℝ) = Set.univ := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      exact Submodule.subset_span (by simp)
  simp [huniv_sub, hcone_univ]

/-- Helper for Example 17 33: along a normal ray issued from a point of `C`, the distance to `C`
grows exactly like the ray parameter. -/
lemma infDist_eq_along_normal_ray_of_mem
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {p v : H} (hp : p ∈ C) (hv : v ∈ N[C] p) (hv_norm : ‖v‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    Metric.infDist (p + t • v) C = t := by
  let hC_cheb' := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let P' : H → H := P[C, hC_cheb']
  have htv_mem : t • v ∈ N[C] p := by
    -- The normal cone is stable under nonnegative scalar multiplication.
    rw [Set.normalCone_of_mem hp] at hv ⊢
    have hv_pointwise :
        ∀ y ∈ C, inner ℝ (y - p) v ≤ 0 :=
      (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := v) (p := p)).1 hv
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff
        (C := C) (u := t • v) (p := p)).2 <| by
          intro y hy
          simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
            mul_nonpos_of_nonneg_of_nonpos ht (hv_pointwise y hy)
  have hproj : p = P' (p + t • v) := by
    -- Prove the projection identity first, so the distance reduces to one norm.
    exact
      (eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
        (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
        (hC_convex := hC_convex) (x := p + t • v) (p := p)).2 <| by
          simpa [sub_eq_add_neg] using htv_mem
  have hshift : p + t • v - p = t • v := by
    abel
  calc
    Metric.infDist (p + t • v) C = dist (p + t • v) (P' (p + t • v)) := by
      simpa [P', hC_cheb'] using (projectionPoint_isBestApproximation C hC_cheb' (p + t • v)).2.symm
    _ = ‖t • v‖ := by rw [← hproj, dist_eq_norm, hshift]
    _ = t := by rw [norm_smul, Real.norm_of_nonneg ht, hv_norm, mul_one]

/-- Helper for Example 17 33: away from `C`, the positive distance value lies in the relative
interior of the range of `Metric.infDist`. -/
lemma infDist_mem_relativeInterior_range_of_not_mem
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∉ C) :
    Metric.infDist x C ∈ Set.relativeInterior (Set.range (fun y : H ↦ Metric.infDist y C)) := by
  let d : ℝ := Metric.infDist x C
  let hC_cheb' := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let P' : H → H := P[C, hC_cheb']
  let v : H := d⁻¹ • (x - P' x)
  have hd_pos : 0 < d := by
    dsimp [d]
    exact (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hPx : P' x ∈ C := projectionPoint_mem C hC_cheb' x
  have hv_normal : v ∈ N[C] (P' x) := by
    dsimp [v, d]
    simpa using
      normalized_projection_residual_mem_normalCone_of_not_mem
        (C := C) hC_nonempty hC_closed hC_convex hx
  have hv_norm : ‖v‖ = 1 := by
    dsimp [v, d]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd_pos.le)]
    rw [projection_residual_norm_eq_infDist (C := C) hC_nonempty hC_closed hC_convex]
    exact inv_mul_cancel₀ hd_ne
  have hdist_on_ray :
      ∀ t : ℝ, 0 ≤ t → t ∈ Set.range (fun y : H ↦ Metric.infDist y C) := by
    intro t ht
    refine ⟨P' x + t • v, ?_⟩
    exact
      infDist_eq_along_normal_ray_of_mem
        (C := C) hC_nonempty hC_closed hC_convex hPx hv_normal hv_norm ht
  let S : Set ℝ := Set.range (fun y : H ↦ Metric.infDist y C) - ({d} : Set ℝ)
  have hd_mem : d ∈ Set.range (fun y : H ↦ Metric.infDist y C) := by
    exact ⟨x, rfl⟩
  have hzero_mem_range : 0 ∈ Set.range (fun y : H ↦ Metric.infDist y C) := by
    rcases hC_nonempty with ⟨p, hp⟩
    exact ⟨p, Metric.infDist_zero_of_mem hp⟩
  rw [Set.mem_relativeInterior_iff]
  refine ⟨hd_mem, ?_⟩
  have hd_singleton : d ∈ ({d} : Set ℝ) := by
    simp
  have hd_mem_S : d ∈ S := by
    refine Set.mem_sub.2 ?_
    refine ⟨2 * d, hdist_on_ray (2 * d) (by positivity), d, hd_singleton, ?_⟩
    ring
  have hnegd_mem_S : -d ∈ S := by
    refine Set.mem_sub.2 ?_
    refine ⟨0, hzero_mem_range, d, hd_singleton, ?_⟩
    ring
  have hzero_mem_S : (0 : ℝ) ∈ S := by
    exact Set.mem_sub.2 ⟨d, hd_mem, d, hd_singleton, sub_self d⟩
  have hcone_univ : Set.cone S = Set.univ := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rw [Set.cone_def]
      by_cases hy_zero : y = 0
      · subst hy_zero
        exact ConvexCone.subset_hull hzero_mem_S
      · by_cases hy_nonneg : 0 ≤ y
        · have hy_pos : 0 < y := by
            refine lt_of_le_of_ne hy_nonneg ?_
            simpa [eq_comm] using hy_zero
          have hy_eq : (y / d : ℝ) • d = y := by
            have hy_mul : (y / d : ℝ) * d = y := by
              field_simp [hd_ne]
            simpa [smul_eq_mul] using hy_mul
          rw [← hy_eq]
          exact (ConvexCone.hull ℝ S).smul_mem (div_pos hy_pos hd_pos)
            (ConvexCone.subset_hull hd_mem_S)
        · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
          have hy_eq : (((-y) / d : ℝ) • (-d)) = y := by
            have hy_mul : (((-y) / d : ℝ) * (-d)) = y := by
              field_simp [hd_ne]
            simpa [smul_eq_mul] using hy_mul
          rw [← hy_eq]
          have hscale_pos : 0 < (-y) / d := by
            exact div_pos (by linarith) hd_pos
          exact (ConvexCone.hull ℝ S).smul_mem hscale_pos
            (ConvexCone.subset_hull hnegd_mem_S)
  have hspan_eq_top : Submodule.span ℝ S = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have hsingleton_subset : ({d} : Set ℝ) ⊆ S := by
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hd_mem_S
    have hy_singleton : y ∈ Submodule.span ℝ ({d} : Set ℝ) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨y / d, ?_⟩
      have hy_mul : (y / d : ℝ) * d = y := by
        field_simp [hd_ne]
      simpa [smul_eq_mul] using hy_mul
    exact (Submodule.span_mono hsingleton_subset) hy_singleton
  have hspan_univ : (Submodule.span ℝ S : Set ℝ) = Set.univ := by
    simpa using congrArg (fun V : Submodule ℝ ℝ ↦ (V : Set ℝ)) hspan_eq_top
  simpa [S] using hcone_univ.trans hspan_univ.symm

/-- Helper for Example 17 33: for the distance-to-set map, the scalar-composition chain rule from
Corollary 16.72 collapses to a scalar multiple of `∂ d_C(x)` outside `C`. -/
lemma subdifferential_comp_distanceToSet_eq_deriv_smul_subdifferential_of_not_mem
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφdiff : DifferentiableOn ℝ φ (Set.Ici (0 : ℝ)))
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    {x : H} (hx : x ∉ C) :
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x =
      (deriv φ (Metric.infDist x C)) • ((∂ (fun y : H ↦ Metric.infDist y C).toEReal) x) := by
  have hdist_cont : Continuous (fun y : H ↦ Metric.infDist y C) :=
    Metric.continuous_infDist_pt C
  have hdist_conv :
      _root_.ConvexOn ℝ Set.univ (fun y : H ↦ Metric.infDist y C) :=
    convexOn_univ_infDist_of_nonempty_isClosed_convex
      (C := C) hC_nonempty hC_closed hC_convex
  have hφcont : Continuous φ := by
    exact continuousOn_univ.mp (hφconv.continuousOn isOpen_univ)
  have hφΓ : φ.toEReal ∈ Γ₀(ℝ) :=
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ φ hφcont hφconv
  have hφmono :=
    monotoneOn_nonnegative_of_monotoneOn_or_even (φ := φ) hφconv hφ_mono_or_even
  have hmono_range : MonotoneOn φ.toEReal (Set.range (fun y : H ↦ Metric.infDist y C)) := by
    -- Route correction: isolate the monotonicity transfer through `Metric.infDist ≥ 0`.
    have hmono_range_real :
        MonotoneOn φ (Set.range (fun y : H ↦ Metric.infDist y C)) :=
      monotoneOn_infDist_range_of_monotoneOn_nonnegative (C := C) (φ := φ) hφmono
    intro a ha b hb hab
    change ((φ a : ℝ) : EReal) ≤ ((φ b : ℝ) : EReal)
    exact_mod_cast hmono_range_real ha hb hab
  have hφdiff_at : DifferentiableAt ℝ φ (Metric.infDist x C) :=
    (hφdiff (Metric.infDist x C) (Metric.infDist_nonneg (x := x) (s := C))).differentiableAt <| by
      have hIoi : Set.Ioi (0 : ℝ) ∈ nhds (Metric.infDist x C) := by
        exact Ioi_mem_nhds <| (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
      exact Filter.mem_of_superset hIoi (by
        intro y hy
        have hy' : 0 < y := hy
        exact hy'.le)
  have hregular :
      ((Set.relativeInterior (Set.range (fun y : H ↦ Metric.infDist y C)) + Set.Ioi (0 : ℝ)) ∩
        Set.relativeInterior (effectiveDomain φ.toEReal)).Nonempty := by
    refine ⟨Metric.infDist x C + 1, ?_⟩
    rw [Function.effectiveDomain_toEReal]
    constructor
    · exact Set.mem_add.2 ⟨Metric.infDist x C,
        infDist_mem_relativeInterior_range_of_not_mem
          (C := C) hC_nonempty hC_closed hC_convex hx,
        1, by simp, by ring⟩
    · exact mem_relativeInterior_univ_real (Metric.infDist x C + 1)
  have hdist_dom : Metric.infDist x C ∈ effectiveDomain φ.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hchain :=
    subdifferential_comp_eq_iUnion_smul_of_continuous_convexOn_univ_of_monotoneOn_range
      (f := fun y : H ↦ Metric.infDist y C) (φ := φ.toEReal)
      hdist_cont hdist_conv hφΓ hmono_range hregular x hdist_dom
  have hscalar :
      (∂ φ.toEReal) (Metric.infDist x C) = ({deriv φ (Metric.infDist x C)} : Set ℝ) :=
    scalar_subdifferential_toEReal_eq_singleton_deriv φ hφconv hφdiff_at
  -- Corollary 16.72 gives the scalar-indexed union; differentiability collapses that union to
  -- the single exterior scale `deriv φ (d(x, C))`.
  calc
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x
        = ⋃ α ∈ (∂ φ.toEReal) (Metric.infDist x C),
            α • ((∂ (fun y : H ↦ Metric.infDist y C).toEReal) x) := by
            simpa [Function.comp_apply, Function.toEReal_apply] using hchain
    _ = ⋃ α ∈ ({deriv φ (Metric.infDist x C)} : Set ℝ),
          α • ((∂ (fun y : H ↦ Metric.infDist y C).toEReal) x) := by
          rw [hscalar]
    _ = (deriv φ (Metric.infDist x C)) • ((∂ (fun y : H ↦ Metric.infDist y C).toEReal) x) := by
          exact iUnion_smul_singleton_eq
            (a := deriv φ (Metric.infDist x C))
            ((∂ (fun y : H ↦ Metric.infDist y C).toEReal) x)

/-- Helper for Example 17 33: scaling the singleton exterior branch of `∂ d_C(x)` collapses to
the displayed singleton involving `(deriv φ (d(x, C)) / d(x, C)) • (x - P x)`. -/
lemma singleton_deriv_smul_normalized_projectionResidual_eq
    (φ : ℝ → ℝ) {x : H} (_hx : x ∉ C) :
    (deriv φ (Metric.infDist x C)) • ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) =
      ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H) := by
  ext u
  simp [div_eq_mul_inv, smul_smul]

/-- Helper for Example 17 33: away from `C`, Proposition 17.32 and the exterior branch of
Example 16.62 reduce the composition subdifferential to the scaled projection residual. -/
lemma subdifferential_comp_distanceToSet_eq_singleton_deriv_smul_projectionResidual_of_not_mem
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφdiff : DifferentiableOn ℝ φ (Set.Ici (0 : ℝ)))
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    {x : H} (hx : x ∉ C) :
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x =
      ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H) := by
  -- Apply the local chain-rule reduction for `f = d_C`, then rewrite the exterior branch of
  -- `∂ d_C(x)` from Example 16.62.
  calc
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x
        = (deriv φ (Metric.infDist x C)) • ((∂ (fun y : H ↦ Metric.infDist y C).toEReal) x) := by
            exact
              subdifferential_comp_distanceToSet_eq_deriv_smul_subdifferential_of_not_mem
                (C := C) hC_nonempty hC_closed hC_convex φ hφconv hφdiff hφ_mono_or_even hx
    _ = (deriv φ (Metric.infDist x C)) • ({(Metric.infDist x C)⁻¹ • (x - P x)} : Set H) := by
          rw [subdifferential_distanceToSet_eq_singleton_normalizedResidual_of_not_mem
            (C := C) hC_nonempty hC_closed hC_convex hx]
    _ = ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H) := by
          simpa using singleton_deriv_smul_normalized_projectionResidual_eq
            (C := C) hC_nonempty hC_closed hC_convex (φ := φ) (x := x) hx


/-- Helper for Example 17 33: on the nonnegative ray, the canonical right derivative at `0`
is nonnegative and defines a supporting affine minorant for `φ`. -/
lemma rightDerivative_toReal_nonneg_and_support_line_on_nonnegative
    (φ : ℝ → ℝ) (_hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφmono : MonotoneOn φ (Set.Ici (0 : ℝ))) :
    0 ≤ (((φ.toEReal)′₊(0)).toReal) ∧
      ∀ t : ℝ, 0 ≤ t → φ 0 + (((φ.toEReal)′₊(0)).toReal) * t ≤ φ t := by
  have hφconv_toEReal : ConvexOn φ.toEReal (effectiveDomain φ.toEReal) :=
    comp_distance_convexOn_toEReal_of_convexOn_univ φ _hφconv
  have hzero_mem : (0 : ℝ) ∈ effectiveDomain φ.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hright_nonneg : (0 : EReal) ≤ (φ.toEReal)′₊(0) := by
    change (0 : EReal) ≤ sInf (Set.range (directionalDifferenceQuotient φ.toEReal 0 1))
    refine le_sInf ?_
    rintro _ ⟨a, rfl⟩
    have hmono_a : φ 0 ≤ φ (a : ℝ) := by
      exact hφmono (by simp) (show 0 ≤ (a : ℝ) by exact a.2.le) a.2.le
    have hquot_nonneg : 0 ≤ ((φ (a : ℝ) - φ 0) / (a : ℝ) : ℝ) := by
      exact div_nonneg (sub_nonneg.mpr hmono_a) a.2.le
    have hquot_eq :
        directionalDifferenceQuotient φ.toEReal 0 1 a =
          ((((φ (a : ℝ) - φ 0) / (a : ℝ) : ℝ)) : EReal) := by
      simpa [directionalDifferenceQuotient, Function.toEReal_apply, sub_eq_add_neg] using
        differenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
          (f := φ.toEReal) (x := (0 : ℝ)) (d := (1 : ℝ))
          (hx := by simp) (hα := a.2) (hαdom := by simp)
    rw [hquot_eq]
    exact EReal.coe_nonneg.2 hquot_nonneg
  have hright_ne_top : (φ.toEReal)′₊(0) ≠ ⊤ := by
    have hbound :
        (φ.toEReal)′₊(0) ≤
          directionalDifferenceQuotient φ.toEReal 0 1 ⟨1, by norm_num⟩ := by
      change sInf (Set.range (directionalDifferenceQuotient φ.toEReal 0 1)) ≤ _
      exact sInf_le ⟨⟨1, by norm_num⟩, rfl⟩
    intro htop
    have htop_le :
        (⊤ : EReal) ≤ directionalDifferenceQuotient φ.toEReal 0 1 ⟨1, by norm_num⟩ := by
      simpa [htop] using hbound
    have hquot_top :
        directionalDifferenceQuotient φ.toEReal 0 1 ⟨1, by norm_num⟩ = ⊤ := top_unique htop_le
    have hquot_top' : (↑(φ 1) - ↑(φ 0) : EReal) = ⊤ := by
      simpa [directionalDifferenceQuotient, Function.toEReal_apply] using hquot_top
    have hfinite : (↑(φ 1) - ↑(φ 0) : EReal) ≠ ⊤ := by
      rw [← EReal.coe_sub]
      exact EReal.coe_ne_top _
    exact hfinite hquot_top'
  have hright_ne_bot : (φ.toEReal)′₊(0) ≠ ⊥ := by
    intro hbot
    have htmp := hright_nonneg
    simp [hbot] at htmp
  let ρ : ℝ := ((φ.toEReal)′₊(0)).toReal
  have hρ_coe : ((ρ : ℝ) : EReal) = (φ.toEReal)′₊(0) := by
    dsimp [ρ]
    simpa using EReal.coe_toReal hright_ne_top hright_ne_bot
  have hρ_mem_sub :
      ρ ∈ (∂ φ.toEReal) (0 : ℝ) := by
    rw [subdifferential_eq_Icc_oneSidedDerivatives
      (f := φ.toEReal) (hconv := hφconv_toEReal) hzero_mem]
    change ((ρ : ℝ) : EReal) ∈ Set.Icc ((φ.toEReal)′₋(0)) ((φ.toEReal)′₊(0))
    constructor
    · simpa [hρ_coe] using
        leftDerivative_le_rightDerivative
          (f := φ.toEReal) (hconv := hφconv_toEReal) hzero_mem
    · simp [hρ_coe]
  have hρ_nonneg : 0 ≤ ρ := by
    have hρ_nonnegE : (0 : EReal) ≤ ((ρ : ℝ) : EReal) := by
      have htmp := hright_nonneg
      simpa [hρ_coe] using htmp
    exact EReal.coe_nonneg.mp hρ_nonnegE
  refine ⟨hρ_nonneg, ?_⟩
  intro t ht
  have hsub :=
    (ERealFunction.mem_subdifferential_iff
      (f := φ.toEReal) (x := (0 : ℝ)) (u := ρ)).1 hρ_mem_sub t
  have hsub_real : inner ℝ t ρ + φ 0 ≤ φ t := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [Function.toEReal_apply, EReal.coe_add] using hsub
  have hinner : inner ℝ t ρ = t * ρ := by
    simpa [RCLike.inner_apply] using (mul_comm ρ t)
  simpa [ρ, hinner, add_comm, add_left_comm, add_assoc, mul_comm] using hsub_real

/-- Helper for Example 17 33: any nonnegative slope whose affine function minorizes `φ` on
`[0, ∞)` is bounded above by the canonical right derivative at `0`. -/
lemma slope_le_rightDerivative_toReal_of_support_line_on_nonnegative
    (φ : ℝ → ℝ) {a : ℝ} (ha_nonneg : 0 ≤ a)
    (hminor : ∀ t : ℝ, 0 ≤ t → φ 0 + a * t ≤ φ t) :
    a ≤ (((φ.toEReal)′₊(0)).toReal) := by
  have ha_le_dir : ((a : ℝ) : EReal) ≤ (φ.toEReal)′₊(0) := by
    change ((a : ℝ) : EReal) ≤ sInf (Set.range (directionalDifferenceQuotient φ.toEReal 0 1))
    refine le_sInf ?_
    rintro _ ⟨t, rfl⟩
    have hminor_t : φ 0 + a * (t : ℝ) ≤ φ (t : ℝ) := hminor (t : ℝ) t.2.le
    have hquot_lower : a ≤ (φ (t : ℝ) - φ 0) / (t : ℝ) := by
      have ht_pos : 0 < (t : ℝ) := t.2
      exact (le_div_iff₀ ht_pos).2 <| by linarith
    have hquot_eq :
        directionalDifferenceQuotient φ.toEReal 0 1 t =
          ((((φ (t : ℝ) - φ 0) / (t : ℝ) : ℝ)) : EReal) := by
      simpa [directionalDifferenceQuotient, Function.toEReal_apply, sub_eq_add_neg] using
        differenceQuotient_eq_coe_toReal_of_mem_effectiveDomain
          (f := φ.toEReal) (x := (0 : ℝ)) (d := (1 : ℝ))
          (hx := by simp) (hα := t.2) (hαdom := by simp)
    rw [hquot_eq]
    exact EReal.coe_le_coe_iff.mpr hquot_lower
  have hright_ne_top : (φ.toEReal)′₊(0) ≠ ⊤ := by
    have hbound :
        (φ.toEReal)′₊(0) ≤
          directionalDifferenceQuotient φ.toEReal 0 1 ⟨1, by norm_num⟩ := by
      change sInf (Set.range (directionalDifferenceQuotient φ.toEReal 0 1)) ≤ _
      exact sInf_le ⟨⟨1, by norm_num⟩, rfl⟩
    intro htop
    have htop_le :
        (⊤ : EReal) ≤ directionalDifferenceQuotient φ.toEReal 0 1 ⟨1, by norm_num⟩ := by
      simpa [htop] using hbound
    have hquot_top :
        directionalDifferenceQuotient φ.toEReal 0 1 ⟨1, by norm_num⟩ = ⊤ := top_unique htop_le
    have hquot_top' : (↑(φ 1) - ↑(φ 0) : EReal) = ⊤ := by
      simpa [directionalDifferenceQuotient, Function.toEReal_apply] using hquot_top
    have hfinite : (↑(φ 1) - ↑(φ 0) : EReal) ≠ ⊤ := by
      rw [← EReal.coe_sub]
      exact EReal.coe_ne_top _
    exact hfinite hquot_top'
  have hright_ne_bot : (φ.toEReal)′₊(0) ≠ ⊥ := by
    intro hbot
    have hnonnegE : (0 : EReal) ≤ ((a : ℝ) : EReal) := by
      exact_mod_cast ha_nonneg
    have : (0 : EReal) ≤ (⊥ : EReal) := by
      simpa [hbot] using le_trans hnonnegE ha_le_dir
    simp at this
  have ha_le_dir_real :
      ((a : ℝ) : EReal) ≤ ((((φ.toEReal)′₊(0)).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hright_ne_top hright_ne_bot] using ha_le_dir
  exact EReal.coe_le_coe_iff.mp ha_le_dir_real

/-- Helper for Example 17 33: along an outward normal ray issued from a frontier point, the
distance to `C` grows exactly like the ray parameter. -/
lemma infDist_eq_along_outward_normal_ray_of_mem_frontier
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x v : H} (hx : x ∈ frontier C) (hv : v ∈ N[C] x) (hv_norm : ‖v‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    Metric.infDist (x + t • v) C = t := by
  exact
    infDist_eq_along_normal_ray_of_mem
      (C := C) hC_nonempty hC_closed hC_convex (hC_closed.frontier_subset hx) hv hv_norm ht

/-- Helper for Example 17 33: every boundary subgradient of `x ↦ φ (Metric.infDist x C)` lies in
the normal cone and in the closed ball of radius `((φ.toEReal)′₊(0)).toReal`. -/
lemma subdifferential_comp_distanceToSet_frontier_subset_normalCone_closedBall
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    {x u : H} (hx : x ∈ frontier C)
    (hu : u ∈ (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x) :
    u ∈ N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal) := by
  have hxC : x ∈ C := hC_closed.frontier_subset hx
  have hφmono :=
    monotoneOn_nonnegative_of_monotoneOn_or_even (φ := φ) hφconv hφ_mono_or_even
  let ρ : ℝ := (((φ.toEReal)′₊(0)).toReal)
  have hρpack :=
    rightDerivative_toReal_nonneg_and_support_line_on_nonnegative
      (φ := φ) hφconv hφmono
  rcases hρpack with ⟨hρ_nonneg, _hρ_support⟩
  have hu_affine :=
    (comp_distanceToSet_mem_subdifferential_iff_real (C := C) (φ := φ) (x := x) (u := u)).1 hu
  have hu_normal : u ∈ N[C] x := by
    -- Testing on points of `C` collapses the affine inequality to the normal-cone condition.
    rw [Set.normalCone_of_mem hxC]
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).2 <| by
        intro y hy
        have htest := hu_affine y
        rw [Metric.infDist_zero_of_mem hxC, Metric.infDist_zero_of_mem hy] at htest
        simpa using htest
  constructor
  · exact hu_normal
  · rw [Metric.mem_closedBall, dist_eq_norm]
    by_cases hu0 : u = 0
    · simp [hu0, hρ_nonneg]
    · let v : H := ‖u‖⁻¹ • u
      have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
      have hv_normal : v ∈ N[C] x := by
        -- Normalize the nonzero normal vector so the ray formula applies.
        rw [Set.normalCone_of_mem hxC] at hu_normal ⊢
        have hu_pointwise :
            ∀ y ∈ C, inner ℝ (y - x) u ≤ 0 :=
          (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).1 hu_normal
        exact
          (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := v) (p := x)).2 <| by
            intro y hy
            simpa [v, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
              mul_nonpos_of_nonneg_of_nonpos
                (inv_nonneg.mpr (norm_nonneg u)) (hu_pointwise y hy)
      have hv_norm : ‖v‖ = 1 := by
        dsimp [v]
        simpa using norm_smul_inv_norm hu0
      have huv : inner ℝ v u = ‖u‖ := by
        -- The normalized ray direction converts the vector inequality into a scalar slope bound.
        dsimp [v]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp [hu_norm_ne]
      have hminor : ∀ t : ℝ, 0 ≤ t → φ 0 + ‖u‖ * t ≤ φ t := by
        intro t ht
        have hray :=
          infDist_eq_along_outward_normal_ray_of_mem_frontier
            (C := C) hC_nonempty hC_closed hC_convex hx hv_normal hv_norm ht
        have htest := hu_affine (x + t • v)
        have hshift : (x + t • v) - x = t • v := by
          abel
        rw [Metric.infDist_zero_of_mem hxC, hray] at htest
        have htest' : t * ‖u‖ + φ 0 ≤ φ t := by
          simpa [hshift, real_inner_smul_left, huv] using htest
        simpa [mul_comm, add_comm, add_left_comm, add_assoc] using htest'
      have hnorm_le_ρ :
          ‖u‖ ≤ (((φ.toEReal)′₊(0)).toReal) :=
        slope_le_rightDerivative_toReal_of_support_line_on_nonnegative
          (φ := φ) (a := ‖u‖) (norm_nonneg u) hminor
      simpa [ρ] using hnorm_le_ρ

omit [CompleteSpace H] in
/-- Helper for Example 17 33: normalizing a nonzero normal vector produces a point of
`N[C] x ∩ Metric.closedBall (0 : H) 1`. -/
lemma normalized_mem_normalCone_inter_closedBall_unit_of_nonzero
    {x u : H} (hxC : x ∈ C) (huN : u ∈ N[C] x) (hu_ne : u ≠ 0) :
    ‖u‖⁻¹ • u ∈ N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  constructor
  · -- Rewrite the normal-cone membership pointwise and scale by the nonnegative inverse norm.
    rw [Set.normalCone_of_mem hxC] at huN ⊢
    have hu_pointwise : ∀ y ∈ C, inner ℝ (y - x) u ≤ 0 :=
      (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).1 huN
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff
        (C := C) (u := ‖u‖⁻¹ • u) (p := x)).2 <| by
          intro y hy
          simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
            mul_nonpos_of_nonneg_of_nonpos
              (inv_nonneg.mpr (norm_nonneg u)) (hu_pointwise y hy)
  · -- The normalized vector has norm `1`.
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using (norm_smul_inv_norm hu_ne).le

omit [CompleteSpace H] in
/-- Helper for Example 17 33: a normalized boundary subgradient of `d_C` yields the corresponding
distance minorant after scaling back by `‖u‖`. -/
lemma scaled_distance_subgradient_minorant_of_normalized
    {x u : H} (hxC : x ∈ C) (hu_ne : u ≠ 0)
    (hu_sub :
      ‖u‖⁻¹ • u ∈ (∂ (fun z : H ↦ Metric.infDist z C).toEReal) x) :
    ∀ y : H, inner ℝ (y - x) u ≤ ‖u‖ * Metric.infDist y C := by
  have hu_affine :=
    (distanceToSet_mem_subdifferential_iff_zero_value
      (C := C) (x := x) (u := ‖u‖⁻¹ • u) hxC).1 hu_sub
  have hu_norm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu_ne
  have hu_rescale : ‖u‖ • (‖u‖⁻¹ • u) = u := by
    -- Rewrite `u` through its normalized direction so the subgradient inequality can be scaled.
    rw [smul_smul, mul_inv_cancel₀ hu_norm_ne, one_smul]
  intro y
  have hscaled :
      ‖u‖ * inner ℝ (y - x) (‖u‖⁻¹ • u) ≤ ‖u‖ * Metric.infDist y C := by
    -- Multiply the unit-radius minorant by the nonnegative factor `‖u‖`.
    exact mul_le_mul_of_nonneg_left (hu_affine y) (norm_nonneg u)
  calc
    inner ℝ (y - x) u = inner ℝ (y - x) (‖u‖ • (‖u‖⁻¹ • u)) := by rw [hu_rescale]
    _ = ‖u‖ * inner ℝ (y - x) (‖u‖⁻¹ • u) := by rw [real_inner_smul_right]
    _ ≤ ‖u‖ * Metric.infDist y C := hscaled

/-- Helper for Example 17 33: every vector in the boundary normal-cone/closed-ball branch
satisfies the subgradient inequality for `x ↦ φ (Metric.infDist x C)`. -/
lemma normalCone_closedBall_subset_subdifferential_comp_distanceToSet_frontier
    (_hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    {x u : H} (hx : x ∈ frontier C)
    (hu : u ∈ N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal)) :
    u ∈ (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x := by
  -- Route correction: isolate the normalization/rescaling step and then combine it with the
  -- scalar support line at the boundary value `Metric.infDist x C = 0`.
  have hxC : x ∈ C := hC_closed.frontier_subset hx
  have hφmono :=
    monotoneOn_nonnegative_of_monotoneOn_or_even (φ := φ) hφconv hφ_mono_or_even
  let ρ : ℝ := (((φ.toEReal)′₊(0)).toReal)
  have hρpack :=
    rightDerivative_toReal_nonneg_and_support_line_on_nonnegative
      (φ := φ) hφconv hφmono
  rcases hρpack with ⟨hρ_nonneg, hρ_support⟩
  rw [comp_distanceToSet_mem_subdifferential_iff_real (C := C) (φ := φ) (x := x) (u := u)]
  by_cases hu_ne : u ≠ 0
  · have huN : u ∈ N[C] x := hu.1
    have hu_norm_le_ρ : ‖u‖ ≤ ρ := by
      simpa [ρ, Metric.mem_closedBall, dist_eq_norm] using hu.2
    have hw_mem :
        ‖u‖⁻¹ • u ∈ N[C] x ∩ Metric.closedBall (0 : H) 1 :=
      normalized_mem_normalCone_inter_closedBall_unit_of_nonzero
        (C := C) hxC huN hu_ne
    have hw_sub :
        ‖u‖⁻¹ • u ∈ (∂ (fun z : H ↦ Metric.infDist z C).toEReal) x := by
      -- Example 16.62 provides the exact frontier subdifferential of the distance map.
      rw [subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
        (C := C) hC_closed hC_convex hx]
      exact hw_mem
    have hdist_minorant :
        ∀ y : H, inner ℝ (y - x) u ≤ ‖u‖ * Metric.infDist y C :=
      scaled_distance_subgradient_minorant_of_normalized
        (C := C) hxC hu_ne hw_sub
    intro y
    have hnorm_cmp : ‖u‖ * Metric.infDist y C ≤ ρ * Metric.infDist y C := by
      exact mul_le_mul_of_nonneg_right hu_norm_le_ρ (Metric.infDist_nonneg (x := y) (s := C))
    have hsupport :
        φ 0 + ρ * Metric.infDist y C ≤ φ (Metric.infDist y C) :=
      hρ_support (Metric.infDist y C) (Metric.infDist_nonneg (x := y) (s := C))
    have hfinal : inner ℝ (y - x) u + φ 0 ≤ φ (Metric.infDist y C) := by
      linarith [hdist_minorant y, hnorm_cmp, hsupport]
    simpa [Metric.infDist_zero_of_mem hxC] using hfinal
  · have hu0 : u = 0 := by simpa using hu_ne
    intro y
    have hsupport :
        φ 0 + ρ * Metric.infDist y C ≤ φ (Metric.infDist y C) :=
      hρ_support (Metric.infDist y C) (Metric.infDist_nonneg (x := y) (s := C))
    have hρ_term_nonneg : 0 ≤ ρ * Metric.infDist y C := by
      exact mul_nonneg hρ_nonneg (Metric.infDist_nonneg (x := y) (s := C))
    have hfinal : φ 0 ≤ φ (Metric.infDist y C) := by
      linarith
    simpa [hu0, Metric.infDist_zero_of_mem hxC] using hfinal

/-- Helper for Example 17 33: at a frontier point, the subdifferential of
`x ↦ φ (Metric.infDist x C)` is the normal cone intersected with the closed ball whose radius is
the right derivative of `φ` at `0`. -/
lemma subdifferential_comp_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (_hφdiff : DifferentiableOn ℝ φ (Set.Ici (0 : ℝ)))
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    {x : H} (hx : x ∈ frontier C) :
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x =
      N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal) := by
  -- Route correction: split the frontier proof into two stable inclusions instead of one large
  -- transport-heavy argument.
  refine Set.Subset.antisymm ?_ ?_
  · intro u hu
    exact
      subdifferential_comp_distanceToSet_frontier_subset_normalCone_closedBall
        (C := C) hC_nonempty hC_closed hC_convex φ hφconv hφ_mono_or_even hx hu
  · intro u hu
    exact
      normalCone_closedBall_subset_subdifferential_comp_distanceToSet_frontier
        (C := C) hC_nonempty hC_closed hC_convex φ hφconv hφ_mono_or_even hx hu

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 17 33: a point of `C` that is not on `frontier C` must lie in `interior C`.
-/
lemma mem_interior_of_mem_and_not_mem_frontier
    {x : H} (hxC : x ∈ C) (hxbdry : x ∉ frontier C) :
    x ∈ interior C := by
  -- On points of `C`, the frontier complement is exactly the interior.
  rw [mem_frontier_iff_notMem_interior hxC] at hxbdry
  exact not_not.mp hxbdry

/-- Helper for Example 17 33: once the membership decisions `x ∈ C` and `x ∉ frontier C` are
fixed, the displayed piecewise value reduces to the interior singleton branch `{0}`. -/
lemma piecewise_branch_eq_singleton_zero_of_mem_and_not_mem_frontier
    (φ : ℝ → ℝ) {x : H} (hxC : x ∈ C) (hxbdry : x ∉ frontier C) :
    (if _hxC : x ∈ C then
        if _hxbdry : x ∈ frontier C then
          N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal)
        else
          ({0} : Set H)
      else
        ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H)) =
      ({0} : Set H) := by
  -- The chosen membership decisions remove all branches except the interior singleton.
  simp [hxC, hxbdry]

/- Source/core/bridge triage:
- `source-facing`: Example 17.33 is the piecewise subdifferential formula for
  `x ↦ φ (Metric.infDist x C)`.
- `core/canonical`: the owner surface is `Metric.infDist`, `∂`, `P`, `N[C]`, and
  the one-sided scalar derivative owner `(φ.toEReal)′₊(0)` at the boundary value `0`.
- `bridge/view`: Proposition 17.32 composes subdifferentials with a differentiable convex scalar
  function away from the boundary, while Example 16.62 provides the distance-to-set branch
  formulas.

The refinement therefore keeps the source-facing theorem and rewrites it directly against those
chapter owners instead of parallel lower-level spellings. -/

-- Proof sketch: away from the boundary, apply Proposition 17.32 to
-- `f := fun y ↦ Metric.infDist y C`, using the convexity and continuity of `Metric.infDist` and
-- Example 16.62 for `∂ d_C`. At boundary points, `Metric.infDist x C = 0`, so only the
-- one-sided scalar behavior along `ℝ₊` is available; the correct branch is therefore governed by
-- the canonical right derivative `(φ.toEReal)′₊(0)` rather than the ambient derivative `deriv φ 0`.
-- If `φ` is even, Proposition 11.7(ii) upgrades even convexity to monotonicity on `ℝ₊`, reducing
-- to the previous case; then rewrite the scaled distance subdifferential branch-by-branch to
-- obtain the displayed piecewise formula.
/-- Example 17 33: if `C` is a nonempty closed convex subset of a real Hilbert space and
`φ : ℝ → ℝ` is convex, differentiable on `ℝ₊`, and either increasing on `ℝ₊` or even, then the
subdifferential of `x ↦ φ (d(x, C))` is the scaled projection residual outside `C`, the
intersection `N[C] x ∩ Metric.closedBall (0 : H) (φ′₊(0))` on `frontier C`, and `{0}` on the
interior of `C`, encoded here by the corresponding piecewise formula; the boundary radius is the
canonical right derivative of `φ.toEReal` at `0`, rendered below as `((φ.toEReal)′₊(0)).toReal`.
-/
theorem subdifferential_comp_distanceToSet_eq_piecewise_of_nonempty_isClosed_convex
    (φ : ℝ → ℝ) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφdiff : DifferentiableOn ℝ φ (Set.Ici (0 : ℝ)))
    (hφ_mono_or_even : MonotoneOn φ (Set.Ici (0 : ℝ)) ∨ Function.Even φ)
    (x : H) :
    (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x =
      if _hxC : x ∈ C then
        if _hxbdry : x ∈ frontier C then
          N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal)
        else
          ({0} : Set H)
      else
        ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H) := by
  have hφmono := monotoneOn_nonnegative_of_monotoneOn_or_even (φ := φ) hφconv hφ_mono_or_even
  by_cases hxC : x ∈ C
  · by_cases hxbdry : x ∈ frontier C
    · -- The boundary clause is exactly the frontier helper.
      simpa [hxC, hxbdry] using
        subdifferential_comp_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
          (C := C) hC_nonempty hC_closed hC_convex φ hφconv hφdiff hφ_mono_or_even hxbdry
    · have hx_int : x ∈ interior C :=
        mem_interior_of_mem_and_not_mem_frontier (C := C) hxC hxbdry
      -- The interior branch is the locally constant case.
      calc
        (∂ (fun y : H ↦ φ (Metric.infDist y C)).toEReal) x = ({0} : Set H) := by
          simpa using
            subdifferential_comp_distanceToSet_eq_singleton_zero_of_mem_interior
              (C := C) (φ := φ) hφmono hx_int
        _ =
            (if _hxC : x ∈ C then
              if _hxbdry : x ∈ frontier C then
                N[C] x ∩ Metric.closedBall (0 : H) (((φ.toEReal)′₊(0)).toReal)
              else
                ({0} : Set H)
            else
              ({(deriv φ (Metric.infDist x C) / Metric.infDist x C) • (x - P x)} : Set H)) := by
              symm
              exact
                piecewise_branch_eq_singleton_zero_of_mem_and_not_mem_frontier
                  (C := C) hC_nonempty hC_closed hC_convex φ hxC hxbdry
  · -- Outside `C`, Proposition 17.32 already reduces the answer to the scaled residual singleton.
    simpa [hxC] using
      subdifferential_comp_distanceToSet_eq_singleton_deriv_smul_projectionResidual_of_not_mem
        (C := C) hC_nonempty hC_closed hC_convex φ hφconv hφdiff hφ_mono_or_even hxC

end DifferentiabilityOfDistanceCompositions

end

end ERealFunction
