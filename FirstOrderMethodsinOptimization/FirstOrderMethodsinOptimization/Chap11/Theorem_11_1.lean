import Mathlib
import FirstOrderMethodsinOptimization.Chap03.Definition_3_17
import FirstOrderMethodsinOptimization.Chap03.Theorem_3_1
import FirstOrderMethodsinOptimization.Chap03.Theorem_3_14
import FirstOrderMethodsinOptimization.Chap10.Definition_10_9
import FirstOrderMethodsinOptimization.Chap06.Theorem_6_39
import FirstOrderMethodsinOptimization.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient Pointwise

noncomputable section

universe u v

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [instBlockInner : InnerProductSpace ℝ ((i : ι) → Ei i)]
local instance : NormedSpace ℝ ((i : ι) → Ei i) := InnerProductSpace.toNormedSpace
local instance : Module ℝ ((i : ι) → Ei i) := NormedSpace.toModule
variable [FiniteDimensional ℝ ((i : ι) → Ei i)]

-- Proof sketch: unfold the Chapter 3 owner `is_stationary_point` for the composite problem
-- `f + separableSum g`, keeping the source-faithful finite-domain interior condition from
-- Definition 3.10. Derive the block restrictions of the ambient gradient from the source-facing
-- block-slice hypotheses
-- `HasFDerivAt (block_coordinate_slice f x i)
--    (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0`, and rewrite the
-- block-separable subdifferential into its coordinatewise Euclidean/vector-side form.
/-- Theorem 11.1 (1): under the blockwise proper/closed/convex hypotheses on `g_i`, stationarity
of the composite problem with regularizer `x ↦ ∑ i, g_i(x_i)` is equivalent to the coordinatewise
block condition `-∇ᵢ f(x) ∈ ∂ g_i(x_i)`, expressed through the Chapter 3 vector-side bridge
`euclideanSubdifferential`; the chosen block gradients are assumed to be the gradients of the
one-block slices `d ↦ f(x + Pi.single i d)` at `d = 0`, at points where `f` is finite-valued as
required by the Chapter 3 stationarity owner. -/
theorem is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
    {f : ((i : ι) → Ei i) → EReal}
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hblock_fderiv_spec : ∀ (i : ι) {x : ((j : ι) → Ei j)},
        x ∈ interior (finite_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (x : interior (finite_domain f)) :
    is_stationary_point f (separableSum g) (x : ((i : ι) → Ei i)) ↔
      ∀ i : ι,
        -(block_gradient i (x : ((i : ι) → Ei i))) ∈
          euclideanSubdifferential (g i) ((x : ((i : ι) → Ei i)) i) :=
  -- TODO: the source-faithful proof rewrites stationarity using the ambient gradient of
  -- `fun y ↦ (f y).toReal` and then splits `∂ (separableSum g)` coordinatewise. As written, the
  -- hypotheses only provide separate block-slice Fréchet derivatives, which do not suffice to
  -- recover `DifferentiableAt` of the ambient product-space map.
  sorry

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

-- Proof sketch: positive scaling by `1 / M` preserves properness, lower semicontinuity, and
-- convexity of `g i`; then `prox_eq_singleton_of_proper_closed_convex` identifies the relevant
-- proximal set as a singleton, and `block_partial_prox_grad_point` is defined to be its unique
-- point.
/-- The one-block proximal-gradient point is the unique proximal point of `(1 / M) g_i` at
`x_i - (1 / M) • block_gradient_i(x)`. -/
theorem block_partial_prox_grad_point_eq_singleton
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : ((i : ι) → Ei i)) (i : ι) :
    prox[((((1 / M : PosReal) : EReal) • g i))]
      (x i - (1 / M : ℝ) • block_gradient i x) =
        {T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} :=
  by
    let hscaled :=
      scaled_function_proper_closed_convex_of_pos
        (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
    -- The Chapter 11 block prox point is defined by choosing the unique element of this singleton.
    simpa [block_partial_prox_grad_point, hscaled] using
      (Classical.choose_spec <|
        prox_eq_singleton_of_proper_closed_convex
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x))

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

-- Proof sketch: rewrite `G^i_{M_i}(x) = 0` via the defining residual formula, apply the second
-- prox theorem blockwise to identify the proximal fixed-point condition with blockwise
-- subdifferential membership, and then invoke part (1) at the same finite-domain interior point.
section

variable [instBlockInner : InnerProductSpace ℝ ((i : ι) → Ei i)]
local instance : NormedSpace ℝ ((i : ι) → Ei i) := InnerProductSpace.toNormedSpace
local instance : Module ℝ ((i : ι) → Ei i) := NormedSpace.toModule
variable [FiniteDimensional ℝ ((i : ι) → Ei i)]

/-- Helper for Theorem 11.1: for a fixed block, vanishing of the block gradient mapping is
equivalent to the negative block gradient belonging to the Euclidean subdifferential of the
corresponding block penalty. -/
theorem block_partial_gradient_mapping_eq_zero_iff_negative_block_gradient_mem_euclideanSubdifferential
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : ((i : ι) → Ei i)) (i : ι) :
    G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
      -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
  have hfixed :
      G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
        T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i := by
    constructor
    · intro hG
      have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos M)
      have hres :
          x i - T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 := by
        rw [block_partial_gradient_mapping_def] at hG
        exact (smul_eq_zero.mp hG).resolve_left hM_ne
      -- A zero residual means the prox point is already the current block.
      exact (sub_eq_zero.mp hres).symm
    · intro hT
      -- Conversely, a blockwise fixed point makes the residual formula collapse to zero.
      rw [block_partial_gradient_mapping_def, hT]
      simp
  have hprox_self :
      T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i ↔
        prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} := by
    constructor
    · intro hT
      -- Rewrite only the singleton target, leaving the forward point unchanged.
      simpa [hT] using
        block_partial_prox_grad_point_eq_singleton
          g block_gradient hg_proper hg_closed hg_convex M x i
    · intro hprox
      have hsingleton :
          ({T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) =
            ({x i} : Set (Ei i)) := by
        calc
          ({T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) =
              prox[((((1 / M : PosReal) : EReal) • g i))]
                (x i - (1 / M : ℝ) • block_gradient i x) := by
            symm
            exact
              block_partial_prox_grad_point_eq_singleton
                g block_gradient hg_proper hg_closed hg_convex M x i
          _ = ({x i} : Set (Ei i)) := hprox
      have hmem :
          T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i ∈
            ({x i} : Set (Ei i)) := by
        simpa [hsingleton] using
          (show T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i ∈
              ({T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) by
            simp)
      simpa using hmem
  have hprox_sub :
      prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} ↔
        (((1 / M : ℝ) •
            (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
              Module.Dual ℝ (Ei i))) :
              Module.Dual ℝ (Ei i)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := by
    have hscaled :=
      scaled_function_proper_closed_convex_of_pos
        (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
    have hprox :
        prox[((((1 / M : PosReal) : EReal) • g i))]
            (x i - (1 / M : ℝ) • block_gradient i x) = {x i} ↔
          InnerProductSpace.toDualMap ℝ (Ei i)
              ((x i - (1 / M : ℝ) • block_gradient i x) - x i) ∈
            strongDualSubdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := by
      -- Apply the second prox theorem to the scaled block penalty at the forward block-gradient
      -- point.
      simpa using
        (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x)
          (x i))
    -- Rewrite the strong-dual conclusion into the Chapter 3 owner `subdifferential`.
    simpa [mem_strongDualSubdifferential, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      sub_eq_add_neg, smul_neg, neg_smul] using hprox
  have hscaled_sub :
      (((1 / M : ℝ) •
          (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
            Module.Dual ℝ (Ei i))) :
            Module.Dual ℝ (Ei i)) ∈
        subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) ↔
      (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
          Module.Dual ℝ (Ei i)) ∈
        subdifferential (g i) (x i) := by
    have hM_pos : 0 < (1 / M : ℝ) := one_div_pos.mpr (PosReal.coe_pos M)
    have hscaled :
        subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) =
          (1 / M : ℝ) • subdifferential (g i) (x i) := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (subdifferential_pos_real_mul (g i) (1 / M : ℝ) hM_pos (x i))
    have hM_ne : (1 / M : ℝ) ≠ 0 := ne_of_gt hM_pos
    -- Positive scaling of the block penalty scales the owner subdifferential by the same scalar.
    constructor
    · intro hmem
      rw [hscaled, Set.mem_smul_set] at hmem
      rcases hmem with ⟨y, hy, hy_eq⟩
      have hy' :
          y =
            (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
              Module.Dual ℝ (Ei i)) := by
        have hM0 : (M : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos M)
        have happly :=
          congrArg (fun z : Module.Dual ℝ (Ei i) ↦ ((1 / M : ℝ)⁻¹) • z) hy_eq
        simpa [smul_smul, one_div, hM0] using happly
      simpa [hy'] using hy
    · intro hmem
      rw [hscaled, Set.mem_smul_set]
      refine ⟨(-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
          Module.Dual ℝ (Ei i)), hmem, ?_⟩
      simp
  have heuclidean :
      (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
          Module.Dual ℝ (Ei i)) ∈
        subdifferential (g i) (x i) ↔
      -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := by
    -- The owner subdifferential and the Euclidean/block-vector view are the same via Riesz.
    simpa [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential,
      InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  calc
    G[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = 0 ↔
        T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i = x i := hfixed
    _ ↔
        prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) = {x i} := hprox_self
    _ ↔
        (((1 / M : ℝ) •
            (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
              Module.Dual ℝ (Ei i))) :
              Module.Dual ℝ (Ei i)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g i)) (x i) := hprox_sub
    _ ↔
        (-InnerProductSpace.toDual ℝ (Ei i) (block_gradient i x) :
            Module.Dual ℝ (Ei i)) ∈
          subdifferential (g i) (x i) := hscaled_sub
    _ ↔ -(block_gradient i x) ∈ euclideanSubdifferential (g i) (x i) := heuclidean

/-- Theorem 11.1 (2): for any positive block stepsizes `M i`, stationarity of the block-separable
composite problem is equivalent to vanishing of every block gradient mapping `G^i_{M_i}(x)`,
assuming only the blockwise proper/closed/convex hypotheses needed to define `G^i_{M_i}` and the
block-slice Fréchet-derivative specification for the chosen block partial gradients, again at
points in the interior of the finite domain of `f` required by the stationarity owner. -/
theorem is_stationary_point_iff_block_partial_gradient_mapping_eq_zero
    {f : ((i : ι) → Ei i) → EReal}
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (hblock_fderiv_spec : ∀ (i : ι) {x : ((j : ι) → Ei j)},
        x ∈ interior (finite_domain f) →
          HasFDerivAt (block_coordinate_slice f x i)
            (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0)
    (M : (i : ι) → PosReal) (x : interior (finite_domain f)) :
    is_stationary_point f (separableSum g) (x : ((i : ι) → Ei i)) ↔
      ∀ i : ι,
        G[M i; g, block_gradient, hg_proper, hg_closed, hg_convex]
          (x : ((i : ι) → Ei i)) i = 0 :=
  -- TODO: part (b) is reduced blockwise by
  -- `block_partial_gradient_mapping_eq_zero_iff_negative_block_gradient_mem_euclideanSubdifferential`,
  -- then closed using part (a). The remaining blocker is the missing ambient differentiability
  -- hypothesis needed to justify part (a) as stated.
  sorry

end

end
