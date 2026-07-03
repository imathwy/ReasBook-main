import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_4 (from Chap11) -/
noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}

/-- The block-separable regularizer `x ↦ ∑ i, g_i(x_i)` is proper when every block penalty `g_i`
is proper. -/
theorem separableSum_proper
    (g : (i : ι) → Ei i → EReal)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i)) :
    IsProperExtendedRealFunction (separableSum g) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ (fun i ↦ g i (x i))
      (fun i _ ↦ (hg_proper i).ne_bot (x i))
  · let x : (i : ι) → Ei i := fun i ↦ Classical.choose (hg_proper i).effective_domain_nonempty
    have hx : ∀ i, x i ∈ effective_domain (g i) := by
      intro i
      exact Classical.choose_spec (hg_proper i).effective_domain_nonempty
    refine ⟨x, ?_⟩
    rw [mem_effective_domain, separableSum_apply]
    exact ereal_sum_lt_top Finset.univ (fun i ↦ g i (x i))
      (fun i _ ↦ mem_effective_domain.mp (hx i))

/-- A finite value of the block-separable regularizer forces each coordinate penalty to be finite.
-/
theorem block_mem_effective_domain_of_mem_separableSum_effective_domain
    (g : (i : ι) → Ei i → EReal)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) (i : ι) :
    x i ∈ effective_domain (g i) := by
  classical
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hgi_top
  have hrest_ne_bot :
      Finset.sum (Finset.univ.erase i) (fun j ↦ g j (x j)) ≠ ⊥ := by
    exact ereal_sum_ne_bot (Finset.univ.erase i) (fun j ↦ g j (x j))
      (fun j _ ↦ (hg_proper j).ne_bot (x j))
  have hsum :
      Finset.sum Finset.univ (fun j ↦ g j (x j)) =
        g i (x i) + Finset.sum (Finset.univ.erase i) (fun j ↦ g j (x j)) := by
    symm
    exact Finset.add_sum_erase Finset.univ (fun j ↦ g j (x j)) (Finset.mem_univ i)
  have hsum_eq_top : separableSum g x = ⊤ := by
    rw [separableSum_apply, hsum, hgi_top, EReal.top_add_of_ne_bot hrest_ne_bot]
  exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hx)) hsum_eq_top

instance instIsProperExtendedRealFunctionSeparableSum
    (g : (i : ι) → Ei i → EReal) [∀ i, IsProperExtendedRealFunction (g i)] :
    IsProperExtendedRealFunction (separableSum g) :=
  separableSum_proper g (fun i ↦ (inferInstance : IsProperExtendedRealFunction (g i)))

end

-- DIAGNOSTIC_BOUNDARY
section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, TopologicalSpace (Ei i)]

/-- Helper for Definition 11.4: composing a block penalty with the coordinate projection preserves
lower semicontinuity. -/
lemma coordinate_eval_lowerSemicontinuous
    (g : (i : ι) → Ei i → EReal) (i : ι)
    (hg : LowerSemicontinuous (g i)) :
    LowerSemicontinuous (fun x : ((j : ι) → Ei j) ↦ g i (x i)) := by
  -- Pull back lower semicontinuity along the continuous coordinate projection.
  simpa [Function.comp] using hg.comp (continuous_apply i)

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, TopologicalSpace (Ei i)]

/-- Helper for Definition 11.4: a finite sum of `EReal`-valued lower semicontinuous functions is
lower semicontinuous. -/
lemma lowerSemicontinuous_finset_sum_ereal
    {κ α : Type*} [TopologicalSpace α] (a : Finset κ) (f : κ → α → EReal)
    (ha : ∀ i ∈ a, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x : α ↦ Finset.sum a (fun i ↦ f i x)) := by
  classical
  revert ha
  refine Finset.induction_on a ?_ ?_
  · intro _ha
    -- The empty sum is the constant zero function.
    simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : α ↦ (0 : EReal)))
  · intro i s hi ih hs
    have hi_lsc : LowerSemicontinuous (f i) := hs i (by simp)
    have hs_lsc : LowerSemicontinuous (fun x : α ↦ Finset.sum s (fun j ↦ f j x)) := by
      -- Restrict the family hypothesis to the tail of the finite sum.
      refine ih ?_
      intro j hj
      exact hs j (by simp [hj])
    -- Route correction: use the liminf characterization and `EReal.le_liminf_add` instead of the
    -- unavailable `[ContinuousAdd EReal]` finite-sum API.
    refine (lowerSemicontinuous_iff_le_liminf).2 ?_
    intro x
    have hi_le : f i x ≤ Filter.liminf (f i) (nhds x) := hi_lsc.le_liminf x
    have hs_le :
        Finset.sum s (fun j ↦ f j x) ≤
          Filter.liminf (fun y ↦ Finset.sum s (fun j ↦ f j y)) (nhds x) := hs_lsc.le_liminf x
    -- Rewrite the inserted sum as a head-plus-tail decomposition, then combine the liminf bounds.
    calc
      Finset.sum (insert i s) (fun j ↦ f j x) = f i x + Finset.sum s (fun j ↦ f j x) := by
        simp [Finset.sum_insert, hi]
      _ ≤
          Filter.liminf (f i) (nhds x) +
            Filter.liminf (fun y ↦ Finset.sum s (fun j ↦ f j y)) (nhds x) :=
        add_le_add hi_le hs_le
      _ ≤ Filter.liminf (fun y ↦ f i y + Finset.sum s (fun j ↦ f j y)) (nhds x) :=
        EReal.le_liminf_add
      _ = Filter.liminf (fun y ↦ Finset.sum (insert i s) (fun j ↦ f j y)) (nhds x) := by
        simp [hi]

/-- The block-separable regularizer `x ↦ ∑ i, g_i(x_i)` is lower semicontinuous when every block
penalty `g_i` is lower semicontinuous. -/
theorem separableSum_closed
    (g : (i : ι) → Ei i → EReal)
    (hg_closed : ∀ i, LowerSemicontinuous (g i)) :
    LowerSemicontinuous (separableSum g) := by
  classical
  have hcoord :
      ∀ i, LowerSemicontinuous (fun x : ((j : ι) → Ei j) ↦ g i (x i)) := by
    intro i
    -- Each summand is the pullback of a block penalty along the `i`-th coordinate evaluation map.
    exact coordinate_eval_lowerSemicontinuous g i (hg_closed i)
  -- Apply the `EReal`-specific finite-sum lemma to the coordinate summands.
  simpa [separableSum] using
    lowerSemicontinuous_finset_sum_ereal
      (a := Finset.univ)
      (f := fun i ↦ fun x : ((j : ι) → Ei j) ↦ g i (x i))
      (fun i _ ↦ hcoord i)

instance instFactLowerSemicontinuousSeparableSum
    (g : (i : ι) → Ei i → EReal) [∀ i, Fact (LowerSemicontinuous (g i))] :
    Fact (LowerSemicontinuous (separableSum g)) :=
  ⟨separableSum_closed g (fun i ↦ (Fact.out : LowerSemicontinuous (g i)))⟩

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, AddCommMonoid (Ei i)] [∀ i, Module ℝ (Ei i)]

/-- The block-separable regularizer `x ↦ ∑ i, g_i(x_i)` is convex when every block penalty `g_i`
is convex. -/
theorem separableSum_convex
    (g : (i : ι) → Ei i → EReal)
    (hg_convex : ∀ i, is_convex_function (g i)) :
    is_convex_function (separableSum g) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let G : Fin (Fintype.card ι) → ((i : ι) → Ei i) → EReal :=
    fun k x ↦ g (e.symm k) (x (e.symm k))
  have hG : ∀ k : Fin (Fintype.card ι), is_convex_function (G k) := by
    intro k
    -- Each coordinate summand inherits convexity directly from the corresponding block penalty.
    rw [is_convex_function_iff_segment_ineq]
    intro x hx y hy t ht
    simpa [G] using
      (is_convex_function_iff_segment_ineq (f := g (e.symm k))).1
        (hg_convex (e.symm k))
        (x (e.symm k))
        hx
        (y (e.symm k))
        hy
        ht
  have hsum :
      is_convex_function
        (fun x : ((i : ι) → Ei i) ↦
          ∑ k : Fin (Fintype.card ι), G k x) := by
    simpa [G] using
      is_convex_function_finset_nonneg_weighted_sum
        (f := G) hG (fun _ ↦ (1 : NNReal))
  have hsum_eq :
      (fun x : ((i : ι) → Ei i) ↦
        ∑ k : Fin (Fintype.card ι), G k x) = separableSum g := by
    funext x
    -- Reindex the finite sum from `Fin (card ι)` back to the original block index type.
    simpa [G, e, separableSum] using
      (Fintype.sum_equiv e
        (fun i ↦ g i (x i))
        (fun k ↦ G k x)
        (fun i ↦ by
          simpa [G] using congrArg (fun j : ι ↦ g j (x j)) (e.left_inv i).symm)).symm
  simpa [hsum_eq] using hsum

instance instFactIsConvexFunctionSeparableSum
    (g : (i : ι) → Ei i → EReal) [∀ i, Fact (is_convex_function (g i))] :
    Fact (is_convex_function (separableSum g)) :=
  ⟨separableSum_convex g (fun i ↦ (Fact.out : is_convex_function (g i)))⟩

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, Zero (Ei i)]

/- The canonical dependent-product block insertion map is the existing owner `Pi.single`; the
source-facing Chapter 11 surface uses the textbook notation `𝒰[i]`. -/
notation "𝒰[" i "]" => @Pi.single _ _ _ (Classical.decEq _) i

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, AddZeroClass (Ei i)]

local instance : DecidableEq ι := Classical.decEq ι

/-- Updating only the `i`-th block of `x` by the displacement `d`, equivalently `x + 𝒰[i] d`. -/
def block_coordinate_update
    (x : (i : ι) → Ei i) (i : ι) (d : Ei i) : (i : ι) → Ei i :=
  x + 𝒰[i] d

-- Proof sketch: in the updated block we add the inserted displacement `d` to `x i`.
/-- The `i`-th coordinate of the one-block update is `x i + d`. -/
@[simp] theorem block_coordinate_update_apply_same
    (x : (i : ι) → Ei i) (i : ι) (d : Ei i) :
    block_coordinate_update x i d i = x i + d := by
  -- At the updated coordinate, `Pi.single` contributes exactly the inserted displacement.
  classical
  simp [block_coordinate_update]

-- Proof sketch: away from the updated block the inserted displacement vanishes.
/-- Away from the updated block, `block_coordinate_update` agrees with the original point. -/
@[simp] theorem block_coordinate_update_apply_ne
    (x : (i : ι) → Ei i) {i j : ι} (d : Ei i) (hji : j ≠ i) :
    block_coordinate_update x i d j = x j := by
  -- Away from the chosen block, `Pi.single` vanishes.
  classical
  simp [block_coordinate_update, hji]

-- Proof sketch: compare `block_coordinate_update x i d` and `Function.update x i (x i + d)`
-- coordinatewise; both agree with `x i + d` at the active block and with `x` elsewhere.
/-- Updating block `i` by the displacement `d` is the same as `Function.update` at the new block
value `x i + d`. -/
theorem block_coordinate_update_eq_update
    [DecidableEq ι]
    (x : (i : ι) → Ei i) (i : ι) (d : Ei i) :
    block_coordinate_update x i d =
      Function.update x i (x i + d) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [block_coordinate_update]
  · simp [block_coordinate_update, Function.update, hj]

/-- Fixing all blocks except the `i`-th one turns the smooth term `f` into the one-block slice
`d ↦ f(x + 𝒰[i] d)`. -/
def block_coordinate_slice (f : ((i : ι) → Ei i) → EReal)
    (x : (i : ι) → Ei i) (i : ι) : Ei i → ℝ :=
  fun d ↦ (f (block_coordinate_update x i d)).toReal

-- Proof sketch: unfold `block_coordinate_slice`; evaluation at `d` is exactly the translated
-- one-block slice `f (x + 𝒰[i] d)`.
/-- Evaluating the `i`-th block slice at `d` gives
`(f (x + 𝒰[i] d)).toReal`. -/
@[simp] theorem block_coordinate_slice_apply
    (f : ((i : ι) → Ei i) → EReal) (x : (i : ι) → Ei i) (i : ι) (d : Ei i) :
    block_coordinate_slice f x i d = (f (block_coordinate_update x i d)).toReal :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- Positive scaling preserves properness, lower semicontinuity, and convexity. -/
lemma scaled_function_pcc_of_pos
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (lam : PosReal) :
    IsProperExtendedRealFunction (((lam : EReal) • f)) ∧
      LowerSemicontinuous (((lam : EReal) • f)) ∧
      is_convex_function (((lam : EReal) • f)) := by
  -- Reuse the canonical Chapter 6 scaling package instead of duplicating the epigraph argument.
  simpa using
    scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/-- The one-block proximal-gradient update determined by the block partial gradient
`block_gradient i x`. -/
def block_partial_prox_grad_point
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  let hg_scaled := scaled_function_pcc_of_pos
    (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
  Classical.choose <|
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / M : PosReal) : EReal) • g i))
      hg_scaled.1
      hg_scaled.2.1
      hg_scaled.2.2
      (x i - (1 / M : ℝ) • block_gradient i x)

/-- The block partial gradient mapping `G^i_M(x)` is the stepsize-scaled residual of the current
block and its one-block proximal-gradient update. -/
def block_partial_gradient_mapping
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  (M : ℝ) •
    (x i - block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x)

/-- Textbook notation for the Chapter 11 one-block proximal-gradient update `T_M^i(x)`. -/
scoped[Gradient] notation3:max
    "T[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x

/-- Direct-application form of the Chapter 11 notation `T_M^i(x)`. -/
scoped[Gradient] notation3:max
    "T[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x

/-- Textbook notation for the Chapter 11 block partial gradient mapping `G_M^i(x)`. -/
scoped[Gradient] notation3:max
    "G[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x

/-- Direct-application form of the Chapter 11 notation `G_M^i(x)`. -/
scoped[Gradient] notation3:max
    "G[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x

-- Proof sketch: unfold `block_partial_gradient_mapping`; the statement is exactly the defining
-- residual formula `M • (x_i - T_M^i(x))`.
/-- Evaluating the block partial gradient mapping gives the stepsize-scaled residual
`M • (x_i - T_M^i(x))`. -/
@[simp] theorem block_partial_gradient_mapping_def
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : (i : ι) → Ei i) (i : ι) [ProperSpace (Ei i)] :
    block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x =
      (M : ℝ) •
        (x i -
          block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x) :=
  rfl

end

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/- The blockwise data common to Definitions 11.4 and 11.13 already form a reusable Chapter 11
`core/canonical` owner. The source-facing items then add only their genuinely extra hypotheses:
Definition 11.4 adds convexity of `effective_domain f` together with a global `L_f`-smoothness
bound, while Definition 11.13 adds convexity and mere differentiability of `f`. -/

/-- The Chapter 11 core owner for block proximal-gradient problems packages the blockwise penalty
assumptions, the domain-compatibility and optimizer data, and the one-block gradient/Lipschitz
clauses determined by the explicit block constants `L_i`. -/
class IsBlockProximalGradientProblem
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (XStar : Set ((i : ι) → Ei i)) (FOpt : ℝ)
    (Li : (i : ι) → PosReal) : Prop where
  f_ne_bot (x) : f x ≠ ⊥
  block_g_proper (i) : IsProperExtendedRealFunction (g i)
  block_g_closed (i) : LowerSemicontinuous (g i)
  block_g_convex (i) : is_convex_function (g i)
  f_closed : LowerSemicontinuous f
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain (separableSum g) ⊆ interior (effective_domain f)
  optimal_set_eq :
    XStar =
      unconstrained_problem_solutions
        (composite_model_objective f (separableSum g))
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB
      (Set.range (composite_model_objective f (separableSum g)))
      (FOpt : EReal)
  block_partial_gradient_spec
      (i : ι) {x : (i : ι) → Ei i}
      (hx : x ∈ interior (effective_domain f)) :
      HasFDerivAt (block_coordinate_slice f x i)
        (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x)) 0
  block_partial_gradient_lipschitz
      (i : ι) {x : (i : ι) → Ei i} {d : Ei i}
      (hx : x ∈ interior (effective_domain f))
      (hxd : block_coordinate_update x i d ∈ interior (effective_domain f)) :
      ‖block_gradient i x - block_gradient i (block_coordinate_update x i d)‖ ≤
        (Li i : ℝ) * ‖d‖

/- Definition 11.4 is `source-facing`: it fixes the standing assumptions for the block proximal
gradient method in their textbook blockwise form. With the shared Chapter 11 core owner above,
the only additional primitive data here are the convexity of `effective_domain f` and the global
`L_f`-smoothness of `(fun x ↦ (f x).toReal)` on `interior (effective_domain f)`. The Chapter 10
owner `IsCompositeSmoothMinimizationProblem` remains the downstream `bridge/view`. -/

/-- Definition 11.4: assumptions (A)-(E) for the block proximal-gradient method mean that each
block penalty `g_i : E_i → (-∞, ∞]` is proper, closed, and convex; the smooth term
`f : (Π i, E_i) → (-∞, ∞]` never takes the value `-∞`, is closed with convex effective domain,
the effective domain of `x ↦ ∑ i, g_i(x_i)` lies in the interior of the effective domain of `f`,
and `x ↦ (f x).toReal` is differentiable and `L_f`-smooth on that interior, so these clauses imply
that `f` is proper; for each block index `i`, the chosen block gradient map
`block_gradient i x = ∇_i f(x)` is the gradient of the one-block slice
`d ↦ f(x + 𝒰[i] d)` at `d = 0` and is `L_i`-Lipschitz along the `i`-th block direction;
and `XStar = X^*` is the nonempty optimal set of the composite objective with optimal value
`FOpt = F_opt`. -/
class BlockProximalGradientAssumptions
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (XStar : Set ((i : ι) → Ei i)) (FOpt : ℝ)
    (Lf : NNReal) (Li : (i : ι) → PosReal) : Prop
    extends IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li where
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  f_toReal_smooth_on_interior_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf

/-- The source-facing Chapter 11 assumptions inherit the shared block proximal-gradient problem
owner. -/
instance instIsBlockProximalGradientProblemOfBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
  h.toIsBlockProximalGradientProblem

namespace IsBlockProximalGradientProblem

/-- The canonical one-block proximal-gradient update attached to a Chapter 11 block problem owner.
-/
abbrev prox_point
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  block_partial_prox_grad_point
    g
    block_gradient
    h.block_g_proper
    h.block_g_closed
    h.block_g_convex
    M
    i
    x

/-- The canonical one-block partial gradient mapping attached to a Chapter 11 block problem owner.
-/
abbrev gradient_mapping
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (i : ι) → Ei i) : Ei i :=
  block_partial_gradient_mapping
    g
    block_gradient
    h.block_g_proper
    h.block_g_closed
    h.block_g_convex
    M
    i
    x

/-- Evaluating the owner-level one-block residual map gives the textbook formula
`M • (x_i - T_M^i(x))`. -/
@[simp] theorem gradient_mapping_def
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (x : (i : ι) → Ei i) (i : ι) [ProperSpace (Ei i)] :
    h.gradient_mapping M i x = (M : ℝ) • (x i - h.prox_point M i x) :=
  rfl

/-- The owner-level one-block prox point lies in the effective domain of the selected block
penalty. -/
theorem prox_point_mem_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (i : ι) [ProperSpace (Ei i)] (x : (j : ι) → Ei j) :
    h.prox_point M i x ∈ effective_domain (g i) := by
  let hscaled :=
    scaled_function_pcc_of_pos
      (g i)
      (h.block_g_proper i)
      (h.block_g_closed i)
      (h.block_g_convex i)
      (1 / M)
  have hprox :
      prox[((((1 / M : PosReal) : EReal) • g i))]
          (x i - (1 / M : ℝ) • block_gradient i x) =
        {h.prox_point M i x} := by
    simpa [IsBlockProximalGradientProblem.prox_point, block_partial_prox_grad_point, hscaled] using
      (Classical.choose_spec <|
        prox_eq_singleton_of_proper_closed_convex
          ((((1 / M : PosReal) : EReal) • g i))
          hscaled.1
          hscaled.2.1
          hscaled.2.2
          (x i - (1 / M : ℝ) • block_gradient i x))
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g i)
      (μ := 1 / M)
      (h.block_g_proper i)
      (h.block_g_convex i)
      (x i - (1 / M : ℝ) • block_gradient i x)
      (h.prox_point M i x)
      hprox with
    ⟨hmem, _⟩
  simpa using hmem

/-- Replacing one block by the owner-level prox point preserves the effective domain of the
block-separable regularizer. -/
theorem block_coordinate_update_prox_point_mem_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (M : PosReal) (x : effective_domain (separableSum g)) (i : ι) [ProperSpace (Ei i)] :
    let x' : (j : ι) → Ei j := x.1
    block_coordinate_update x' i (h.prox_point M i x' - x' i) ∈
      effective_domain (separableSum g) := by
  let x' : (j : ι) → Ei j := x.1
  let xPlus : (j : ι) → Ei j :=
    block_coordinate_update x' i (h.prox_point M i x' - x' i)
  have hx_top : ∀ j, g j (x' j) < ⊤ := by
    intro j
    exact
      mem_effective_domain.mp
        (block_mem_effective_domain_of_mem_separableSum_effective_domain g h.block_g_proper x.2 j)
  have hxPlus_top : ∀ j, g j (xPlus j) < ⊤ := by
    intro j
    by_cases hji : j = i
    · subst j
      have hi_mem : h.prox_point M i x' ∈ effective_domain (g i) :=
        h.prox_point_mem_effective_domain M i x'
      simpa [xPlus, block_coordinate_update] using mem_effective_domain.mp hi_mem
    · simpa [xPlus, block_coordinate_update, hji] using hx_top j
  rw [mem_effective_domain, separableSum_apply]
  exact ereal_sum_lt_top Finset.univ (fun j ↦ g j (xPlus j)) (fun j _ ↦ hxPlus_top j)

/- Textbook notation for the Chapter 11 one-block proximal-gradient update `T_M^i(x)` attached
to a block-problem owner. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "T[" M "; " h "]" =>
  fun x i ↦ IsBlockProximalGradientProblem.prox_point h M i x

/- Direct-application form of the Chapter 11 owner notation `T_M^i(x)`. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "T[" M "; " h "]" x:arg i:arg =>
  IsBlockProximalGradientProblem.prox_point h M i x

/- Textbook notation for the Chapter 11 block partial gradient mapping `G_M^i(x)` attached to a
block-problem owner. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "G[" M "; " h "]" =>
  fun x i ↦ IsBlockProximalGradientProblem.gradient_mapping h M i x

/- Direct-application form of the Chapter 11 owner notation `G_M^i(x)`. -/
set_option quotPrecheck false in
scoped[Gradient] notation:max "G[" M "; " h "]" x:arg i:arg =>
  IsBlockProximalGradientProblem.gradient_mapping h M i x

/-- Under blockwise completeness, the primitive Fréchet-derivative specification recovers the
usual gradient formulation for the one-block slice. -/
-- Proof sketch: `HasGradientAt` is the Hilbert-space reformulation of `HasFDerivAt` through
-- `InnerProductSpace.toDualMap`, so the class field already provides the desired statement.
theorem block_partial_gradient_hasGradientAt
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (i : ι) → Ei i}
    (hx : x ∈ interior (effective_domain f)) :
    HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0 := by
  -- The class field is already the Fréchet-derivative version of the desired gradient statement.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using h.block_partial_gradient_spec i hx

/-- The blockwise properness assumptions and the domain-compatibility clause force
`effective_domain f` to be nonempty. -/
-- Proof sketch: use a finite point in `effective_domain (separableSum g)` from blockwise
-- properness, then push it into `interior (effective_domain f)` via the compatibility field.
theorem f_effective_domain_nonempty
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    (effective_domain f).Nonempty := by
  rcases (separableSum_proper g h.block_g_proper).effective_domain_nonempty with ⟨x, hx⟩
  -- The compatibility field moves a finite point of `separableSum g` into the interior of
  -- `effective_domain f`, hence in particular into `effective_domain f` itself.
  exact ⟨x, interior_subset (h.g_effective_domain_subset_interior_f_effective_domain hx)⟩

/-- Under the Chapter 11 block proximal-gradient assumptions, every point of the effective domain
of the block-separable regularizer lies in `interior (effective_domain f)`. -/
theorem mem_interior_effective_domain_of_mem_g_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    {x : (i : ι) → Ei i} (hx : x ∈ effective_domain (separableSum g)) :
    x ∈ interior (effective_domain f) :=
  h.g_effective_domain_subset_interior_f_effective_domain hx

/-- A point in the effective domain of the block-separable regularizer canonically determines a
point of `interior (effective_domain f)` under the Chapter 11 assumptions. -/
def interior_effective_domain_point
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : effective_domain (separableSum g)) : interior (effective_domain f) :=
  ⟨x, h.mem_interior_effective_domain_of_mem_g_effective_domain x.2⟩

/-- Coercing the canonical interior-domain point attached to
`x ∈ effective_domain (separableSum g)` recovers `x`. -/
@[simp] theorem interior_effective_domain_point_coe
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : effective_domain (separableSum g)) :
    ((h.interior_effective_domain_point x : interior (effective_domain f)) :
        ((i : ι) → Ei i)) = x :=
  rfl

/-- The Chapter 11 block proximal-gradient assumptions canonically provide properness of `f`. -/
-- Proof sketch: combine the primitive non-`⊥` field with the derived nonemptiness of
-- `effective_domain f`.
theorem f_proper
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    IsProperExtendedRealFunction f := by
  refine ⟨h.f_ne_bot, h.f_effective_domain_nonempty⟩

/-- The smooth term of a Chapter 11 block proximal-gradient problem is proper. -/
instance instIsProperExtendedRealFunctionOfIsBlockProximalGradientProblem
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li) :
    IsProperExtendedRealFunction f :=
  h.f_proper

end IsBlockProximalGradientProblem

namespace BlockProximalGradientAssumptions

/-- The source-facing block proximal-gradient assumptions canonically induce the Chapter 10
composite smooth minimization owner for the aggregate regularizer
`x ↦ ∑ i, g_i(x_i)`. -/
-- Proof sketch: populate the Chapter 10 owner field-by-field from the Chapter 11 blockwise
-- assumptions and the separable-sum bridge lemmas for properness, closedness, and convexity.
theorem toIsCompositeSmoothMinimizationProblem
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsCompositeSmoothMinimizationProblem
      f (separableSum g) XStar FOpt Lf := by
  -- Populate the Chapter 10 owner directly from the Chapter 11 owner fields and the
  -- aggregate regularizer bridge lemmas proved above.
  refine
    { f_ne_bot := h.f_ne_bot
      g_proper := separableSum_proper g h.block_g_proper
      f_closed := h.f_closed
      g_closed := separableSum_closed g h.block_g_closed
      g_convex := separableSum_convex g h.block_g_convex
      f_effective_domain_convex := h.f_effective_domain_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        h.g_effective_domain_subset_interior_f_effective_domain
      f_toReal_smooth_on_interior_effective_domain :=
        h.f_toReal_smooth_on_interior_effective_domain
      optimal_set_eq := h.optimal_set_eq
      optimal_set_nonempty := h.optimal_set_nonempty
      optimal_value_isGLB := h.optimal_value_isGLB }

/-- The induced aggregate regularizer `x ↦ ∑ i, g_i(x_i)` is proper. -/
theorem separableSum_proper
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    IsProperExtendedRealFunction (separableSum g) :=
  (toIsCompositeSmoothMinimizationProblem h).g_proper

/-- The induced aggregate regularizer `x ↦ ∑ i, g_i(x_i)` is lower semicontinuous. -/
theorem separableSum_closed
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    LowerSemicontinuous (separableSum g) :=
  (toIsCompositeSmoothMinimizationProblem h).g_closed

/-- The induced aggregate regularizer `x ↦ ∑ i, g_i(x_i)` is convex. -/
theorem separableSum_convex
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    is_convex_function (separableSum g) :=
  (toIsCompositeSmoothMinimizationProblem h).g_convex

/-- The Chapter 10 smoothness owner reused by Definition 11.4 already implies differentiability
of `x ↦ (f x).toReal` on `interior (effective_domain f)`. -/
-- Proof sketch: the `L_f`-smoothness field in the induced Chapter 10 owner yields a derivative at
-- each interior-domain point, hence differentiability on that set.
theorem f_toReal_differentiableOn_interior_effective_domain
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal} {Li : (i : ι) → PosReal}
    (h :
      BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li) :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f)) := by
  intro x hx
  -- Smoothness on the interior gives pointwise differentiability there, and `DifferentiableOn`
  -- is the within-set version of that pointwise statement.
  have hsmooth :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf :=
    (toIsCompositeSmoothMinimizationProblem h).f_toReal_smooth_on_interior_effective_domain
  exact (hsmooth.1 x hx).differentiableWithinAt

end BlockProximalGradientAssumptions

end

/-! ### Lemma_11_4 (from Chap11) -/
noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/- Lemma 11.4 is a `bridge/view` file in the Chapter 11 CBPG domain.

Domain sampling against the surrounding owner declarations identifies:
- `cyclic_block_proximal_gradient_method` and
  `cyclic_block_proximal_gradient_inner_iterate` from Algorithm 11.4 as the iterate owners;
- the one-block sufficient-decrease owner from Lemma 11.3 as the source-faithful route for
  parts (a) and (b), once that upstream file is available in a compilable state;
- `PiLp (2 : ENNReal) Ei` together with `PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei` as the
  canonical Hilbert-product owner for the full-cycle norm in equation (11.11).

Primitive data here are only the Chapter 11 CBPG assumption package, the initial effective-domain
point, and the finite block-step family `Li`. The decrease statements below are derived API on the
CBPG iterates, so the public surface should reuse the block owner directly and keep the block
index at the canonical `Fin p` level rather than as a natural number plus a separate bound proof.
For the outer-step estimate, the norm must live on the canonical `L²` product owner rather than
on the raw dependent-function sup norm.
-/

section

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The minimum block Lipschitz constant `L_min = min_i L_i` of a nonempty finite block family
`i ↦ L_i`. -/
def cbpg_min_block_stepsize (Li : ι → PosReal) : PosReal :=
  Finset.univ.inf' Finset.univ_nonempty Li

/-- The maximum block Lipschitz constant `L_max = max_i L_i` of a nonempty finite block family
`i ↦ L_i`. -/
def cbpg_max_block_stepsize (Li : ι → PosReal) : PosReal :=
  Finset.univ.sup' Finset.univ_nonempty Li

/-- Expanding `cbpg_max_block_stepsize` yields the finite maximum of the block constants
`i ↦ L_i`. -/
theorem cbpg_max_block_stepsize_def (Li : ι → PosReal) :
    cbpg_max_block_stepsize Li =
      Finset.univ.sup' Finset.univ_nonempty Li :=
  rfl

end

section

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "F" => composite_model_objective f (separableSum g)
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
local notation "x0'" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0' k
local notation "x[" k "," i "]" =>
  cyclic_block_proximal_gradient_inner_iterate hproblem x[k] i

/-- Helper for Lemma 11.4: a single auxiliary CBPG step changes only its active block in the raw
product coordinates. -/
lemma cbpg_stage_difference_single
    (k : ℕ) (j : Fin p) :
    x[k, j.1] - x[k, j.1 + 1] =
      Pi.single j (x[k, j.1] j - x[k, j.1 + 1] j) := by
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The next auxiliary stage is exactly the owner one-block update in block `j`.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ
        (hproblem := hproblem)
        (x0 := x0')
        k
        j.2
  -- Coordinatewise, only the active block contributes to the stage difference.
  rw [hsucc]
  ext i
  by_cases hij : i = j
  · subst i
    simp [block_coordinate_update]
  · simp [block_coordinate_update, hij]

/-- Helper for Lemma 11.4: the raw-product norm of one auxiliary step is exactly the norm of its
updated block difference. -/
lemma cbpg_auxiliary_step_norm_eq_block_norm
    (k : ℕ) (j : Fin p) :
    ‖x[k, j.1] - x[k, j.1 + 1]‖ =
      ‖x[k, j.1] j - x[k, j.1 + 1] j‖ := by
  -- A singleton raw-product vector has norm equal to the norm of its active entry.
  rw [cbpg_stage_difference_single hproblem x0 k j]
  simpa using (Pi.norm_single (x[k, j.1] j - x[k, j.1 + 1] j))

/-- Helper for Lemma 11.4: after transporting to the canonical `PiLp` product, a single auxiliary
step is still supported on only its active block. -/
lemma cbpg_stage_difference_toPiLp_single
    (k : ℕ) (j : Fin p) :
    toPiLp x[k, j.1] - toPiLp x[k, j.1 + 1] =
      PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j) := by
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- Use the owner one-block update formula for the next auxiliary stage.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ
        (hproblem := hproblem)
        (x0 := x0')
        k
        j.2
  -- Transporting to `PiLp` preserves the same singleton support pattern.
  ext i
  rw [hsucc]
  by_cases hij : i = j
  · subst i
    simp [block_coordinate_update]
  · simp [block_coordinate_update, hij]

/-- Helper for Lemma 11.4: if the outer iterate `x^k` lies in the effective domain, then every
auxiliary inner stage `x^{k,m}` with `m ≤ p` also lies in the effective domain. -/
lemma cbpg_auxiliary_iterate_mem_effective_domain_of_outer_iterate
    (k : ℕ)
    (hxk : x[k] ∈ effective_domain (separableSum g))
    (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  induction m with
  | zero =>
      -- The zeroth inner stage is the current outer iterate itself.
      simpa using hxk
  | succ m ihm =>
      have hm_lt : m < p := Nat.lt_of_succ_le hm
      have hm_le : m ≤ p := Nat.le_of_lt hm_lt
      let jm : Fin p := ⟨m, hm_lt⟩
      let xm : effective_domain (separableSum g) :=
        ⟨x[k, m], ihm hm_le⟩
      have hsucc :
          x[k, m + 1] =
            block_coordinate_update
              x[k, m]
              jm
              (hproblem.toIsBlockProximalGradientProblem.prox_point (Li jm) jm x[k, m] -
                x[k, m] jm) := by
        -- The successor inner stage is exactly the owner one-block prox update.
        simpa [block_coordinate_update] using
          cyclic_block_proximal_gradient_method_inner_succ
            (hproblem := hproblem)
            (x0 := x0')
            k
            hm_lt
      have hnext :
          block_coordinate_update
              x[k, m]
              jm
              (hproblem.toIsBlockProximalGradientProblem.prox_point (Li jm) jm x[k, m] -
                x[k, m] jm) ∈
            effective_domain (separableSum g) := by
        -- Domain membership propagates through one owner-level prox update.
        simpa [xm] using
          IsBlockProximalGradientProblem.block_coordinate_update_prox_point_mem_effective_domain
            (h := hproblem.toIsBlockProximalGradientProblem)
            (M := Li jm)
            (x := xm)
            (i := jm)
      rw [hsucc]
      exact hnext

/-- Helper for Lemma 11.4: every auxiliary iterate `x^{k,m}` with `m ≤ p` stays in the effective
domain of the block-separable regularizer. -/
lemma cbpg_auxiliary_iterate_mem_effective_domain
    (k : ℕ) (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  induction k generalizing m with
  | zero =>
      have hx0 : x[0] ∈ effective_domain (separableSum g) := by
        -- The initial outer iterate is the given starting point in the effective domain.
        simpa using x0.2
      exact
        cbpg_auxiliary_iterate_mem_effective_domain_of_outer_iterate
          (hproblem := hproblem)
          (x0 := x0)
          0
          hx0
          m
          hm
  | succ k ih =>
      have hxsucc : x[k + 1] ∈ effective_domain (separableSum g) := by
        -- The next outer iterate is the terminal inner stage of the previous cycle.
        rw [cyclic_block_proximal_gradient_method_succ]
        exact ih p (Nat.le_refl _)
      exact
        cbpg_auxiliary_iterate_mem_effective_domain_of_outer_iterate
          (hproblem := hproblem)
          (x0 := x0)
          (k + 1)
          hxsucc
          m
          hm

/-- Helper for Lemma 11.4: the transported outer-step difference is the telescoping sum of the
transported auxiliary stage differences. -/
lemma cbpg_outer_step_toPiLp_eq_sum_stage_differences
    (k : ℕ) :
    toPiLp x[k] - toPiLp x[k + 1] =
      Finset.sum (Finset.range p) (fun n ↦ toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
  have hprefix :
      ∀ n : ℕ,
        n ≤ p →
          toPiLp x[k] - toPiLp x[k, n] =
            Finset.sum (Finset.range n) (fun m ↦ toPiLp x[k, m] - toPiLp x[k, m + 1]) := by
    intro n hn
    induction n with
    | zero =>
        -- The empty prefix contributes no stage differences.
        simp
    | succ n ihn =>
        have hn_le : n ≤ p := Nat.le_of_succ_le hn
        -- Extend the telescoping identity by one more stage difference.
        calc
          toPiLp x[k] - toPiLp x[k, n + 1] =
              (toPiLp x[k] - toPiLp x[k, n]) +
                (toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
            simpa using
              (sub_add_sub_cancel
                (toPiLp x[k])
                (toPiLp x[k, n])
                (toPiLp x[k, n + 1])).symm
          _ =
              Finset.sum (Finset.range n) (fun m ↦ toPiLp x[k, m] - toPiLp x[k, m + 1]) +
                (toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
            rw [ihn hn_le]
          _ =
              Finset.sum (Finset.range (n + 1))
                (fun m ↦ toPiLp x[k, m] - toPiLp x[k, m + 1]) := by
            rw [Finset.sum_range_succ]
  -- Apply the prefix telescoping identity at the full cycle length `p`.
  calc
    toPiLp x[k] - toPiLp x[k + 1] = toPiLp x[k] - toPiLp x[k, p] := by
      rw [cyclic_block_proximal_gradient_method_succ]
    _ =
        Finset.sum (Finset.range p) (fun n ↦ toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
      exact hprefix p (Nat.le_refl _)

/-- Helper for Lemma 11.4: the squared `PiLp` norm of one outer CBPG step is the sum of the
squared norms of the auxiliary one-block steps. -/
lemma cbpg_outer_step_sq_norm_eq_sum_auxiliary_sq_norm
    (k : ℕ) :
    ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) =
      Finset.sum Finset.univ (fun j : Fin p ↦ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
  have hsum_single :
      Finset.sum (Finset.range p) (fun n ↦ toPiLp x[k, n] - toPiLp x[k, n + 1]) =
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact cbpg_stage_difference_toPiLp_single hproblem x0 k j
  -- Rewrite the outer step as a sum of singleton-supported `PiLp` vectors, then expand the
  -- `L²` norm coordinatewise.
  calc
    ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) =
        ‖Finset.sum Finset.univ
            (fun j : Fin p ↦
              PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j))‖ ^ (2 : ℕ) := by
      rw [cbpg_outer_step_toPiLp_eq_sum_stage_differences, hsum_single]
    _ =
        Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖x[k, j.1] j - x[k, j.1 + 1] j‖ ^ (2 : ℕ)) := by
      simpa [PiLp.single_eq_same] using
        (PiLp.norm_sq_eq_of_L2
          (fun i : Fin p ↦ Ei i)
          (Finset.sum Finset.univ
            (fun j : Fin p ↦
              PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j))))
    _ =
        Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [cbpg_auxiliary_step_norm_eq_block_norm]

-- Proof sketch: apply the Chapter 11 one-block sufficient-decrease owner
-- `BlockProximalGradientAssumptions.block_partial_gradient_sufficient_decrease` to the current
-- auxiliary state `x^{k,j}` with block index `j` and stepsize `L_j`, then rewrite the updated
-- point as the next auxiliary state `x^{k,j+1}`.
/-- Lemma 11.4 (1): for part (a), the objective decrease across one cyclic block update satisfies
equation (11.9),
`F(x^{k,j}) - F(x^{k,j+1}) ≥ (1 / (2 L_j)) ‖G_{L_j}^j(x^{k,j})‖^2`. -/
theorem cbpg_auxiliary_sufficient_decrease_gradient_mapping
    (k : ℕ) (j : Fin p) :
    F x[k, j.1] - F x[k, j.1 + 1] ≥
      ((((1 : ℝ) / (2 * (Li j : ℝ))) *
          ‖G[Li j; (hproblem.toIsBlockProximalGradientProblem)] x[k, j.1] j‖ ^
            (2 : ℕ) : ℝ) : EReal) :=
  by
  let xj : effective_domain (separableSum g) :=
    ⟨x[k, j.1], cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k j.1 (Nat.le_of_lt j.2)⟩
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The next auxiliary stage is the canonical one-block prox update.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ
        (hproblem := hproblem)
        (x0 := x0')
        k
        j.2
  -- Apply the owner one-block sufficient-decrease theorem at the current auxiliary iterate.
  simpa [xj, hsucc] using
    hproblem.block_partial_gradient_sufficient_decrease j xj

-- Proof sketch: apply Proposition 11.1 to the auxiliary state `x^{k,j}`, then identify the
-- resulting one-block update with the next auxiliary iterate `x^{k,j+1}`.
/-- Lemma 11.4 (2): for part (a), equation (11.10) gives the equivalent step-norm form
`F(x^{k,j}) - F(x^{k,j+1}) ≥ (L_j / 2) ‖x^{k,j} - x^{k,j+1}‖^2`. -/
theorem cbpg_auxiliary_sufficient_decrease_step_norm
    (k : ℕ) (j : Fin p) :
    F x[k, j.1] - F x[k, j.1 + 1] ≥
      ((((Li j : ℝ) / 2) *
          ‖x[k, j.1] - x[k, j.1 + 1]‖ ^
            (2 : ℕ) : ℝ) : EReal) := by
  let xj : effective_domain (separableSum g) :=
    ⟨x[k, j.1], cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k j.1 (Nat.le_of_lt j.2)⟩
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The stage update matches the proposition's one-block update owner.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ
        (hproblem := hproblem)
        (x0 := x0')
        k
        j.2
  -- Reuse Proposition 11.1 at the auxiliary iterate and rewrite its updated point.
  simpa [xj, hsucc] using
    hproblem.block_partial_gradient_sufficient_decrease_step_norm j xj

-- Proof sketch: sum the one-block inequality from equation (11.10) over one full cycle
-- `j = 0, ..., p - 1`, bound each coefficient below by `L_min`, and use that the block updates
-- are orthogonal across the canonical `L²` block product, so the squared norms telescope to
-- `‖x₂^k - x₂^(k+1)‖^2`.
/-- Helper for Lemma 11.4: every outer CBPG objective value is finite, so it is neither `⊤` nor
`⊥`. -/
lemma cbpg_objective_value_finite
    (k : ℕ) :
    F x[k] ≠ ⊤ ∧ F x[k] ≠ ⊥ := by
  have hxg : x[k] ∈ effective_domain (separableSum g) := by
    simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k 0 (Nat.zero_le p)
  have hxf : x[k] ∈ effective_domain f := by
    -- Effective-domain compatibility makes `f` finite at every CBPG outer iterate.
    exact interior_subset (hproblem.g_effective_domain_subset_interior_f_effective_domain hxg)
  have hf_top : f x[k] ≠ ⊤ := (mem_effective_domain.mp hxf).ne
  have hg_top : separableSum g x[k] ≠ ⊤ := (mem_effective_domain.mp hxg).ne
  have hf_bot : f x[k] ≠ ⊥ := hproblem.f_ne_bot (x[k])
  have hg_bot : separableSum g x[k] ≠ ⊥ := by
    -- Proper block penalties keep the separable regularizer away from `-∞`.
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ
      (fun i ↦ g i (x[k] i))
      (fun i _ ↦ (hproblem.block_g_proper i).ne_bot _)
  constructor
  · simpa [composite_model_objective] using EReal.add_ne_top hf_top hg_top
  · simpa [composite_model_objective] using EReal.add_ne_bot_iff.mpr ⟨hf_bot, hg_bot⟩

/-- Helper for Lemma 11.4: the first `n` auxiliary stage decreases telescope additively into the
full outer-cycle decrease. -/
lemma cbpg_outer_cycle_partial_additive_telescope
    (k n : ℕ) (hn : n ≤ p) :
    (Finset.sum (Finset.range n)
        (fun m ↦
          if hm : m < p then
            ((((Li ⟨m, hm⟩ : ℝ) / 2) *
                ‖x[k, m] - x[k, m + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
          else 0)) +
        F x[k, n] ≤
      F x[k] := by
  let δ : ℕ → EReal := fun m ↦
    if hm : m < p then
      ((((Li ⟨m, hm⟩ : ℝ) / 2) *
          ‖x[k, m] - x[k, m + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
    else 0
  -- Build the full-cycle estimate prefix-by-prefix so Lean never normalizes the whole sum at once.
  induction n with
  | zero =>
      simpa [δ]
  | succ n ihn =>
      have hn_le : n ≤ p := Nat.le_of_succ_le hn
      have hn_lt : n < p := Nat.lt_of_succ_le hn
      have hprefix :
          Finset.sum (Finset.range n) δ + F x[k, n] ≤ F x[k] := by
        exact ihn hn_le
      have hstage_sub :
          δ n ≤ F x[k, n] - F x[k, n + 1] := by
        -- Convert the stagewise sufficient decrease into the prefix summand shape `δ n`.
        simpa [δ, hn_lt] using
          (cbpg_auxiliary_sufficient_decrease_step_norm hproblem x0 k ⟨n, hn_lt⟩ :
            F x[k, n] - F x[k, n + 1] ≥
              ((((Li ⟨n, hn_lt⟩ : ℝ) / 2) *
                  ‖x[k, n] - x[k, n + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))
      have hstage :
          δ n + F x[k, n + 1] ≤ F x[k, n] := by
        -- Rewrite the stage estimate in additive form before appending it to the prefix.
        exact EReal.add_le_of_le_sub hstage_sub
      calc
        (Finset.sum (Finset.range (n + 1)) δ) + F x[k, n + 1] =
            Finset.sum (Finset.range n) δ + (δ n + F x[k, n + 1]) := by
          rw [Finset.sum_range_succ]
          abel
        _ ≤ Finset.sum (Finset.range n) δ + F x[k, n] := by
          calc
            Finset.sum (Finset.range n) δ + (δ n + F x[k, n + 1]) =
                (δ n + F x[k, n + 1]) + Finset.sum (Finset.range n) δ := by
              abel
            _ ≤ F x[k, n] + Finset.sum (Finset.range n) δ := by
              exact add_le_add_left hstage (Finset.sum (Finset.range n) δ)
            _ = Finset.sum (Finset.range n) δ + F x[k, n] := by
              abel
        _ ≤ F x[k] := hprefix

/-- Helper for Lemma 11.4: summing the stagewise additive telescope across all `p` blocks gives
the full outer-cycle additive decrease inequality. -/
lemma cbpg_outer_cycle_additive_telescope
    (k : ℕ) :
    (Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((((Li j : ℝ) / 2) *
              ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
        F x[k + 1] ≤
      F x[k] := by
  have hpartial :=
    cbpg_outer_cycle_partial_additive_telescope hproblem x0 k p (Nat.le_refl p)
  let φ : ℕ → EReal := fun m ↦
    if hm : m < p then
      ((((Li ⟨m, hm⟩ : ℝ) / 2) *
          ‖x[k, m] - x[k, m + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
    else 0
  have hsum :
      Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        Finset.sum (Finset.range p)
          φ := by
    simpa [φ] using (Fin.sum_univ_eq_sum_range φ p)
  -- Replace the prefix range sum with the canonical `Fin p` sum and identify `x[k,p] = x[k+1]`.
  calc
    (Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((((Li j : ℝ) / 2) *
              ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
        F x[k + 1] =
        (Finset.sum (Finset.range p) φ) +
          F x[k, p] := by
      rw [hsum, cyclic_block_proximal_gradient_method_succ]
    _ ≤ F x[k] := by
      simpa [φ] using hpartial

/-- Helper for Lemma 11.4: replacing each block coefficient `L_j / 2` by the smaller common
coefficient `L_min / 2` yields a lower bound for the full-cycle quadratic term. -/
lemma cbpg_outer_cycle_real_coefficient_bound
    [Nonempty (Fin p)]
    (k : ℕ) :
    ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤
      Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
  -- First rewrite the outer-step norm square as the sum of the orthogonal stage norms.
  calc
    ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) =
        ((Lmin : ℝ) / 2) *
          Finset.sum Finset.univ
            (fun j : Fin p ↦ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      rw [cbpg_outer_step_sq_norm_eq_sum_auxiliary_sq_norm]
    _ =
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((Lmin : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      rw [Finset.mul_sum]
    _ ≤
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hLmin_le_pos : Lmin ≤ Li j := by
        simpa [cbpg_min_block_stepsize] using
          (Finset.inf'_le (s := Finset.univ) (f := Li) (b := j) (h := by simp))
      have hLmin_le : (Lmin : ℝ) ≤ (Li j : ℝ) := by
        exact_mod_cast hLmin_le_pos
      have hcoeff : ((Lmin : ℝ) / 2) ≤ ((Li j : ℝ) / 2) := by
        exact div_le_div_of_nonneg_right hLmin_le (by norm_num)
      have hsq_nonneg : 0 ≤ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) := by
        positivity
      exact mul_le_mul_of_nonneg_right hcoeff hsq_nonneg

/-- Helper for Lemma 11.4: the real coefficient comparison can be transported once into `EReal`
before composing it with the additive telescope. -/
lemma cbpg_outer_cycle_ereal_coefficient_bound
    [Nonempty (Fin p)]
    (k : ℕ) :
    ((((Lmin : ℝ) / 2) *
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((((Li j : ℝ) / 2) *
              ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  -- Keep the real algebra separate and cast it only once into the `EReal` additive telescope.
  have hreal :=
    cbpg_outer_cycle_real_coefficient_bound hproblem x0 k
  have hsum :
      (((Finset.sum Finset.univ
            (fun j : Fin p ↦
              ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) : ℝ) : EReal)) =
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    exact
      map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun j : Fin p ↦
          ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ))
        Finset.univ
  have hcast :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        (((Finset.sum Finset.univ
              (fun j : Fin p ↦
                ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact hcast.trans_eq hsum

/-- Lemma 11.4 (3): for part (b), the objective decrease across one full CBPG cycle satisfies
equation (11.11), expressed on the canonical Hilbert-product owner
`PiLp (2 : ENNReal) Ei` identified with the raw block tuple by
`PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei`,
`F(x^k) - F(x^{k+1}) ≥ (L_min / 2) ‖x₂^k - x₂^(k+1)‖^2`. -/
theorem cbpg_sufficient_decrease_outer_step
    [Nonempty (Fin p)]
    (k : ℕ) :
    F x[k] - F x[k + 1] ≥
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Route correction: the final `EReal` subtraction is postponed until the last line, after the
  -- additive telescope and the real coefficient comparison have already been separated.
  have hcoeff :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) :=
    cbpg_outer_cycle_ereal_coefficient_bound hproblem x0 k
  have htelescope :
      (Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
          F x[k + 1] ≤
        F x[k] :=
    cbpg_outer_cycle_additive_telescope hproblem x0 k
  have hadd :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) +
        F x[k + 1] ≤
      F x[k] := by
    calc
      ((((Lmin : ℝ) / 2) *
            ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) +
          F x[k + 1] ≤
          (Finset.sum Finset.univ
              (fun j : Fin p ↦
                ((((Li j : ℝ) / 2) *
                    ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
            F x[k + 1] := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left hcoeff (F x[k + 1])
      _ ≤ F x[k] := htelescope
  have hfinite : F x[k + 1] ≠ ⊤ ∧ F x[k + 1] ≠ ⊥ :=
    cbpg_objective_value_finite hproblem x0 (k + 1)
  -- Convert the additive estimate back to the stated subtraction form only at the end.
  have hsub :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        F x[k] - F x[k + 1] := by
    exact (EReal.le_sub_iff_add_le (.inl hfinite.2) (.inl hfinite.1)).2 hadd
  simpa using hsub

end

end
