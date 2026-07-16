import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap14.Algorithm_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open InnerProductSpace (toDualMap)
open scoped Gradient

section

variable {Ei : Fin 2 → Type v}

/- `Lemma 14.3` is `source-facing`: its public step data are the exact alternating-minimization
half-step `x^{k+1/2}` and next iterate `x^{k+1}` from the Chapter 14 Gauss-Seidel minimization
rule, not a Chapter 11 prox-gradient update map.

Route correction: the generated `Chap14.Algorithm_14_3` import reaches a missing
`Chap11/Definition_11_4.olean`, so this file carries the minimal Chapter 11/14 support surface it
needs locally. The proof route itself is unchanged: compare each exact block minimizer against the
corresponding one-block prox-gradient candidate and then apply the textbook sufficient-decrease
estimate on that candidate. -/

section LocalSupport

variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/-- Helper for Lemma 14.3: a finite value of the two-block separable regularizer forces the
selected block penalty to be finite. -/
lemma block_mem_effective_domain_of_mem_separableSum_effective_domain
    (g : (i : Fin 2) → Ei i → EReal)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    {x : (i : Fin 2) → Ei i} (hx : x ∈ effective_domain (separableSum g)) (i : Fin 2) :
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

/-- Helper for Lemma 14.3: updating only block `i` by a displacement is the same as replacing the
block value by `x i + d`. -/
def block_coordinate_update
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (d : Ei i) : (i : Fin 2) → Ei i :=
  x + Pi.single i d

/-- Helper for Lemma 14.3: a zero block displacement leaves the ambient point unchanged. -/
@[simp] theorem block_coordinate_update_zero
    (x : (i : Fin 2) → Ei i) (i : Fin 2) :
    block_coordinate_update x i 0 = x := by
  -- The zero single-coordinate perturbation is the zero function, so the update is trivial.
  ext j
  by_cases hji : j = i
  · subst j
    simp [block_coordinate_update]
  · simp [block_coordinate_update]

/-- Helper for Lemma 14.3: the updated block takes the shifted value `x i + d`. -/
@[simp] theorem block_coordinate_update_apply_same
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (d : Ei i) :
    block_coordinate_update x i d i = x i + d := by
  classical
  simp [block_coordinate_update]

/-- Helper for Lemma 14.3: updating block `i` by the residual to a target value reaches that
target exactly. -/
@[simp] theorem block_coordinate_update_apply_target
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (yi : Ei i) :
    block_coordinate_update x i (yi - x i) i = yi := by
  -- Replacing the active block by the residual displacement lands exactly at the target.
  simp [block_coordinate_update, sub_eq_add_neg, add_left_comm]

/-- Helper for Lemma 14.3: away from the active block, a block update leaves the point unchanged.
-/
@[simp] theorem block_coordinate_update_apply_ne
    (x : (i : Fin 2) → Ei i) {i j : Fin 2} (d : Ei i) (hji : j ≠ i) :
    block_coordinate_update x i d j = x j := by
  classical
  simp [block_coordinate_update, hji]

/-- Helper for Lemma 14.3: a one-block displacement update is pointwise the corresponding
`Function.update`. -/
theorem block_coordinate_update_eq_update
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (d : Ei i) :
    block_coordinate_update x i d =
      Function.update x i (x i + d) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [block_coordinate_update]
  · simp [block_coordinate_update, Function.update, hj]

/-- Helper for Lemma 14.3: updating block `i` by the residual to a target value is the direct
`Function.update` to that target. -/
theorem block_coordinate_update_eq_update_target
    (x : (i : Fin 2) → Ei i) (i : Fin 2) (yi : Ei i) :
    block_coordinate_update x i (yi - x i) = Function.update x i yi := by
  -- Route correction: the comparison theorems are stated with `Function.update`, while the local
  -- prox candidate is built by a displacement update.
  ext j
  by_cases hj : j = i
  · subst j
    simp [Function.update]
  · simp [block_coordinate_update, Function.update, hj]

/-- Helper for Lemma 14.3: freezing all but one block turns `f` into the corresponding one-block
slice. -/
def block_coordinate_slice
    (f : ((i : Fin 2) → Ei i) → EReal)
    (x : (i : Fin 2) → Ei i) (i : Fin 2) : Ei i → ℝ :=
  fun d ↦ (f (block_coordinate_update x i d)).toReal

/-- Helper for Lemma 14.3: evaluating the frozen one-block slice at a displacement updates only
the chosen block. -/
@[simp] theorem block_coordinate_slice_apply
    (f : ((i : Fin 2) → Ei i) → EReal) (x : (i : Fin 2) → Ei i) (i : Fin 2) (d : Ei i) :
    block_coordinate_slice f x i d = (f (block_coordinate_update x i d)).toReal :=
  rfl

/-- Helper for Lemma 14.3: the one-block prox-gradient point is the chosen element of the scaled
proximal singleton for the active block. -/
def block_partial_prox_grad_point
    (g : (i : Fin 2) → Ei i → EReal)
    (block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : Fin 2) [ProperSpace (Ei i)] (x : (i : Fin 2) → Ei i) : Ei i :=
  let hg_scaled := scaled_function_proper_closed_convex_of_pos
    (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
  Classical.choose <|
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / M : PosReal) : EReal) • g i))
      hg_scaled.1
      hg_scaled.2.1
      hg_scaled.2.2
      (x i - (1 / M : ℝ) • block_gradient i x)

/-- Helper for Lemma 14.3: the block gradient mapping is the stepsize-scaled residual between the
current block and its one-block prox-gradient point. -/
def block_partial_gradient_mapping
    (g : (i : Fin 2) → Ei i → EReal)
    (block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (i : Fin 2) [ProperSpace (Ei i)] (x : (i : Fin 2) → Ei i) : Ei i :=
  (M : ℝ) •
    (x i - block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x)

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "T[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦ block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "T[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "G[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦ block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "G[" M "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x

/-- Helper for Lemma 14.3: evaluating the block gradient mapping gives the defining residual
formula `M • (x_i - T_M^i(x))`. -/
@[simp] theorem block_partial_gradient_mapping_def
    (g : (i : Fin 2) → Ei i → EReal)
    (block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : (i : Fin 2) → Ei i) (i : Fin 2) [ProperSpace (Ei i)] :
    block_partial_gradient_mapping g block_gradient hg_proper hg_closed hg_convex M i x =
      (M : ℝ) •
        (x i -
          block_partial_prox_grad_point g block_gradient hg_proper hg_closed hg_convex M i x) :=
  rfl

/-- Helper for Lemma 14.3: the one-block prox-gradient point is the unique proximal point of the
scaled active block penalty. -/
theorem block_partial_prox_grad_point_eq_singleton
    (g : (i : Fin 2) → Ei i → EReal)
    (block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i)
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))
    (M : PosReal) (x : ((i : Fin 2) → Ei i)) (i : Fin 2) [ProperSpace (Ei i)] :
    prox[((((1 / M : PosReal) : EReal) • g i))]
      (x i - (1 / M : ℝ) • block_gradient i x) =
        {T[M; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} := by
  let hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / M)
  -- The local Chapter 11 prox point is defined by choosing the unique element of this singleton.
  simpa [block_partial_prox_grad_point, hscaled] using
    (Classical.choose_spec <|
      prox_eq_singleton_of_proper_closed_convex
        ((((1 / M : PosReal) : EReal) • g i))
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        (x i - (1 / M : ℝ) • block_gradient i x))

/-- Helper for Lemma 14.3: the frozen one-block slice satisfies the standard quadratic descent
estimate once smoothness and the gradient at the base point are available. -/
theorem block_coordinate_descent_lemma_of_slice_smooth
    (f : ((i : Fin 2) → Ei i) → EReal)
    (block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i)
    (L : NNReal)
    (i : Fin 2) [ProperSpace (Ei i)]
    {x : (j : Fin 2) → Ei j}
    (h_slice_convex :
      Convex ℝ {d : Ei i | block_coordinate_update x i d ∈ interior (effective_domain f)})
    (h_slice_smooth :
      is_l_smooth_on
        (block_coordinate_slice f x i)
        {d : Ei i | block_coordinate_update x i d ∈ interior (effective_domain f)}
        L)
    (h_block_gradient_spec :
      HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0)
    {d : Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hxd : block_coordinate_update x i d ∈ interior (effective_domain f)) :
    (f (block_coordinate_update x i d)).toReal ≤
      (f x).toReal + inner ℝ (block_gradient i x) d + ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
  have h0 :
      (0 : Ei i) ∈ {d : Ei i | block_coordinate_update x i d ∈ interior (effective_domain f)} := by
    -- The slice descent lemma starts at the zero displacement, which recovers the base point `x`.
    simpa [block_coordinate_update_zero] using hx
  have hdescent :=
    is_l_smooth_on_descent_lemma h_slice_convex h_slice_smooth h0 hxd
  -- Rewrite the frozen slice values at `0` and `d` back into the ambient objective.
  simpa
      [block_coordinate_slice_apply, block_coordinate_update_zero, h_block_gradient_spec.gradient]
    using hdescent

/-- Helper for Lemma 14.3: the composite one-block objective of alternating minimization is the
smooth term evaluated at the mixed state plus the active block penalty. -/
def alternating_minimization_composite_block_objective
    (f : ((i : Fin 2) → Ei i) → EReal)
    (g : (i : Fin 2) → Ei i → EReal)
    (xk xNext : (i : Fin 2) → Ei i) (i : Fin 2) : Ei i → EReal :=
  composite_model_objective
    (alternating_minimization_block_objective f xk xNext i)
    (g i)

/-- Helper for Lemma 14.3: evaluating the local Chapter 14 block objective gives the textbook
mixed-state expression. -/
@[simp] theorem alternating_minimization_composite_block_objective_apply
    (f : ((i : Fin 2) → Ei i) → EReal)
    (g : (i : Fin 2) → Ei i → EReal)
    (xk xNext : (i : Fin 2) → Ei i) (i : Fin 2) (xi : Ei i) :
    alternating_minimization_composite_block_objective f g xk xNext i xi =
      f (alternating_minimization_partial_state xk xNext i xi) + g i xi := by
  simp [alternating_minimization_composite_block_objective]

/-- Helper for Lemma 14.3: the standing exact alternating-minimization assumptions package the
blockwise regularizer hypotheses, the non-`⊥` clause for `f`, the convexity of
`effective_domain f`, and the domain compatibility needed for the Chapter 14 proof. -/
class IsAlternatingMinimizationCompositeModel
    (f : ((i : Fin 2) → Ei i) → EReal)
    (g : (i : Fin 2) → Ei i → EReal) : Prop where
  g_proper (i : Fin 2) : IsProperExtendedRealFunction (g i)
  g_closed (i : Fin 2) : LowerSemicontinuous (g i)
  g_convex (i : Fin 2) : is_convex_function (g i)
  g_continuousOn_effective_domain (i : Fin 2) :
    ContinuousOn (g i) (effective_domain (g i))
  f_ne_bot (x : (i : Fin 2) → Ei i) : f x ≠ ⊥
  f_closed : LowerSemicontinuous f
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  f_toReal_differentiableOn_interior_effective_domain :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f))
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain (separableSum g) ⊆ interior (effective_domain f)

/-- Helper for Lemma 14.3: one exact alternating-minimization step chooses each updated block as
a global minimizer of the corresponding mixed one-block composite objective. -/
class IsAlternatingMinimizationCompositeStep
    (f : ((i : Fin 2) → Ei i) → EReal)
    (g : (i : Fin 2) → Ei i → EReal)
    (xk xNext : (i : Fin 2) → Ei i) : Prop
    extends IsAlternatingMinimizationCompositeModel f g where
  block_isMinOn (i : Fin 2) :
    IsMinOn
      (alternating_minimization_composite_block_objective f g xk xNext i)
      Set.univ
      (xNext i)

end LocalSupport

section Comparison

variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

variable {f : ((i : Fin 2) → Ei i) → EReal} {g : (i : Fin 2) → Ei i → EReal}
variable {block_gradient : (i : Fin 2) → ((j : Fin 2) → Ei j) → Ei i}
variable {Li : (i : Fin 2) → PosReal}

local notation "F" => composite_model_objective f (separableSum g)

variable {xk : effective_domain (separableSum g)} {xNext : (i : Fin 2) → Ei i}
variable (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)

local notation "xHalf" => alternating_minimization_partial_state xk xNext 0 (xNext 0)

/-- Helper for Lemma 14.3: in the first subproblem of a two-block cycle, the Chapter 14 mixed
state is just the direct update of the first coordinate. -/
lemma alternating_minimization_partial_state_zero_eq_update
    (xk xNext : (j : Fin 2) → Ei j) (xi : Ei 0) :
    alternating_minimization_partial_state xk xNext 0 xi =
      Function.update xk 0 xi := by
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state, Function.update]
  · simp [alternating_minimization_partial_state, Function.update]

/-- Helper for Lemma 14.3: in the second subproblem, the mixed state is the half-step with only
the second coordinate replaced by the candidate value. -/
lemma alternating_minimization_partial_state_one_eq_update_half
    (xk xNext : (j : Fin 2) → Ei j) (xi : Ei 1) :
    alternating_minimization_partial_state xk xNext 1 xi =
      Function.update (alternating_minimization_partial_state xk xNext 0 (xNext 0)) 1 xi := by
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state, Function.update]
  · simp [alternating_minimization_partial_state, Function.update]

/-- Helper for Lemma 14.3: updating the half-step at the second block by the chosen next-block
value recovers the full next iterate. -/
lemma half_step_update_second_eq_next
    (xk xNext : (j : Fin 2) → Ei j) :
    Function.update (alternating_minimization_partial_state xk xNext 0 (xNext 0)) 1 (xNext 1) =
      xNext := by
  funext j
  fin_cases j
  · simp [alternating_minimization_partial_state, Function.update]
  · simp [alternating_minimization_partial_state, Function.update]

/-- Helper for Lemma 14.3: two successive updates of the same block add their displacements. -/
lemma block_coordinate_update_add
    {i : Fin 2} (x : (j : Fin 2) → Ei j) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i e =
      block_coordinate_update x i (d + e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [block_coordinate_update, add_assoc, add_left_comm, add_comm]
  · simp [block_coordinate_update, hji]

/-- Helper for Lemma 14.3: re-updating a block by the residual displacement reaches the target
value directly. -/
lemma block_coordinate_update_sub
    {i : Fin 2} (x : (j : Fin 2) → Ei j) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i (e - d) =
      block_coordinate_update x i e := by
  -- Collapse the second displacement into a single update on the original state.
  calc
    block_coordinate_update (block_coordinate_update x i d) i (e - d) =
        block_coordinate_update x i (d + (e - d)) := by
      rw [block_coordinate_update_add]
    _ = block_coordinate_update x i e := by
      congr 2
      abel

/-- Helper for Lemma 14.3: affine combinations commute with a fixed block update. -/
lemma block_coordinate_update_affine_combination
    {i : Fin 2} (x : (j : Fin 2) → Ei j) (d e : Ei i)
    {a b : ℝ} (hab : a + b = 1) :
    a • block_coordinate_update x i d + b • block_coordinate_update x i e =
      block_coordinate_update x i (a • d + b • e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    calc
      a • block_coordinate_update x i d i + b • block_coordinate_update x i e i =
          (a • x i + b • x i) + (a • d + b • e) := by
            simp [block_coordinate_update, smul_add, add_assoc, add_left_comm, add_comm]
      _ = (a + b) • x i + (a • d + b • e) := by
        rw [← add_smul]
      _ = x i + (a • d + b • e) := by
        simp [hab]
      _ = block_coordinate_update x i (a • d + b • e) i := by
        simp [block_coordinate_update]
  · calc
      a • block_coordinate_update x i d j + b • block_coordinate_update x i e j =
          a • x j + b • x j := by
            simp [block_coordinate_update, hji]
      _ = (a + b) • x j := by
        rw [← add_smul]
      _ = block_coordinate_update x i (a • d + b • e) j := by
        simp [block_coordinate_update, hji, hab]

/-- Helper for Lemma 14.3: finiteness of the two-block separable sum forces finiteness of the
first block term. -/
lemma first_block_mem_effective_domain_of_separableSum
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    {x : (j : Fin 2) → Ei j}
    (hx : x ∈ effective_domain (separableSum g)) :
    x 0 ∈ effective_domain (g 0) := by
  have hxsum : g 0 (x 0) + g 1 (x 1) < ⊤ := by
    simpa [effective_domain, separableSum_apply] using hx
  have htop : g 0 (x 0) ≠ ⊤ := by
    intro h0top
    have hsum_top : g 0 (x 0) + g 1 (x 1) = ⊤ := by
      simpa [h0top] using EReal.top_add_of_ne_bot ((hg_proper 1).ne_bot (x 1))
    exact (lt_irrefl (⊤ : EReal)) (hsum_top ▸ hxsum)
  simpa [effective_domain, lt_top_iff_ne_top] using htop

/-- Helper for Lemma 14.3: finiteness of the two-block separable sum forces finiteness of the
second block term. -/
lemma second_block_mem_effective_domain_of_separableSum
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    {x : (j : Fin 2) → Ei j}
    (hx : x ∈ effective_domain (separableSum g)) :
    x 1 ∈ effective_domain (g 1) := by
  have hxsum : g 0 (x 0) + g 1 (x 1) < ⊤ := by
    simpa [effective_domain, separableSum_apply] using hx
  have htop : g 1 (x 1) ≠ ⊤ := by
    intro h1top
    have hsum_top : g 0 (x 0) + g 1 (x 1) = ⊤ := by
      simpa [h1top] using EReal.add_top_of_ne_bot ((hg_proper 0).ne_bot (x 0))
    exact (lt_irrefl (⊤ : EReal)) (hsum_top ▸ hxsum)
  simpa [effective_domain, lt_top_iff_ne_top] using htop

/-- Helper for Lemma 14.3: replacing one finite block by another finite block value preserves the
effective domain of the two-block separable sum. -/
lemma block_coordinate_update_mem_effective_domain_separableSum
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    {i : Fin 2} {x : (j : Fin 2) → Ei j}
    (hx : x ∈ effective_domain (separableSum g))
    {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    block_coordinate_update x i (yi - x i) ∈ effective_domain (separableSum g) := by
  -- Route correction: for two blocks it is cheaper to rewrite each branch explicitly than to
  -- rebuild a general inactive-penalty API.
  fin_cases i
  · have hx1 : x 1 ∈ effective_domain (g 1) :=
      second_block_mem_effective_domain_of_separableSum hg_proper hx
    change Ei 0 at yi
    change yi ∈ effective_domain (g 0) at hyi
    have hact : x 0 + (yi - x 0) = yi := by
      abel
    have hsum_ne_top : g 0 yi + g 1 (x 1) ≠ ⊤ :=
      EReal.add_ne_top (mem_effective_domain.mp hyi).ne (mem_effective_domain.mp hx1).ne
    refine mem_effective_domain.mpr (lt_top_iff_ne_top.mpr ?_)
    -- The first updated point has coordinates `(yi, x 1)`, so both regularizer terms stay finite.
    intro htop
    change separableSum g (block_coordinate_update x 0 (yi - x 0)) = ⊤ at htop
    have hcoord0 : block_coordinate_update x 0 (yi - x 0) 0 = x 0 + (yi - x 0) := by
      simp [block_coordinate_update]
    have hcoord1 : block_coordinate_update x 0 (yi - x 0) 1 = x 1 := by
      simp [block_coordinate_update]
    rw [separableSum_apply, Fin.sum_univ_two, hcoord0, hcoord1] at htop
    rw [hact] at htop
    have hsum_top : g 0 yi + g 1 (x 1) = ⊤ := htop
    exact hsum_ne_top hsum_top
  · have hx0 : x 0 ∈ effective_domain (g 0) :=
      first_block_mem_effective_domain_of_separableSum hg_proper hx
    change Ei 1 at yi
    change yi ∈ effective_domain (g 1) at hyi
    have hact : x 1 + (yi - x 1) = yi := by
      abel
    have hsum_ne_top : g 0 (x 0) + g 1 yi ≠ ⊤ :=
      EReal.add_ne_top (mem_effective_domain.mp hx0).ne (mem_effective_domain.mp hyi).ne
    refine mem_effective_domain.mpr (lt_top_iff_ne_top.mpr ?_)
    -- The second updated point has coordinates `(x 0, yi)`, so the same finite-sum argument
    -- applies in the other branch.
    intro htop
    change separableSum g (block_coordinate_update x 1 (yi - x 1)) = ⊤ at htop
    have hcoord0 : block_coordinate_update x 1 (yi - x 1) 0 = x 0 := by
      simp [block_coordinate_update]
    have hcoord1 : block_coordinate_update x 1 (yi - x 1) 1 = x 1 + (yi - x 1) := by
      simp [block_coordinate_update]
    rw [separableSum_apply, Fin.sum_univ_two, hcoord0, hcoord1] at htop
    rw [hact] at htop
    have hsum_top : g 0 (x 0) + g 1 yi = ⊤ := htop
    exact hsum_ne_top hsum_top

/-- Helper for Lemma 14.3: replacing one block by a target value splits the full objective into
the active block term plus the frozen inactive penalty. -/
lemma block_update_full_objective_split
    {i : Fin 2} {x : (j : Fin 2) → Ei j} (yi : Ei i) :
    F (block_coordinate_update x i (yi - x i)) =
      f (block_coordinate_update x i (yi - x i)) + g i yi +
        ∑ j ∈ Finset.univ.erase i, g j (x j) := by
  fin_cases i
  · -- For the first block, the inactive penalty is exactly the second coordinate term.
    change Ei 0 at yi
    have hsum0 : ∑ j ∈ Finset.univ.erase 0, g j (x j) = g 1 (x 1) := by
      rw [show (Finset.univ.erase (0 : Fin 2)) = ({1} : Finset (Fin 2)) by decide]
      simp
    have hact : x 0 + (yi - x 0) = yi := by
      abel
    calc
      F (block_coordinate_update x 0 (yi - x 0)) =
          f (block_coordinate_update x 0 (yi - x 0)) +
            (g 0 (x 0 + (yi - x 0)) + g 1 (x 1)) := by
              rw [composite_model_objective_apply, separableSum_apply, Fin.sum_univ_two]
              simp [block_coordinate_update]
      _ = f (block_coordinate_update x 0 (yi - x 0)) + g 0 yi +
            ∑ j ∈ Finset.univ.erase 0, g j (x j) := by
              rw [hact, hsum0]
              simp [add_assoc]
  · -- The second-block branch is the symmetric decomposition.
    change Ei 1 at yi
    have hsum1 : ∑ j ∈ Finset.univ.erase 1, g j (x j) = g 0 (x 0) := by
      rw [show (Finset.univ.erase (1 : Fin 2)) = ({0} : Finset (Fin 2)) by decide]
      simp
    have hact : x 1 + (yi - x 1) = yi := by
      abel
    calc
      F (block_coordinate_update x 1 (yi - x 1)) =
          f (block_coordinate_update x 1 (yi - x 1)) +
            (g 0 (x 0) + g 1 (x 1 + (yi - x 1))) := by
              rw [composite_model_objective_apply, separableSum_apply, Fin.sum_univ_two]
              simp [block_coordinate_update, add_assoc, add_left_comm, add_comm]
      _ = f (block_coordinate_update x 1 (yi - x 1)) + g 1 yi +
            ∑ j ∈ Finset.univ.erase 1, g j (x j) := by
              rw [hact, hsum1]
              simp [add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 14.3: the frozen inactive penalty is finite at every point of the
two-block separable effective domain. -/
lemma inactive_penalty_eq_coe_toReal_of_mem_separableSum_effective_domain
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    {i : Fin 2} {x : (j : Fin 2) → Ei j}
    (hx : x ∈ effective_domain (separableSum g)) :
    (∑ j ∈ Finset.univ.erase i, g j (x j)) =
      ((((∑ j ∈ Finset.univ.erase i, g j (x j)).toReal : ℝ)) : EReal) := by
  fin_cases i
  · have hx1 : x 1 ∈ effective_domain (g 1) :=
      second_block_mem_effective_domain_of_separableSum hg_proper hx
    -- The erased first-block sum is the single inactive second-block penalty.
    have hsum : (∑ j ∈ Finset.univ.erase 0, g j (x j)) = g 1 (x 1) := by
      rw [show (Finset.univ.erase (0 : Fin 2)) = ({1} : Finset (Fin 2)) by decide]
      simp
    calc
      (∑ j ∈ Finset.univ.erase 0, g j (x j)) = g 1 (x 1) := hsum
      _ = ((((g 1 (x 1)).toReal : ℝ)) : EReal) := by
            exact
              (EReal.coe_toReal
                (mem_effective_domain.mp hx1).ne
                ((hg_proper 1).ne_bot (x 1))).symm
      _ = ((((∑ j ∈ Finset.univ.erase 0, g j (x j)).toReal : ℝ)) : EReal) := by
            simp [hsum]
  · have hx0 : x 0 ∈ effective_domain (g 0) :=
      first_block_mem_effective_domain_of_separableSum hg_proper hx
    -- The erased second-block sum is the single inactive first-block penalty.
    have hsum : (∑ j ∈ Finset.univ.erase 1, g j (x j)) = g 0 (x 0) := by
      rw [show (Finset.univ.erase (1 : Fin 2)) = ({0} : Finset (Fin 2)) by decide]
      simp
    calc
      (∑ j ∈ Finset.univ.erase 1, g j (x j)) = g 0 (x 0) := hsum
      _ = ((((g 0 (x 0)).toReal : ℝ)) : EReal) := by
            exact
              (EReal.coe_toReal
                (mem_effective_domain.mp hx0).ne
                ((hg_proper 0).ne_bot (x 0))).symm
      _ = ((((∑ j ∈ Finset.univ.erase 1, g j (x j)).toReal : ℝ)) : EReal) := by
            simp [hsum]

/-- Helper for Lemma 14.3: a real active-block inequality upgrades to the full `EReal` objective
inequality once the common inactive penalty is rewritten as a finite real coercion. -/
lemma full_objective_sufficient_decrease_of_active_real_inequality
    {i : Fin 2} {x : (j : Fin 2) → Ei j} {yi : Ei i} {c : ℝ}
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    (h_f_ne_bot : ∀ y : ((j : Fin 2) → Ei j), f y ≠ ⊥)
    (hxg : x ∈ effective_domain (separableSum g))
    (hyg : block_coordinate_update x i (yi - x i) ∈ effective_domain (separableSum g))
    (hx : x ∈ interior (effective_domain f))
    (hy : block_coordinate_update x i (yi - x i) ∈ interior (effective_domain f))
    (hreal :
      c + (f (block_coordinate_update x i (yi - x i))).toReal + (g i yi).toReal ≤
        (f x).toReal + (g i (x i)).toReal) :
    (((c : ℝ) : EReal)) + F (block_coordinate_update x i (yi - x i)) ≤ F x := by
  let y := block_coordinate_update x i (yi - x i)
  let inactive : EReal := ∑ j ∈ Finset.univ.erase i, g j (x j)
  have hx_finite : x ∈ effective_domain f := interior_subset hx
  have hy_finite : y ∈ effective_domain f := interior_subset hy
  have hyi :
      yi ∈ effective_domain (g i) := by
    have hy_block :
        y i ∈ effective_domain (g i) :=
      block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hyg i
    simpa [y] using hy_block
  have hxi :
      x i ∈ effective_domain (g i) :=
    block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hxg i
  have hfx_val :
      f x = ((((f x).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hx_finite).ne
        (h_f_ne_bot x)).symm
  have hfy_val :
      f y = ((((f y).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hy_finite).ne
        (h_f_ne_bot y)).symm
  have hgyi_val :
      g i yi = ((((g i yi).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hyi).ne
        ((hg_proper i).ne_bot yi)).symm
  have hxi_val :
      g i (x i) = ((((g i (x i)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hxi).ne
        ((hg_proper i).ne_bot (x i))).symm
  have hinactive_val :
      inactive = ((((inactive.toReal : ℝ)) : EReal)) := by
    simpa [inactive] using
      inactive_penalty_eq_coe_toReal_of_mem_separableSum_effective_domain
        (g := g) hg_proper hxg
  have hsplit_y :
      F y = f y + g i yi + inactive := by
    dsimp [y, inactive]
    simpa only using
      block_update_full_objective_split (f := f) (g := g) (x := x) (i := i) (yi := yi)
  have hsplit_x :
      F x = f x + g i (x i) + inactive := by
    dsimp [inactive]
    simpa [block_coordinate_update_zero] using
      block_update_full_objective_split (f := f) (g := g) (x := x) (i := i) (yi := x i)
  have hFy :
      F y =
        ((((f y).toReal + (g i yi).toReal : ℝ)) : EReal) +
          ((((inactive.toReal : ℝ)) : EReal)) := by
    -- Rewrite `F y` into its active finite real part plus the frozen inactive penalty.
    calc
      F y = f y + g i yi + inactive := hsplit_y
      _ = ((((f y).toReal : ℝ)) : EReal) +
            ((((g i yi).toReal : ℝ)) : EReal) +
            ((((inactive.toReal : ℝ)) : EReal)) := by
              rw [hfy_val, hgyi_val, hinactive_val]
              simp
      _ = ((((f y).toReal + (g i yi).toReal : ℝ)) : EReal) +
            ((((inactive.toReal : ℝ)) : EReal)) := by
              simp [EReal.coe_add, add_assoc]
  have hFx :
      F x =
        ((((f x).toReal + (g i (x i)).toReal : ℝ)) : EReal) +
          ((((inactive.toReal : ℝ)) : EReal)) := by
    -- Apply the same split at the base point, where the active update is the zero displacement.
    calc
      F x = f x + g i (x i) + inactive := hsplit_x
      _ = ((((f x).toReal : ℝ)) : EReal) +
            ((((g i (x i)).toReal : ℝ)) : EReal) +
            ((((inactive.toReal : ℝ)) : EReal)) := by
              rw [hfx_val, hxi_val, hinactive_val]
              simp
      _ = ((((f x).toReal + (g i (x i)).toReal : ℝ)) : EReal) +
            ((((inactive.toReal : ℝ)) : EReal)) := by
              simp [EReal.coe_add, add_assoc]
  have hreal' :
      c + ((f y).toReal + (g i yi).toReal) ≤
        (f x).toReal + (g i (x i)).toReal := by
    simpa [y, add_assoc] using hreal
  have hrealE :
      ((((c + ((f y).toReal + (g i yi).toReal) : ℝ)) : EReal)) ≤
        ((((f x).toReal + (g i (x i)).toReal : ℝ)) : EReal) := by
    exact_mod_cast hreal'
  have hshifted :
      ((((c + ((f y).toReal + (g i yi).toReal) : ℝ)) : EReal)) +
          ((((inactive.toReal : ℝ)) : EReal)) ≤
        ((((f x).toReal + (g i (x i)).toReal : ℝ)) : EReal) +
          ((((inactive.toReal : ℝ)) : EReal)) := by
    exact ((EReal.addLECancellable_coe inactive.toReal).add_le_add_iff_right).mpr hrealE
  -- Cancel the common inactive penalty after both sides are rewritten into finite active parts.
  calc
    (((c : ℝ) : EReal)) + F y =
        ((((c + ((f y).toReal + (g i yi).toReal) : ℝ)) : EReal)) +
          ((((inactive.toReal : ℝ)) : EReal)) := by
            rw [hFy]
            simp [EReal.coe_add, add_assoc]
    _ ≤ ((((f x).toReal + (g i (x i)).toReal : ℝ)) : EReal) +
          ((((inactive.toReal : ℝ)) : EReal)) := hshifted
    _ = F x := hFx.symm

/-- Helper for Lemma 14.3: the derivative specification at the updated state transports back to a
derivative of the original frozen slice at the corresponding displacement. -/
lemma block_coordinate_slice_hasGradientAt_at_update
    {i : Fin 2} [ProperSpace (Ei i)] {x : (j : Fin 2) → Ei j} {d : Ei i}
    (h_block_gradient_spec :
      ∀ {y : ((j : Fin 2) → Ei j)},
        y ∈ interior (effective_domain f) →
          HasFDerivAt
            (block_coordinate_slice f y i)
            (toDualMap ℝ (Ei i) (block_gradient i y))
            0)
    (hd : block_coordinate_update x i d ∈ interior (effective_domain f)) :
    HasGradientAt
      (block_coordinate_slice f x i)
      (block_gradient i (block_coordinate_update x i d))
      d := by
  let y := block_coordinate_update x i d
  have hy :
      block_coordinate_slice f y i =
        fun e : Ei i ↦ block_coordinate_slice f x i (d + e) := by
    funext e
    simp [y, block_coordinate_slice_apply, block_coordinate_update_add]
  have hshift :
      HasGradientAt
        (fun e : Ei i ↦ block_coordinate_slice f x i (d + e))
        (block_gradient i y)
        0 := by
    -- Recenter the slice at the updated state and use the given block derivative there.
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [hy, y] using h_block_gradient_spec (y := y) hd
  -- Transport the derivative from the translated origin back to the displacement point `d`.
  rw [hasGradientAt_iff_hasFDerivAt] at hshift ⊢
  simpa using (hasFDerivAt_comp_add_left d).1 hshift

/-- Helper for Lemma 14.3: convexity of `effective_domain f` makes the admissible slice-domain
for a fixed block update convex. -/
lemma block_coordinate_slice_domain_convex_of_effective_domain_convex
    {i : Fin 2} {x : (j : Fin 2) → Ei j}
    (h_f_effective_domain_convex : Convex ℝ (effective_domain f)) :
    Convex ℝ {d : Ei i | block_coordinate_update x i d ∈ interior (effective_domain f)} := by
  let hinterior : Convex ℝ (interior (effective_domain f)) :=
    h_f_effective_domain_convex.interior
  intro d hd e he a b ha hb hab
  -- Push convexity from the ambient interior domain through the fixed block-update map.
  have hcomb := hinterior hd he ha hb hab
  have hcomb' :
      a • block_coordinate_update x i d + b • block_coordinate_update x i e ∈
        interior (effective_domain f) := by
    simpa using hcomb
  have hcomb'' :
      block_coordinate_update x i (a • d + b • e) ∈ interior (effective_domain f) := by
    simpa [block_coordinate_update_affine_combination (x := x) (d := d) (e := e) hab] using hcomb'
  simpa using hcomb''

/-- Helper for Lemma 14.3: the block derivative and block-Lipschitz hypotheses make the frozen
one-block slice `L_i`-smooth on its admissible update domain. -/
lemma block_coordinate_slice_is_l_smooth_on_of_block_lipschitz
    {i : Fin 2} [ProperSpace (Ei i)] {x : (j : Fin 2) → Ei j}
    (h_block_gradient_spec :
      ∀ {y : ((j : Fin 2) → Ei j)},
        y ∈ interior (effective_domain f) →
          HasFDerivAt
            (block_coordinate_slice f y i)
            (toDualMap ℝ (Ei i) (block_gradient i y))
            0)
    (h_block_gradient_lipschitz :
      ∀ {y : ((j : Fin 2) → Ei j)} {d : Ei i},
        y ∈ interior (effective_domain f) →
          block_coordinate_update y i d ∈ interior (effective_domain f) →
            ‖block_gradient i y - block_gradient i (block_coordinate_update y i d)‖ ≤
              (Li i : ℝ) * ‖d‖) :
    is_l_smooth_on
      (block_coordinate_slice f x i)
      {d : Ei i | block_coordinate_update x i d ∈ interior (effective_domain f)}
      (PosReal.toNNReal (Li i)) := by
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro d hd
    -- The derivative of the recentered slice at `d` is the chosen block gradient at the updated
    -- ambient point.
    exact
      (block_coordinate_slice_hasGradientAt_at_update
        (x := x)
        (i := i)
        (d := d)
        h_block_gradient_spec
        hd).differentiableAt
  · intro d hd e he
    have hde :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) =
          block_coordinate_update x i e := by
      simpa using block_coordinate_update_sub (x := x) (i := i) (d := d) (e := e)
    have he' :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) ∈
          interior (effective_domain f) := by
      rw [hde]
      exact he
    have hlip :
        ‖block_gradient i (block_coordinate_update x i d) -
            block_gradient i
              (block_coordinate_update
                (block_coordinate_update x i d)
                i
                (e - d))‖ ≤
          (Li i : ℝ) * ‖e - d‖ := by
      exact h_block_gradient_lipschitz hd he'
    have hdgrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (block_coordinate_update x i d))
          d :=
      block_coordinate_slice_hasGradientAt_at_update
        (x := x)
        (i := i)
        (d := d)
        h_block_gradient_spec
        hd
    have hegrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (block_coordinate_update x i e))
          e :=
      block_coordinate_slice_hasGradientAt_at_update
        (x := x)
        (i := i)
        (d := e)
        h_block_gradient_spec
        he
    -- Rewrite the endpoint reached by the residual displacement back to the direct update at `e`.
    simpa [hde, hdgrad.gradient, hegrad.gradient, norm_sub_rev] using hlip

/-- Helper for Lemma 14.3: the one-block proximal-gradient point lies in the effective domain of
the corresponding block penalty. -/
lemma block_partial_prox_grad_point_mem_effective_domain
    {i : Fin 2} [ProperSpace (Ei i)] {x : (j : Fin 2) → Ei j}
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    (hg_closed : ∀ j : Fin 2, LowerSemicontinuous (g j))
    (hg_convex : ∀ j : Fin 2, is_convex_function (g j)) :
    T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i ∈ effective_domain (g i) := by
  have hprox :
      prox[((((1 / Li i : PosReal) : EReal) • g i))]
          (x i - (1 / Li i : ℝ) • block_gradient i x) =
        {T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} := by
    -- Identify the chosen prox point with the singleton proximal set of the scaled block penalty.
    simpa using
      block_partial_prox_grad_point_eq_singleton
        g
        block_gradient
        hg_proper
        hg_closed
        hg_convex
        (Li i)
        x
        i
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g i)
      (μ := 1 / Li i)
      (hg_proper i)
      (hg_convex i)
      (x i - (1 / Li i : ℝ) • block_gradient i x)
      (T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i)
      hprox with
    ⟨hmem, _⟩
  simpa using hmem

/-- Helper for Lemma 14.3: proximal optimality for the active block controls the corresponding
linear term by the change in the block penalty and the squared residual. -/
lemma block_prox_linear_term_le_toReal
    {i : Fin 2} [ProperSpace (Ei i)] {x : (j : Fin 2) → Ei j}
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    (hg_closed : ∀ j : Fin 2, LowerSemicontinuous (g j))
    (hg_convex : ∀ j : Fin 2, is_convex_function (g j))
    (hxi : x i ∈ effective_domain (g i)) :
    let xPlus := T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
    inner ℝ (block_gradient i x) (xPlus - x i) ≤
      -(Li i : ℝ) * ‖xPlus - x i‖ ^ (2 : ℕ) +
        (g i (x i)).toReal - (g i xPlus).toReal := by
  let xPlus := T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  let z : Ei i := x i - (1 / Li i : ℝ) • block_gradient i x
  have hxPlus_eff :
      xPlus ∈ effective_domain (g i) :=
    block_partial_prox_grad_point_mem_effective_domain
      (i := i)
      (x := x)
      hg_proper
      hg_closed
      hg_convex
  have hprox :
      prox[((((1 / Li i : PosReal) : EReal) • g i))] z = {xPlus} := by
    -- Re-express the local prox point as the unique element of the scaled proximal set.
    simpa [xPlus, z] using
      block_partial_prox_grad_point_eq_singleton
        g
        block_gradient
        hg_proper
        hg_closed
        hg_convex
        (Li i)
        x
        i
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g i)
      (μ := 1 / Li i)
      (hg_proper i)
      (hg_convex i)
      z
      xPlus
      hprox with
    ⟨_, hsupport⟩
  have hx_val :
      g i (x i) = ((((g i (x i)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hxi).ne
        ((hg_proper i).ne_bot (x i))).symm
  have hxPlus_val :
      g i xPlus = ((((g i xPlus).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hxPlus_eff).ne
        ((hg_proper i).ne_bot xPlus)).symm
  have hsupport_real :
      inner ℝ ((1 / (1 / Li i : PosReal) : ℝ) • (z - xPlus)) (x i - xPlus) ≤
        (g i (x i)).toReal - (g i xPlus).toReal := by
    have hsupportE := hsupport (x i) hxi
    rw [hx_val, hxPlus_val] at hsupportE
    have hsupportE' :
        (((inner ℝ ((1 / (1 / Li i : PosReal) : ℝ) • (z - xPlus)) (x i - xPlus) : ℝ)) :
            EReal) ≤
          ((((g i (x i)).toReal - (g i xPlus).toReal : ℝ)) : EReal) := by
      simpa [EReal.coe_sub] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hMinv :
      (1 / (1 / Li i : PosReal) : ℝ) = (Li i : ℝ) := by
    simp
  have hLi_ne : (Li i : ℝ) ≠ 0 := ne_of_gt (Li i).2
  have hleft :
      inner ℝ ((1 / (1 / Li i : PosReal) : ℝ) • (z - xPlus)) (x i - xPlus) =
        (Li i : ℝ) * ‖x i - xPlus‖ ^ (2 : ℕ) -
          inner ℝ (block_gradient i x) (x i - xPlus) := by
    have hz_sub :
        z - xPlus = (x i - xPlus) - (1 / Li i : ℝ) • block_gradient i x := by
      dsimp [z]
      abel
    rw [hMinv, hz_sub, smul_sub, inner_sub_left]
    have hnorm :
        inner ℝ ((Li i : ℝ) • (x i - xPlus)) (x i - xPlus) =
          (Li i : ℝ) * ‖x i - xPlus‖ ^ (2 : ℕ) := by
      calc
        inner ℝ ((Li i : ℝ) • (x i - xPlus)) (x i - xPlus) =
            (starRingEnd ℝ) (Li i : ℝ) * inner ℝ (x i - xPlus) (x i - xPlus) := by
              rw [inner_smul_left]
        _ = (Li i : ℝ) * ‖x i - xPlus‖ ^ (2 : ℕ) := by
              simp
    have hgrad :
        inner ℝ ((Li i : ℝ) • ((1 / Li i : ℝ) • block_gradient i x)) (x i - xPlus) =
          inner ℝ (block_gradient i x) (x i - xPlus) := by
      rw [smul_smul]
      have hcancel : ((Li i : ℝ) * (1 / Li i : ℝ)) = 1 := by
        field_simp [hLi_ne]
      rw [hcancel, one_smul]
    rw [hnorm, hgrad]
  have haux :
      -inner ℝ (block_gradient i x) (x i - xPlus) ≤
        -(Li i : ℝ) * ‖x i - xPlus‖ ^ (2 : ℕ) +
          (g i (x i)).toReal - (g i xPlus).toReal := by
    rw [hleft] at hsupport_real
    linarith
  have hdir :
      inner ℝ (block_gradient i x) (xPlus - x i) =
        -inner ℝ (block_gradient i x) (x i - xPlus) := by
    have hsub : xPlus - x i = -(x i - xPlus) := by
      abel
    rw [hsub, inner_neg_right]
  simpa [xPlus, hdir, norm_sub_rev] using haux

/-- Helper for Lemma 14.3: under the one-block Lipschitz hypothesis, replacing block `i` by its
Chapter 11 prox-gradient candidate decreases the full composite objective by the standard squared
gradient-mapping term. -/
lemma block_prox_candidate_sufficient_decrease
    {i : Fin 2} [ProperSpace (Ei i)] {x : (j : Fin 2) → Ei j}
    (hg_proper : ∀ j : Fin 2, IsProperExtendedRealFunction (g j))
    (hg_closed : ∀ j : Fin 2, LowerSemicontinuous (g j))
    (hg_convex : ∀ j : Fin 2, is_convex_function (g j))
    (h_f_effective_domain_convex : Convex ℝ (effective_domain f))
    (h_g_effective_domain_subset_interior_f_effective_domain :
      effective_domain (separableSum g) ⊆ interior (effective_domain f))
    (h_f_ne_bot : ∀ y : ((j : Fin 2) → Ei j), f y ≠ ⊥)
    (hxg : x ∈ effective_domain (separableSum g))
    (hx : x ∈ interior (effective_domain f))
    (h_block_gradient_spec :
      ∀ {y : ((j : Fin 2) → Ei j)},
        y ∈ interior (effective_domain f) →
          HasFDerivAt
            (block_coordinate_slice f y i)
            (toDualMap ℝ (Ei i) (block_gradient i y))
            0)
    (h_block_gradient_lipschitz :
      ∀ {y : ((j : Fin 2) → Ei j)} {d : Ei i},
        y ∈ interior (effective_domain f) →
          block_coordinate_update y i d ∈ interior (effective_domain f) →
            ‖block_gradient i y - block_gradient i (block_coordinate_update y i d)‖ ≤
              (Li i : ℝ) * ‖d‖) :
    F x - F
        (block_coordinate_update x i
          (T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i - x i)) ≥
      ((((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖G[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ) : ℝ) :
        EReal) := by
  let xPlus := T[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  let y := block_coordinate_update x i (xPlus - x i)
  have hxi :
      x i ∈ effective_domain (g i) :=
    block_mem_effective_domain_of_mem_separableSum_effective_domain g hg_proper hxg i
  have hxPlus_eff :
      xPlus ∈ effective_domain (g i) := by
    simpa [xPlus] using
      block_partial_prox_grad_point_mem_effective_domain
        (g := g)
        (block_gradient := block_gradient)
        (Li := Li)
        (i := i)
        (x := x)
        hg_proper
        hg_closed
        hg_convex
  have hyg :
      y ∈ effective_domain (separableSum g) := by
    -- The prox point is feasible in the active block, so the updated ambient point stays feasible.
    simpa [xPlus, y] using
      block_coordinate_update_mem_effective_domain_separableSum
        (g := g)
        hg_proper
        hxg
        (yi := xPlus)
        hxPlus_eff
  have hy :
      y ∈ interior (effective_domain f) :=
    h_g_effective_domain_subset_interior_f_effective_domain hyg
  have hgrad0 :
      HasGradientAt
        (block_coordinate_slice f x i)
        (block_gradient i x)
        0 := by
    -- The block descent lemma is anchored at the zero displacement of the frozen slice.
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using h_block_gradient_spec (y := x) hx
  have hdescent :
      (f y).toReal ≤
        (f x).toReal + inner ℝ (block_gradient i x) (xPlus - x i) +
          ((Li i : ℝ) / 2) * ‖xPlus - x i‖ ^ (2 : ℕ) := by
    -- Apply the slice descent lemma on the convex admissible block domain.
    simpa [xPlus, y] using
      block_coordinate_descent_lemma_of_slice_smooth
        (f := f)
        (block_gradient := block_gradient)
        (L := PosReal.toNNReal (Li i))
        (i := i)
        (x := x)
        (d := xPlus - x i)
        (block_coordinate_slice_domain_convex_of_effective_domain_convex
          (f := f)
          (i := i)
          (x := x)
          h_f_effective_domain_convex)
        (block_coordinate_slice_is_l_smooth_on_of_block_lipschitz
          (f := f)
          (block_gradient := block_gradient)
          (Li := Li)
          (i := i)
          (x := x)
          h_block_gradient_spec
          h_block_gradient_lipschitz)
        hgrad0
        hx
        hy
  have hprox :
      inner ℝ (block_gradient i x) (xPlus - x i) ≤
        -(Li i : ℝ) * ‖xPlus - x i‖ ^ (2 : ℕ) +
          (g i (x i)).toReal - (g i xPlus).toReal := by
    -- Proximal optimality contributes the regularizer gap and the negative quadratic term.
    simpa [xPlus] using
      block_prox_linear_term_le_toReal
        (g := g)
        (block_gradient := block_gradient)
        (Li := Li)
        (i := i)
        (x := x)
        hg_proper
        hg_closed
        hg_convex
        hxi
  have hcoeff_eq :
      (((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖G[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ)) =
        ((Li i : ℝ) / 2) * ‖xPlus - x i‖ ^ (2 : ℕ) := by
    have hLi_nonneg : 0 ≤ (Li i : ℝ) := le_of_lt (Li i).2
    have hLi_ne : (Li i : ℝ) ≠ 0 := ne_of_gt (Li i).2
    -- Rewrite the gradient-mapping norm into the residual norm and simplify the scalar factor.
    calc
      (((1 : ℝ) / (2 * (Li i : ℝ))) *
          ‖G[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ)) =
          (((1 : ℝ) / (2 * (Li i : ℝ))) *
            (((Li i : ℝ) * ‖xPlus - x i‖) ^ (2 : ℕ))) := by
              rw [block_partial_gradient_mapping_def]
              simp [xPlus, norm_smul, Real.norm_of_nonneg hLi_nonneg, norm_sub_rev]
      _ = ((Li i : ℝ) / 2) * ‖xPlus - x i‖ ^ (2 : ℕ) := by
            field_simp [hLi_ne]
  have hreal_base :
      ((Li i : ℝ) / 2) * ‖xPlus - x i‖ ^ (2 : ℕ) +
          (f y).toReal + (g i xPlus).toReal ≤
        (f x).toReal + (g i (x i)).toReal := by
    -- After the smooth and prox inequalities are reduced to reals, the textbook combination is
    -- linear arithmetic.
    linarith
  have hreal :
      ((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖G[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ) +
          (f y).toReal + (g i xPlus).toReal ≤
        (f x).toReal + (g i (x i)).toReal := by
    rw [hcoeff_eq]
    exact hreal_base
  have hbridge :
      ((((1 : ℝ) / (2 * (Li i : ℝ))) *
            ‖G[Li i; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ) : ℝ) :
          EReal) +
          F y ≤
        F x := by
    -- Route correction: the remaining step is the single `EReal` bridge from the active real
    -- inequality to the full objective decrease.
    exact
      full_objective_sufficient_decrease_of_active_real_inequality
        (f := f)
        (g := g)
        (i := i)
        (x := x)
        (yi := xPlus)
        hg_proper
        h_f_ne_bot
        hxg
        hyg
        hx
        hy
        hreal
  have hy_sum_ne_bot : separableSum g y ≠ ⊥ := by
    rw [separableSum_apply, Fin.sum_univ_two]
    rw [EReal.add_ne_bot_iff]
    exact ⟨(hg_proper 0).ne_bot (y 0), (hg_proper 1).ne_bot (y 1)⟩
  have hFy_ne_bot : F y ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨h_f_ne_bot y, hy_sum_ne_bot⟩
  have hFy_ne_top : F y ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact EReal.add_ne_top (mem_effective_domain.mp (interior_subset hy)).ne
      (mem_effective_domain.mp hyg).ne
  -- Convert the bridged additive inequality back to the displayed subtraction estimate.
  exact (EReal.le_sub_iff_add_le (Or.inl hFy_ne_bot) (Or.inl hFy_ne_top)).2 hbridge

/-- Helper for Lemma 14.3: the exact first-block minimizer beats every first-block competitor in
the full composite objective. -/
lemma first_block_exact_step_le_candidate
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (xi : Ei 0) :
    F xHalf ≤ F (Function.update (xk : (j : Fin 2) → Ei j) 0 xi) := by
  have hmin := hstep.block_isMinOn 0
  rw [isMinOn_iff] at hmin
  have hcompare := hmin xi (by simp)
  have hcompare' := add_le_add_right hcompare (g 1 ((xk : (j : Fin 2) → Ei j) 1))
  -- Rewrite the first mixed-state subproblem into the full objective with the unchanged second
  -- block penalty added to both sides.
  simpa [alternating_minimization_partial_state_zero_eq_update,
    composite_model_objective_apply, separableSum_apply,
    add_assoc, add_left_comm, add_comm] using hcompare'

/-- Helper for Lemma 14.3: the exact half-step remains in the effective domain of the
block-separable regularizer. -/
lemma half_step_mem_effective_domain :
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext) →
    xHalf ∈ effective_domain (separableSum g) := by
  intro hstep
  have hFxHalf_le_Fxk :
      F xHalf ≤ F (xk : (j : Fin 2) → Ei j) := by
    simpa using first_block_exact_step_le_candidate
      (hstep := hstep)
      (xi := (xk : (j : Fin 2) → Ei j) 0)
  have hfxk_top : f (xk : (j : Fin 2) → Ei j) ≠ ⊤ := by
    exact (mem_effective_domain.mp (interior_subset (hstep.g_effective_domain_subset_interior_f_effective_domain xk.2))).ne
  have hFxk_top : F (xk : (j : Fin 2) → Ei j) ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact EReal.add_ne_top hfxk_top (mem_effective_domain.mp xk.2).ne
  have hFxHalf_top : F xHalf ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hFxHalf_le_Fxk (lt_top_iff_ne_top.mpr hFxk_top))
  refine mem_effective_domain.mpr (lt_top_iff_ne_top.mpr ?_)
  intro hsum_top
  have hFxHalf_eq_top : F xHalf = ⊤ := by
    -- If the separable regularizer were `⊤`, then adding the non-`⊥` smooth part would force the
    -- whole composite objective to be `⊤`.
    rw [composite_model_objective_apply, hsum_top,
      EReal.add_top_of_ne_bot (hstep.f_ne_bot xHalf)]
  exact hFxHalf_top hFxHalf_eq_top

/-- Helper for Lemma 14.3: the exact second-block minimizer beats every second-block competitor in
the full composite objective. -/
lemma second_block_exact_step_le_candidate
    (hstep : IsAlternatingMinimizationCompositeStep f g xk xNext)
    (xi : Ei 1) :
    F xNext ≤ F (Function.update xHalf 1 xi) := by
  have hmin := hstep.block_isMinOn 1
  rw [isMinOn_iff] at hmin
  have hcompare := hmin xi (by simp)
  have hcompare' := add_le_add_right hcompare (g 0 (xHalf 0))
  -- Rewrite the second mixed-state subproblem into the full objective with the unchanged first
  -- block penalty added to both sides.
  simpa [alternating_minimization_partial_state_one_eq_update_half,
    half_step_update_second_eq_next, composite_model_objective_apply, separableSum_apply,
    add_assoc, add_left_comm, add_comm] using hcompare'

-- Proof sketch: since `xNext 0` is an exact minimizer of the first frozen-block subproblem,
-- `F xHalf` is at most the value at any competitor, in particular the first-block prox-gradient
-- candidate from Lemma 11.3. Applying
-- `block_partial_gradient_sufficient_decrease_of_block_lipschitz` to the current iterate `xk`
-- and block `0` then yields the displayed lower bound.
/-- Lemma 14.3 (1): if `x^{k+1}` is obtained from `x^k` by an exact two-block alternating
minimization step, then the decrease from `x^k` to the exact half-step `x^{k+1/2}` is at least
the Chapter 11 prox-gradient decrease for the first frozen-block slice. The exact Chapter 14
minimizer remains the public step object; the prox-gradient point is only a comparison point in
the proof. -/
theorem alternating_minimization_two_block_half_step_sufficient_decrease
    [ProperSpace (Ei 0)]
    (h_block_gradient_spec :
      ∀ {x : ((j : Fin 2) → Ei j)},
        x ∈ interior (effective_domain f) →
          HasFDerivAt
            (block_coordinate_slice f x 0)
            (toDualMap ℝ (Ei 0) (block_gradient 0 x))
            0)
    (h_block_gradient_lipschitz :
      ∀ {x : ((j : Fin 2) → Ei j)} {d : Ei 0},
        x ∈ interior (effective_domain f) →
          block_coordinate_update x 0 d ∈ interior (effective_domain f) →
            ‖block_gradient 0 x - block_gradient 0 (block_coordinate_update x 0 d)‖ ≤
              (Li 0 : ℝ) * ‖d‖) :
    F xk - F xHalf ≥
      ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
          ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
            (2 : ℕ) : ℝ) : EReal) := by
  let xPlus := T[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0
  let y := block_coordinate_update (xk : (j : Fin 2) → Ei j) 0 (xPlus - (xk : (j : Fin 2) → Ei j) 0)
  have hxk_int :
      (xk : (j : Fin 2) → Ei j) ∈ interior (effective_domain f) :=
    hstep.g_effective_domain_subset_interior_f_effective_domain xk.2
  have hxPlus_eff :
      xPlus ∈ effective_domain (g 0) := by
    dsimp [xPlus]
    simpa only using
      block_partial_prox_grad_point_mem_effective_domain
        (g := g)
        (block_gradient := block_gradient)
        (Li := Li)
        (i := 0)
        (x := (xk : (j : Fin 2) → Ei j))
        hstep.g_proper
        hstep.g_closed
        hstep.g_convex
  have hyg :
      y ∈ effective_domain (separableSum g) := by
    -- The first-block prox candidate is a legitimate competitor for the exact first subproblem.
    dsimp [xPlus, y]
    simpa only using
      block_coordinate_update_mem_effective_domain_separableSum
        (g := g)
        hstep.g_proper
        xk.2
        (yi := xPlus)
        hxPlus_eff
  have hy :
      y ∈ interior (effective_domain f) :=
    hstep.g_effective_domain_subset_interior_f_effective_domain hyg
  have hcandidate :
      F (xk : (j : Fin 2) → Ei j) - F y ≥
        ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
            ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
              (2 : ℕ) : ℝ) : EReal) := by
    -- Invoke the finished one-block sufficient-decrease estimate at the current iterate.
    dsimp [xPlus, y]
    simpa only using
      block_prox_candidate_sufficient_decrease
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        (Li := Li)
        (i := 0)
        (x := (xk : (j : Fin 2) → Ei j))
        hstep.g_proper
        hstep.g_closed
        hstep.g_convex
        hstep.f_effective_domain_convex
        hstep.g_effective_domain_subset_interior_f_effective_domain
        hstep.f_ne_bot
        xk.2
        hxk_int
        h_block_gradient_spec
        h_block_gradient_lipschitz
  have hcompare :
      F xHalf ≤ F y := by
    -- Compare the exact first-block minimizer against that prox candidate.
    dsimp [xPlus, y]
    simpa [block_coordinate_update_eq_update_target] using
      first_block_exact_step_le_candidate
        (hstep := hstep)
        (xi := xPlus)
  have hy_sum_ne_bot : separableSum g y ≠ ⊥ := by
    rw [separableSum_apply, Fin.sum_univ_two]
    rw [EReal.add_ne_bot_iff]
    exact ⟨(hstep.g_proper 0).ne_bot (y 0), (hstep.g_proper 1).ne_bot (y 1)⟩
  have hFy_ne_bot : F y ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hstep.f_ne_bot y, hy_sum_ne_bot⟩
  have hFy_ne_top : F y ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact EReal.add_ne_top (mem_effective_domain.mp (interior_subset hy)).ne
      (mem_effective_domain.mp hyg).ne
  have hxHalfg :
      xHalf ∈ effective_domain (separableSum g) :=
    half_step_mem_effective_domain
      (f := f) (g := g) (xk := xk) (xNext := xNext) hstep
  have hxHalf :
      xHalf ∈ interior (effective_domain f) :=
    hstep.g_effective_domain_subset_interior_f_effective_domain hxHalfg
  have hxHalf_sum_ne_bot : separableSum g xHalf ≠ ⊥ := by
    rw [separableSum_apply, Fin.sum_univ_two]
    rw [EReal.add_ne_bot_iff]
    exact ⟨(hstep.g_proper 0).ne_bot (xHalf 0), (hstep.g_proper 1).ne_bot (xHalf 1)⟩
  have hFxHalf_ne_bot : F xHalf ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hstep.f_ne_bot xHalf, hxHalf_sum_ne_bot⟩
  have hFxHalf_ne_top : F xHalf ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact EReal.add_ne_top (mem_effective_domain.mp (interior_subset hxHalf)).ne
      (mem_effective_domain.mp hxHalfg).ne
  have hcandidate_add :
      ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
            ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
              (2 : ℕ) : ℝ) : EReal) +
          F y ≤
        F xk := by
    exact (EReal.le_sub_iff_add_le (Or.inl hFy_ne_bot) (Or.inl hFy_ne_top)).1 hcandidate
  have hhalf_add :
      ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
            ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
              (2 : ℕ) : ℝ) : EReal) +
          F xHalf ≤
        F xk := by
    -- Add the exact-step comparison on the left, then compose with the candidate decrease.
    have hcompare_add :
        F xHalf +
            ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
                ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                  (2 : ℕ) : ℝ) : EReal) ≤
          F y +
            ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
                ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                  (2 : ℕ) : ℝ) : EReal) := by
      exact add_le_add_left hcompare _
    have hcompare_add' :
        ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
              ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                (2 : ℕ) : ℝ) : EReal) +
            F xHalf ≤
          ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
              ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                (2 : ℕ) : ℝ) : EReal) +
            F y := by
      calc
        ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
              ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                (2 : ℕ) : ℝ) : EReal) +
            F xHalf =
            F xHalf +
              ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
                  ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                    (2 : ℕ) : ℝ) : EReal) := by
              rw [add_comm]
        _ ≤ F y +
              ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
                  ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                    (2 : ℕ) : ℝ) : EReal) := hcompare_add
        _ =
            ((((1 : ℝ) / (2 * (Li 0 : ℝ))) *
                ‖G[Li 0; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xk 0‖ ^
                  (2 : ℕ) : ℝ) : EReal) +
              F y := by
              rw [add_comm]
    exact
      le_trans hcompare_add' hcandidate_add
  exact
    (EReal.le_sub_iff_add_le (Or.inl hFxHalf_ne_bot) (Or.inl hFxHalf_ne_top)).2
      hhalf_add

-- Proof sketch: now compare the exact second-block minimizer `xNext 1` against the second-block
-- prox-gradient candidate starting from the exact half-step `xHalf`. Since `xNext 1` minimizes
-- the second frozen-block objective, `F xNext` is no larger than the prox-gradient comparison
-- value. Apply the Chapter 11 one-block sufficient-decrease estimate at `xHalf` and block `1`.
/-- Lemma 14.3 (2): under the same exact-step and block-smoothness hypotheses, the decrease from
the exact half-step `x^{k+1/2}` to the exact next iterate `x^{k+1}` is at least the Chapter 11
prox-gradient decrease for the second frozen-block slice. -/
theorem alternating_minimization_two_block_next_step_sufficient_decrease
    [ProperSpace (Ei 1)]
    (h_block_gradient_spec :
      ∀ {x : ((j : Fin 2) → Ei j)},
        x ∈ interior (effective_domain f) →
          HasFDerivAt
            (block_coordinate_slice f x 1)
            (toDualMap ℝ (Ei 1) (block_gradient 1 x))
            0)
    (h_block_gradient_lipschitz :
      ∀ {x : ((j : Fin 2) → Ei j)} {d : Ei 1},
        x ∈ interior (effective_domain f) →
          block_coordinate_update x 1 d ∈ interior (effective_domain f) →
            ‖block_gradient 1 x - block_gradient 1 (block_coordinate_update x 1 d)‖ ≤
              (Li 1 : ℝ) * ‖d‖) :
    F xHalf - F xNext ≥
      ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
          ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
            (2 : ℕ) : ℝ) : EReal) := by
  let xPlus := T[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1
  let y := block_coordinate_update xHalf 1 (xPlus - xHalf 1)
  have hxHalfg :
      xHalf ∈ effective_domain (separableSum g) :=
    half_step_mem_effective_domain
      (f := f) (g := g) (xk := xk) (xNext := xNext) hstep
  have hxHalf :
      xHalf ∈ interior (effective_domain f) :=
    hstep.g_effective_domain_subset_interior_f_effective_domain hxHalfg
  have hxPlus_eff :
      xPlus ∈ effective_domain (g 1) := by
    dsimp [xPlus]
    simpa only using
      block_partial_prox_grad_point_mem_effective_domain
        (g := g)
        (block_gradient := block_gradient)
        (Li := Li)
        (i := 1)
        (x := xHalf)
        hstep.g_proper
        hstep.g_closed
        hstep.g_convex
  have hyg :
      y ∈ effective_domain (separableSum g) := by
    -- The second-block prox candidate is a valid competitor after the exact half-step.
    dsimp [xPlus, y]
    simpa only using
      block_coordinate_update_mem_effective_domain_separableSum
        (g := g)
        hstep.g_proper
        hxHalfg
        (yi := xPlus)
        hxPlus_eff
  have hy :
      y ∈ interior (effective_domain f) :=
    hstep.g_effective_domain_subset_interior_f_effective_domain hyg
  have hcandidate :
      F xHalf - F y ≥
        ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
            ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
              (2 : ℕ) : ℝ) : EReal) := by
    -- Apply the same one-block sufficient-decrease estimate at the exact half-step.
    dsimp [xPlus, y]
    simpa only using
      block_prox_candidate_sufficient_decrease
        (f := f)
        (g := g)
        (block_gradient := block_gradient)
        (Li := Li)
        (i := 1)
        (x := xHalf)
        hstep.g_proper
        hstep.g_closed
        hstep.g_convex
        hstep.f_effective_domain_convex
        hstep.g_effective_domain_subset_interior_f_effective_domain
        hstep.f_ne_bot
        hxHalfg
        hxHalf
        h_block_gradient_spec
        h_block_gradient_lipschitz
  have hcompare :
      F xNext ≤ F y := by
    -- Compare the exact second-block minimizer against the prox candidate built from `xHalf`.
    dsimp [xPlus, y]
    simpa [block_coordinate_update_eq_update_target] using
      second_block_exact_step_le_candidate
        (hstep := hstep)
        (xi := xPlus)
  have hy_sum_ne_bot : separableSum g y ≠ ⊥ := by
    rw [separableSum_apply, Fin.sum_univ_two]
    rw [EReal.add_ne_bot_iff]
    exact ⟨(hstep.g_proper 0).ne_bot (y 0), (hstep.g_proper 1).ne_bot (y 1)⟩
  have hFy_ne_bot : F y ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hstep.f_ne_bot y, hy_sum_ne_bot⟩
  have hFy_ne_top : F y ≠ ⊤ := by
    rw [composite_model_objective_apply]
    exact EReal.add_ne_top (mem_effective_domain.mp (interior_subset hy)).ne
      (mem_effective_domain.mp hyg).ne
  have hxNext_sum_ne_bot : separableSum g xNext ≠ ⊥ := by
    rw [separableSum_apply, Fin.sum_univ_two]
    rw [EReal.add_ne_bot_iff]
    exact ⟨(hstep.g_proper 0).ne_bot (xNext 0), (hstep.g_proper 1).ne_bot (xNext 1)⟩
  have hFxNext_ne_bot : F xNext ≠ ⊥ := by
    rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
    exact ⟨hstep.f_ne_bot xNext, hxNext_sum_ne_bot⟩
  have hFxNext_ne_top : F xNext ≠ ⊤ := by
    have hnext_le_half : F xNext ≤ F xHalf := by
      simpa using second_block_exact_step_le_candidate (hstep := hstep) (xi := xHalf 1)
    have hFxHalf_ne_top : F xHalf ≠ ⊤ := by
      rw [composite_model_objective_apply]
      exact EReal.add_ne_top (mem_effective_domain.mp (interior_subset hxHalf)).ne
        (mem_effective_domain.mp hxHalfg).ne
    exact lt_top_iff_ne_top.mp <|
      lt_of_le_of_lt hnext_le_half (lt_top_iff_ne_top.mpr hFxHalf_ne_top)
  have hcandidate_add :
      ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
            ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
              (2 : ℕ) : ℝ) : EReal) +
          F y ≤
        F xHalf := by
    exact (EReal.le_sub_iff_add_le (Or.inl hFy_ne_bot) (Or.inl hFy_ne_top)).1 hcandidate
  have hnext_add :
      ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
            ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
              (2 : ℕ) : ℝ) : EReal) +
          F xNext ≤
        F xHalf := by
    -- Add the exact-step comparison on the left and compose with the candidate decrease.
    have hcompare_add :
        F xNext +
            ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
                ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                  (2 : ℕ) : ℝ) : EReal) ≤
          F y +
            ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
                ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                  (2 : ℕ) : ℝ) : EReal) := by
      exact add_le_add_left hcompare _
    have hcompare_add' :
        ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
              ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                (2 : ℕ) : ℝ) : EReal) +
            F xNext ≤
          ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
              ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                (2 : ℕ) : ℝ) : EReal) +
            F y := by
      calc
        ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
              ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                (2 : ℕ) : ℝ) : EReal) +
            F xNext =
            F xNext +
              ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
                  ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                    (2 : ℕ) : ℝ) : EReal) := by
              rw [add_comm]
        _ ≤ F y +
              ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
                  ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                    (2 : ℕ) : ℝ) : EReal) := hcompare_add
        _ =
            ((((1 : ℝ) / (2 * (Li 1 : ℝ))) *
                ‖G[Li 1; g, block_gradient, hstep.g_proper, hstep.g_closed, hstep.g_convex] xHalf 1‖ ^
                  (2 : ℕ) : ℝ) : EReal) +
              F y := by
              rw [add_comm]
    exact
      le_trans hcompare_add' hcandidate_add
  exact
    (EReal.le_sub_iff_add_le (Or.inl hFxNext_ne_bot) (Or.inl hFxNext_ne_top)).2
      hnext_add

end Comparison

end
