import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_12 (from Chap10) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 10.12 is `source-facing`: the textbook specifies a fixed positive parameter `c`, an
initial point `x^0 = x0`, and the recursive update `x^{k+1} ∈ prox_{c g}(x^k)`. The canonical
owner for proximal points is the set-valued mapping `prox[...]`, so the weakest source-facing API
is the trajectory predicate below. When stronger hypotheses make each scaled proximal set a
singleton, the file then upgrades to the point-valued operator and recursively chosen iterate
family as a bridge/view, rather than treating those chosen points as primitive data. -/

/-- Definition 10.12: a sequence `x^k` follows the proximal-point method for `g` with parameter
`c > 0` and initial point `x^0 = x0` when it starts at `x0` and each successor iterate belongs to
the scaled proximal set `prox[((c : EReal) • g)] (x^k)`. -/
def is_proximal_point_trajectory
    (g : E → EReal) (x0 : E) (c : PosReal) (x : ℕ → E) : Prop :=
  x 0 = x0 ∧ ∀ k : ℕ, x (k + 1) ∈ prox[((c : EReal) • g)] (x k)

/-- A proximal-point trajectory starts at the prescribed initial point `x^0 = x0`. -/
theorem is_proximal_point_trajectory_zero
    {g : E → EReal} {x0 : E} {c : PosReal} {x : ℕ → E}
    (h : is_proximal_point_trajectory g x0 c x) :
    x 0 = x0 :=
  h.1

/-- At each iteration `k`, a proximal-point trajectory satisfies the canonical scaled-proximal
update rule `x^(k+1) ∈ prox[((c : EReal) • g)] (x^k)`. -/
theorem is_proximal_point_trajectory_step
    {g : E → EReal} {x0 : E} {c : PosReal} {x : ℕ → E}
    (h : is_proximal_point_trajectory g x0 c x) (k : ℕ) :
    x (k + 1) ∈ prox[((c : EReal) • g)] (x k) :=
  h.2 k

section

variable [InnerProductSpace ℝ E] [ProperSpace E]

/- Under the proper closed convex hypotheses used later in Chapter 10, each scaled proximal set is
a singleton. The declarations in this section are therefore `bridge/view`: they refine the
source-facing trajectory owner to a point-valued operator and the recursively chosen sequence
`x^(k+1) = prox_{c g}(x^k)`. -/

private theorem scaled_prox_eq_singleton
    (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (c : PosReal) (x : E) :
    ∃ u : E, prox[((c : EReal) • g)] x = {u} := by
  have hg_closed : LowerSemicontinuous g := Fact.out
  have hg_convex : is_convex_function g := Fact.out
  rcases scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex c with
    ⟨hg_scaled_proper, hg_scaled_closed, hg_scaled_convex⟩
  exact
    prox_eq_singleton_of_proper_closed_convex
      (((c : EReal) • g))
      hg_scaled_proper
      hg_scaled_closed
      hg_scaled_convex
      x

variable (g : E → EReal) [IsProperExtendedRealFunction g]
variable [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
variable (x0 : E) (c : PosReal)

/-- The one-step proximal-point operator with parameter `c > 0`, namely the unique point of
`prox[(c : EReal) • g] x`. -/
def proximal_point_operator : E → E :=
  fun x ↦ Classical.choose <| scaled_prox_eq_singleton g c x

/- Surface notation for the point-valued proximal update `x ↦ prox_{c g}(x)` attached to the
singleton proximal set `prox[((c : EReal) • g)] x`. The supporting lower-semicontinuity and
convexity assumptions are resolved from the ambient instance context, so the notation keeps only
the mathematical data `c` and `g` on the public surface. -/
@[inherit_doc] scoped[ProximalPoint] notation:max
    "proxₚ[" c ", " g "]" =>
  proximal_point_operator g c

open scoped ProximalPoint

-- Proof sketch: positive scaling by `c` preserves properness, lower semicontinuity, and
-- convexity of `g`; Theorem 6.3 then identifies `prox[(c : EReal) • g] x` as a singleton, and
-- `proximal_point_operator` is defined to be its unique point.
/-- The proximal-point operator is the unique proximal point of the scaled function `c g` at the
base point `x`. -/
theorem proximal_point_operator_eq_singleton (x : E) :
    prox[((c : EReal) • g)] x = {proxₚ[c, g] x} := by
  simpa [proximal_point_operator] using
    (Classical.choose_spec <| scaled_prox_eq_singleton g c x)

/-- The proximal-point operator is a point of the scaled proximal set `prox[c g] x`. -/
@[simp] theorem proximal_point_operator_mem (x : E) :
    proxₚ[c, g] x ∈ prox[((c : EReal) • g)] x := by
  rw [proximal_point_operator_eq_singleton]
  simp

-- Proof sketch: `proximal_point_operator_mem` places the chosen point in the scaled proximal set;
-- the canonical Chapter 6 bridge `isMinOn_moreau_penalty_of_mem_scaled_prox` then converts that
-- proximal membership directly into minimization of the textbook penalized objective.
/-- The proximal-point operator minimizes the textbook penalized objective
`y ↦ g y + (1 / (2 c)) ‖y - x‖²`. -/
theorem proximal_point_operator_isMinOn (x : E) :
    IsMinOn
      (fun y : E ↦ g y + ((((1 / (2 * c) : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal))
      Set.univ
      (proxₚ[c, g] x) := by
  simpa [norm_sub_rev] using
    isMinOn_moreau_penalty_of_mem_scaled_prox (proximal_point_operator_mem g c x)

/-- Definition 10.12: for a proper closed convex objective `g`, an initial point `x^0 = x0`, and
a parameter `c > 0`, the proximal point method is the recursive sequence
`x^(k+1) = prox_{c g}(x^k)`. -/
def proximal_point_method : ℕ → E
  | 0 => x0
  | k + 1 => proxₚ[c, g] (proximal_point_method k)

/-- The recursive proximal-point sequence agrees with the iterate view
`x^k = (prox_{c g})^[k] (x^0)`. -/
theorem proximal_point_method_def :
    proximal_point_method g x0 c =
      fun k ↦ Nat.iterate (proxₚ[c, g]) k x0 :=
  by
    funext k
    induction k with
    | zero => rfl
    | succ k hk =>
        simp [proximal_point_method, hk, Function.iterate_succ_apply']

/-- The proximal-point method starts at the chosen initial point `x0`. -/
@[simp] theorem proximal_point_method_zero :
    proximal_point_method g x0 c 0 = x0 :=
  rfl

/-- Each successor iterate of the proximal point method is obtained by applying the one-step
proximal-point operator to the previous iterate. -/
@[simp] theorem proximal_point_method_succ (k : ℕ) :
    proximal_point_method g x0 c (k + 1) =
      proxₚ[c, g] (proximal_point_method g x0 c k) :=
  rfl

/-- The recursively chosen proximal-point sequence is a proximal-point trajectory for the canonical
scaled proximal-set owner. -/
theorem proximal_point_method_is_proximal_point_trajectory :
    is_proximal_point_trajectory g x0 c (proximal_point_method g x0 c) := by
  refine ⟨rfl, ?_⟩
  intro k
  simpa using proximal_point_operator_mem g c (proximal_point_method g x0 c k)

end

end

/-! ### Lemma_10_12 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Lemma 10.12 is a `bridge/view` theorem in the Chapter 10 proximal-gradient API. The owner
`gradient_mapping` from Definition 10.5 is already canonical; this file only specializes that
owner to a real-valued smooth term via the shared bridge/view surface `G[L; f, g]`. -/

/-- Helper for Lemma 10.12: the Chapter 10 prox-gradient point is the unique proximal point of
the scaled penalty at the forward-gradient input. -/
lemma prox_gradient_operator_eq_singleton_forward
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    prox[((((1 / L : PosReal) : EReal) • g))] (x - (1 / (L : ℝ)) • ∇ f x) =
      {T[L; f, g] x} := by
  -- Unfold the source-facing prox-gradient operator into the singleton proximal step.
  simpa [proximal_gradient_step] using
    (prox_grad_operator_eq_singleton (f := f.toEReal) (g := g) L
      (interior_effective_domain_point_of_real f x))

/-- Helper for Lemma 10.12: global convex `L`-smoothness on `Set.univ` implies the standard
`1 / L`-cocoercivity inequality for the gradient. -/
lemma smooth_gradient_cocoercive_univ
    (f : E → ℝ) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    (x y : E) :
    inner ℝ (∇ f x - ∇ f y) (x - y) ≥
      (1 / (L : ℝ)) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompactSpace ℝ
  have hf_diff : Differentiable ℝ f := by
    -- Global smoothness on `Set.univ` gives differentiability at every point.
    intro z
    exact hf_smooth.1 z (by simp)
  have hLnn : 0 < PosReal.toNNReal L := by
    exact_mod_cast L.2
  have htfae :=
    convex_l_smooth_tfae_descent_gradient_lower_bound_cocoercive_convex_combo
      f hf_convex hf_diff (PosReal.toNNReal L) hLnn
  have hcoco :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≥
        (1 / (((PosReal.toNNReal L : NNReal) : ℝ))) *
          ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) := by
    -- Extract clause `(iv)` from Theorem 5.8.
    have hcoco_all :
        ∀ x y : E,
          inner ℝ (∇ f x - ∇ f y) (x - y) ≥
            (1 / (((PosReal.toNNReal L : NNReal) : ℝ))) *
              ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) :=
      (List.TFAE.out htfae 0 3
        (a := is_l_smooth_on f Set.univ (PosReal.toNNReal L))
        (b := ∀ x y : E,
          inner ℝ (∇ f x - ∇ f y) (x - y) ≥
            (1 / (((PosReal.toNNReal L : NNReal) : ℝ))) *
              ‖∇ f x - ∇ f y‖ ^ (2 : ℕ))).mp hf_smooth
    exact hcoco_all x y
  simpa using hcoco

/-- Helper for Lemma 10.12: convex global `L`-smoothness controls the gradient difference at the
prox-gradient pair `(x, T_L(x))` by the Chapter 5 cocoercivity inequality. -/
lemma convex_smooth_gradient_difference_sq_le
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) ≤
      (L : ℝ) *
        inner ℝ (∇ f (T[L; f, g] x) - ∇ f x) (T[L; f, g] x - x) := by
  have hcoco :
      (1 / (L : ℝ)) * ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) ≤
        inner ℝ (∇ f (T[L; f, g] x) - ∇ f x) (T[L; f, g] x - x) := by
    -- Specialize the Chapter 5 cocoercivity inequality to `(T_L(x), x)`.
    simpa using
      smooth_gradient_cocoercive_univ
        (f := f) (L := L) hf_convex hf_smooth (T[L; f, g] x) x
  have hmul := mul_le_mul_of_nonneg_left hcoco (le_of_lt L.2)
  have hL : (L : ℝ) * (1 / (L : ℝ)) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
  -- Multiply the cocoercivity estimate by `L` to recover the textbook inequality.
  calc
    ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) =
        ((L : ℝ) * (1 / (L : ℝ))) *
          ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) := by
            rw [hL, one_mul]
    _ = (L : ℝ) *
          ((1 / (L : ℝ)) * ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ)) := by
            rw [mul_assoc]
    _ ≤ (L : ℝ) *
          inner ℝ (∇ f (T[L; f, g] x) - ∇ f x) (T[L; f, g] x - x) := hmul

/-- Helper for Lemma 10.12: the two forward-gradient points entering the consecutive prox steps
are at most one prox-gradient step apart. -/
lemma prox_gradient_forward_points_dist_le_step
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖(x - (1 / (L : ℝ)) • ∇ f x) -
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))‖ ≤
      ‖x - T[L; f, g] x‖ := by
  let a := ∇ f (T[L; f, g] x) - ∇ f x
  let b := T[L; f, g] x - x
  have hgrad :
      ‖a‖ ^ (2 : ℕ) ≤ (L : ℝ) * inner ℝ a b := by
    -- Rewrite the Chapter 5 inequality in the compact `a,b` notation from the source proof.
    simpa [a, b] using
      convex_smooth_gradient_difference_sq_le
        (f := f) (g := g) (L := L) hf_convex hf_smooth x
  have hsq :
      ‖((1 / (L : ℝ)) • a) - b‖ ^ (2 : ℕ) ≤ ‖b‖ ^ (2 : ℕ) := by
    -- Expand the squared norm and reduce to the scalar inequality coming from `hgrad`.
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr L.2), pow_two, inner_smul_left]
    simp only [starRingEnd_apply]
    have hLinv_nonneg : 0 ≤ (1 / (L : ℝ)) := le_of_lt (one_div_pos.mpr L.2)
    have hLinv : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
      field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
    have hdiv :
        (1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ) ≤ inner ℝ a b := by
      have hmul := mul_le_mul_of_nonneg_left hgrad hLinv_nonneg
      calc
        (1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ) ≤
            (1 / (L : ℝ)) * ((L : ℝ) * inner ℝ a b) := hmul
        _ = ((1 / (L : ℝ)) * (L : ℝ)) * inner ℝ a b := by rw [mul_assoc]
        _ = inner ℝ a b := by rw [hLinv, one_mul]
    have hinner_nonneg : 0 ≤ inner ℝ a b := by
      have hleft_nonneg : 0 ≤ (1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ) := by
        exact mul_nonneg hLinv_nonneg (sq_nonneg ‖a‖)
      exact le_trans hleft_nonneg hdiv
    have hdiv' :
        (1 / (L : ℝ)) * ((1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ)) ≤
          (1 / (L : ℝ)) * inner ℝ a b := by
      exact mul_le_mul_of_nonneg_left hdiv hLinv_nonneg
    have hsq_aux :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) ≤
          (1 / (L : ℝ)) * inner ℝ a b := by
      nlinarith [hdiv', norm_nonneg a]
    have hs_nonneg : 0 ≤ (1 / (L : ℝ)) * inner ℝ a b := by
      exact mul_nonneg hLinv_nonneg hinner_nonneg
    have htwice :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) ≤
          2 * ((1 / (L : ℝ)) * inner ℝ a b) := by
      nlinarith [hsq_aux, hs_nonneg]
    have hcore :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) -
          2 * ((1 / (L : ℝ)) * inner ℝ a b) ≤ 0 := by
      linarith [htwice]
    have hcore' :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) -
          2 * (star (1 / (L : ℝ)) * inner ℝ a b) ≤ 0 := by
      simpa using hcore
    linarith [hcore']
  have hnorm :
      ‖((1 / (L : ℝ)) • a) - b‖ ≤ ‖b‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hforward :
      (x - (1 / (L : ℝ)) • ∇ f x) -
          (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x)) =
        ((1 / (L : ℝ)) • a) - b := by
    -- This is the exact forward-point difference from the source proof.
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Convert the compact estimate back to the original forward-gradient points.
  calc
    ‖(x - (1 / (L : ℝ)) • ∇ f x) -
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))‖ =
        ‖((1 / (L : ℝ)) • a) - b‖ := by
          rw [hforward]
    _ ≤ ‖b‖ := hnorm
    _ = ‖x - T[L; f, g] x‖ := by
          simp [b, norm_sub_rev]

/-- Helper for Lemma 10.12: nonexpansivity of the proximal map turns the forward-point estimate
into monotonicity of successive prox-gradient step lengths. -/
lemma prox_gradient_step_distance_monotone
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖T[L; f, g] x - T[L; f, g] (T[L; f, g] x)‖ ≤ ‖x - T[L; f, g] x‖ := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  have hx :
      prox[((((1 / L : PosReal) : EReal) • g))]
        (x - (1 / (L : ℝ)) • ∇ f x) =
          {T[L; f, g] x} := by
    -- The Chapter 10 prox-gradient point is exactly the unique proximal point at the forward input.
    simpa using prox_gradient_operator_eq_singleton_forward (f := f) (g := g) (L := L) x
  have hy :
      prox[((((1 / L : PosReal) : EReal) • g))]
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x)) =
          {T[L; f, g] (T[L; f, g] x)} := by
    -- Apply the same singleton description one step later.
    simpa using
      prox_gradient_operator_eq_singleton_forward
        (f := f) (g := g) (L := L) (T[L; f, g] x)
  have hnonexp :
      ‖T[L; f, g] x - T[L; f, g] (T[L; f, g] x)‖ ≤
        ‖(x - (1 / (L : ℝ)) • ∇ f x) -
          (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))‖ := by
    -- Proximal nonexpansivity compares the two consecutive prox-gradient updates.
    simpa [norm_sub_rev] using
      prox_eq_singleton_nonexpansive
        (f := ((((1 / L : PosReal) : EReal) • g)))
        (x - (1 / (L : ℝ)) • ∇ f x)
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))
        (T[L; f, g] x)
        (T[L; f, g] (T[L; f, g] x))
        hg_scaled.1 hg_scaled.2.1 hg_scaled.2.2 hx hy
  -- Chain nonexpansivity with the forward-point estimate proved above.
  exact
    le_trans hnonexp <|
      prox_gradient_forward_points_dist_le_step
        (f := f) (g := g) (L := L) hf_convex hf_smooth x

-- Route correction: this proof follows the textbook forward-point comparison plus proximal
-- nonexpansivity, rather than the earlier residual-cocoercivity shortcut.
/-- Lemma 10.12: if `f` is convex and globally `L`-smooth for a positive
stepsize `L`, and `g` is proper closed convex, then one prox-gradient step
does not increase the norm of the gradient mapping:
`‖G_L(T_L(x))‖ ≤ ‖G_L(x)‖`. -/
theorem prox_grad_step_gradient_mapping_norm_monotone
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖G[L; f, g] (T[L; f, g] x)‖ ≤ ‖G[L; f, g] x‖ := by
  let xPlus := T[L; f, g] x
  let xNext := T[L; f, g] xPlus
  have hstep :
      ‖xPlus - xNext‖ ≤ ‖x - xPlus‖ := by
    -- First compare the lengths of two consecutive prox-gradient steps.
    simpa [xPlus, xNext] using
      prox_gradient_step_distance_monotone
        (f := f) (g := g) (L := L) hf_convex hf_smooth x
  have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt L.2)
  have hGxPlus :
      ‖G[L; f, g] xPlus‖ = (L : ℝ) * ‖xPlus - xNext‖ := by
    -- Rewrite the residual at `x⁺` as the scaled step `L (x⁺ - x⁺⁺)`.
    calc
      ‖G[L; f, g] xPlus‖ =
          ‖(L : ℝ) •
              ((interior_effective_domain_point_of_real f xPlus : E) -
                T[L, f.toEReal, g] (interior_effective_domain_point_of_real f xPlus))‖ := by
            rw [prox_gradient_mapping_apply, gradient_mapping_apply]
      _ = (L : ℝ) *
            ‖(interior_effective_domain_point_of_real f xPlus : E) -
              T[L, f.toEReal, g] (interior_effective_domain_point_of_real f xPlus)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_of_lt L.2)]
      _ = (L : ℝ) * ‖xPlus - xNext‖ := by
            congr 1
  have hGx :
      ‖G[L; f, g] x‖ = (L : ℝ) * ‖x - xPlus‖ := by
    -- The same residual rewrite at the original point gives the right-hand side.
    calc
      ‖G[L; f, g] x‖ =
          ‖(L : ℝ) •
              ((interior_effective_domain_point_of_real f x : E) -
                T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x))‖ := by
            rw [prox_gradient_mapping_apply, gradient_mapping_apply]
      _ = (L : ℝ) *
            ‖(interior_effective_domain_point_of_real f x : E) -
              T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_of_lt L.2)]
      _ = (L : ℝ) * ‖x - xPlus‖ := by
            congr 1
  -- After both residual rewrites, the theorem is exactly the step-length monotonicity above.
  calc
    ‖G[L; f, g] (T[L; f, g] x)‖ = ‖G[L; f, g] xPlus‖ := by simp [xPlus]
    _ = (L : ℝ) * ‖xPlus - xNext‖ := hGxPlus
    _ ≤ (L : ℝ) * ‖x - xPlus‖ := hmul
    _ = ‖G[L; f, g] x‖ := hGx.symm

end
