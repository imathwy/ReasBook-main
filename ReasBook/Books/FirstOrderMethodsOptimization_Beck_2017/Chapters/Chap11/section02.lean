import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_2 (from Chap11) -/
/- Definition 11.2 is a `bridge/view` recall in the proximal-gradient chapter.

Domain sampling shows that the correct owner abstraction is already present upstream:
- Definition 10.2's `composite_model_objective`, the chapter owner for the source-facing
  composite objective `F(x) = f(x) + g(x)`;
- Definition 10.66, which already reuses the same owner in a later proximal-gradient setting with
  no new owner-level data;
- Definition 11.3, where the genuinely new Chapter 11 content first appears as the block-product
  specialization of that same owner.

The primitive data remain only the two summands `f` and `g`; Chapter 11.2 adds no new canonical
object beyond the existing pointwise-sum objective. This file should therefore recall
`composite_model_objective` directly rather than keep a second wrapper or alias specialized to the
proximal-gradient section. -/

/- Definition 11.2: the proximal gradient model
`min_{x ∈ E} f(x) + g(x)` is the same composite objective owner
`composite_model_objective` used earlier for the pointwise sum `F(x) = f(x) + g(x)`. -/
recall composite_model_objective

/-! ### Lemma_11_2 (from Chap11) -/
noncomputable section

universe u v

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/- Domain sampling for this refinement:
- Chapter 5's `is_l_smooth_on` is the owner predicate for quadratic upper models on convex sets.
- `𝒰[i]` and `block_coordinate_slice` from `Definition_11_4` are the canonical one-block update
  and frozen-slice owners.
- `IsBlockProximalGradientProblem.block_partial_gradient_hasGradientAt` is the owner-level bridge
  from the Chapter 11 block-gradient data to the gradient of the one-block slice.

Lemma 11.2 is `source-facing`: it is the one-block quadratic upper model along the textbook update
`x + 𝒰[i] d`. Its best `core/canonical` owner for the labeled chapter statement is
`BlockProximalGradientAssumptions`, while the lower-level Chapter 5 invocation remains a
`bridge/view` theorem with explicit slice smoothness data. The primitive data for that bridge are
only the chosen block `i`, its smoothness constant, the slice smoothness owner, and the block
gradient at the base point; under the Chapter 11 owner these are all derived. -/

-- Proof sketch: apply the Chapter 5 descent lemma to the fixed one-block slice
-- `block_coordinate_slice f x i : Ei i → ℝ` on the admissible block set
-- `{d | x + 𝒰[i] d ∈ interior (effective_domain f)}`. Convexity of that slice
-- domain is assumed
-- directly, the owner hypothesis `h_slice_smooth` supplies the smoothness input, and the
-- gradient specification at `0` identifies the linear term with
-- `block_gradient i x`.
/-- Bridge lemma for Lemma 11.2: fix a block index `i` and a base point `x`, and suppose the
admissible one-block slice domain
`{d | x + 𝒰[i] d ∈ interior (effective_domain f)}` is convex. If the `i`-th
slice `d ↦ f (x + 𝒰[i] d)` is `L`-smooth on that admissible slice domain and has gradient
`block_gradient i x` at `d = 0`, then the block update satisfies the quadratic upper model
`f (x + 𝒰[i] d) ≤ f x + ⟪block_gradient i x, d⟫ + (L / 2) ‖d‖²`
whenever both endpoints lie in `interior (effective_domain f)`. -/
theorem block_coordinate_descent_lemma_of_slice_smooth
    (f : ((i : ι) → Ei i) → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (L : NNReal)
    (i : ι) [CompleteSpace (Ei i)]
    {x : (j : ι) → Ei j}
    (h_slice_convex :
      Convex ℝ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)})
    (h_slice_smooth :
      is_l_smooth_on
        (block_coordinate_slice f x i)
        {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
        L)
    (h_block_gradient_spec :
      HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0)
    {d : Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hxd : x + 𝒰[i] d ∈ interior (effective_domain f)) :
    (f (x + 𝒰[i] d)).toReal ≤
      (f x).toReal + inner ℝ (block_gradient i x) d + ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
  have h0 :
      (0 : Ei i) ∈ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)} := by
    simpa [block_coordinate_update] using hx
  have hdescent :=
    is_l_smooth_on_descent_lemma h_slice_convex h_slice_smooth h0 hxd
  simpa
      [block_coordinate_slice_apply, block_coordinate_update, h_block_gradient_spec.gradient] using
    hdescent

namespace IsBlockProximalGradientProblem

variable [Fintype ι]
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Li : (i : ι) → PosReal}

omit [∀ i, InnerProductSpace ℝ (Ei i)] [Fintype ι] in
private theorem block_coordinate_update_update_sub
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i (e - d) =
      block_coordinate_update x i e := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [block_coordinate_update, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · simp [block_coordinate_update, hji]

omit [∀ i, InnerProductSpace ℝ (Ei i)] [Fintype ι] in
private theorem block_coordinate_update_update
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i e =
      block_coordinate_update x i (d + e) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [block_coordinate_update, add_left_comm, add_comm]
  · simp [block_coordinate_update, hji]

/-- Re-centering the one-block slice at `d` identifies its gradient with the Chapter 11 block
gradient at the updated point `x + 𝒰[i] d`. -/
theorem block_coordinate_slice_hasGradientAt
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (j : ι) → Ei j} {d : Ei i}
    (hxd : x + 𝒰[i] d ∈ interior (effective_domain f)) :
    HasGradientAt
      (block_coordinate_slice f x i)
      (block_gradient i (x + 𝒰[i] d))
      d := by
  let y := block_coordinate_update x i d
  have hy :
      block_coordinate_slice f y i =
        fun e : Ei i ↦ block_coordinate_slice f x i (d + e) := by
    funext e
    simp [y, block_coordinate_slice_apply, block_coordinate_update_update]
  have hshift :
      HasGradientAt
        (fun e : Ei i ↦ block_coordinate_slice f x i (d + e))
        (block_gradient i y)
        0 := by
    have hbase :
        HasGradientAt
          (block_coordinate_slice f y i)
          (block_gradient i y)
          0 :=
      hproblem.block_partial_gradient_hasGradientAt i hxd
    rw [hy] at hbase
    exact hbase
  rw [hasGradientAt_iff_hasFDerivAt] at hshift ⊢
  simpa using (hasFDerivAt_comp_add_left d).1 hshift

/-- The Chapter 11 block-Lipschitz owner implies that the frozen one-block slice is
`L_i`-smooth on its natural admissible domain. -/
theorem block_coordinate_slice_is_l_smooth_on
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (j : ι) → Ei j} :
    is_l_smooth_on
      (block_coordinate_slice f x i)
      {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
      (PosReal.toNNReal (Li i)) := by
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro d hd
    exact (hproblem.block_coordinate_slice_hasGradientAt i hd).differentiableAt
  · intro d hd e he
    have hde :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) =
          block_coordinate_update x i e :=
      block_coordinate_update_update_sub x i d e
    have hde' :
        block_coordinate_update (x + 𝒰[i] d) i (e - d) = x + 𝒰[i] e := by
      simpa [block_coordinate_update] using hde
    have he' :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) ∈
          interior (effective_domain f) := by
      rw [hde]
      exact he
    have he'' :
        block_coordinate_update (x + 𝒰[i] d) i (e - d) ∈
          interior (effective_domain f) := by
      simpa [block_coordinate_update] using he'
    have hlip :=
      hproblem.block_partial_gradient_lipschitz
        i
        hd
        he''
    have hdgrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (x + 𝒰[i] d))
          d :=
      hproblem.block_coordinate_slice_hasGradientAt i hd
    have hegrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (x + 𝒰[i] e))
          e :=
      hproblem.block_coordinate_slice_hasGradientAt i he
    have hlip' :
        ‖block_gradient i (x + 𝒰[i] d) - block_gradient i (x + 𝒰[i] e)‖ ≤
          ↑(Li i) * ‖d - e‖ := by
      simpa [hde', norm_sub_rev] using hlip
    simpa [hdgrad.gradient, hegrad.gradient] using hlip'

end IsBlockProximalGradientProblem

namespace BlockProximalGradientAssumptions

variable [Fintype ι]
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

omit [Fintype ι] in
private theorem block_coordinate_update_combo
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) {a b : ℝ} (hab : a + b = 1) :
    a • block_coordinate_update x i d + b • block_coordinate_update x i e =
      block_coordinate_update x i (a • d + b • e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    calc
      a • block_coordinate_update x i d i + b • block_coordinate_update x i e i
          = (a • x i + b • x i) + (a • d + b • e) := by
              simp [block_coordinate_update, smul_add, add_assoc, add_left_comm, add_comm]
      _ = (a + b) • x i + (a • d + b • e) := by rw [← add_smul]
      _ = x i + (a • d + b • e) := by simp [hab]
      _ = block_coordinate_update x i (a • d + b • e) i := by
            simp [block_coordinate_update]
  · calc
      a • block_coordinate_update x i d j + b • block_coordinate_update x i e j
          = a • x j + b • x j := by simp [block_coordinate_update, hji]
      _ = (a + b) • x j := by rw [← add_smul]
      _ = block_coordinate_update x i (a • d + b • e) j := by
            simp [block_coordinate_update, hji, hab]

/-- The admissible one-block slice domain is convex under the Chapter 11 standing assumptions. -/
theorem block_coordinate_slice_domain_convex
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) {x : (j : ι) → Ei j} :
    Convex ℝ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)} := by
  let hinterior : Convex ℝ (interior (effective_domain f)) :=
    hproblem.f_effective_domain_convex.interior
  intro d hd e he a b ha hb hab
  have hcomb := hinterior hd he ha hb hab
  have hcomb' :
      a • block_coordinate_update x i d + b • block_coordinate_update x i e ∈
        interior (effective_domain f) := by
    simpa [block_coordinate_update] using hcomb
  have hcomb'' :
      block_coordinate_update x i (a • d + b • e) ∈ interior (effective_domain f) := by
    simpa [block_coordinate_update_combo x i d e hab] using hcomb'
  simpa [block_coordinate_update] using hcomb''

/-- Lemma 11.2: under Definition 11.4, the textbook one-block update satisfies the quadratic
upper model with the corresponding block Lipschitz constant `L_i`. -/
theorem block_coordinate_descent_lemma
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (j : ι) → Ei j} {d : Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hxd : x + 𝒰[i] d ∈ interior (effective_domain f)) :
    (f (x + 𝒰[i] d)).toReal ≤
      (f x).toReal + inner ℝ (block_gradient i x) d + ((Li i : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
  let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
    hproblem.toIsBlockProximalGradientProblem
  have hsmooth :
      is_l_smooth_on
        (block_coordinate_slice f x i)
        {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
        (PosReal.toNNReal (Li i)) :=
    hcore.block_coordinate_slice_is_l_smooth_on i
  have hgrad : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0 :=
    hcore.block_partial_gradient_hasGradientAt i hx
  exact
    block_coordinate_descent_lemma_of_slice_smooth
      f
      block_gradient
      (PosReal.toNNReal (Li i))
      i
      (hproblem.block_coordinate_slice_domain_convex i)
      hsmooth
      hgrad
      hx
      hxd

end BlockProximalGradientAssumptions

end

/-! ### Theorem_11_2 (from Chap11) -/
noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {f : ((j : ι) → Ei j) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable
    (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
    (hg_closed : ∀ i, LowerSemicontinuous (g i))
    (hg_convex : ∀ i, is_convex_function (g i))

set_option quotPrecheck false in
local notation "BlockSpace" => (j : ι) → Ei j

/- Theorem 11.2 is `source-facing` for a fixed Chapter 11 block. Its `core/canonical` owner is
Chapter 10's prox-gradient mapping for the frozen one-block slice `block_coordinate_slice f x i`
against the single penalty `g i`, while the family-valued Chapter 11 mapping `G^i_L(x)` is the
relevant `bridge/view`. The public API stays source-facing: the two monotonicity clauses below
are derived from Theorem 10.9 for the frozen slice, without adding a separate public
slice-specialization theorem. -/

section

variable (i : ι) [ProperSpace (Ei i)]

local instance : IsProperExtendedRealFunction (g i) :=
  hg_proper i

local instance : Fact (LowerSemicontinuous (g i)) :=
  ⟨hg_closed i⟩

local instance : Fact (is_convex_function (g i)) :=
  ⟨hg_convex i⟩

/-- Helper for Theorem 11.2: translating the block slice from the displacement variable `d`
to the coordinate variable `y = x_i + d` moves the gradient statement from `0` to `x_i`
without changing the block gradient. -/
lemma translated_block_coordinate_slice_hasGradientAt
    (x : BlockSpace)
    (hblock : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0) :
    HasGradientAt
      (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i))
      (block_gradient i x)
      (x i) := by
  -- Translating the coordinate variable by `x i` carries the derivative at `0` to `x i`.
  rw [hasGradientAt_iff_hasFDerivAt]
  have houter :
      HasFDerivAt
        (block_coordinate_slice f x i)
        (InnerProductSpace.toDualMap ℝ (Ei i) (block_gradient i x))
        (x i - x i) := by
    simpa using hblock.hasFDerivAt
  simpa [Function.comp] using
    (HasFDerivAt.comp
      (f := fun y : Ei i ↦ y - x i)
      (g := block_coordinate_slice f x i)
      (x := x i)
      houter
      (hasFDerivAt_sub_const (x i)))

/-- Helper for Theorem 11.2: the Chapter 11 one-block prox point is the unique proximal point of
`(1 / L) g_i` at the forward block-gradient point. -/
lemma block_partial_prox_grad_point_eq_prox_singleton
    (L : PosReal) (x : BlockSpace) :
    prox[((((1 / L : PosReal) : EReal) • g i))]
      (x i - (1 / L : ℝ) • block_gradient i x) =
        {T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} := by
  let hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / L)
  -- The Chapter 11 prox point is defined by choosing the unique element of this singleton set.
  simpa [block_partial_prox_grad_point, hscaled] using
    (Classical.choose_spec <|
      prox_eq_singleton_of_proper_closed_convex
        ((((1 / L : PosReal) : EReal) • g i))
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        (x i - (1 / L : ℝ) • block_gradient i x))

/-- Helper for Theorem 11.2: the translated Chapter 10 prox-gradient point agrees with the
Chapter 11 one-block proximal-gradient point. -/
lemma translated_block_coordinate_slice_prox_point_eq_block_partial_prox_grad_point
    [IsProperExtendedRealFunction (g i)]
    [Fact (LowerSemicontinuous (g i))]
    [Fact (is_convex_function (g i))]
    (L : PosReal) (x : BlockSpace)
    (hblock : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0) :
    T[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i) =
      T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i := by
  have hgrad :
      ∇ (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)) (x i) = block_gradient i x := by
    -- The translated slice inherits the prescribed block gradient at `x i`.
    exact (translated_block_coordinate_slice_hasGradientAt
      (i := i) (x := x) hblock).gradient
  have hgrad' :
      ∇ (fun y : Ei i ↦ (f (block_coordinate_update x i (y - x i))).toReal) (x i) =
        block_gradient i x := by
    -- Expanding the translated slice puts the gradient in the exact shape used by Chapter 10.
    simpa [block_coordinate_slice_apply] using hgrad
  have htranslated_singleton :
      prox[((((1 / L : PosReal) : EReal) • g i))]
        (x i - (1 / L : ℝ) • block_gradient i x) =
          {T[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i)} := by
    -- Route correction: the translated slice at `x i` has the same forward point as the Chapter 11
    -- block update, unlike the unshifted slice at `0`.
    simpa [proximal_gradient_step, hgrad', interior_effective_domain_point_of_real] using
      (prox_grad_operator_eq_singleton
        ((fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)).toEReal)
        (g i)
        L
        (interior_effective_domain_point_of_real
          (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i))
          (x i)))
  have hblock_singleton :
      prox[((((1 / L : PosReal) : EReal) • g i))]
        (x i - (1 / L : ℝ) • block_gradient i x) =
          {T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} := by
    -- The Chapter 11 prox point is chosen from that same singleton proximal set.
    exact block_partial_prox_grad_point_eq_prox_singleton
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)
      L
      x
  have hsingleton :
      ({T[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i)} : Set (Ei i)) =
        {T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} := by
    exact htranslated_singleton.symm.trans hblock_singleton
  have hmem :
      T[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i) ∈
        ({T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i} : Set (Ei i)) := by
    have hmem_self :
        T[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i) ∈
          ({T[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i)} :
            Set (Ei i)) := by
      simp
    rw [hsingleton] at hmem_self
    simpa using hmem_self
  simpa using hmem

/-- Helper for Theorem 11.2: the translated Chapter 10 gradient mapping is exactly the Chapter 11
partial gradient mapping for the fixed block. -/
lemma translated_block_coordinate_slice_gradient_mapping_eq_block_partial_gradient_mapping
    [IsProperExtendedRealFunction (g i)]
    [Fact (LowerSemicontinuous (g i))]
    [Fact (is_convex_function (g i))]
    (L : PosReal) (x : BlockSpace)
    (hblock : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0) :
    G[L; (fun y : Ei i ↦ block_coordinate_slice f x i (y - x i)), g i] (x i) =
      G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i := by
  -- Once both mappings are expanded as `L • (current point - prox point)`, the prox-point bridge
  -- makes the residuals coincide.
  rw [prox_gradient_mapping_apply, gradient_mapping_apply]
  simpa [block_partial_gradient_mapping_def] using
    congrArg
      (fun z : Ei i ↦ (L : ℝ) • (x i - z))
      (translated_block_coordinate_slice_prox_point_eq_block_partial_prox_grad_point
        (hg_proper := hg_proper)
        (hg_closed := hg_closed)
        (hg_convex := hg_convex)
        (i := i)
        L
        x
        hblock)

/-- Helper for Theorem 11.2: the Chapter 11 one-block prox point is the current block minus the
scaled block partial gradient mapping residual. -/
lemma block_partial_prox_grad_point_eq_sub_gradient_mapping
    (L : PosReal) (x : BlockSpace) :
    T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i =
      x i - (1 / (L : ℝ)) • G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i := by
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt L.2
  have hL : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
    field_simp [hL_ne]
  -- Solve the defining residual identity `G_L^i(x) = L • (x_i - T_L^i(x))` for `T_L^i(x)`.
  calc
    T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i =
        x i - (x i - T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i) := by
          exact
            (sub_sub_cancel
              (x i)
              (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i)).symm
    _ =
        x i - (1 / (L : ℝ)) • G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i := by
          rw [block_partial_gradient_mapping_def, smul_smul, hL, one_smul]

/-- Helper for Theorem 11.2: the singleton proximal characterization of the one-block update
yields the real-valued affine support inequality for the residual
`G_L^i(x) - block_gradient i x`. -/
lemma block_partial_gradient_mapping_support_ineq_real
    (L : PosReal) (x : BlockSpace) :
    T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i ∈ effective_domain (g i) ∧
      ∀ y ∈ effective_domain (g i),
        inner ℝ
            (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i - block_gradient i x)
            (y - T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i) ≤
          (g i y).toReal -
            (g i (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i)).toReal := by
  let μ : PosReal := 1 / L
  let z : Ei i := x i - (1 / (L : ℝ)) • block_gradient i x
  let Tpoint := T[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  have hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g i)
      (hg_proper i)
      (hg_closed i)
      (hg_convex i)
      μ
  have hprox :
      prox[(((μ : EReal) • g i))] z = {Tpoint} := by
    -- The Chapter 11 block prox point is defined as the unique point of this singleton.
    simpa [μ, z, Tpoint] using
      block_partial_prox_grad_point_eq_prox_singleton
        (hg_proper := hg_proper)
        (hg_closed := hg_closed)
        (hg_convex := hg_convex)
        (i := i)
        L
        x
  rcases prox_singleton_implies_effective_domain_and_inner_support
      (((μ : EReal) • g i))
      hscaled.1
      hscaled.2.2
      z
      Tpoint
      hprox with
    ⟨hTx_eff_scaled, hsupport⟩
  have hTx_eff : Tpoint ∈ effective_domain (g i) := by
    rw [mem_effective_domain] at hTx_eff_scaled ⊢
    refine lt_top_iff_ne_top.mpr ?_
    intro hTx_top
    have hscaled_top : (((μ : EReal) • g i) Tpoint) = ⊤ := by
      rw [Pi.smul_apply, smul_eq_mul, hTx_top]
      exact EReal.coe_mul_top_of_pos μ.2
    exact (lt_irrefl (⊤ : EReal)) (hscaled_top ▸ hTx_eff_scaled)
  refine ⟨hTx_eff, ?_⟩
  intro y hy
  have hy_scaled : y ∈ effective_domain (((μ : EReal) • g i)) := by
    rw [mem_effective_domain] at hy ⊢
    rw [Pi.smul_apply, smul_eq_mul]
    have hμ_nonneg : (0 : EReal) ≤ (μ : ℝ) := by
      exact_mod_cast (show 0 ≤ (μ : ℝ) by exact le_of_lt μ.2)
    exact
      lt_top_iff_ne_top.mpr <|
        (EReal.mul_ne_top _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hμ_nonneg,
            Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hy).ne⟩
  have hy_ne_bot : g i y ≠ ⊥ := (hg_proper i).ne_bot y
  have hy_val :
      g i y = (((g i y).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hy).ne
        hy_ne_bot).symm
  have hTx_ne_bot : g i Tpoint ≠ ⊥ :=
    (hg_proper i).ne_bot _
  have hTx_val : g i Tpoint = (((g i Tpoint).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hTx_eff).ne
        hTx_ne_bot).symm
  have hTx_scaled_val :
      (((μ : EReal) • g i) Tpoint) = ((((μ : ℝ) * (g i Tpoint).toReal : ℝ)) : EReal) := by
    have htoReal : ((((μ : EReal) • g i) Tpoint).toReal) = (μ : ℝ) * (g i Tpoint).toReal := by
      rw [Pi.smul_apply, smul_eq_mul, EReal.toReal_mul, EReal.toReal_coe]
    calc
      (((μ : EReal) • g i) Tpoint) = ((((((μ : EReal) • g i) Tpoint).toReal : ℝ)) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hTx_eff_scaled).ne (hscaled.1.ne_bot Tpoint)]
      _ = ((((μ : ℝ) * (g i Tpoint).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hy_scaled_val :
      (((μ : EReal) • g i) y) = ((((μ : ℝ) * (g i y).toReal : ℝ)) : EReal) := by
    have htoReal : ((((μ : EReal) • g i) y).toReal) = (μ : ℝ) * (g i y).toReal := by
      rw [Pi.smul_apply, smul_eq_mul, EReal.toReal_mul, EReal.toReal_coe]
    calc
      (((μ : EReal) • g i) y) = ((((((μ : EReal) • g i) y).toReal : ℝ)) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hy_scaled).ne (hscaled.1.ne_bot y)]
      _ = ((((μ : ℝ) * (g i y).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hsupport_real :
      inner ℝ (z - Tpoint) (y - Tpoint) ≤ (μ : ℝ) * ((g i y).toReal - (g i Tpoint).toReal) := by
    have hsupportE := hsupport y hy_scaled
    rw [hTx_scaled_val, hy_scaled_val] at hsupportE
    have hsupportE' :
        (((inner ℝ (z - Tpoint) (y - Tpoint) : ℝ)) : EReal) ≤
          ((((μ : ℝ) * ((g i y).toReal - (g i Tpoint).toReal) : ℝ)) : EReal) := by
      simpa [EReal.coe_sub, mul_sub_left_distrib] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hsupport_div :
      inner ℝ ((1 / μ : ℝ) • (z - Tpoint)) (y - Tpoint) ≤
        (g i y).toReal - (g i Tpoint).toReal := by
    have hscaled_le :
        (1 / μ : ℝ) * inner ℝ (z - Tpoint) (y - Tpoint) ≤
          (1 / μ : ℝ) * ((μ : ℝ) * ((g i y).toReal - (g i Tpoint).toReal)) := by
      have hμ_inv_nonneg : 0 ≤ (1 / μ : ℝ) := by
        simpa [one_div] using inv_nonneg.mpr (show 0 ≤ (μ : ℝ) by exact le_of_lt μ.2)
      exact mul_le_mul_of_nonneg_left hsupport_real hμ_inv_nonneg
    have hcancel :
        (1 / μ : ℝ) * ((μ : ℝ) * ((g i y).toReal - (g i Tpoint).toReal)) =
          (g i y).toReal - (g i Tpoint).toReal := by
      have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
      field_simp [hμ_ne]
    rw [show inner ℝ ((1 / μ : ℝ) • (z - Tpoint)) (y - Tpoint) =
        (1 / μ : ℝ) * inner ℝ (z - Tpoint) (y - Tpoint) by
          simpa using inner_smul_left (z - Tpoint) (y - Tpoint) (1 / μ : ℝ)]
    rw [hcancel] at hscaled_le
    exact hscaled_le
  have hGdef :
      G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i =
        (L : ℝ) • (x i - Tpoint) := by
    -- Use the defining residual formula for the Chapter 11 block gradient mapping.
    simpa [Tpoint] using
      (block_partial_gradient_mapping_def
        g
        block_gradient
        hg_proper
        hg_closed
        hg_convex
        L
        x
        i)
  have hz :
      z - Tpoint =
        (1 / (L : ℝ)) •
          (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i - block_gradient i x) := by
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt L.2
    have hLinvL : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
      field_simp [hL_ne]
    -- Rewrite the forward point using the defining residual formula for `G_L^i(x)`.
    calc
      z - Tpoint = (x i - Tpoint) - (1 / (L : ℝ)) • block_gradient i x := by
        dsimp [z]
        abel
      _ =
          ((1 / (L : ℝ)) * (L : ℝ)) • (x i - Tpoint) -
            (1 / (L : ℝ)) • block_gradient i x := by
              rw [hLinvL, one_smul]
      _ =
          (1 / (L : ℝ)) • ((L : ℝ) • (x i - Tpoint)) -
            (1 / (L : ℝ)) • block_gradient i x := by
              rw [smul_smul]
      _ =
          (1 / (L : ℝ)) •
            G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i -
              (1 / (L : ℝ)) • block_gradient i x := by
                rw [← hGdef]
      _ =
          (1 / (L : ℝ)) •
            (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i - block_gradient i x) := by
              rw [smul_sub]
  have hvector :
      ((1 / μ : ℝ) • (z - Tpoint)) =
        G[L; g, block_gradient, hg_proper, hg_closed, hg_convex] x i - block_gradient i x := by
    have hμinv : (1 / μ : ℝ) = (L : ℝ) := by
      simp [μ, one_div]
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt L.2
    have hcancel : (L : ℝ) * (1 / (L : ℝ)) = 1 := by
      field_simp [hL_ne]
    -- The Chapter 6 scaling exactly cancels the reciprocal stepsize.
    rw [hz, hμinv, smul_smul, hcancel, one_smul]
  -- Rewriting the scaled support inequality gives the residual support estimate in real form.
  rw [hvector] at hsupport_div
  simpa [Tpoint] using hsupport_div

/-- Helper for Theorem 11.2: the two one-block support inequalities imply the quadratic norm
bound for the Chapter 11 block partial gradient mappings. -/
lemma block_partial_gradient_mapping_quadratic_bound
    (L₁ L₂ : PosReal) (x : BlockSpace) :
    (1 / (L₁ : ℝ)) *
          ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ) +
        (1 / (L₂ : ℝ)) *
          ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ^ (2 : ℕ) ≤
      ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) *
        ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ *
        ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ := by
  let grad := block_gradient i x
  let G₁ := G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  let G₂ := G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  let T₁ := T[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  let T₂ := T[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i
  rcases block_partial_gradient_mapping_support_ineq_real
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)
      L₁
      x with
    ⟨hT₁_eff, hsupport₁⟩
  rcases block_partial_gradient_mapping_support_ineq_real
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)
      L₂
      x with
    ⟨hT₂_eff, hsupport₂⟩
  have h₁ :
      inner ℝ (G₁ - grad) (T₂ - T₁) ≤
        (g i T₂).toReal - (g i T₁).toReal := by
    simpa [G₁, T₁, T₂, grad] using hsupport₁ T₂ hT₂_eff
  have h₂ :
      inner ℝ (G₂ - grad) (T₁ - T₂) ≤
        (g i T₁).toReal - (g i T₂).toReal := by
    simpa [G₂, T₁, T₂, grad] using hsupport₂ T₁ hT₁_eff
  have hsum :
      0 ≤ inner ℝ (G₁ - G₂) (T₁ - T₂) := by
    have hsum0 :
        inner ℝ (G₁ - grad) (T₂ - T₁) +
            inner ℝ (G₂ - grad) (T₁ - T₂) ≤
          0 := by
      linarith
    have hleft :
        inner ℝ (G₁ - grad) (T₂ - T₁) +
            inner ℝ (G₂ - grad) (T₁ - T₂) =
          -inner ℝ (G₁ - G₂) (T₁ - T₂) := by
      have hneg : T₂ - T₁ = -(T₁ - T₂) := by
        abel
      have hsub : (G₂ - grad) - (G₁ - grad) = -(G₁ - G₂) := by
        abel
      -- Adding the two inequalities cancels the common block-gradient term.
      calc
        inner ℝ (G₁ - grad) (T₂ - T₁) + inner ℝ (G₂ - grad) (T₁ - T₂) =
            inner ℝ (-(G₁ - grad)) (T₁ - T₂) + inner ℝ (G₂ - grad) (T₁ - T₂) := by
              rw [hneg, inner_neg_right, inner_neg_left]
        _ = inner ℝ (-(G₁ - grad) + (G₂ - grad)) (T₁ - T₂) := by
              rw [← inner_add_left]
        _ = inner ℝ ((G₂ - grad) - (G₁ - grad)) (T₁ - T₂) := by
              abel
        _ = -inner ℝ (G₁ - G₂) (T₁ - T₂) := by
              rw [hsub, inner_neg_left]
    rw [hleft] at hsum0
    linarith
  have hstep :
      T₁ - T₂ = (1 / (L₂ : ℝ)) • G₂ - (1 / (L₁ : ℝ)) • G₁ := by
    -- Rewrite both prox points as the current block minus the scaled residual.
    dsimp [T₁, T₂]
    rw [block_partial_prox_grad_point_eq_sub_gradient_mapping
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)]
    rw [block_partial_prox_grad_point_eq_sub_gradient_mapping
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)]
    abel
  have hinner :
      inner ℝ (G₁ - G₂) ((1 / (L₂ : ℝ)) • G₂ - (1 / (L₁ : ℝ)) • G₁) =
        ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) * inner ℝ G₁ G₂ -
          (1 / (L₁ : ℝ)) * ‖G₁‖ ^ (2 : ℕ) -
          (1 / (L₂ : ℝ)) * ‖G₂‖ ^ (2 : ℕ) := by
    -- Expanding the inner product isolates the norm squares and the mixed term.
    rw [inner_sub_right, inner_smul_right, inner_smul_right]
    have hleft :
        inner ℝ (G₁ - G₂) G₂ = inner ℝ G₁ G₂ - ‖G₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have hright :
        inner ℝ (G₁ - G₂) G₁ = ‖G₁‖ ^ (2 : ℕ) - inner ℝ G₂ G₁ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
    rw [hleft, hright, real_inner_comm G₂ G₁]
    ring
  have hcs : inner ℝ G₁ G₂ ≤ ‖G₁‖ * ‖G₂‖ := by
    -- Cauchy--Schwarz bounds the mixed inner product by the product of the norms.
    exact real_inner_le_norm G₁ G₂
  rw [hstep, hinner] at hsum
  have hcore :
      (1 / (L₁ : ℝ)) * ‖G₁‖ ^ (2 : ℕ) +
          (1 / (L₂ : ℝ)) * ‖G₂‖ ^ (2 : ℕ) ≤
        ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) * inner ℝ G₁ G₂ := by
    nlinarith
  have hcoeff_nonneg : 0 ≤ (1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ)) := by
    exact add_nonneg
      (one_div_nonneg.mpr (le_of_lt L₁.2))
      (one_div_nonneg.mpr (le_of_lt L₂.2))
  have hmul := mul_le_mul_of_nonneg_left hcs hcoeff_nonneg
  exact le_trans hcore <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Theorem 11.2: the quadratic bound forces both monotonicity of
`‖G_L^i(x)‖` and antitonicity of `‖G_L^i(x)‖ / L` in the block stepsize. -/
lemma block_partial_gradient_mapping_norm_ratio_bounds
    {L₁ L₂ : PosReal}
    (hL : L₂ ≤ L₁)
    (x : BlockSpace) :
    ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ≤
        ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ∧
      ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ / (L₁ : ℝ) ≤
        ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ / (L₂ : ℝ) := by
  let a : ℝ := ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖
  let b : ℝ := ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖
  have ha : 0 ≤ a := by
    dsimp [a]
    exact norm_nonneg _
  have hb : 0 ≤ b := by
    dsimp [b]
    exact norm_nonneg _
  have hquad :=
    block_partial_gradient_mapping_quadratic_bound
      (g := g)
      (block_gradient := block_gradient)
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)
      L₁
      L₂
      x
  have hquad_ab :
      (1 / (L₁ : ℝ)) * a ^ (2 : ℕ) + (1 / (L₂ : ℝ)) * b ^ (2 : ℕ) ≤
        ((1 / (L₁ : ℝ)) + (1 / (L₂ : ℝ))) * a * b := by
    simpa [a, b] using hquad
  have hL₁_ne : (L₁ : ℝ) ≠ 0 := ne_of_gt L₁.2
  have hL₂_ne : (L₂ : ℝ) ≠ 0 := ne_of_gt L₂.2
  have hquad' :
      (L₂ : ℝ) * a ^ (2 : ℕ) + (L₁ : ℝ) * b ^ (2 : ℕ) ≤
        ((L₁ : ℝ) + (L₂ : ℝ)) * a * b := by
    have hclear := hquad_ab
    -- Clearing the positive denominators exposes the scalar quadratic inequality.
    field_simp [hL₁_ne, hL₂_ne] at hclear
    nlinarith
  have hmono : b ≤ a := by
    by_contra hba
    have hba' : a < b := lt_of_not_ge hba
    have hLb : (L₂ : ℝ) * a < (L₁ : ℝ) * b := by
      have h₁ : (L₂ : ℝ) * a < (L₂ : ℝ) * b := by
        exact mul_lt_mul_of_pos_left hba' L₂.2
      have h₂ : (L₂ : ℝ) * b ≤ (L₁ : ℝ) * b := by
        exact mul_le_mul_of_nonneg_right hL hb
      exact lt_of_lt_of_le h₁ h₂
    have hcontr :
        ((L₁ : ℝ) + (L₂ : ℝ)) * a * b <
          (L₂ : ℝ) * a ^ (2 : ℕ) + (L₁ : ℝ) * b ^ (2 : ℕ) := by
      nlinarith
    exact (not_lt_of_ge hquad') hcontr
  have hratio_num : (L₂ : ℝ) * a ≤ (L₁ : ℝ) * b := by
    by_contra hratio
    have hratio' : (L₁ : ℝ) * b < (L₂ : ℝ) * a := lt_of_not_ge hratio
    have hab_strict : b < a := by
      by_contra hab
      have hab' : a ≤ b := le_of_not_gt hab
      have h₁ : (L₂ : ℝ) * a ≤ (L₂ : ℝ) * b := by
        exact mul_le_mul_of_nonneg_left hab' (le_of_lt L₂.2)
      have h₂ : (L₂ : ℝ) * b ≤ (L₁ : ℝ) * b := by
        exact mul_le_mul_of_nonneg_right hL hb
      exact (not_lt_of_ge (le_trans h₁ h₂)) hratio'
    have hcontr :
        ((L₁ : ℝ) + (L₂ : ℝ)) * a * b <
          (L₂ : ℝ) * a ^ (2 : ℕ) + (L₁ : ℝ) * b ^ (2 : ℕ) := by
      nlinarith
    exact (not_lt_of_ge hquad') hcontr
  refine ⟨?_, ?_⟩
  · simpa [a, b] using hmono
  · -- Divide the numerator inequality by the positive product `L₁ L₂`.
    refine (div_le_div_iff₀ L₁.2 L₂.2).2 ?_
    simpa [a, b, mul_comm] using hratio_num

-- Route correction: instead of closing through an imported Chapter 10 theorem, prove the support,
-- quadratic, and scalar ratio lemmas directly for the Chapter 11 block owner and project the two
-- textbook clauses from that local owner-level result.
-- Proof sketch: use the local ratio-bounds lemma, which packages the direct Chapter 11 support
-- inequality and quadratic norm argument for the fixed block owner `G[L; ...] x i`.
/-- Theorem 11.2 (1): for a fixed block index `i`, the norm of the partial gradient mapping
`G_L^i(x)` is monotone nondecreasing in the positive parameter `L`. Thus if `L₁ ≥ L₂ > 0`, then
`‖G^i_{L₂}(x)‖ ≤ ‖G^i_{L₁}(x)‖`. -/
theorem block_partial_gradient_mapping_norm_monotone
    (L₁ L₂ : PosReal) (hL : L₂ ≤ L₁) (x : BlockSpace)
    (hblock : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0) :
    ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ ≤
      ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ :=
  by
  let _ := hblock
  -- The local ratio-bounds lemma already contains the desired monotonicity inequality.
  exact
    (block_partial_gradient_mapping_norm_ratio_bounds
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)
      hL
      x).1

-- Proof sketch: reuse the same owner-level ratio-bounds lemma and project its normalized
-- antitonicity conclusion for the fixed block owner `G[L; ...] x i`.
/-- Theorem 11.2 (2): for a fixed block index `i`, the normalized norm of the partial gradient
mapping `G_L^i(x)` is monotone nonincreasing in `L`. Thus if `L₁ ≥ L₂ > 0`, then
`‖G^i_{L₁}(x)‖ / L₁ ≤ ‖G^i_{L₂}(x)‖ / L₂`. -/
theorem block_partial_gradient_mapping_norm_div_stepsize_antitone
    (L₁ L₂ : PosReal) (hL : L₂ ≤ L₁) (x : BlockSpace)
    (hblock : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0) :
    ‖G[L₁; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ / (L₁ : ℝ) ≤
      ‖G[L₂; g, block_gradient, hg_proper, hg_closed, hg_convex] x i‖ / (L₂ : ℝ) :=
  by
  let _ := hblock
  -- The same local ratio-bounds lemma gives the normalized monotonicity directly.
  exact
    (block_partial_gradient_mapping_norm_ratio_bounds
      (hg_proper := hg_proper)
      (hg_closed := hg_closed)
      (hg_convex := hg_convex)
      (i := i)
      hL
      x).2

end

end
