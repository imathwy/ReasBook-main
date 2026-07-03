import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_11_7 (from Chap11) -/
/-
Definition 11.7 is a `bridge/view` in the Chapter 11 block proximal-gradient domain.

Domain sampling identifies the relevant declarations as follows:
- `block_partial_gradient_mapping` from Definition 11.4 is the Chapter 11 `source-facing` owner
  for the one-block residual `G_L^i(x)`;
- the notation `(G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i` is the canonical
  theorem-surface spelling of that owner;
- `block_partial_gradient_mapping_def` is the defining residual formula;
- Theorem 10.7's zero-penalty specialization is the nearby canonical pattern for collapsing a
  prox-gradient residual to an ordinary gradient when the penalty vanishes.

The primitive data are only the block penalties `g_i`, the chosen block gradient map, the
positive stepsize `L`, the base point `x`, and the block index `i`. Since the upstream Chapter 11
owner file is not part of the local proof frontier for this item, this file keeps a private
file-local owner for the one-block residual and proves only the interior-domain bridge statement
for Definition 11.7. -/

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
variable (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
variable (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
variable (hg_closed : ∀ i, LowerSemicontinuous (g i))
variable (hg_convex : ∀ i, is_convex_function (g i))

set_option quotPrecheck false in
local notation "BlockSpace" => ((j : ι) → Ei j)

/-- Helper for Definition 11.7: the one-block proximal-gradient point is the unique proximal point
of the scaled block penalty at the translated block-gradient step. -/
private def block_partial_prox_grad_point_local
    (L : PosReal) (i : ι) (x : BlockSpace) : Ei i :=
  let hscaled := scaled_function_proper_closed_convex_of_pos
    (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / L)
  Classical.choose <|
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / L : PosReal) : EReal) • g i))
      hscaled.1
      hscaled.2.1
      hscaled.2.2
      (x i - (1 / L : ℝ) • block_gradient i x)

/-- Helper for Definition 11.7: the one-block partial gradient mapping is the stepsize-scaled
residual of the ambient block point and its one-block proximal-gradient update. -/
private def block_partial_gradient_mapping_local
    (L : PosReal) (i : ι) (x : BlockSpace) : Ei i :=
  (L : ℝ) • (x i - block_partial_prox_grad_point_local g block_gradient hg_proper hg_closed
    hg_convex L i x)

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "T[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_prox_grad_point_local g block_gradient hg_proper hg_closed hg_convex L i x

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "T[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_prox_grad_point_local g block_gradient hg_proper hg_closed hg_convex L i x

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "G[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_gradient_mapping_local g block_gradient hg_proper hg_closed hg_convex L i x

set_option quotPrecheck false in
scoped[Gradient] notation3:max
    "G[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_gradient_mapping_local g block_gradient hg_proper hg_closed hg_convex L i x

/-- The one-block prox-gradient point is the unique proximal point of `(1 / L) g_i` at
`x_i - (1 / L) • block_gradient i x`. -/
theorem block_partial_prox_grad_point_eq_singleton_on_interior
    (L : PosReal) (i : ι) (x : BlockSpace) :
    prox[((((1 / L : PosReal) : EReal) • g i))]
      (x i - (1 / L : ℝ) • block_gradient i x) =
      {(T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i} := by
  let hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / L)
  -- The Chapter 11 owner `T_L^i` is defined by choosing the unique element of the corresponding
  -- scaled proximal singleton.
  simpa [block_partial_prox_grad_point_local, hscaled] using
    (Classical.choose_spec <|
      prox_eq_singleton_of_proper_closed_convex
        ((((1 / L : PosReal) : EReal) • g i))
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        (x i - (1 / L : ℝ) • block_gradient i x))

/-- Evaluating the Chapter 11 owner `G_L^i` at an interior-domain point gives the residual
`L • (x_i - T_L^i(x))`. -/
@[simp] theorem partial_gradient_mapping_apply
    (L : PosReal) (i : ι) (x : BlockSpace) :
    (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
      (L : ℝ) •
        (x i -
          (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i) := by
  rfl

/-- Helper for Definition 11.7: when the `i`th block penalty is the zero function, the scaled
proximal mapping for that block is the singleton containing the translated gradient step. -/
theorem scaled_zero_block_penalty_prox_eq_singleton
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) (x : BlockSpace) :
    prox[((((1 / L : PosReal) : EReal) • g i))]
      (x i - (1 / L : ℝ) • block_gradient i x) =
      {x i - (1 / L : ℝ) • block_gradient i x} := by
  let _ := (inferInstance : ∀ j, ProperSpace (Ei j))
  -- Rewrite the block penalty to the zero function and use the Chapter 6 zero-objective prox
  -- computation at the translated block point.
  rw [hgi_zero]
  simpa using
    (prox_zero_eq_singleton
      (x i - (1 / L : ℝ) • block_gradient i x))

/-- Helper for Definition 11.7: if the `i`th block penalty vanishes, then the Chapter 11
one-block proximal-gradient point is the translated block gradient step. -/
theorem block_partial_prox_grad_point_eq_gradient_step_of_block_penalty_eq_zero
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) (x : BlockSpace) :
    (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
      x i - (1 / L : ℝ) • block_gradient i x := by
  -- Compare the two singleton descriptions of the same proximal set: the Chapter 11 singleton
  -- owner identifies it with `{T_L^i(x)}`, while the zero-penalty specialization identifies it
  -- with the translated gradient step.
  apply Set.singleton_injective
  calc
    {(T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i} =
        prox[((((1 / L : PosReal) : EReal) • g i))]
          (x i - (1 / L : ℝ) • block_gradient i x) := by
      symm
      exact block_partial_prox_grad_point_eq_singleton_on_interior
        g block_gradient hg_proper hg_closed hg_convex L i x
    _ = {x i - (1 / L : ℝ) • block_gradient i x} := by
      exact scaled_zero_block_penalty_prox_eq_singleton
        g block_gradient L i hgi_zero x

/-- Helper for Definition 11.7: the Chapter 11 one-block residual `G_L^i(x)` collapses to the
chosen block gradient when the `i`th block penalty is zero. -/
theorem partial_gradient_mapping_apply_eq_block_gradient_of_block_penalty_eq_zero
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) (x : BlockSpace) :
    (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
      block_gradient i x := by
  have hT :
      (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
        x i - (1 / L : ℝ) • block_gradient i x := by
    exact block_partial_prox_grad_point_eq_gradient_step_of_block_penalty_eq_zero
      g block_gradient hg_proper hg_closed hg_convex L i hgi_zero x
  have hL : ((L : ℝ) * (1 / L : ℝ)) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 by exact (PosReal.coe_pos L).ne']
  -- Rewrite the residual by the explicit prox point from the previous helper, then collapse the
  -- scalar factor `L • ((1 / L) • ·)` to the identity.
  calc
    (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
        (L : ℝ) •
          (x i -
            (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i) := by
      rw [partial_gradient_mapping_apply]
    _ = (L : ℝ) • ((1 / L : ℝ) • block_gradient i x) := by
      rw [hT]
      simp
    _ = block_gradient i x := by
      rw [smul_smul, hL, one_smul]

-- Proof sketch: extensionality on `interior (effective_domain f)` reduces the statement to the
-- proximal characterization of `T_L^i`; when `g i = 0`, the proximal point is the translated
-- point itself, so the residual collapses to `block_gradient i x`.
/-- Definition 11.7: if the `i`th block penalty vanishes identically, then the `i`th partial
gradient mapping
namely `x ↦ (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i`, coincides on
`interior (effective_domain f)` with the map `x ↦ block_gradient i x`, which encodes
`x ↦ ∇_i f(x)` in the standing block setup. -/
theorem partial_gradient_mapping_eq_block_gradient_of_block_penalty_eq_zero
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) :
    (fun x : interior (effective_domain f) ↦
      (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) (x : BlockSpace) i) =
      fun x : interior (effective_domain f) ↦ block_gradient i (x : BlockSpace) := by
  -- Function extensionality reduces the statement to the pointwise residual collapse proved
  -- above.
  funext x
  simpa using partial_gradient_mapping_apply_eq_block_gradient_of_block_penalty_eq_zero
    g block_gradient hg_proper hg_closed hg_convex L i hgi_zero (x : BlockSpace)

end

/-! ### Lemma_11_7 (from Chap11) -/
noncomputable section

section

/- `prompt_add/` is absent in this workspace, so the owner-abstraction review is done against
mathlib and nearby project files. Domain sampling against the closest project recurrences,
`Chap10/Lemma_10_70`, `Chap13/Lemma_13_13`, and the chapter-wide positive-parameter owner
`PosReal` from `Chap06/Definition_6_7` shows the intended split:
- the public source-facing owner remains the plain sequence `a : ℕ → ℝ`;
- the step inequality remains theorem-level input rather than being packaged into a wrapper; and
- genuinely positive scalar data such as the recurrence constant belongs in `PosReal`, not in a
  raw real parameter plus a separate positivity proof.
This item is therefore kept `source-facing`, with the two independent conclusions split into
atomic lemmas. -/

variable {a : ℕ → ℝ} {γ : PosReal}

variable (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
variable (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)

/-- Helper for Lemma 11.7: the number of halving steps among the first `m` transitions. -/
abbrev halvingCount (a : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k ↦ a (k + 1) ≤ a k / 2).card

/-- Helper for Lemma 11.7: the number of strict-half-ratio steps among the first `m`
transitions. -/
abbrev strictHalfRatioCount (a : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k ↦ a k / 2 < a (k + 1)).card

/-- Helper for Lemma 11.7: the quadratic recurrence makes the sequence antitone. -/
lemma quadratic_step_recurrence_antitone
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2) :
    Antitone a := by
  -- Each step decreases because the quadratic term in the recurrence is nonnegative.
  have hsucc : ∀ k : ℕ, a (k + 1) ≤ a k := by
    intro k
    have hsq_nonneg : 0 ≤ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ) := by
      exact mul_nonneg (one_div_nonneg.mpr (PosReal.coe_pos γ).le) (sq_nonneg (a (k + 1)))
    linarith [hstep k]
  exact antitone_nat_of_succ_le hsucc

/-- Helper for Lemma 11.7: the halving-step count gains one exactly when the latest step halves. -/
private lemma halvingCount_succ (m : ℕ) :
    halvingCount a (m + 1) =
      halvingCount a m + if a (m + 1) ≤ a m / 2 then 1 else 0 := by
  classical
  by_cases hm : a (m + 1) ≤ a m / 2
  · rw [halvingCount, halvingCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]
  · rw [halvingCount, halvingCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]

/-- Helper for Lemma 11.7: the strict-half-ratio count gains one exactly when the latest step is
strictly above the half ratio. -/
private lemma strictHalfRatioCount_succ (m : ℕ) :
    strictHalfRatioCount a (m + 1) =
      strictHalfRatioCount a m + if a m / 2 < a (m + 1) then 1 else 0 := by
  classical
  by_cases hm : a m / 2 < a (m + 1)
  · rw [strictHalfRatioCount, strictHalfRatioCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]
  · rw [strictHalfRatioCount, strictHalfRatioCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]

/-- Helper for Lemma 11.7: each prefix step is either a halving step or a strict-half-ratio
step, so the two counts partition the prefix. -/
private lemma halvingCount_add_strictHalfRatioCount_eq (m : ℕ) :
    halvingCount a m + strictHalfRatioCount a m = m := by
  classical
  -- The two predicates are exact complements on `ℝ`.
  simpa [halvingCount, strictHalfRatioCount, not_le] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range m) (p := fun k ↦ a (k + 1) ≤ a k / 2))

/-- Helper for Lemma 11.7: a strict-half-ratio step yields a uniform reciprocal increment. -/
lemma reciprocal_increment_ge_one_div_two_gamma_of_strict_half_ratio
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)
    (k : ℕ)
    (hak : 0 < a k)
    (hak_succ : 0 < a (k + 1))
    (hhalf : a k / 2 < a (k + 1)) :
    1 / (2 * (γ : ℝ)) ≤ 1 / a (k + 1) - 1 / a k := by
  have hγ_ne : (γ : ℝ) ≠ 0 := (PosReal.coe_pos γ).ne'
  have hrecip :
      1 / a (k + 1) - 1 / a k = (a k - a (k + 1)) / (a k * a (k + 1)) := by
    field_simp [hak.ne', hak_succ.ne']
  rw [hrecip]
  -- Divide the quadratic decrease inequality by the positive denominator.
  have hden_pos : 0 < a k * a (k + 1) := mul_pos hak hak_succ
  have hstep_div :
      ((1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) / (a k * a (k + 1)) ≤
        (a k - a (k + 1)) / (a k * a (k + 1)) := by
    exact div_le_div_of_nonneg_right (hstep k) (le_of_lt hden_pos)
  have hsimpl :
      ((1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) / (a k * a (k + 1)) =
        (1 / (γ : ℝ)) * (a (k + 1) / a k) := by
    field_simp [hak.ne', hak_succ.ne', hγ_ne]
  rw [hsimpl] at hstep_div
  have hratio : (1 / 2 : ℝ) < a (k + 1) / a k := by
    have hhalf' : (1 / 2 : ℝ) * a k < a (k + 1) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hhalf
    rw [lt_div_iff₀ hak]
    exact hhalf'
  have hleft :
      1 / (2 * (γ : ℝ)) = (1 / (γ : ℝ)) * (1 / 2 : ℝ) := by
    field_simp [hγ_ne]
  have hratio_mul :
      (1 / (γ : ℝ)) * (1 / 2 : ℝ) ≤ (1 / (γ : ℝ)) * (a (k + 1) / a k) := by
    exact mul_le_mul_of_nonneg_left hratio.le (one_div_nonneg.mpr (PosReal.coe_pos γ).le)
  calc
    1 / (2 * (γ : ℝ)) = (1 / (γ : ℝ)) * (1 / 2 : ℝ) := hleft
    _ ≤ (1 / (γ : ℝ)) * (a (k + 1) / a k) := hratio_mul
    _ ≤ (a k - a (k + 1)) / (a k * a (k + 1)) := hstep_div

/-- Helper for Lemma 11.7: every halving step contributes one factor `1 / 2` to the prefix
bound. -/
lemma geometric_prefix_bound_of_halving_count
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)
    (m : ℕ) :
    a m ≤ ((1 / 2 : ℝ) ^ halvingCount a m) * a 0 := by
  -- Induct on the prefix length and record whether the last step halves.
  induction m with
  | zero =>
      simp [halvingCount]
  | succ m ih =>
      have ha_anti := quadratic_step_recurrence_antitone (a := a) (γ := γ) hstep
      have hcount := halvingCount_succ (a := a) (m := m)
      by_cases hhalf : a (m + 1) ≤ a m / 2
      · -- A halving step adds one more factor `1 / 2`.
        rw [hcount, if_pos hhalf]
        calc
          a (m + 1) ≤ a m / 2 := hhalf
          _ ≤ (((1 / 2 : ℝ) ^ halvingCount a m) * a 0) / 2 := by
            exact div_le_div_of_nonneg_right ih (by norm_num)
          _ = ((1 / 2 : ℝ) ^ (halvingCount a m + 1)) * a 0 := by
            rw [div_eq_mul_inv, show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, pow_succ]
            ring
      · -- Otherwise the halving count is unchanged, and monotonicity controls the last step.
        rw [hcount, if_neg hhalf]
        calc
          a (m + 1) ≤ a m := ha_anti (Nat.le_succ m)
          _ ≤ ((1 / 2 : ℝ) ^ halvingCount a m) * a 0 := ih

/-- Helper for Lemma 11.7: every strict-half-ratio step contributes one reciprocal increment of
size at least `1 / (2γ)`. -/
lemma reciprocal_prefix_bound_of_strict_half_ratio_count
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)
    (m : ℕ) (hm_pos : 0 < a m) :
    (strictHalfRatioCount a m : ℝ) / (2 * (γ : ℝ)) ≤ 1 / a m - 1 / a 0 := by
  -- Induct on the prefix length and split according to the final step of the dichotomy.
  induction m with
  | zero =>
      simp [strictHalfRatioCount]
  | succ m ih =>
      have ha_anti := quadratic_step_recurrence_antitone (a := a) (γ := γ) hstep
      have hcount := strictHalfRatioCount_succ (a := a) (m := m)
      have hm_prev_pos : 0 < a m := lt_of_lt_of_le hm_pos (ha_anti (Nat.le_succ m))
      by_cases hstrict : a m / 2 < a (m + 1)
      · -- A strict-half-ratio step adds one more reciprocal increment.
        have hprefix := ih hm_prev_pos
        have hinc :=
          reciprocal_increment_ge_one_div_two_gamma_of_strict_half_ratio
            (a := a) (γ := γ) hstep m hm_prev_pos hm_pos hstrict
        rw [hcount, if_pos hstrict]
        have hcast :
            ((strictHalfRatioCount a m + 1 : ℕ) : ℝ) / (2 * (γ : ℝ)) =
              (strictHalfRatioCount a m : ℝ) / (2 * (γ : ℝ)) + 1 / (2 * (γ : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_one, add_div]
        rw [hcast]
        linarith
      · -- Without a strict-half-ratio step, the count stays fixed and reciprocals still increase.
        rw [hcount, if_neg hstrict]
        have hprefix := ih hm_prev_pos
        have hrecip_mono : 1 / a m ≤ 1 / a (m + 1) := by
          exact one_div_le_one_div_of_le hm_pos (ha_anti (Nat.le_succ m))
        have htarget : 1 / a m - 1 / a 0 ≤ 1 / a (m + 1) - 1 / a 0 := by
          linarith
        exact le_trans hprefix htarget

/-- Helper for Lemma 11.7: if the halving and strict-half-ratio counts partition a prefix, then at
least one of the two counts is at least half of the prefix length. -/
private lemma half_count_dichotomy_of_partition {h r m : ℕ} (hsum : h + r = m) :
    ((m : ℝ) / 2 ≤ h) ∨ ((m : ℝ) / 2 ≤ r) := by
  -- Cast the exact partition identity to `ℝ` and split by whether the first count already
  -- reaches half of the prefix length.
  have hsum_real : (h : ℝ) + r = m := by
    exact_mod_cast hsum
  by_cases hh : ((m : ℝ) / 2 ≤ h)
  · exact Or.inl hh
  · right
    linarith

/-- Helper for Lemma 11.7: once at least half of the first `m` steps are halving steps, the
geometric prefix bound is at most the textbook target `((1 / 2) ^ (m / 2)) * a0`. -/
private lemma geometric_branch_le_target_of_halving_count
    {a0 : ℝ} (ha0 : 0 ≤ a0) {h m : ℕ}
    (hhalf : ((m : ℝ) / 2 ≤ h)) :
    ((1 / 2 : ℝ) ^ h) * a0 ≤ ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 := by
  -- Since `0 < 1 / 2 < 1`, increasing the exponent only decreases the real power.
  have hpow :
      ((1 / 2 : ℝ) ^ h) ≤ (1 / 2 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) h]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hhalf
  exact mul_le_mul_of_nonneg_right hpow ha0

/-- Helper for Lemma 11.7: once at least half of the first `m` steps are strict-half-ratio steps,
the reciprocal prefix bound inverts to the textbook sublinear target `4γ / m`. -/
private lemma sublinear_branch_le_target_of_strict_half_ratio_count
    {x : ℝ} (hx : 0 < x) {r m : ℕ} (hm : 1 ≤ m)
    (hhalf : ((m : ℝ) / 2 ≤ r))
    (hrecip : (r : ℝ) / (2 * (γ : ℝ)) ≤ 1 / x) :
    x ≤ 4 * (γ : ℝ) / (m : ℝ) := by
  -- First convert the count lower bound into the linear estimate `m ≤ 2r`.
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hm)
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hγ_pos : 0 < (γ : ℝ) := PosReal.coe_pos γ
  have htwoγ_pos : 0 < 2 * (γ : ℝ) := by positivity
  have hm_le_two_r : (m : ℝ) ≤ 2 * (r : ℝ) := by
    linarith
  -- Next clear the reciprocal inequality to obtain a direct bound on `r * x`.
  have hr_le_div : (r : ℝ) ≤ (2 * (γ : ℝ)) / x := by
    have hdiv := (div_le_iff₀ htwoγ_pos).mp hrecip
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hrx_le : (r : ℝ) * x ≤ 2 * (γ : ℝ) := by
    calc
      (r : ℝ) * x ≤ ((2 * (γ : ℝ)) / x) * x := by
        exact mul_le_mul_of_nonneg_right hr_le_div hx_nonneg
      _ = 2 * (γ : ℝ) := by
        field_simp [hx.ne']
  -- Finally combine `m ≤ 2r` with the estimate on `r * x` and divide by the positive `m`.
  have hmx_le : (m : ℝ) * x ≤ 4 * (γ : ℝ) := by
    calc
      (m : ℝ) * x ≤ (2 * (r : ℝ)) * x := by
        exact mul_le_mul_of_nonneg_right hm_le_two_r hx_nonneg
      _ = 2 * ((r : ℝ) * x) := by ring
      _ ≤ 2 * (2 * (γ : ℝ)) := by gcongr
      _ = 4 * (γ : ℝ) := by ring
  exact (le_div_iff₀ hm_real_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmx_le)

/-- Helper for Lemma 11.7: the logarithmic lower bound on the iteration count forces the
geometric term below `ε`. -/
lemma geometric_term_le_epsilon_of_log_bound
    {a0 : ℝ} (ha0 : 0 < a0) (ε : PosReal) {m : ℕ}
    (hlog :
      (2 / Real.log 2) * (Real.log a0 + Real.log (1 / (ε : ℝ))) ≤ (m : ℝ)) :
    ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 ≤ ε := by
  -- Convert the threshold into a bound on the logarithm of `a0 * (1 / ε)`.
  have hε_pos : 0 < (ε : ℝ) := PosReal.coe_pos ε
  have hlog2_pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  have hscaled :
      Real.log a0 + Real.log (1 / (ε : ℝ)) ≤ ((m : ℝ) / 2) * Real.log 2 := by
    have hquot :
        (2 * (Real.log a0 + Real.log (1 / (ε : ℝ)))) / Real.log 2 ≤ (m : ℝ) := by
      have hrewrite :
          (2 / Real.log 2) * (Real.log a0 + Real.log (1 / (ε : ℝ))) =
            (2 * (Real.log a0 + Real.log (1 / (ε : ℝ)))) / Real.log 2 := by
        ring
      rw [hrewrite] at hlog
      exact hlog
    have hmul :
        2 * (Real.log a0 + Real.log (1 / (ε : ℝ))) ≤ (m : ℝ) * Real.log 2 := by
      exact (div_le_iff₀ hlog2_pos).mp hquot
    calc
      Real.log a0 + Real.log (1 / (ε : ℝ)) =
          (2 * (Real.log a0 + Real.log (1 / (ε : ℝ)))) / 2 := by
        ring
      _ ≤ ((m : ℝ) * Real.log 2) / 2 := by
        exact div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((m : ℝ) / 2) * Real.log 2 := by
        ring
  -- Compare the logarithms of the concrete quantities appearing in the target inequality.
  have hlog_compare :
      Real.log (a0 * (1 / (ε : ℝ))) ≤ Real.log ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
    rw [show Real.log (a0 * (1 / (ε : ℝ))) = Real.log (a0 * ((ε : ℝ)⁻¹)) by simp [one_div]]
    rw [Real.log_mul ha0.ne' (inv_ne_zero ε.2.ne')]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    simpa [one_div] using hscaled
  have hmul_le :
      a0 * (1 / (ε : ℝ)) ≤ (2 : ℝ) ^ ((m : ℝ) / 2) := by
    exact (Real.log_le_log_iff (mul_pos ha0 (one_div_pos.mpr hε_pos))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mp hlog_compare
  -- Rewrite the target as a division by `2 ^ (m / 2)` and divide the previous inequality.
  have hpow_pos : 0 < (2 : ℝ) ^ ((m : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hbound :
      a0 / ((2 : ℝ) ^ ((m : ℝ) / 2)) ≤ ε := by
    have hmul_eps : a0 ≤ ε * ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
      calc
        a0 = (a0 * (1 / (ε : ℝ))) * ε := by
          field_simp [hε_pos.ne']
        _ ≤ ((2 : ℝ) ^ ((m : ℝ) / 2)) * ε := by
          gcongr
        _ = ε * ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
          ring
    exact (div_le_iff₀ hpow_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_eps)
  have hhalf :
      (1 / 2 : ℝ) ^ ((m : ℝ) / 2) = ((2 : ℝ) ^ ((m : ℝ) / 2))⁻¹ := by
    rw [show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 = a0 / ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
      rw [hhalf]
      ring
    _ ≤ ε := hbound

-- Proof sketch: follow the textbook dichotomy on each ratio `a (k + 1) / a k`. Either
-- `a (k + 1) ≤ a k / 2`, which contributes one geometric halving step, or
-- `a (k + 1) / a k > 1 / 2`, in which case dividing the recurrence by `a k * a (k + 1)` gives a
-- uniform increment lower bound for `1 / a (k + 1) - 1 / a k`. Counting how many times each case
-- occurs among the first `n - 1` indices yields the maximum of the geometric and sublinear bounds.
include ha_nonneg hstep

/-- Lemma 11.7 (1): if a nonnegative scalar sequence satisfies
`a k - a (k + 1) ≥ (1 / γ) * a (k + 1)^2` for every `k` and some positive `γ`, then for every
`n ≥ 2` one has
`a n ≤ max {((1 / 2)^((n - 1) / 2)) * a 0, 4γ / (n - 1)}`. -/
lemma nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
    {n : ℕ} (hn : 2 ≤ n) :
    a n ≤
      max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
        (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
  -- Route correction: keep the count-partition proof skeleton and isolate the cast-heavy closing
  -- steps into the dedicated branch lemmas above.
  by_cases han_zero : a n = 0
  · -- If the terminal value vanishes, the bound is immediate from the nonnegative sublinear term.
    have hm_nat : 1 ≤ n - 1 := by
      omega
    have hm_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hm_nat
    have hsub_nonneg : 0 ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      exact div_nonneg (mul_nonneg (by norm_num) (PosReal.coe_pos γ).le) hm_pos.le
    rw [han_zero]
    exact le_trans (by norm_num) (le_trans hsub_nonneg (le_max_right _ _))
  · -- Otherwise `a n > 0`, so the reciprocal branch can be evaluated at the prefix `n - 1`.
    have ha_anti := quadratic_step_recurrence_antitone (a := a) (γ := γ) hstep
    have han_pos : 0 < a n := lt_of_le_of_ne (ha_nonneg n) (Ne.symm han_zero)
    have hprev_pos : 0 < a (n - 1) := by
      exact lt_of_lt_of_le han_pos (ha_anti (Nat.sub_le n 1))
    have hprefix_mono : a n ≤ a (n - 1) := ha_anti (Nat.sub_le n 1)
    have hpartition :
        halvingCount a (n - 1) + strictHalfRatioCount a (n - 1) = n - 1 :=
      halvingCount_add_strictHalfRatioCount_eq (a := a) (m := n - 1)
    have hcount_split :
        ((((n - 1 : ℕ) : ℝ) / 2) ≤ halvingCount a (n - 1)) ∨
          ((((n - 1 : ℕ) : ℝ) / 2) ≤ strictHalfRatioCount a (n - 1)) :=
      half_count_dichotomy_of_partition
        (h := halvingCount a (n - 1))
        (r := strictHalfRatioCount a (n - 1))
        (m := n - 1) hpartition
    cases hcount_split with
    | inl hhalf =>
        -- Many halving steps immediately give the geometric target.
        have hgeo_prefix :
            a (n - 1) ≤ ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 :=
          geometric_prefix_bound_of_halving_count
            (a := a) (γ := γ) hstep (m := n - 1)
        have hgeo_target :
            ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 ≤
              ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 :=
          geometric_branch_le_target_of_halving_count
            (a0 := a 0) (ha0 := ha_nonneg 0) hhalf
        calc
          a n ≤ a (n - 1) := hprefix_mono
          _ ≤ ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 := hgeo_prefix
          _ ≤ ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 := hgeo_target
          _ ≤
              max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
                (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := le_max_left _ _
    | inr hstrict =>
        -- Otherwise at least half of the steps are strict-half-ratio steps, so reciprocals grow
        -- linearly and invert to the sublinear target.
        have hm : 1 ≤ n - 1 := by
          omega
        have hrecip_prefix :
            (strictHalfRatioCount a (n - 1) : ℝ) / (2 * (γ : ℝ)) ≤
              1 / a (n - 1) - 1 / a 0 :=
          reciprocal_prefix_bound_of_strict_half_ratio_count
            (a := a) (γ := γ) hstep (m := n - 1) hprev_pos
        have hrecip :
            (strictHalfRatioCount a (n - 1) : ℝ) / (2 * (γ : ℝ)) ≤ 1 / a (n - 1) := by
          have hrecip0_nonneg : 0 ≤ 1 / a 0 := one_div_nonneg.mpr (ha_nonneg 0)
          linarith
        have hsub_target :
            a (n - 1) ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) :=
          sublinear_branch_le_target_of_strict_half_ratio_count
            (γ := γ) (x := a (n - 1)) hprev_pos hm hstrict hrecip
        calc
          a n ≤ a (n - 1) := hprefix_mono
          _ ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) := hsub_target
          _ ≤
              max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
                (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := le_max_right _ _

-- Proof sketch: apply part (1) at the given index `n`, then force each of the two terms in the
-- maximum to be at most `ε`. The geometric term is controlled by rearranging
-- `((1 / 2)^((n - 1) / 2)) * a 0 ≤ ε` into the logarithmic lower bound on `n`, while the
-- sublinear term is controlled by `4γ / ε ≤ n - 1`.
/-- Lemma 11.7 (2): if `ε > 0` and
`n ≥ max {(2 / log 2) * (log (a 0) + log (1 / ε)), 4γ / ε} + 1`,
then the same recurrence implies `a n ≤ ε`. -/
lemma nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence
    (ε : PosReal)
    {n : ℕ}
    (hn :
      max
          ((2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) +
        1 ≤
        (n : ℝ)) :
    a n ≤ ε := by
  -- First extract the natural-number lower bound needed for part (1).
  have hthreshold_pos : 0 < 4 * (γ : ℝ) / (ε : ℝ) := by
    exact div_pos (mul_pos (by norm_num) (PosReal.coe_pos γ)) (PosReal.coe_pos ε)
  have hone_lt_n : (1 : ℝ) < n := by
    have hmax_pos :
        0 < max
            ((2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))))
            (4 * (γ : ℝ) / (ε : ℝ)) := by
      exact lt_of_lt_of_le hthreshold_pos (le_max_right _ _)
    linarith
  have hn_nat_lt : (1 : ℕ) < n := by
    exact_mod_cast hone_lt_n
  have hn_nat : 2 ≤ n := Nat.succ_le_of_lt hn_nat_lt
  -- Apply the first part and reduce the `max` bound termwise to `ε`.
  have hmain :=
    nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := a) (γ := γ) ha_nonneg hstep hn_nat
  have hmax_le :
      max
          ((2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) ≤
        (n : ℝ) - 1 := by
    linarith
  have hgeom_threshold :
      (2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))) ≤
        (((n - 1 : ℕ) : ℝ)) := by
    have hgeom_to_sub : (2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))) ≤
        (n : ℝ) - 1 := by
      exact le_trans (le_max_left _ _) hmax_le
    have hcast_sub : (n : ℝ) - 1 = (((n - 1 : ℕ) : ℝ)) := by
      have h1 : 1 ≤ n := by omega
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_sub h1]
    rw [hcast_sub] at hgeom_to_sub
    exact hgeom_to_sub
  have hsub_threshold :
      4 * (γ : ℝ) / (ε : ℝ) ≤ (((n - 1 : ℕ) : ℝ)) := by
    have hsub_to_sub : 4 * (γ : ℝ) / (ε : ℝ) ≤ (n : ℝ) - 1 := by
      exact le_trans (le_max_right _ _) hmax_le
    have hcast_sub : (n : ℝ) - 1 = (((n - 1 : ℕ) : ℝ)) := by
      have h1 : 1 ≤ n := by omega
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_sub h1]
    rw [hcast_sub] at hsub_to_sub
    exact hsub_to_sub
  have hgeom_le_eps :
      ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 ≤ ε := by
    by_cases ha0_zero : a 0 = 0
    · simpa [ha0_zero] using (show (0 : ℝ) ≤ ε by exact (PosReal.coe_pos ε).le)
    · have ha0_pos : 0 < a 0 := lt_of_le_of_ne (ha_nonneg 0) (Ne.symm ha0_zero)
      exact geometric_term_le_epsilon_of_log_bound
        (a0 := a 0) ha0_pos ε hgeom_threshold
  have hsub_le_eps :
      4 * (γ : ℝ) / (((n - 1 : ℕ) : ℝ)) ≤ ε := by
    have hm_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
      have hm_nat : 1 ≤ n - 1 := by
        omega
      exact_mod_cast hm_nat
    have hmul :
        4 * (γ : ℝ) ≤ ε * (((n - 1 : ℕ) : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ (PosReal.coe_pos ε)).mp hsub_threshold
    exact (div_le_iff₀ hm_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hmax_target :
      max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
        (4 * (γ : ℝ) / (((n - 1 : ℕ) : ℝ))) ≤ ε := by
    exact max_le hgeom_le_eps hsub_le_eps
  exact le_trans hmain hmax_target

end

/-! ### Theorem_11_7 (from Chap11) -/
noncomputable section

universe v

open Metric

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, CompleteSpace (Ei i)] [∀ i, ProperSpace (Ei i)]
variable [Nonempty (Fin p)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/-- Helper for Theorem 11.7: the Chapter 11 quadratic-gap coefficient
`L_min / (2 p (L_f + L_max)^2 R^2)`. -/
private def cbpg_quadratic_gap_constant
    (Lf : NNReal) (Li : (i : Fin p) → PosReal) (R : PosReal) : ℝ :=
  (cbpg_min_block_stepsize Li : ℝ) /
    (2 * (p : ℝ) * (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) *
      ((R : ℝ) ^ (2 : ℕ)))

/- Theorem 11.7 is `source-facing`: it gives the convex CBPG objective-gap rate. The owner
abstractions already live upstream:
- `CyclicBlockProximalGradientConvexAssumptions` is the Chapter 11 source-facing problem owner;
- `cyclic_block_proximal_gradient_method` is the owner of the CBPG outer iterates;
- `cbpg_quadratic_gap_constant` is the canonical Chapter 11 coefficient
  `L_min / (2 p (L_f + L_max)^2 R_α^2)`;
- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence` and
  `nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence` are the scalar recurrence owners
  from Lemma 11.7.

Primitive data are therefore only the convex CBPG assumptions and the canonical initial datum
`x0 ∈ effective_domain (separableSum g)`. The objective gap is derived API, and the passage from
the CBPG step estimate to the scalar recurrence is a `bridge/view`, not a second wrapper owner. -/

section

variable
  (hconvex : CyclicBlockProximalGradientConvexAssumptions
    f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "hproblem" =>
  hconvex.toBlockProximalGradientAssumptions
local notation "x0I" =>
  hconvex.interior_effective_domain_point x0
set_option quotPrecheck false in
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0I k
set_option quotPrecheck false in
local notation "x[" k "," i "]" =>
  cyclic_block_proximal_gradient_inner_iterate hproblem x[k] i
local notation "F" =>
  composite_model_objective f (separableSum g)
set_option quotPrecheck false in
local notation "Δ[" k "]" => (F x[k]).toReal - FOpt
set_option quotPrecheck false in
local notation "RadiusBound" =>
  fun Rα : PosReal ↦
    ∀ ⦃x⦄,
      F x ≤ F x[0] →
      infDist x XStar ≤ Rα
set_option quotPrecheck false in
local notation "GapBound[" Rα "," k "]" =>
  max
    (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * Δ[0])
    (4 / (cbpg_quadratic_gap_constant Lf Li Rα * ((k - 1 : ℕ) : ℝ)))
set_option quotPrecheck false in
local notation "IterationThreshold[" Rα "," ε "]" =>
  max
      ((2 / Real.log 2) *
        (Real.log (Δ[0]) + Real.log (1 / (ε : ℝ))))
      (4 / (cbpg_quadratic_gap_constant Lf Li Rα * (ε : ℝ))) +
    1

/-- Helper for Theorem 11.7: every auxiliary iterate `x^{k,m}` with `m ≤ p` remains in the
effective domain of the block-separable regularizer. -/
lemma cbpg_inner_stage_mem_effective_domain
    (k : ℕ) (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  simpa using
    cbpg_auxiliary_iterate_mem_effective_domain
      (hconvex.toBlockProximalGradientAssumptions) x0 k m hm

/-- Helper for Theorem 11.7: every outer CBPG iterate remains in the effective domain of the
block-separable regularizer. -/
lemma cbpg_outer_iterate_mem_effective_domain
    (k : ℕ) :
    x[k] ∈ effective_domain (separableSum g) := by
  simpa using
    cbpg_inner_stage_mem_effective_domain
      (hconvex := hconvex) (x0 := x0) k 0 (Nat.zero_le p)

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite. -/
lemma cbpg_objective_value_finite
    (k : ℕ) :
    F x[k] ≠ ⊤ ∧ F x[k] ≠ ⊥ := by
  have hxg : x[k] ∈ effective_domain (separableSum g) :=
    cbpg_outer_iterate_mem_effective_domain (hconvex := hconvex) (x0 := x0) k
  have hxf : x[k] ∈ effective_domain f := by
    -- The regularizer domain lies in `interior (effective_domain f)`, hence `f` is finite there.
    let hbase := hconvex.toBlockProximalGradientAssumptions
    exact interior_subset (hbase.g_effective_domain_subset_interior_f_effective_domain hxg)
  have hf_top : f x[k] ≠ ⊤ := (mem_effective_domain.mp hxf).ne
  have hg_top : separableSum g x[k] ≠ ⊤ := (mem_effective_domain.mp hxg).ne
  have hf_bot : f x[k] ≠ ⊥ :=
    hconvex.toBlockProximalGradientAssumptions.f_ne_bot (x[k])
  have hg_bot : separableSum g x[k] ≠ ⊥ := by
    -- Proper block penalties keep the separable sum away from `-∞`.
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ
      (fun i ↦ g i (x[k] i))
      (fun i _ ↦ (hconvex.toBlockProximalGradientAssumptions.block_g_proper i).ne_bot _)
  constructor
  · simpa [composite_model_objective] using EReal.add_ne_top hf_top hg_top
  · simpa [composite_model_objective] using EReal.add_ne_bot_iff.mpr ⟨hf_bot, hg_bot⟩

/-- Helper for Theorem 11.7: the quadratic CBPG gap coefficient is positive for every positive
radius parameter. -/
lemma cbpg_quadratic_gap_constant_pos
    (Rα : PosReal) :
    0 < cbpg_quadratic_gap_constant Lf Li Rα := by
  have hp_nat : 0 < p := by
    simpa using Fintype.card_pos_iff.mpr ‹Nonempty (Fin p)›
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast hp_nat
  have hsum : 0 < (Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ) := by
    exact add_pos_of_nonneg_of_pos (show 0 ≤ (Lf : ℝ) by exact_mod_cast Lf.2)
      (PosReal.coe_pos (cbpg_max_block_stepsize Li))
  have hsum_sq : 0 < (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) := by
    nlinarith [hsum]
  have hR_sq : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    rw [pow_two]
    exact mul_pos (PosReal.coe_pos Rα) (PosReal.coe_pos Rα)
  have htwo_p : 0 < 2 * (p : ℝ) := by positivity
  have hden :
      0 <
        2 * (p : ℝ) *
          (((Lf : ℝ) + (cbpg_max_block_stepsize Li : ℝ)) ^ (2 : ℕ)) *
          ((Rα : ℝ) ^ (2 : ℕ)) := by
    exact mul_pos (mul_pos htwo_p hsum_sq) hR_sq
  dsimp [cbpg_quadratic_gap_constant]
  exact div_pos (PosReal.coe_pos (cbpg_min_block_stepsize Li)) hden

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite from
above. -/
lemma cbpg_objective_value_ne_top
    (k : ℕ) :
    F x[k] ≠ ⊤ := by
  exact (cbpg_objective_value_finite (hconvex := hconvex) (x0 := x0) k).1

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite from
below. -/
lemma cbpg_objective_value_ne_bot
    (k : ℕ) :
    F x[k] ≠ ⊥ := by
  exact (cbpg_objective_value_finite (hconvex := hconvex) (x0 := x0) k).2

/-- Helper for Theorem 11.7: the CBPG objective gap sequence is nonnegative. -/
lemma cbpg_objective_gap_nonneg
    (k : ℕ) :
    0 ≤ Δ[k] := by
  have hlower : (FOpt : EReal) ≤ F x[k] :=
    hconvex.optimal_value_isGLB.1 ⟨x[k], rfl⟩
  have htop := cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) k
  have hbot := cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) k
  lift (F x[k]) to ℝ using ⟨htop, hbot⟩ with rk
  norm_num at hlower ⊢
  linarith

/-- Helper for Theorem 11.7: once the two consecutive objective values are known to be finite,
their EReal difference is the coercion of the corresponding real difference. -/
lemma cbpg_objective_step_decrease_real_form
    (k : ℕ) :
    F x[k] - F x[k + 1] =
      ((((F x[k]).toReal - (F x[k + 1]).toReal : ℝ)) : EReal) := by
  -- Rewrite both finite objective values as real coercions before using `EReal.coe_sub`.
  have hxk_val :
      F x[k] = (((F x[k]).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) k)
        (cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) k)).symm
  have hxk1_val :
      F x[k + 1] = (((F x[k + 1]).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) (k + 1))
        (cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) (k + 1))).symm
  -- After the coercion rewrite, the EReal subtraction reduces to the real subtraction.
  rw [hxk_val, hxk1_val]
  simp [EReal.coe_sub]

/-- Helper for Theorem 11.7: subtracting two consecutive gaps cancels the common optimal-value
offset and leaves the real difference of the corresponding objective values. -/
lemma cbpg_objective_gap_difference_eq_toReal_difference
    (k : ℕ) :
    Δ[k] - Δ[k + 1] =
      (F x[k]).toReal - (F x[k + 1]).toReal := by
  -- Expand the gap definition and cancel the common `FOpt` term.
  calc
    Δ[k] - Δ[k + 1]
        = ((F x[k]).toReal - FOpt) - ((F x[k + 1]).toReal - FOpt) := by
          rfl
    _ = (F x[k]).toReal - (F x[k + 1]).toReal := by
          ring

/-- Helper for Theorem 11.7: the one-step CBPG decrease estimate induces the scalar quadratic
recurrence for the objective-gap sequence. -/
lemma cbpg_objective_gap_step_recurrence
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) :
    Δ[k] - Δ[k + 1] ≥
      cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := by
  -- Route correction: keep the source-faithful plan fixed. The only missing piece is the earlier
  -- Lemma 11.6 owner; the cast-down and cancellation steps are now factored out and verified here.
  -- Convert the one-step EReal decrease estimate from Lemma 11.6 into an inequality in `ℝ`.
  have hstepE :
      (((cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) : ℝ) : EReal)) ≤
        F x[k] - F x[k + 1] := sorry
  have hstep_realE :
      (((cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) : ℝ) : EReal)) ≤
        ((((F x[k]).toReal - (F x[k + 1]).toReal : ℝ)) : EReal) := by
    simpa [cbpg_objective_step_decrease_real_form
      (hconvex := hconvex) (x0 := x0) k] using hstepE
  have hstep_real :
      (F x[k]).toReal - (F x[k + 1]).toReal ≥
        cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := by
    simpa [ge_iff_le] using EReal.coe_le_coe_iff.mp hstep_realE
  -- Cancel the common optimal-value offset in the consecutive gap difference.
  calc
    Δ[k] - Δ[k + 1]
        = (F x[k]).toReal - (F x[k + 1]).toReal := by
          simpa using
            cbpg_objective_gap_difference_eq_toReal_difference
              (hconvex := hconvex) (x0 := x0) k
    _ ≥ cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := hstep_real

/-- Helper for Theorem 11.7: the convex CBPG assumptions supply a radius controlling the initial
sublevel set through the distance-to-`XStar` formulation used in Lemma 11.6. -/
lemma cbpg_exists_initial_sublevel_radius :
    ∃ Rα : PosReal, RadiusBound Rα := by
  have hx0f : (x0 : (i : Fin p) → Ei i) ∈ effective_domain f := by
    let hbase := hconvex.toBlockProximalGradientAssumptions
    exact interior_subset (hbase.g_effective_domain_subset_interior_f_effective_domain x0.2)
  have hf_top : f x0 ≠ ⊤ := (mem_effective_domain.mp hx0f).ne
  have hg_top : separableSum g x0 ≠ ⊤ := (mem_effective_domain.mp x0.2).ne
  have hf_bot : f x0 ≠ ⊥ := hconvex.toBlockProximalGradientAssumptions.f_ne_bot x0
  have hg_bot : separableSum g x0 ≠ ⊥ := by
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ
      (fun i ↦ g i ((x0 : (i : Fin p) → Ei i) i))
      (fun i _ ↦ (hconvex.toBlockProximalGradientAssumptions.block_g_proper i).ne_bot _)
  have hF_top : F x0 ≠ ⊤ := by
    simpa [composite_model_objective] using EReal.add_ne_top hf_top hg_top
  have hF_bot : F x0 ≠ ⊥ := by
    simpa [composite_model_objective] using EReal.add_ne_bot_iff.mpr ⟨hf_bot, hg_bot⟩
  have hF_val : F x0 = (((F x0).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hF_top hF_bot).symm
  have hα_pos : 0 < |(F x0).toReal| + 1 := by
    positivity
  let α : PosReal := ⟨|(F x0).toReal| + 1, hα_pos⟩
  have hα : F x0 ≤ ((α : ℝ) : EReal) := by
    have hle : (F x0).toReal ≤ |(F x0).toReal| + 1 := by
      nlinarith [le_abs_self (F x0).toReal]
    have hleE :
        ((((F x0).toReal : ℝ)) : EReal) ≤
          (((|(F x0).toReal| + 1 : ℝ)) : EReal) := by
      exact_mod_cast hle
    rw [hF_val]
    simpa [α] using hleE
  simpa using
    hconvex.bounded_initial_sublevel_distance_to_optimal_set
      (x0 := (x0 : (i : Fin p) → Ei i)) (α := α) hα

/-- Helper for Theorem 11.7: after setting the scalar recurrence parameter to the reciprocal of
the CBPG quadratic-gap coefficient, the sublinear term from Lemma 11.7 rewrites to the textbook
quantity `4 / (c t)`. -/
lemma cbpg_sublinear_term_eq
    (Rα : PosReal) (t : ℝ) :
    let γ : PosReal :=
      ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
        inv_pos.mpr
          (cbpg_quadratic_gap_constant_pos Rα)⟩
    4 * (γ : ℝ) / t =
      4 / (cbpg_quadratic_gap_constant Lf Li Rα * t) := by
  dsimp
  have hc : cbpg_quadratic_gap_constant Lf Li Rα ≠ 0 :=
    (cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα).ne'
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [hc, ht]

-- Proof sketch: specialize the Chapter 11 quadratic decrease estimate
-- `cbpg_step_decrease_ge_sq_objective_gap` to the gap sequence
-- `a_k = Δ[k]`, derive nonnegativity from the canonical optimal-value
-- owner in `hconvex`, and apply Lemma 11.7's scalar recurrence estimate.
/-- If a radius `R_α` bounds the distance from the initial sublevel set
`{x | F(x) ≤ F(x^0)}` to the optimal set `X^*`, then the objective gap at iteration `k ≥ 2`
is bounded by the maximum of the geometric term
`(1 / 2)^((k - 1) / 2) (F(x^0) - F_opt)` and the sublinear term
`8 p (L_f + L_max)^2 R_α^2 / (L_min (k - 1))`. -/
theorem cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) (hk : 2 ≤ k) :
    Δ[k] ≤ GapBound[Rα,k] := by
  let γ : PosReal :=
    ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
      inv_pos.mpr (cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα)⟩
  have hstep :
      ∀ n : ℕ,
        Δ[n] - Δ[n + 1] ≥ (1 / (γ : ℝ)) * (Δ[n + 1] ^ (2 : ℕ)) := by
    intro n
    simpa [γ, cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα] using
      cbpg_objective_gap_step_recurrence
        (hconvex := hconvex) (x0 := x0) Rα hRα n
  have hmain :=
    _root_.nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := fun n ↦ Δ[n])
      (γ := γ)
      (ha_nonneg := cbpg_objective_gap_nonneg (hconvex := hconvex) (x0 := x0))
      (hstep := hstep)
      hk
  have hsub :
      4 * (γ : ℝ) / ((k - 1 : ℕ) : ℝ) =
        4 / (cbpg_quadratic_gap_constant Lf Li Rα * ((k - 1 : ℕ) : ℝ)) := by
    simpa [γ] using
      cbpg_sublinear_term_eq (Lf := Lf) (Li := Li) (Rα := Rα) (((k - 1 : ℕ) : ℝ))
  rw [hsub] at hmain
  exact hmain

-- Proof sketch: obtain an initial-sublevel radius witness from the canonical bridge
-- `hconvex.bounded_initial_sublevel_distance_to_optimal_set`, then apply the preceding theorem.
/-- Theorem 11.7 (1): under Assumptions 11.1 and 11.15, there exists a radius `R_α` together with
the corresponding initial-sublevel distance witness such that the CBPG objective gap at
iteration `k ≥ 2` is bounded by the maximum of the geometric and sublinear terms with that
`R_α`. -/
theorem cbpg_objective_gap_le_max_geometric_or_sublinear
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ Rα : PosReal,
      RadiusBound Rα ∧
      Δ[k] ≤ GapBound[Rα,k] := by
  rcases cbpg_exists_initial_sublevel_radius (hconvex := hconvex) (x0 := x0) with ⟨Rα, hRα⟩
  exact ⟨Rα, hRα,
    cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius
      (hconvex := hconvex) (x0 := x0) Rα hRα k hk⟩

-- Proof sketch: combine the previous maximum bound with the explicit lower bound on `n`. The
-- logarithmic term controls the geometric contribution, and the `1 / ε` term controls the
-- sublinear contribution, yielding `Δ[n] ≤ ε`.
/-- If a radius `R_α` controls the initial sublevel set and the iteration index `n` satisfies the
textbook lower bound involving `ε`, then the CBPG objective gap at step `n` is at most `ε`. -/
theorem cbpg_objective_gap_le_of_iteration_count_bound_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (ε : PosReal) (n : ℕ)
    (hn : IterationThreshold[Rα,ε] ≤ (n : ℝ)) :
    Δ[n] ≤ ε := by
  let γ : PosReal :=
    ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
      inv_pos.mpr (cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα)⟩
  have hstep :
      ∀ k : ℕ,
        Δ[k] - Δ[k + 1] ≥ (1 / (γ : ℝ)) * (Δ[k + 1] ^ (2 : ℕ)) := by
    intro k
    simpa [γ, cbpg_quadratic_gap_constant_pos (Lf := Lf) (Li := Li) Rα] using
      cbpg_objective_gap_step_recurrence
        (hconvex := hconvex) (x0 := x0) Rα hRα k
  have hn' :
      max
          ((2 / Real.log 2) * (Real.log (Δ[0]) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) +
        1 ≤
        (n : ℝ) := by
    have hsub :
        4 * (γ : ℝ) / (ε : ℝ) =
          4 / (cbpg_quadratic_gap_constant Lf Li Rα * (ε : ℝ)) := by
      simpa [γ] using
        cbpg_sublinear_term_eq (Lf := Lf) (Li := Li) (Rα := Rα) (ε : ℝ)
    simpa [hsub] using hn
  exact
    _root_.nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence
      (a := fun k ↦ Δ[k])
      (γ := γ)
      (ha_nonneg := cbpg_objective_gap_nonneg (hconvex := hconvex) (x0 := x0))
      (hstep := hstep)
      ε
      hn'

-- Proof sketch: extract an initial-sublevel radius witness from the canonical convex CBPG owner
-- and apply the preceding theorem with that witness.
/-- Theorem 11.7 (2): under Assumptions 11.1 and 11.15, there exists a radius `R_α` together with
the corresponding initial-sublevel distance witness such that, whenever the iteration index `n`
satisfies the textbook lower bound with that `R_α`, the objective gap at step `n` is at most
`ε`. -/
theorem cbpg_objective_gap_le_of_iteration_count_bound
    (ε : PosReal) (n : ℕ) :
    ∃ Rα : PosReal,
      RadiusBound Rα ∧
      (IterationThreshold[Rα,ε] ≤ (n : ℝ) →
        Δ[n] ≤ ε) := by
  rcases cbpg_exists_initial_sublevel_radius (hconvex := hconvex) (x0 := x0) with ⟨Rα, hRα⟩
  exact ⟨Rα, hRα, fun hn ↦
    cbpg_objective_gap_le_of_iteration_count_bound_of_initial_sublevel_radius
      (hconvex := hconvex) (x0 := x0) Rα hRα ε n hn⟩

end

end
