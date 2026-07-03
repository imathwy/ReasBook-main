import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_11 (from Chap06) -/
noncomputable section

/- Definition 6.11 is `source-facing` in the Chapter 6 extended-real convex-analysis API.
Domain sampling against nearby scalar/object owners shows:

- `positive_reciprocal_barrier` from Chapter 2 is the existing project pattern for a scalar
  extended-real function defined by a finite branch on a positivity domain and `⊤` elsewhere;
- `huber_function` from Definition 6.8 is the nearby Chapter 6 source-facing owner for a named
  textbook penalty, with the pointwise evaluation formula kept as derived API;
- `l1SquareVariationalSummand` from Lemma 6.69 is only a downstream use of this same quadratic-
  over-linear scalar pattern inside a simplex objective, not a second owner.

There is no upstream mathlib/project owner for this exact extended-real quadratic-over-linear
function, so the canonical owner abstraction in this chapter is the source-facing declaration
`quadratic_over_linear` itself. The primitive data are only the pair `(s, t)`; the displayed
piecewise formula is derived API. -/

/-- Definition 6.11: the extended-real quadratic-over-linear function `φ : ℝ × ℝ → EReal` given
by `φ(s, t) = s^2 / t` for `t > 0`, `φ(0, 0) = 0`, and `φ(s, t) = ∞` in all other cases. -/
def quadratic_over_linear : ℝ × ℝ → EReal :=
  fun p ↦
    if 0 < p.2 then
      ((p.1 ^ (2 : ℕ) / p.2 : ℝ) : EReal)
    else if p.1 = 0 ∧ p.2 = 0 then
      0
    else
      ⊤

@[inherit_doc] notation "φ" => quadratic_over_linear

-- Proof sketch: unfold `quadratic_over_linear`; the displayed piecewise formula is exactly the
-- defining expression specialized to the pair `(s, t)`.
/-- Evaluating `φ` at `(s, t)` gives the textbook piecewise formula. -/
@[simp] theorem quadratic_over_linear_apply (s t : ℝ) :
    φ (s, t) =
      if 0 < t then
        ((s ^ (2 : ℕ) / t : ℝ) : EReal)
      else if s = 0 ∧ t = 0 then
        0
      else
        ⊤ :=
  rfl

-- Proof sketch: this is the defining equation of `quadratic_over_linear`, so the function-level
-- identity is definitional.
/-- The notation `φ` denotes the quadratic-over-linear function written in its defining
piecewise form on `ℝ × ℝ`. -/
@[simp] theorem quadratic_over_linear_def :
    (φ : ℝ × ℝ → EReal) =
      fun p ↦
        if 0 < p.2 then
          ((p.1 ^ (2 : ℕ) / p.2 : ℝ) : EReal)
        else if p.1 = 0 ∧ p.2 = 0 then
          0
        else
          ⊤ :=
  rfl

-- Proof sketch: in the branch `0 < t`, the defining `if` in `quadratic_over_linear_apply`
-- simplifies by `if_pos ht`.
/-- On the half-plane `t > 0`, the quadratic-over-linear function agrees with its finite
quadratic branch. -/
theorem quadratic_over_linear_of_pos {s t : ℝ} (ht : 0 < t) :
    φ (s, t) = ((s ^ (2 : ℕ) / t : ℝ) : EReal) := by
  simp [quadratic_over_linear, ht]

-- Proof sketch: evaluate `quadratic_over_linear_apply` at `(0, 0)`; both `if` tests simplify to
-- the zero-zero branch.
/-- At the origin, the quadratic-over-linear function takes the value `0`. -/
@[simp] theorem quadratic_over_linear_zero_zero :
    φ (0, 0) = 0 := by
  simp [quadratic_over_linear]

-- Proof sketch: if `t ≤ 0` and `(s, t) ≠ (0, 0)`, both defining branches in
-- `quadratic_over_linear_apply` are false, so the value is `⊤`.
/-- Outside the positive-`t` branch and away from the origin, the quadratic-over-linear function
takes the value `∞`. -/
theorem quadratic_over_linear_of_nonpos_of_ne_origin {s t : ℝ} (ht : t ≤ 0)
    (hst : (s, t) ≠ (0, 0)) :
    φ (s, t) = ⊤ := by
  have hst' : ¬ (s = 0 ∧ t = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hst rfl
  simp [quadratic_over_linear, ht, hst']

/-! ### Theorem_6_11 (from Chap06) -/
noncomputable section

universe u

open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 6.11 is `source-facing` in the Chapter 6 proximal-mapping API. Domain sampling in the
minimal proximal-transport closure identifies:

- `proximal_objective` and `prox[...]` from Definition 6.1 as the core/canonical owners,
- `prox_add_const` from Definition 6.1 as the owner-level derived invariance already upstream,
- `proximal_mapping_smul_precompose_inv_smul` from Theorem 6.12 as the nearby source-facing
  scalar transport theorem,
- `proximal_mapping_precompose_continuousAffineMap` from Theorem 6.15 as a later `bridge/view`
  generalization under stronger `InnerProductSpace` and `CompleteSpace` assumptions.

The primitive data here are therefore only `g`, `lam`, `a`, and `x`. The inverse affine map on
the right-hand side is derived from that data, so the public statement should stay directly on the
owner `prox[...]` rather than introducing any auxiliary affine wrapper or chosen package. -/

-- Proof sketch: write the proximal objective for `f(y) = g (lam • y + a)`, make the change of
-- variables `z = lam • y + a`, and use `‖y - x‖² = lam⁻² ‖z - (lam • x + a)‖²`. This identifies
-- minimizers of the two objectives, and the inverse affine change of variables transports the
-- minimizing set by `z ↦ lam⁻¹ • (z - a)`.
/-- Theorem 6.11: scaling and translation for the source-facing set-valued proximal mapping.
For `f x = g (lam • x + a)`, the proximal points of `f` at `x` are exactly the inverse affine
image of the proximal points of `z ↦ lam² g z` at `lam • x + a`. The textbook properness
hypothesis on `g` is redundant for this minimizer-set identity, so the canonical Lean statement
omits it. -/
theorem proximal_mapping_scaling_translation
    (g : E → EReal) (lam : ℝ) (hlam : lam ≠ 0) (a x : E) :
    prox[fun y ↦ g (lam • y + a)] x =
      (fun z ↦ lam⁻¹ • (z - a)) ''
        prox[((lam ^ 2 : ℝ) : EReal) • g] (lam • x + a) := by
  let f : E → EReal := fun y ↦ g (lam • y + a)
  let s : EReal := ((lam ^ 2 : ℝ) : EReal)
  let g' : E → EReal := s • g
  let S : E → E := fun u ↦ lam • u + a
  let T : E → E := fun z ↦ lam⁻¹ • (z - a)
  have hs_nonneg : 0 ≤ s := by
    change (0 : EReal) ≤ ((lam ^ 2 : ℝ) : EReal)
    exact_mod_cast sq_nonneg lam
  have hs_top : s ≠ ⊤ := EReal.coe_ne_top _
  have hs_bot : s ≠ ⊥ := EReal.coe_ne_bot _
  have hs_zero : s ≠ 0 := by
    simpa [s] using (show (lam ^ 2 : ℝ) ≠ 0 from pow_ne_zero 2 hlam)
  have hST (z : E) : S (T z) = z := by
    calc
      S (T z) = lam • (lam⁻¹ • (z - a)) + a := rfl
      _ = (z - a) + a := by rw [smul_inv_smul₀ hlam]
      _ = z := sub_add_cancel z a
  have hTS (u : E) : T (S u) = u := by
    calc
      T (S u) = lam⁻¹ • (lam • u + a - a) := rfl
      _ = lam⁻¹ • (lam • u) := by simp
      _ = u := inv_smul_smul₀ hlam u
  have hquad (u : E) :
      ((1 / 2 : ℝ) * ‖S u - S x‖ ^ (2 : ℕ)) =
        lam ^ 2 * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) := by
    change ((1 / 2 : ℝ) * ‖(lam • u + a) - (lam • x + a)‖ ^ (2 : ℕ)) =
      lam ^ 2 * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ))
    rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs]
    ring_nf
    simp [sq_abs]
    ring
  have hobjective (u : E) :
      proximal_objective g' (S x) (S u) = s * proximal_objective f x u := by
    calc
      proximal_objective g' (S x) (S u)
          = s * g (lam • u + a) +
              ((((lam ^ 2 : ℝ) * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
              rw [proximal_objective, hquad]
              simp [g', s, S]
      _ = s * g (lam • u + a) +
            s * ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
              simp [s, EReal.coe_mul]
      _ = s * (g (lam • u + a) +
            ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal)) := by
              rw [EReal.left_distrib_of_nonneg_of_ne_top hs_nonneg hs_top]
      _ = s * proximal_objective f x u := by
              simp [proximal_objective, f]
  have hobjective_inv (z : E) :
      proximal_objective g' (S x) z = s * proximal_objective f x (T z) := by
    calc
      proximal_objective g' (S x) z
          = proximal_objective g' (S x) (S (T z)) := by rw [hST z]
      _ = s * proximal_objective f x (T z) := hobjective (T z)
  have hmem_transport (u : E) :
      u ∈ prox[f] x ↔ S u ∈ prox[g'] (S x) := by
    rw [mem_proximal_mapping_iff, mem_proximal_mapping_iff, isMinOn_univ_iff, isMinOn_univ_iff]
    constructor
    · intro hu z
      have huz :
          s * proximal_objective f x u ≤ s * proximal_objective f x (T z) :=
        mul_le_mul_of_nonneg_left (hu (T z)) hs_nonneg
      rw [← hobjective u, ← hobjective_inv z] at huz
      exact huz
    · intro hu v
      have huv :
          s * proximal_objective f x (T (S u)) ≤
            s * proximal_objective f x v := by
        rw [← hobjective_inv (S u), ← hobjective v]
        exact hu (S v)
      have huv' :
          (s * proximal_objective f x (T (S u))) / s ≤
            (s * proximal_objective f x v) / s :=
        EReal.monotone_div_right_of_nonneg hs_nonneg huv
      rw [mul_comm s (proximal_objective f x (T (S u))),
        mul_comm s (proximal_objective f x v),
        ← EReal.mul_div_right,
        ← EReal.mul_div_right,
        EReal.div_mul_cancel hs_bot hs_top hs_zero,
        EReal.div_mul_cancel hs_bot hs_top hs_zero,
        hTS u] at huv'
      exact huv'
  ext u
  constructor
  · intro hu
    rw [Set.mem_image]
    exact ⟨S u, (hmem_transport u).mp hu, hTS u⟩
  · rintro ⟨z, hz, rfl⟩
    exact (hmem_transport (T z)).mpr (by simpa [hST z] using hz)

end
