import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap12.Definition_12_20_Core
import BauschkeLean.Chap13.Definition_13_34
import BauschkeLean.Chap13.Proposition_13_19
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap20.PairingEqualityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace translate

universe u

namespace ERealFunction

noncomputable section

section BivariateQuadratic

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Lemma 20.45 is about the real-valued quadratic kernel
  `G : H × H → ℝ`.
- `core/canonical`: the owner abstractions are the quadratic function `halfSquaredNorm.asEReal`,
  the Chapter 20 pairing owner `pairing`, and the Chapter 13 involution owners `transpose` and
  `reverse`, all on the product Hilbert space provided by the Chapter 9 raw-product `ℓ²` bridges.
- `bridge/view`: the real-valued kernel is viewed through the canonical coercion
  `Function.toEReal`, and the source involution `(u, x) ↦ (-x, -u)` is expressed as the owner form
  `(Gᵀ)ᵛ` rather than by a parallel local wrapper.
- primitive data: the real-valued kernel `bivariateQuadraticKernel z w`.
- derived API: the half-squared-norm rewrite after adding the pairing, the conjugate symmetry
  `(Gᵀ)ᵛ`, and the equality/nonnegativity criteria obtained from that rewrite.
- Semantic recall: `lean_leansearch` returned no item-specific hit, so the owner/API choice was
  verified directly from the local pairing and transpose/reverse files.
-/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2 prod_normedSpace_l2
  prod_innerProductSpace_l2

/-- The real-valued bivariate quadratic kernel `G` centered at `(z, w)` from Lemma 20.45,
written in the owner-aligned form
`G(x, u) = -⟪x, u⟫ + ‖x + u - (z + w)‖² / 2`. -/
def bivariateQuadraticKernel (z w : H) : H × H → ℝ :=
  fun p ↦
    -⟪p.1, p.2⟫_ℝ + ‖p.1 + p.2 - (z + w)‖ ^ 2 / 2

variable (z w : H)

-- Local owner names for the quadratic kernel and its canonical `EReal` coercion at `(z, w)`.
local notation "G" => bivariateQuadraticKernel z w
local notation "Gₑ" => fun p : H × H ↦ ((G p : ℝ) : EReal)

/-- Helper for Lemma 20.45: in the local `ℓ²` product geometry on `H × H`, the squared norm is
the sum of the squared coordinate norms. -/
private theorem prod_l2_norm_sq_eq (p : H × H) :
    ‖p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  -- Transport the product norm to the canonical `WithLp` model and read off the squared norm.
  have hnorm : ‖p‖ = ‖WithLp.toLp 2 p‖ := by
    simpa [prod_normedAddCommGroup_l2, prod_seminormedAddCommGroup_l2] using
      (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := H) p)
  have hnorm_sq : ‖p‖ ^ 2 = ‖WithLp.toLp 2 p‖ ^ 2 := by
    simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
  exact hnorm_sq.trans <| by
    simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 p))

/-- The canonical `EReal` view of the quadratic kernel is the translated half-squared norm minus
the Chapter 20 pairing. -/
private theorem bivariateQuadraticKernel_asEReal_eq :
    Gₑ =
      fun p : H × H ↦
        halfSquaredNorm.asEReal (p.1 + p.2 - (z + w)) - pairing p := by
  funext p
  -- Expand the coercions and combine the two finite real terms inside `EReal`.
  simp [bivariateQuadraticKernel, pairing, sub_eq_add_neg, add_comm]
  have hhalf :
      ((((‖p.1 + p.2 + (-z + -w)‖ ^ 2) / 2 : ℝ) : EReal)) =
        ((((2 : ℝ)⁻¹ : ℝ) : EReal)) * ((‖p.1 + p.2 + (-z + -w)‖ ^ 2 : ℝ) : EReal) := by
    rw [show ((‖p.1 + p.2 + (-z + -w)‖ ^ 2) / 2 : ℝ) =
        (2 : ℝ)⁻¹ * ‖p.1 + p.2 + (-z + -w)‖ ^ 2 by ring]
    rw [EReal.coe_mul]
  simpa using congrArg
    (fun t : EReal ↦ -((⟪p.1, p.2⟫_ℝ : ℝ) : EReal) + t) hhalf

/-- Helper for Lemma 20.45: equation (20.31) rewrites the kernel as a translated quadratic plus a
product-space affine perturbation. -/
private theorem bivariateQuadraticKernel_product_affine_form :
    Gₑ =
      τ (z, w) (halfSquaredNorm.asEReal : H × H → EReal) +
        (fun p : H × H ↦ ((⟪p, (-w, -z)⟫_ℝ : ℝ) : EReal)) +
        fun _ : H × H ↦ ((⟪z, w⟫_ℝ : ℝ) : EReal) := by
  funext p
  rcases p with ⟨x, u⟩
  -- Rewrite `Gₑ` to the completed-square form, then compare the two real expressions.
  rw [congrFun (@bivariateQuadraticKernel_asEReal_eq H _ _ z w) (x, u)]
  simp only [Pi.add_apply, translate_apply, Function.asEReal_apply, halfSquaredNorm_apply,
    pairing_apply]
  rw [prod_l2_norm_sq_eq (p := ((x, u) - (z, w) : H × H))]
  rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add]
  congr 1
  have hnorm :
      ‖(x - z) + (u - w)‖ ^ 2 =
        ‖x - z‖ ^ 2 + 2 * ⟪x - z, u - w⟫_ℝ + ‖u - w‖ ^ 2 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using norm_add_sq_real (x - z) (u - w)
  have hcross :
      ⟪x - z, u - w⟫_ℝ =
        ⟪x, u⟫_ℝ - ⟪x, w⟫_ℝ - ⟪u, z⟫_ℝ + ⟪z, w⟫_ℝ := by
    calc
      ⟪x - z, u - w⟫_ℝ = ⟪x, u - w⟫_ℝ - ⟪z, u - w⟫_ℝ := by
        rw [inner_sub_left]
      _ = (⟪x, u⟫_ℝ - ⟪x, w⟫_ℝ) - (⟪z, u⟫_ℝ - ⟪z, w⟫_ℝ) := by
        rw [inner_sub_right, inner_sub_right]
      _ = ⟪x, u⟫_ℝ - ⟪x, w⟫_ℝ - ⟪u, z⟫_ℝ + ⟪z, w⟫_ℝ := by
        rw [real_inner_comm z u]
        ring
  have hnorm' :
      ‖x + u - (z + w)‖ ^ 2 =
        ‖x - z‖ ^ 2 + 2 * ⟪x - z, u - w⟫_ℝ + ‖u - w‖ ^ 2 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm
  have hpair :
      ⟪(x, u), (-w, -z)⟫_ℝ = -⟪w, x⟫_ℝ - ⟪z, u⟫_ℝ := by
    change ⟪x, -w⟫_ℝ + ⟪u, -z⟫_ℝ = -⟪w, x⟫_ℝ - ⟪z, u⟫_ℝ
    simpa [sub_eq_add_neg, real_inner_comm]
  have hnorm_half :
      ‖x + u - (z + w)‖ ^ 2 / 2 =
        ‖x - z‖ ^ 2 / 2 + ⟪x - z, u - w⟫_ℝ + ‖u - w‖ ^ 2 / 2 := by
    nlinarith [hnorm']
  rw [hpair]
  rw [hnorm_half, hcross, real_inner_comm w x, real_inner_comm z u]
  simp [sub_eq_add_neg]
  ring

/-- Helper for Lemma 20.45: the explicit affine correction produced by the Chapter 13 translate
conjugation rule on `H × H` agrees pointwise with the reflected-transposed kernel. -/
private theorem bivariateQuadraticKernel_conjugate_pointwise_normalization
    (x u : H) :
    ((τ (-w, -z) (halfSquaredNorm.asEReal : H × H → EReal)) +
        fun p : H × H ↦
          ((⟪(z, w), p⟫_ℝ : ℝ) : EReal) -
            ((⟪(z, w), (-w, -z)⟫_ℝ : ℝ) : EReal) -
            ((⟪z, w⟫_ℝ : ℝ) : EReal)) (u, x) =
      Gₑ (-x, -u) := by
  have hprod :=
    congrFun (@bivariateQuadraticKernel_product_affine_form H _ _ z w) (-x, -u)
  -- Rewrite the target value through the completed-square form at the reflected point.
  have hprod' : Gₑ (-x, -u) =
      ((τ (z, w) (halfSquaredNorm.asEReal : H × H → EReal)) +
          (fun p : H × H ↦ ((⟪p, (-w, -z)⟫_ℝ : ℝ) : EReal)) +
          fun _ : H × H ↦ ((⟪z, w⟫_ℝ : ℝ) : EReal)) (-x, -u) := by
    simpa [Pi.add_apply] using hprod
  rw [hprod']
  simp only [Pi.add_apply]
  have htranslate :
      τ (-w, -z) (halfSquaredNorm.asEReal : H × H → EReal) (u, x) =
        τ (z, w) (halfSquaredNorm.asEReal : H × H → EReal) (-x, -u) := by
    -- The two translated quadratic values coincide because the `ℓ²` product norm is even.
    simp only [translate_apply, Function.asEReal_apply, halfSquaredNorm_apply]
    have hnorm_sq :
        ‖((u, x) : H × H) - (-w, -z)‖ ^ 2 =
          ‖((-x, -u) : H × H) - (z, w)‖ ^ 2 := by
      rw [prod_l2_norm_sq_eq (p := ((u, x) : H × H) - (-w, -z))]
      rw [prod_l2_norm_sq_eq (p := ((-x, -u) : H × H) - (z, w))]
      have hxnorm : ‖x + z‖ = ‖-z + -x‖ := by
        calc
          ‖x + z‖ = ‖z + x‖ := by simp [add_comm]
          _ = ‖-z + -x‖ := by
            simpa [add_assoc, add_left_comm, add_comm] using (norm_neg (z + x)).symm
      have hunorm : ‖u + w‖ = ‖-w + -u‖ := by
        calc
          ‖u + w‖ = ‖w + u‖ := by simp [add_comm]
          _ = ‖-w + -u‖ := by
            simpa [add_assoc, add_left_comm, add_comm] using (norm_neg (w + u)).symm
      have hx : ‖x + z‖ ^ 2 = ‖-z + -x‖ ^ 2 := by
        exact congrArg (fun t : ℝ ↦ t ^ 2) hxnorm
      have hu : ‖u + w‖ ^ 2 = ‖-w + -u‖ ^ 2 := by
        exact congrArg (fun t : ℝ ↦ t ^ 2) hunorm
      calc
        ‖((u, x) - (-w, -z)).1‖ ^ 2 + ‖((u, x) - (-w, -z)).2‖ ^ 2 =
            ‖u + w‖ ^ 2 + ‖x + z‖ ^ 2 := by
              simp [sub_eq_add_neg]
        _ = ‖-w + -u‖ ^ 2 + ‖-z + -x‖ ^ 2 := by
          rw [hu, hx]
        _ = ‖((-x, -u) - (z, w)).1‖ ^ 2 + ‖((-x, -u) - (z, w)).2‖ ^ 2 := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    exact congrArg (fun t : ℝ ↦ (((t / 2 : ℝ)) : EReal)) hnorm_sq
  have haffine :
      (((⟪(z, w), (u, x)⟫_ℝ : ℝ) : EReal) -
          ((⟪(z, w), (-w, -z)⟫_ℝ : ℝ) : EReal) -
          ((⟪z, w⟫_ℝ : ℝ) : EReal)) =
        ((⟪(-x, -u), (-w, -z)⟫_ℝ : ℝ) : EReal) +
          ((⟪z, w⟫_ℝ : ℝ) : EReal) := by
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    change
      (⟪z, u⟫_ℝ + ⟪w, x⟫_ℝ) - (⟪z, -w⟫_ℝ + ⟪w, -z⟫_ℝ) - ⟪z, w⟫_ℝ =
        (⟪-x, -w⟫_ℝ + ⟪-u, -z⟫_ℝ) + ⟪z, w⟫_ℝ
    simp [sub_eq_add_neg, real_inner_comm, add_assoc, add_left_comm, add_comm]
    ring
  -- Match the translated quadratic term and the finite affine correction separately.
  rw [htranslate, haffine]
  simp [add_assoc]

-- Proof sketch: apply the product-space quadratic self-conjugacy from Proposition 13.19 to the
-- completed-square form from (20.31), then normalize the explicit affine correction pointwise
-- to the reflected transpose.
/-- Lemma 20.45 (1): the quadratic kernel `G` centered at `(z, w)` has Fenchel conjugate
`G* = (Gᵀ)ᵛ`, equivalently `G*(u, x) = G(-x, -u)`. -/
theorem bivariateQuadraticKernel_conjugate_eq_transpose_reverse :
    Gₑ∗ = (Gₑᵀ)ᵛ := by
  let F : H × H → EReal :=
    τ (z, w) (halfSquaredNorm.asEReal : H × H → EReal) +
      (fun p : H × H ↦ ((⟪p, (-w, -z)⟫_ℝ : ℝ) : EReal)) +
      fun _ : H × H ↦ ((⟪z, w⟫_ℝ : ℝ) : EReal)
  -- Rewrite `Gₑ` by the completed-square product-space form from (20.31).
  rw [@bivariateQuadraticKernel_product_affine_form H _ _ z w]
  -- Proposition 13.23 conjugates a translate plus linear term into a translated conjugate.
  rw [conjugate_translate_add_inner_add_const
    (f := (halfSquaredNorm.asEReal : H × H → EReal))
    (y := (z, w)) (v := (-w, -z)) (β := ⟪z, w⟫_ℝ)]
  -- Proposition 13.19 identifies the quadratic conjugate on `H × H` with itself.
  rw [← half_squared_norm_self_conjugate (H := H × H)]
  ext p
  rcases p with ⟨u, x⟩
  -- The remaining pointwise normalization is exactly the dedicated bridge lemma above.
  calc
    (τ (-w, -z) (halfSquaredNorm.asEReal : H × H → EReal) + fun p : H × H ↦
      ((⟪(z, w), p⟫_ℝ : ℝ) : EReal) -
        ((⟪(z, w), (-w, -z)⟫_ℝ : ℝ) : EReal) -
        ((⟪z, w⟫_ℝ : ℝ) : EReal)) (u, x) =
        Gₑ (-x, -u) :=
      @bivariateQuadraticKernel_conjugate_pointwise_normalization H _ _ z w x u
    _ = F (-x, -u) := by
      simpa [F, Pi.add_apply] using
        congrFun (@bivariateQuadraticKernel_product_affine_form H _ _ z w) (-x, -u)
    _ = (Fᵀ)ᵛ (u, x) := by
      simp [F, transpose_apply, ERealFunction.reverse_apply]

/-- Evaluating the conjugate symmetry from Lemma 20.45 rewrites the conjugate value at `(u, x)`
as the kernel value at `(-x, -u)`, still viewed through the canonical `EReal` coercion. -/
theorem bivariateQuadraticKernel_conjugate_apply (x u : H) :
    Gₑ∗ (u, x) = Gₑ (-x, -u) := by
  -- Evaluate the functional symmetry at `(u, x)` and unfold the transpose/reverse owners.
  simpa [transpose_apply, ERealFunction.reverse_apply] using
    congrFun (@bivariateQuadraticKernel_conjugate_eq_transpose_reverse H _ _ z w) (u, x)

-- Proof sketch: expand the definition of `bivariateQuadraticKernel`; the pairing term cancels.
/-- Adding the canonical pairing to the quadratic kernel leaves exactly the translated half-squared
norm term. -/
@[simp] theorem bivariateQuadraticKernel_add_pairing_eq_half_mul_norm_sq
    (x u : H) :
    G (x, u) + ⟪x, u⟫_ℝ =
      (1 / 2 : ℝ) * ‖(x - z) + (u - w)‖ ^ 2 := by
  -- Expand the kernel, cancel the pairing, and normalize the translated sum.
  calc
    G (x, u) + ⟪x, u⟫_ℝ
        = -⟪x, u⟫_ℝ + ‖x + u - (z + w)‖ ^ 2 / 2 + ⟪x, u⟫_ℝ := by
          rfl
    _ = ‖x + u - (z + w)‖ ^ 2 / 2 := by ring
    _ = (1 / 2 : ℝ) * ‖x + u - (z + w)‖ ^ 2 := by ring
    _ = (1 / 2 : ℝ) * ‖(x - z) + (u - w)‖ ^ 2 := by
          congr 1
          abel_nf

-- Proof sketch: rewrite `G(x, u) + ⟪x, u⟫` as
-- `(1 / 2) * ‖(x - z) + (u - w)‖ ^ 2`, which is nonnegative.
/-- Lemma 20.45 (2): adding the pairing `⟪x, u⟫` to the kernel value is always nonnegative. -/
theorem bivariateQuadraticKernel_add_pairing_nonneg (x u : H) :
    0 ≤ G (x, u) + ⟪x, u⟫_ℝ := by
  -- Reduce to the obvious nonnegativity of a squared norm.
  rw [@bivariateQuadraticKernel_add_pairing_eq_half_mul_norm_sq H _ _ z w x u]
  nlinarith [sq_nonneg ‖(x - z) + (u - w)‖]

-- Proof sketch: after the same rewrite as in clause (i), equality holds exactly when the norm
-- vanishes, i.e. when `(x - z) + (u - w) = 0`.
/-- Lemma 20.45 (3): equality in clause (2) holds exactly when `x - z = w - u`. -/
theorem bivariateQuadraticKernel_add_pairing_eq_zero_iff (x u : H) :
    G (x, u) + ⟪x, u⟫_ℝ = 0 ↔ x - z = w - u := by
  constructor
  · intro hzero
    -- Equality in clause (2) forces the translated norm to vanish.
    rw [@bivariateQuadraticKernel_add_pairing_eq_half_mul_norm_sq H _ _ z w x u] at hzero
    have hnorm_sq : ‖(x - z) + (u - w)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(x - z) + (u - w)‖]
    have hnorm : ‖(x - z) + (u - w)‖ = 0 := by
      nlinarith [sq_nonneg ‖(x - z) + (u - w)‖]
    have hsum : (x - z) + (u - w) = 0 := by
      simpa using norm_eq_zero.mp hnorm
    have hrel : x - z = -(u - w) := eq_neg_of_add_eq_zero_left hsum
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrel
  · intro hrel
    -- Conversely, the relation `x - z = w - u` collapses the translated norm to zero.
    rw [@bivariateQuadraticKernel_add_pairing_eq_half_mul_norm_sq H _ _ z w x u]
    have hsum : (x - z) + (u - w) = 0 := by
      rw [hrel]
      abel_nf
    simp [hsum]

-- Proof sketch: clause (ii) gives `x - z = w - u`; substituting this into
-- `⟪z - x, w - u⟫` yields the negative squared norm of `x - z`, so the extra nonnegativity
-- assumption forces `x = z` and then `u = w`.
/-- Lemma 20.45 (4): equality in clause (2) together with
`0 ≤ ⟪z - x, w - u⟫` is equivalent to `(x, u) = (z, w)`. -/
theorem bivariateQuadraticKernel_zero_pairing_and_cross_nonneg_iff
    (x u : H) :
    (G (x, u) + ⟪x, u⟫_ℝ = 0 ∧ 0 ≤ ⟪z - x, w - u⟫_ℝ) ↔ (x, u) = (z, w) := by
  constructor
  · rintro ⟨hzero, hcross⟩
    -- Clause (3) identifies the equality case with the linear relation `x - z = w - u`.
    have hrel :
        x - z = w - u :=
      (@bivariateQuadraticKernel_add_pairing_eq_zero_iff H _ _ z w x u).1 hzero
    have hcross' : 0 ≤ -‖x - z‖ ^ 2 := by
      calc
        0 ≤ ⟪z - x, w - u⟫_ℝ := hcross
        _ = ⟪z - x, x - z⟫_ℝ := by rw [← hrel]
        _ = -‖x - z‖ ^ 2 := by
          have hz : z - x = -(x - z) := by
            abel_nf
          rw [hz, inner_neg_left, real_inner_self_eq_norm_sq]
    have hnorm_sq : ‖x - z‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖x - z‖]
    have hnorm : ‖x - z‖ = 0 := by
      nlinarith [sq_nonneg ‖x - z‖]
    have hxz : x - z = 0 := by
      simpa using norm_eq_zero.mp hnorm
    have hx : x = z := sub_eq_zero.mp hxz
    have hwu : w - u = 0 := by
      simpa [hxz] using hrel.symm
    have hu : u = w := by
      exact (sub_eq_zero.mp hwu).symm
    exact Prod.ext hx hu
  · intro hEq
    cases hEq
    -- At the center point both the norm-square term and the cross term vanish.
    constructor
    · simpa using
        (@bivariateQuadraticKernel_add_pairing_eq_zero_iff H _ _ z w z w).2 (by simp)
    · simp

end BivariateQuadratic

end

end ERealFunction
