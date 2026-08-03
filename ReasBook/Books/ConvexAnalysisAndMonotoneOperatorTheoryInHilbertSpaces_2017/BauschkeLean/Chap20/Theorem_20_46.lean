import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap13.Proposition_13_46
import BauschkeLean.Chap15.Corollary_15_15
import BauschkeLean.Chap15.Definition_15_10
import BauschkeLean.Chap11.Proposition_11_14
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Lemma_20_45

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise
open ERealFunction
open Set

universe u

namespace SetValuedOperator

noncomputable section

section BivariateFenchelEquality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 20.46 studies monotonicity and maximal monotonicity of the
  transpose-conjugate contact operator `pairingEqualityOperator ((F∗)ᵀ)`.
- `core/canonical`: the owner abstraction is the already-defined pairing-contact operator
  `pairingEqualityOperator`.
- `bridge/view`: the theorem specializes that owner to the transpose-conjugate `(F∗)ᵀ`.

Primitive data live in `pairingEqualityOperator`.
Derived API in this file: monotonicity and maximal-monotonicity theorems for the
transpose-conjugate specialization.
Semantic recall: `lean_leansearch` returned no item-specific hit, so the owner names and statement
surface were verified directly from `Definition_20_20`, `PairingEqualityOperator`, and nearby
Chapter 20 precedent. -/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

variable (F : H × H → EReal)

/-- Helper for Theorem 20.46: the midpoint inequality for the conjugate contact set yields the
source monotonicity inequality after expanding the pairing algebra. -/
private theorem conjugateTranspose_contact_midpoint_nonneg
    (hFstarT_ge : ∀ x u : H, pairing (x, u) ≤ ((F∗)ᵀ) (x, u))
    {x u y v : H}
    (hx : ((F∗)ᵀ) (x, u) = pairing (x, u))
    (hy : ((F∗)ᵀ) (y, v) = pairing (y, v)) :
    (0 : ℝ) ≤ ⟪x - y, u - v⟫_ℝ := by
  let a : ℝ := 1 / 2
  have ha0 : 0 ≤ a := by
    norm_num [a]
  have ha1 : a ≤ 1 := by
    norm_num [a]
  have hconv : IsConvex (F∗) := (mem_gamma_iff (F∗)).mp (conjugate_mem_gamma (f := F)) |>.1
  -- Apply Jensen convexity to the swapped midpoint `(u, x)` / `(v, y)`.
  have hmid_conv := hconv (x := (u, x)) (y := (v, y)) (a := a) ha0 ha1
  have hx' : F∗ (u, x) = pairing (x, u) := by
    simpa [transpose_apply] using hx
  have hy' : F∗ (v, y) = pairing (y, v) := by
    simpa [transpose_apply] using hy
  have hpair_mid :
      pairing (a • x + (1 - a) • y, a • u + (1 - a) • v) ≤
        F∗ (a • u + (1 - a) • v, a • x + (1 - a) • y) := by
    simpa [a, transpose_apply] using hFstarT_ge (a • x + (1 - a) • y) (a • u + (1 - a) • v)
  -- Chain the midpoint lower bound with the convex upper bound and rewrite the contact equalities.
  have hineq :
      pairing (a • x + (1 - a) • y, a • u + (1 - a) • v) ≤
        (a : EReal) * pairing (x, u) + (1 - a : EReal) * pairing (y, v) := by
    calc
      pairing (a • x + (1 - a) • y, a • u + (1 - a) • v) ≤
          F∗ (a • u + (1 - a) • v, a • x + (1 - a) • y) := hpair_mid
      _ ≤ (a : EReal) * F∗ (u, x) + (1 - a : EReal) * F∗ (v, y) := hmid_conv
      _ = (a : EReal) * pairing (x, u) + (1 - a : EReal) * pairing (y, v) := by
        rw [hx', hy']
  have hineq' :
      (((⟪a • x + (1 - a) • y, a • u + (1 - a) • v⟫_ℝ : ℝ) : EReal)) ≤
        (((a * ⟪x, u⟫_ℝ + (1 - a) * ⟪y, v⟫_ℝ : ℝ) : EReal)) := by
    simpa [pairing_apply, a, EReal.coe_add, EReal.coe_mul] using hineq
  have hreal :
      ⟪a • x + (1 - a) • y, a • u + (1 - a) • v⟫_ℝ ≤
        a * ⟪x, u⟫_ℝ + (1 - a) * ⟪y, v⟫_ℝ :=
    EReal.coe_le_coe_iff.mp hineq'
  -- Expand the midpoint pairing to isolate the cross terms from the source proof.
  have hcross : ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ + ⟪y, v⟫_ℝ := by
    have hreal_half := hreal
    simp [a, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] at hreal_half
    nlinarith
  have htarget : 0 ≤ ⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ - ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ := by
    linarith
  -- Repackage the cross-term inequality into the monotonicity pairing.
  calc
    0 ≤ ⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ - ⟪y, u⟫_ℝ + ⟪y, v⟫_ℝ := htarget
    _ = ⟪x - y, u - v⟫_ℝ := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      ring

/-- Helper for Theorem 20.46: `F**` dominates the pairing once `F` is convex, `F*` is proper,
and `F` itself dominates the pairing. -/
private theorem pairing_le_biconjugate_of_convex_of_properConjugate
    [CompleteSpace H]
    (hF_conv : IsConvex F) (hFstar_proper : IsProper F∗)
    (hF_ge : ∀ p : H × H, pairing p ≤ F p) :
    ∀ p : H × H, pairing p ≤ F∗∗ p := by
  intro p
  have hpair_lsc :
      LowerSemicontinuousAt pairing p := by
    -- The pairing is continuous on the product Hilbert space, hence lower semicontinuous.
    exact (continuous_coe_real_ereal.comp (continuous_fst.inner continuous_snd)).continuousAt
      |>.lowerSemicontinuousAt
  have hliminf_pair :
      pairing p ≤ liminfAt pairing p := hpair_lsc.le_liminf
  have hliminf_mono :
      liminfAt pairing p ≤ liminfAt F p := by
    -- Pointwise domination passes to the neighborhood-filter liminf.
    simpa [liminfAt] using
      (Filter.liminf_le_liminf (Filter.Eventually.of_forall hF_ge) :
        Filter.liminf pairing (nhds p) ≤ Filter.liminf F (nhds p))
  calc
    pairing p ≤ liminfAt pairing p := hliminf_pair
    _ ≤ liminfAt F p := hliminf_mono
    _ = F∗∗ p := by
      symm
      exact biconjugate_eq_liminfAt_of_isConvex_of_dom_conjugate_nonempty
        hF_conv hFstar_proper.2 p

/-- Helper for Theorem 20.46: the source quadratic kernel has the separated quadratic-affine
normal form needed for continuity and convexity packaging. -/
private theorem bivariateQuadraticKernel_eq_separated_quadratic_affine
    (z w : H) (x u : H) :
    ERealFunction.bivariateQuadraticKernel z w (x, u) =
      (1 / 2 : ℝ) * ‖x - z‖ ^ 2 + (1 / 2 : ℝ) * ‖u - w‖ ^ 2
        - ⟪x, w⟫_ℝ - ⟪u, z⟫_ℝ + ⟪z, w⟫_ℝ := by
  -- Expand the norm square in the source formula and cancel the mixed pairing term.
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
  have hhalf :
      ‖(x - z) + (u - w)‖ ^ 2 / 2 =
        ‖x - z‖ ^ 2 / 2 + ⟪x - z, u - w⟫_ℝ + ‖u - w‖ ^ 2 / 2 := by
    nlinarith [hnorm]
  calc
    ERealFunction.bivariateQuadraticKernel z w (x, u)
        = -⟪x, u⟫_ℝ + ‖(x - z) + (u - w)‖ ^ 2 / 2 := by
            simp [ERealFunction.bivariateQuadraticKernel, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm]
    _ = -⟪x, u⟫_ℝ + (‖x - z‖ ^ 2 / 2 + ⟪x - z, u - w⟫_ℝ + ‖u - w‖ ^ 2 / 2) := by
            rw [hhalf]
    _ = (1 / 2 : ℝ) * ‖x - z‖ ^ 2 + (1 / 2 : ℝ) * ‖u - w‖ ^ 2
          - ⟪x, w⟫_ℝ - ⟪u, z⟫_ℝ + ⟪z, w⟫_ℝ := by
            rw [hcross]
            ring

/-- Helper for Theorem 20.46: the quadratic kernel is a sum of coordinate half-squared norms
plus the affine term determined by `z + w`. -/
private theorem bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm
    (z w x u : H) :
    ERealFunction.bivariateQuadraticKernel z w (x, u) =
      (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2
        - ⟪x, z + w⟫_ℝ - ⟪u, z + w⟫_ℝ + (1 / 2 : ℝ) * ‖z + w‖ ^ 2 := by
  have hsum :
      ‖x + u - (z + w)‖ ^ 2 =
        ‖x + u‖ ^ 2 - 2 * ⟪x + u, z + w⟫_ℝ + ‖z + w‖ ^ 2 := by
    simpa [sub_eq_add_neg, two_mul, real_inner_comm, add_assoc, add_left_comm, add_comm] using
      norm_sub_sq_real (x + u) (z + w)
  have hadd :
      ‖x + u‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, u⟫_ℝ + ‖u‖ ^ 2 := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using norm_add_sq_real x u
  calc
    ERealFunction.bivariateQuadraticKernel z w (x, u)
        = -⟪x, u⟫_ℝ + ‖x + u - (z + w)‖ ^ 2 / 2 := by
            simp [ERealFunction.bivariateQuadraticKernel, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm]
    _ = -⟪x, u⟫_ℝ
          + (‖x + u‖ ^ 2 - 2 * ⟪x + u, z + w⟫_ℝ + ‖z + w‖ ^ 2) / 2 := by
            rw [hsum]
    _ = -⟪x, u⟫_ℝ
          + (‖x‖ ^ 2 + 2 * ⟪x, u⟫_ℝ + ‖u‖ ^ 2 - 2 * ⟪x + u, z + w⟫_ℝ
              + ‖z + w‖ ^ 2) / 2 := by
            rw [hadd]
    _ = (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2
          - ⟪x, z + w⟫_ℝ - ⟪u, z + w⟫_ℝ + (1 / 2 : ℝ) * ‖z + w‖ ^ 2 := by
            rw [inner_add_left]
            ring

/-- Helper for Theorem 20.46: the local `ℓ²` product norm splits coordinatewise. -/
private theorem prodL2_norm_sq_eq (p : H × H) :
    ‖p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  have hnorm : ‖p‖ = ‖WithLp.toLp 2 p‖ := by
    simpa [ERealFunction.prod_normedAddCommGroup_l2, ERealFunction.prod_seminormedAddCommGroup_l2]
      using (WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := H) p)
  have hnorm_sq : ‖p‖ ^ 2 = ‖WithLp.toLp 2 p‖ ^ 2 := by
    simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
  exact hnorm_sq.trans <| by
    simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 p))

/-- Helper for Theorem 20.46: each coordinate norm is bounded by the local `ℓ²` product norm. -/
private theorem norm_fst_le_prodL2_norm (p : H × H) :
    ‖p.1‖ ≤ ‖p‖ := by
  simpa using (WithLp.norm_fst_le (p := 2) (x := WithLp.toLp 2 p))

/-- Helper for Theorem 20.46: each second-coordinate norm is bounded by the local `ℓ²` product
norm. -/
private theorem norm_snd_le_prodL2_norm (p : H × H) :
    ‖p.2‖ ≤ ‖p‖ := by
  simpa using (WithLp.norm_snd_le (p := 2) (x := WithLp.toLp 2 p))

/-- Helper for Theorem 20.46: the quadratic kernel is supercoercive on the product Hilbert
space. -/
private theorem bivariateQuadraticKernel_supercoercive (z w : H) :
    Supercoercive ((ERealFunction.bivariateQuadraticKernel z w).toEReal).asEReal := by
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  let c : H := z + w
  let C : ℝ := ‖c‖ + 1
  let R : ℝ := max 1 (4 * (|ξ| + 2 * C + 1))
  have hR :
      ∀ᶠ p : H × H in Filter.comap (fun p : H × H ↦ ‖p‖) Filter.atTop, R ≤ ‖p‖ := by
    simpa [R] using
      (Filter.Tendsto.eventually_ge_atTop
        (Filter.tendsto_comap : Filter.Tendsto (fun p : H × H ↦ ‖p‖)
          (Filter.comap (fun p : H × H ↦ ‖p‖) Filter.atTop) Filter.atTop) R)
  filter_upwards [hR] with p hpR
  have hp_one : (1 : ℝ) ≤ ‖p‖ := le_trans (le_max_left _ _) hpR
  have hp_big : 4 * (|ξ| + 2 * C + 1) ≤ ‖p‖ := by
    exact le_trans (le_max_right _ _) hpR
  have hp_pos : 0 < ‖p‖ := lt_of_lt_of_le zero_lt_one hp_one
  have hquad :
      (1 / 2 : ℝ) * ‖p.1‖ ^ 2 + (1 / 2 : ℝ) * ‖p.2‖ ^ 2 = (1 / 2 : ℝ) * ‖p‖ ^ 2 := by
    rw [prodL2_norm_sq_eq (p := p)]
    ring
  have hkernel_lower :
      (1 / 2 : ℝ) * ‖p‖ ^ 2 - 2 * C * ‖p‖ ≤
        ERealFunction.bivariateQuadraticKernel z w p := by
    rcases p with ⟨x, u⟩
    have hnormx : ‖x‖ ≤ ‖((x, u) : H × H)‖ := norm_fst_le_prodL2_norm (p := (x, u))
    have hnormu : ‖u‖ ≤ ‖((x, u) : H × H)‖ := norm_snd_le_prodL2_norm (p := (x, u))
    have hlinear :
        -⟪x, c⟫_ℝ - ⟪u, c⟫_ℝ ≥ -2 * C * ‖((x, u) : H × H)‖ := by
      have hx : -⟪x, c⟫_ℝ ≥ -‖x‖ * ‖c‖ := by
        have hxc : ⟪x, c⟫_ℝ ≤ ‖x‖ * ‖c‖ := real_inner_le_norm x c
        linarith
      have hu : -⟪u, c⟫_ℝ ≥ -‖u‖ * ‖c‖ := by
        have huc : ⟪u, c⟫_ℝ ≤ ‖u‖ * ‖c‖ := real_inner_le_norm u c
        linarith
      have hx' : -‖x‖ * ‖c‖ ≥ -‖((x, u) : H × H)‖ * ‖c‖ := by
        have hxc : ‖x‖ * ‖c‖ ≤ ‖((x, u) : H × H)‖ * ‖c‖ := by
          exact mul_le_mul_of_nonneg_right hnormx (norm_nonneg c)
        nlinarith
      have hu' : -‖u‖ * ‖c‖ ≥ -‖((x, u) : H × H)‖ * ‖c‖ := by
        have huc : ‖u‖ * ‖c‖ ≤ ‖((x, u) : H × H)‖ * ‖c‖ := by
          exact mul_le_mul_of_nonneg_right hnormu (norm_nonneg c)
        nlinarith
      have hsum : -‖x‖ * ‖c‖ - ‖u‖ * ‖c‖ ≥ -2 * ‖((x, u) : H × H)‖ * ‖c‖ := by
        nlinarith
      have hsum' : -2 * ‖((x, u) : H × H)‖ * ‖c‖ ≥ -2 * C * ‖((x, u) : H × H)‖ := by
        have hC : ‖c‖ ≤ C := by
          dsimp [C]
          linarith
        nlinarith
      nlinarith
    calc
      (1 / 2 : ℝ) * ‖((x, u) : H × H)‖ ^ 2 - 2 * C * ‖((x, u) : H × H)‖
          ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2
                - ⟪x, c⟫_ℝ - ⟪u, c⟫_ℝ + (1 / 2 : ℝ) * ‖c‖ ^ 2 := by
            rw [← hquad]
            nlinarith
      _ = ERealFunction.bivariateQuadraticKernel z w (x, u) := by
            simpa [c] using
              (bivariateQuadraticKernel_eq_coordinate_halfSquaredNorm (z := z) (w := w) x u).symm
  have htail : ξ < ‖p‖ / 4 - 2 * C := by
    have hbound : |ξ| + 2 * C + 1 ≤ ‖p‖ / 4 := by
      nlinarith
    linarith [le_abs_self ξ]
  have hreal :
      ξ < (ERealFunction.bivariateQuadraticKernel z w p) / ‖p‖ := by
    have hdiv :
        ‖p‖ / 4 - 2 * C ≤ ERealFunction.bivariateQuadraticKernel z w p / ‖p‖ := by
      have hbase :
          (‖p‖ / 4 - 2 * C) * ‖p‖ ≤ ERealFunction.bivariateQuadraticKernel z w p := by
        nlinarith [hkernel_lower]
      exact (le_div_iff₀ hp_pos).2 hbase
    exact lt_of_lt_of_le htail hdiv
  rw [Function.asEReal_apply, Function.toEReal_apply]
  have hcast :
      ((ξ : ℝ) : EReal) <
        (((ERealFunction.bivariateQuadraticKernel z w p / ‖p‖ : ℝ) : EReal)) := by
    exact_mod_cast hreal
  simpa [EReal.coe_div] using hcast

/-- Helper for Theorem 20.46: the source quadratic kernel is continuous on the product Hilbert
space. -/
private theorem continuous_bivariateQuadraticKernel (z w : H) :
    Continuous (ERealFunction.bivariateQuadraticKernel z w) := by
  -- Rewrite the kernel into the separated quadratic-affine normal form.
  have hrepr :
      ERealFunction.bivariateQuadraticKernel z w =
        fun p : H × H ↦
          (1 / 2 : ℝ) * ‖p.1 - z‖ ^ 2 + (1 / 2 : ℝ) * ‖p.2 - w‖ ^ 2
            - ⟪p.1, w⟫_ℝ - ⟪p.2, z⟫_ℝ + ⟪z, w⟫_ℝ := by
    funext p
    rcases p with ⟨x, u⟩
    simpa using bivariateQuadraticKernel_eq_separated_quadratic_affine (z := z) (w := w) x u
  rw [hrepr]
  -- Each quadratic coordinate term and each affine correction is continuous.
  have hfst_sq :
      Continuous (fun p : H × H ↦ (1 / 2 : ℝ) * ‖p.1 - z‖ ^ 2) := by
    exact continuous_const.mul ((continuous_norm.comp (continuous_fst.sub continuous_const)).pow 2)
  have hsnd_sq :
      Continuous (fun p : H × H ↦ (1 / 2 : ℝ) * ‖p.2 - w‖ ^ 2) := by
    exact continuous_const.mul ((continuous_norm.comp (continuous_snd.sub continuous_const)).pow 2)
  have hfst_inner : Continuous (fun p : H × H ↦ ⟪p.1, w⟫_ℝ) :=
    continuous_fst.inner continuous_const
  have hsnd_inner : Continuous (fun p : H × H ↦ ⟪p.2, z⟫_ℝ) :=
    continuous_snd.inner continuous_const
  exact (((hfst_sq.add hsnd_sq).sub hfst_inner).sub hsnd_inner).add continuous_const

/-- Helper for Theorem 20.46: the source quadratic kernel is convex on the full product space. -/
private theorem convexOn_univ_bivariateQuadraticKernel (z w : H) :
    _root_.ConvexOn ℝ (Set.univ : Set (H × H)) (ERealFunction.bivariateQuadraticKernel z w) := by
  have hrepr :
      ERealFunction.bivariateQuadraticKernel z w =
        fun p : H × H ↦
          (1 / 2 : ℝ) * dist p.1 z ^ 2 + (1 / 2 : ℝ) * dist p.2 w ^ 2
            - ⟪p.1, w⟫_ℝ - ⟪p.2, z⟫_ℝ + ⟪z, w⟫_ℝ := by
    funext p
    rcases p with ⟨x, u⟩
    simpa [dist_eq_norm] using
      bivariateQuadraticKernel_eq_separated_quadratic_affine (z := z) (w := w) x u
  rw [hrepr]
  -- The two squared-distance terms are convex after composing `dist` with the coordinate maps.
  have hfst_dist :
      _root_.ConvexOn ℝ (Set.univ : Set (H × H)) (fun p : H × H ↦ dist p.1 z) := by
    have hf : _root_.ConvexOn ℝ (Set.univ : Set H) (fun q : H ↦ dist q z) := convexOn_univ_dist z
    simpa using hf.comp_linearMap (ContinuousLinearMap.fst ℝ H H).toLinearMap
  have hsnd_dist :
      _root_.ConvexOn ℝ (Set.univ : Set (H × H)) (fun p : H × H ↦ dist p.2 w) := by
    have hf : _root_.ConvexOn ℝ (Set.univ : Set H) (fun q : H ↦ dist q w) := convexOn_univ_dist w
    simpa using hf.comp_linearMap (ContinuousLinearMap.snd ℝ H H).toLinearMap
  have hfst_sq :
      _root_.ConvexOn ℝ (Set.univ : Set (H × H))
        (fun p : H × H ↦ (1 / 2 : ℝ) * dist p.1 z ^ 2) := by
    have hsq := hfst_dist.pow (fun p _ ↦ dist_nonneg) 2
    simpa [smul_eq_mul] using hsq.smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hsnd_sq :
      _root_.ConvexOn ℝ (Set.univ : Set (H × H))
        (fun p : H × H ↦ (1 / 2 : ℝ) * dist p.2 w ^ 2) := by
    have hsq := hsnd_dist.pow (fun p _ ↦ dist_nonneg) 2
    simpa [smul_eq_mul] using hsq.smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  let Lw : (H × H) →L[ℝ] ℝ := (innerSL ℝ w).comp (ContinuousLinearMap.fst ℝ H H)
  let Lz : (H × H) →L[ℝ] ℝ := (innerSL ℝ z).comp (ContinuousLinearMap.snd ℝ H H)
  -- The affine corrections are handled as subtraction of concave linear maps.
  have hfst_concave :
      ConcaveOn ℝ (Set.univ : Set (H × H)) (fun p : H × H ↦ ⟪p.1, w⟫_ℝ) := by
    simpa [Lw, innerSL_apply_apply, real_inner_comm] using Lw.toLinearMap.concaveOn convex_univ
  have hsnd_concave :
      ConcaveOn ℝ (Set.univ : Set (H × H)) (fun p : H × H ↦ ⟪p.2, z⟫_ℝ) := by
    simpa [Lz, innerSL_apply_apply, real_inner_comm] using Lz.toLinearMap.concaveOn convex_univ
  -- Assemble the separated normal form and finish with the constant shift.
  exact (((hfst_sq.add hsnd_sq).sub hfst_concave).sub hsnd_concave).add_const ⟪z, w⟫_ℝ

/-- Helper for Theorem 20.46: the quadratic kernel packages canonically as a `Γ₀` function on the
product Hilbert space. -/
private theorem bivariateQuadraticKernel_mem_gammaZero (z w : H) :
    (ERealFunction.bivariateQuadraticKernel z w).toEReal ∈ Γ₀(H × H) := by
  -- Package the real-valued kernel through the standard `toEReal` bridge.
  simpa [Function.toEReal_apply] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (H := H × H)
      (ERealFunction.bivariateQuadraticKernel z w)
      (continuous_bivariateQuadraticKernel (z := z) (w := w))
      (convexOn_univ_bivariateQuadraticKernel (z := z) (w := w))

/-- Helper for Theorem 20.46: the quadratic kernel has full effective domain, so the source
regularity hypothesis against it reduces to the `dom g = univ` case. -/
private theorem bivariateQuadraticKernel_effectiveDomain_univ (z w : H) :
    effectiveDomain ((ERealFunction.bivariateQuadraticKernel z w).toEReal) =
      (Set.univ : Set (H × H)) := by
  simp [Function.effectiveDomain_toEReal]

/-- Helper for Theorem 20.46: if the second effective domain is all of `H × H`, then the
Fenchel-regularity hypothesis `0 ∈ sri (dom f - dom g)` holds automatically. -/
private theorem zero_mem_sri_sub_effectiveDomain_of_dom_univ
    {f g : H × H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H × H))
    (hdom : effectiveDomain g = (Set.univ : Set (H × H))) :
    ((0 : H), (0 : H)) ∈ sri (effectiveDomain f - effectiveDomain g) := by
  -- Rewrite the effective-domain difference against `univ`, then compute the strong relative
  -- interior exactly as in the one-space sibling.
  rw [hdom]
  obtain ⟨p, hp⟩ : (effectiveDomain f).Nonempty := ConvexOn.nonempty hf.2
  have hsub :
      effectiveDomain f - (Set.univ : Set (H × H)) = (Set.univ : Set (H × H)) := by
    ext q
    constructor
    · intro hq
      simp
    · intro hq
      exact Set.mem_sub.mpr ⟨p, hp, p - q, by simp, by abel⟩
  rw [hsub]
  rw [Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext q
  constructor
  · intro hq
    have hspan :
        Submodule.span ℝ (Set.range (fun x : H × H ↦ x - ((0 : H), (0 : H)))) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro q
      refine Submodule.subset_span ?_
      refine ⟨q, ?_⟩
      simp
    simp [hspan]
  · intro hq
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

/-- Helper for Theorem 20.46: the `(-u, -x)` symmetry from Lemma 20.45 is exactly the `g^* = g ∘
L` shape needed by Corollary 15.15. -/
private theorem bivariateQuadraticKernel_conjugate_eq_comp_negSwap (z w : H)
    (L : H × H →L[ℝ] H × H)
    (hL : ∀ p : H × H, L p = (-p.2, -p.1)) :
    ((ERealFunction.bivariateQuadraticKernel z w).toEReal).asEReal∗ =
      ((ERealFunction.bivariateQuadraticKernel z w).toEReal).asEReal ∘ L := by
  ext p
  rcases p with ⟨u, x⟩
  -- Evaluate the kernel conjugate at `(u, x)` and rewrite the target map through `L`.
  rw [Function.comp_apply, hL]
  simpa [Function.asEReal_apply, Function.toEReal_apply] using
    ERealFunction.bivariateQuadraticKernel_conjugate_apply (z := z) (w := w) x u

/-- Helper for Theorem 20.46: packaging `F∗∗` through `properIoi` does not change the next
Fenchel conjugation step, so the dual witness still evaluates against `F∗`. -/
private theorem properIoi_biconjugate_conjugate_apply
    (hbiconj_proper : IsProper F∗∗) (p : H × H) :
    (properIoi (F∗∗) hbiconj_proper).asEReal∗ p = F∗ p := by
  -- The packaged owner coerces back to `F∗∗`, hence its conjugate is the triple conjugate of `F`.
  change F∗∗∗ p = F∗ p
  simpa using congrFun (triple_conjugate_eq_conjugate (f := F)) p

/-- Helper for Theorem 20.46: if `F∗` is proper, then the source proof may package `F∗∗`
through `properIoi` because `F∗∗` is proper as well. -/
private theorem biconjugate_isProper_of_properConjugate
    [CompleteSpace H] (hFstar_proper : IsProper F∗) :
    IsProper F∗∗ := by
  -- `F∗` belongs to `Γ(H × H)` by conjugacy, so one more conjugation preserves properness.
  exact
    conjugate_is_proper_of_mem_gamma hFstar_proper
      (conjugate_mem_gamma (f := F))

/-- Helper for Theorem 20.46: for finite extended-real values, the contact identity `a = -b`
is equivalent to the zero-sum identity `a + b = 0`. -/
private theorem ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
    {a b : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥) :
    a = -b ↔ a + b = 0 := by
  constructor
  · intro hab
    have hab_real : a.toReal = -b.toReal := by
      apply_fun EReal.toReal at hab
      simpa [EReal.toReal_neg_eq] using hab
    have hsum_real : a.toReal + b.toReal = 0 := by
      linarith
    calc
      a + b = (((a.toReal : ℝ) : EReal)) + (((b.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]
      _ = (((a.toReal + b.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_add]
      _ = 0 := by
        exact congrArg (fun t : ℝ ↦ (t : EReal)) hsum_real
  · intro hsum
    have hsum_real : a.toReal + b.toReal = 0 := by
      apply EReal.coe_eq_coe_iff.mp
      calc
        (((a.toReal + b.toReal : ℝ) : EReal)) =
            (((a.toReal : ℝ) : EReal)) + (((b.toReal : ℝ) : EReal)) := by
              rw [EReal.coe_add]
        _ = a + b := by
          rw [EReal.coe_toReal ha_top ha_bot, EReal.coe_toReal hb_top hb_bot]
        _ = 0 := hsum
    have hab_real : a.toReal = -b.toReal := by
      linarith
    calc
      a = (((a.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_toReal ha_top ha_bot]
      _ = (((-b.toReal : ℝ) : EReal)) := by
        exact congrArg (fun t : ℝ ↦ (t : EReal)) hab_real
      _ = -b := by
        rw [EReal.coe_neg, EReal.coe_toReal hb_top hb_bot]

-- Proof sketch: if `(x, u)` and `(y, v)` satisfy the defining equality for `A`, convexity of
-- the Fenchel conjugate `(F∗)` from the canonical owner `conjugate_mem_gamma`, combined with the
-- lower bound `((F∗)ᵀ) ≥ ⟪·, ·⟫`, yields
-- `0 ≤ ⟪x - y, u - v⟫`.
/-- Theorem 20.46 (1): if the transpose-conjugate `((F∗)ᵀ)` dominates the pairing,
equivalently if `((F∗)ᵀ) (x, u) ≥ ⟪x, u⟫` for all `x, u`,
then its pairing-contact operator is monotone. -/
theorem pairingEqualityOperator_conjugateTranspose_isMonotone
    (hFstarT_ge : ∀ x u : H, pairing (x, u) ≤ ((F∗)ᵀ) (x, u))
    : (pairingEqualityOperator ((F∗)ᵀ)).IsMonotone := by
  -- Rewrite graph membership into the pairing-contact equalities and apply the midpoint helper.
  rw [SetValuedOperator.isMonotone_iff]
  intro x u y v hx hy
  exact conjugateTranspose_contact_midpoint_nonneg (F := F) hFstarT_ge hx hy

section HilbertSpace

variable [CompleteSpace H]

/-- Helper for Theorem 20.46: the linear symmetry `(x, u) ↦ (-u, -x)` used in the Corollary 15.15
duality step. -/
private abbrev negSwapContinuousLinearMap : H × H →L[ℝ] H × H :=
  (-ContinuousLinearMap.snd ℝ H H).prod (-ContinuousLinearMap.fst ℝ H H)

/-- Helper for Theorem 20.46: the linear symmetry map acts pointwise by swapping the coordinates
and negating both. -/
private theorem negSwapContinuousLinearMap_apply (p : H × H) :
    negSwapContinuousLinearMap (H := H) p = (-p.2, -p.1) :=
  rfl

/-- Helper for Theorem 20.46: Corollary 15.15 yields a normalized witness `(y, v)` satisfying the
source dual bound `F^*(v, y) + G(y, v) ≤ 0`. -/
private theorem dual_witness_exists_kernel_bound
    (hF_conv : IsConvex F) (hFstar_proper : IsProper F∗)
    (hF_ge : ∀ x u : H, pairing (x, u) ≤ F (x, u))
    (z w : H) :
    ∃ y v : H, F∗ (v, y) + ERealFunction.bivariateQuadraticKernel z w (y, v) ≤ 0 := by
  let hbiconj_proper := biconjugate_isProper_of_properConjugate (F := F) hFstar_proper
  let f : H × H → Set.Ioi (⊥ : EReal) := properIoi (F∗∗) hbiconj_proper
  let g : H × H → Set.Ioi (⊥ : EReal) := (ERealFunction.bivariateQuadraticKernel z w).toEReal
  let L : H × H →L[ℝ] H × H := negSwapContinuousLinearMap (H := H)
  have hf_gamma : f ∈ Γ₀(H × H) := by
    -- Package `F**` through `properIoi`; one more conjugation keeps it in `Γ(H × H)`.
    exact properIoi_mem_gammaZero_of_mem_gamma hbiconj_proper (conjugate_mem_gamma (f := F∗))
  have hg_gamma : g ∈ Γ₀(H × H) :=
    bivariateQuadraticKernel_mem_gammaZero (H := H) (z := z) (w := w)
  have hsri : ((0 : H), (0 : H)) ∈ sri (effectiveDomain f - effectiveDomain g) := by
    -- The kernel has full effective domain, so the regularity condition is automatic.
    exact zero_mem_sri_sub_effectiveDomain_of_dom_univ (H := H) hf_gamma
      (bivariateQuadraticKernel_effectiveDomain_univ (H := H) (z := z) (w := w))
  have hbiconj_ge :
      ∀ p : H × H, pairing p ≤ F∗∗ p := by
    -- The source lower bound on `F` passes to `F**`.
    refine pairing_le_biconjugate_of_convex_of_properConjugate (F := F) hF_conv hFstar_proper ?_
    intro p
    rcases p with ⟨x, u⟩
    exact hF_ge x u
  have hfg_nonneg : ∀ p : H × H, (0 : EReal) ≤ primalObjective f g p := by
    intro p
    rcases p with ⟨x, u⟩
    have hkernel_nonneg :
        (0 : EReal) ≤ pairing (x, u) + ((ERealFunction.bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) := by
      -- Lemma 20.45(ii) gives the nonnegativity of `G + ⟪·, ·⟫`.
      have hkernel_nonneg_real :
          (0 : EReal) ≤
            (((ERealFunction.bivariateQuadraticKernel z w (x, u) + ⟪x, u⟫_ℝ : ℝ) : EReal)) := by
        exact_mod_cast
          (ERealFunction.bivariateQuadraticKernel_add_pairing_nonneg
            (H := H) (z := z) (w := w) x u)
      simpa [pairing_apply, EReal.coe_add, add_comm] using hkernel_nonneg_real
    have hshift :
        pairing (x, u) + ((ERealFunction.bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) ≤
          F∗∗ (x, u) + ((ERealFunction.bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) :=
      by
        simpa [add_comm] using
          add_le_add_right
            (hbiconj_ge (x, u))
            (((ERealFunction.bivariateQuadraticKernel z w (x, u) : ℝ) : EReal))
    -- Replace the packaged primal objective by the concrete sum `F** + G`.
    calc
      (0 : EReal) ≤ pairing (x, u) + ((ERealFunction.bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) :=
        hkernel_nonneg
      _ ≤ F∗∗ (x, u) + ((ERealFunction.bivariateQuadraticKernel z w (x, u) : ℝ) : EReal) :=
        hshift
      _ = primalObjective f g (x, u) := by
        simp [f, g, ERealFunction.primalObjective_apply]
  have hL :
      ∀ p : H × H, L p = (-p.2, -p.1) := by
    intro p
    exact negSwapContinuousLinearMap_apply (H := H) p
  have hg_conj :
      g.asEReal∗ = g.asEReal ∘ L :=
    bivariateQuadraticKernel_conjugate_eq_comp_negSwap (H := H) (z := z) (w := w) L hL
  obtain ⟨q, hq⟩ :=
    ERealFunction.exists_dual_vector_le_zero_of_pointwiseAdd_nonneg_and_conjugate_eq_comp
      f g hf_gamma hg_gamma hsri L hfg_nonneg hg_conj
  have hq' :
      F∗ (-q) + ERealFunction.bivariateQuadraticKernel z w (L q) ≤ 0 := by
    rw [← properIoi_biconjugate_conjugate_apply (F := F) hbiconj_proper (-q)]
    simpa [f, g] using hq
  refine ⟨-q.2, -q.1, ?_⟩
  -- Rewrite the Corollary 15.15 witness into the source-oriented `(y, v)` coordinates.
  change F∗ (-q) + ERealFunction.bivariateQuadraticKernel z w (L q) ≤ 0
  exact hq'

/-- Helper for Theorem 20.46: if the dual witness inequality is squeezed between
`F^*(v, y) ≥ ⟪y, v⟫` and `G(y, v) + ⟪y, v⟫ ≥ 0`, then both inequalities are equalities. -/
private theorem dual_witness_contact_of_pairing_le_and_kernel_nonneg
    {z w y v : H}
    (hFstar_proper : IsProper F∗)
    (hpair_le : pairing (y, v) ≤ F∗ (v, y))
    (hkernel_nonneg : 0 ≤ ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ)
    (hdual : F∗ (v, y) + ERealFunction.bivariateQuadraticKernel z w (y, v) ≤ 0) :
    F∗ (v, y) = pairing (y, v) ∧
      ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ = 0 := by
  have hpair_kernel_nonneg :
      (0 : EReal) ≤ pairing (y, v) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
    -- Convert the real nonnegativity `G(y, v) + ⟪y, v⟫ ≥ 0` to the owner-valued pairing form.
    have hpair_kernel_nonneg_real :
        (0 : EReal) ≤
          (((ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ : ℝ) : EReal)) := by
      exact_mod_cast hkernel_nonneg
    simpa [pairing_apply, EReal.coe_add, add_comm] using hpair_kernel_nonneg_real
  have hpair_kernel_le :
      pairing (y, v) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤ 0 := by
    -- The lower bound `⟪y, v⟫ ≤ F^*(v, y)` upgrades the same sum to the dual-witness sum.
    have hshift :
        pairing (y, v) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤
          F∗ (v, y) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
      simpa [add_comm] using
        add_le_add_right hpair_le
          (((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal))
    exact le_trans hshift hdual
  have hpair_kernel_zero_ereal :
      (((ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ : ℝ) : EReal)) = 0 := by
    have hzero :
        pairing (y, v) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) = 0 :=
      le_antisymm hpair_kernel_le hpair_kernel_nonneg
    simpa [pairing_apply, EReal.coe_add, add_comm] using hzero
  have hkernel_zero :
      ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ = 0 :=
    EReal.coe_eq_coe_iff.mp hpair_kernel_zero_ereal
  have hdual_nonneg :
      (0 : EReal) ≤ F∗ (v, y) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
    have hshift :
        pairing (y, v) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) ≤
          F∗ (v, y) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) := by
      simpa [add_comm] using
        add_le_add_right hpair_le
          (((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal))
    exact le_trans hpair_kernel_nonneg hshift
  have hdual_zero :
      F∗ (v, y) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) = 0 :=
    le_antisymm hdual hdual_nonneg
  have hFstar_ne_bot : F∗ (v, y) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpair_le
    exact not_le_of_gt (by simpa [pairing_apply] using (EReal.bot_lt_coe ⟪y, v⟫_ℝ)) hpair_le
  have hkernel_ne_top :
      (((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal)) ≠ ⊤ :=
    EReal.coe_ne_top _
  have hkernel_ne_bot :
      (((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal)) ≠ ⊥ :=
    EReal.coe_ne_bot _
  have hFstar_ne_top : F∗ (v, y) ≠ ⊤ := by
    intro htop
    have hsum_top :
        F∗ (v, y) + ((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal) = ⊤ := by
      rw [htop]
      exact EReal.top_add_of_ne_bot hkernel_ne_bot
    exact EReal.zero_ne_top (hdual_zero.symm.trans hsum_top)
  have hpair_ne_top : pairing (y, v) ≠ ⊤ := by
    simpa [pairing_apply] using (EReal.coe_ne_top ⟪y, v⟫_ℝ)
  have hpair_ne_bot : pairing (y, v) ≠ ⊥ := by
    simpa [pairing_apply] using (EReal.coe_ne_bot ⟪y, v⟫_ℝ)
  have hFstar_eq_neg :
      F∗ (v, y) = -(((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal)) := by
    exact
      (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
        hFstar_ne_top hFstar_ne_bot hkernel_ne_top hkernel_ne_bot).2 hdual_zero
  have hpair_eq_neg :
      pairing (y, v) = -(((ERealFunction.bivariateQuadraticKernel z w (y, v) : ℝ) : EReal)) := by
    exact
      (ereal_eq_neg_iff_add_eq_zero_of_ne_top_ne_bot
        hpair_ne_top hpair_ne_bot hkernel_ne_top hkernel_ne_bot).2 <| by
          simpa [pairing_apply, EReal.coe_add, add_comm] using hpair_kernel_zero_ereal
  constructor
  · -- Both the dual value and the pairing equal `-G(y, v)`, so the contact identity holds.
    exact hFstar_eq_neg.trans hpair_eq_neg.symm
  · -- The real equality is exactly the squeezed kernel contact from the source proof.
    exact hkernel_zero

/-- Helper for Theorem 20.46: the normalized Corollary 15.15 witness lies in the graph of the
pairing-equality operator, and it carries the zero-kernel identity needed for the rigidity step. -/
private theorem dual_witness_mem_pairingEqualityOperator_of_dual_bound
    (hFstarT_ge : ∀ x u : H, pairing (x, u) ≤ ((F∗)ᵀ) (x, u))
    (hFstar_proper : IsProper F∗)
    {z w y v : H}
    (hdual : F∗ (v, y) + ERealFunction.bivariateQuadraticKernel z w (y, v) ≤ 0) :
    v ∈ pairingEqualityOperator ((F∗)ᵀ) y ∧
      ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ = 0 := by
  have hpair_le : pairing (y, v) ≤ F∗ (v, y) := by
    -- The transpose-conjugate lower bound is exactly the source inequality `⟪y, v⟫ ≤ F^*(v, y)`.
    simpa [transpose_apply] using hFstarT_ge y v
  obtain ⟨hcontact, hkernel_zero⟩ :=
    dual_witness_contact_of_pairing_le_and_kernel_nonneg (F := F) hFstar_proper hpair_le
      (ERealFunction.bivariateQuadraticKernel_add_pairing_nonneg (H := H) (z := z) (w := w) y v)
      hdual
  constructor
  · -- Repackage the contact equality as graph membership in `pairingEqualityOperator ((F∗)ᵀ)`.
    rw [mem_pairingEqualityOperator_iff]
    simpa [transpose_apply] using hcontact
  · exact hkernel_zero

/-- Helper for Theorem 20.46: Lemma 20.45(iv) identifies the normalized witness with the target
pair once the kernel vanishes and the monotonicity relation supplies the cross inequality. -/
private theorem dual_witness_eq_target_of_kernel_zero_and_cross_nonneg
    {z w y v : H}
    (hkernel_zero : ERealFunction.bivariateQuadraticKernel z w (y, v) + ⟪y, v⟫_ℝ = 0)
    (hcross : 0 ≤ ⟪z - y, w - v⟫_ℝ) :
    (y, v) = (z, w) := by
  -- Lemma 20.45(iv) is the source rigidity step closing the maximality argument.
  exact
    (ERealFunction.bivariateQuadraticKernel_zero_pairing_and_cross_nonneg_iff
      (H := H) (z := z) (w := w) y v).1 ⟨hkernel_zero, hcross⟩

-- Proof sketch: apply the maximal-monotonicity graph criterion. For a pair monotonically related
-- to every point of the graph, combine the quadratic kernel from Lemma 20.45 with the lower
-- bounds `F ≥ ⟪·, ·⟫` and `((F∗)ᵀ) ≥ ⟪·, ·⟫`
-- to force equality in the Fenchel relation
-- and recover
-- graph membership.
/-- Theorem 20.46 (2): on a real Hilbert space, if moreover `F(x, u) ≥ ⟪x, u⟫` for all `x, u`,
then the same operator is maximally monotone. The lower bound on the conjugate is stated in the
canonical transpose-conjugate form `((F∗)ᵀ) (x, u) ≥ ⟪x, u⟫`. -/
theorem pairingEqualityOperator_conjugateTranspose_isMaximallyMonotone
    (hFstarT_ge : ∀ x u : H, pairing (x, u) ≤ ((F∗)ᵀ) (x, u))
    (hF_conv : IsConvex F) (hFstar_proper : IsProper F∗)
    (hF_ge : ∀ x u : H, pairing (x, u) ≤ F (x, u))
    : Maximal IsMonotone (pairingEqualityOperator ((F∗)ᵀ)) := by
  -- Route correction: keep the source Corollary 15.15 witness route. The theorem-local helpers
  -- only cache the dual-witness squeeze and the Lemma 20.45(iv) rigidity step, so the Chapter 20
  -- argument stays source-faithful while the main theorem remains flat.
  rw [SetValuedOperator.maximal_iff_mem_iff]
  intro z w
  constructor
  · intro hwA y v hvA
    -- The forward implication is just monotonicity of the contact operator.
    exact (SetValuedOperator.isMonotone_iff (pairingEqualityOperator ((F∗)ᵀ))).1
      (pairingEqualityOperator_conjugateTranspose_isMonotone (F := F) hFstarT_ge) hwA hvA
  · intro hmono_rel
    obtain ⟨y, v, hdual⟩ :=
      dual_witness_exists_kernel_bound (F := F) hF_conv hFstar_proper hF_ge z w
    obtain ⟨hvA, hkernel_zero⟩ :=
      dual_witness_mem_pairingEqualityOperator_of_dual_bound (F := F) hFstarT_ge hFstar_proper
        hdual
    have hcross : 0 ≤ ⟪z - y, w - v⟫_ℝ := hmono_rel hvA
    have hyv_eq : (y, v) = (z, w) := by
      -- The final rigidity step is factored out so the main theorem follows the source skeleton.
      exact dual_witness_eq_target_of_kernel_zero_and_cross_nonneg
        (H := H) (z := z) (w := w) hkernel_zero hcross
    cases hyv_eq
    simpa using hvA

end HilbertSpace

end BivariateFenchelEquality

end

end SetValuedOperator
