import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap01.Theorem_1_50
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap22.Definition_22_1
import BauschkeLean.Chap23.Proposition_23_2
import BauschkeLean.Chap23.Proposition_23_13
import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap26.Proposition_26_1
import BauschkeLean.Chap26.Text_26_0_1

open Filter
open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Proposition 26.16 is the constrained forward-backward recursion on `D` together
  with its linear convergence conclusions.
- `core/canonical`: the reusable owners are the Chapter 23 resolvent `J[((γ : ℝ) • A)]`, the
  singleton-valued restriction `ofFunction D B`, and the Chapter 26 owner
  `primal_inclusion_solution_set A (ofFunction D B)`.
- `bridge/view`: when `A` is maximally monotone, the orbit step can be rewritten using the chosen
  single-valued realizer `resolventMap A hA γ`, and equivalently as the affine inclusion from
  Remark 26.15.
Semantic recall note: `lean_leansearch` did not surface a dedicated constrained forward-backward
owner, so this item keeps the source recursion as a subtype-valued orbit on `D` and bridges to the
verified Chapter 23 singleton resolvent API only through companion lemmas. -/

section Basic

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- A sequence `x : ℕ → D` follows the forward-backward recursion for `(A, B)` with step `γ`
when each iterate belongs to the resolvent value
`J[((γ : ℝ) • A)] (x n - (γ : ℝ) • B (x n))`. -/
structure IsForwardBackwardOrbit
    (D : Set H) (A : SetValuedOperator H H) (B : D → H) (γ : PosReal)
    (x : ℕ → D) : Prop where
  /-- The forward-backward update is `x_{n+1} ∈ J_{γ A} (x_n - γ B x_n)`. -/
  step (n : ℕ) :
    J[((γ : ℝ) • A)] (x n - (γ : ℝ) • B (x n)) (x (n + 1))

namespace IsForwardBackwardOrbit

variable {D : Set H} {A : SetValuedOperator H H} {B : D → H} {γ : PosReal} {x : ℕ → D}

/-
The orbit step is equivalently the residual inclusion
`x_n - γ • B x_n - x_{n+1} ∈ γ • A x_{n+1}`.
-/
theorem step_sub_mem_smul (hOrbit : IsForwardBackwardOrbit D A B γ x) (n : ℕ) :
    x n - (γ : ℝ) • B (x n) - x (n + 1) ∈ (γ : ℝ) • A (x (n + 1)) := by
  simpa using
    (mem_resolvent_smul_iff_sub_mem_smul A γ
      (x n - (γ : ℝ) • B (x n)) (x (n + 1))).1 (hOrbit.step n)

end IsForwardBackwardOrbit

end Basic

noncomputable section

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace IsForwardBackwardOrbit

variable {D : Set H} {A : SetValuedOperator H H} {B : D → H} {γ : PosReal} {x : ℕ → D}

/-- For maximally monotone `A`, the resolvent membership step is equivalent to the equality with
the chosen single-valued resolvent realizer `resolventMap A hA γ`. -/
theorem step_eq_resolventMap (hOrbit : IsForwardBackwardOrbit D A B γ x)
    (hA : Maximal IsMonotone A) (n : ℕ) :
    x (n + 1) = resolventMap A hA γ (x n - (γ : ℝ) • B (x n)) := by
  have hstep := hOrbit.step n
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ
      (x n - (γ : ℝ) • B (x n))] at hstep
  simpa using hstep

end IsForwardBackwardOrbit

/-- Helper for Proposition 26.16: scaling a strongly monotone operator by `γ ∈ ℝ_{++}` rescales
the strong-monotonicity constant by the same factor. -/
private theorem IsStronglyMonotone.smul_posReal
    {A : SetValuedOperator H H} {α : ℝ} (hA : A.IsStronglyMonotone α) (γ : PosReal) :
    ((γ : ℝ) • A).IsStronglyMonotone (α * (γ : ℝ)) := by
  -- Rewriting membership in the scaled graph reduces the claim to the original lower bound.
  refine ⟨mul_pos hA.pos γ.2, ?_⟩
  intro x u y v hu hv
  rw [Pi.smul_apply] at hu hv
  rcases Set.mem_smul_set.mp hu with ⟨u', hu', rfl⟩
  rcases Set.mem_smul_set.mp hv with ⟨v', hv', rfl⟩
  have hineq : α * ‖x - y‖ ^ 2 ≤ ⟪x - y, u' - v'⟫_ℝ := hA.ineq hu' hv'
  have hmul :
      (γ : ℝ) * (α * ‖x - y‖ ^ 2) ≤ (γ : ℝ) * ⟪x - y, u' - v'⟫_ℝ := by
    exact mul_le_mul_of_nonneg_left hineq γ.2.le
  calc
    (α * (γ : ℝ)) * ‖x - y‖ ^ 2 = (γ : ℝ) * (α * ‖x - y‖ ^ 2) := by ring
    _ ≤ (γ : ℝ) * ⟪x - y, u' - v'⟫_ℝ := hmul
    _ = ⟪x - y, (γ : ℝ) • u' - (γ : ℝ) • v'⟫_ℝ := by
          rw [← smul_sub, real_inner_smul_right]

/-- Helper for Proposition 26.16: if `A` is `α`-strongly monotone, then the canonical resolvent
`resolventMap A hA_max γ` is a contraction with factor `1 / (α * γ + 1)`. -/
theorem resolventMap_contractingWith_of_isStronglyMonotone
    {A : SetValuedOperator H H} (hA_max : Maximal IsMonotone A) {α : ℝ}
    (hA_strong : A.IsStronglyMonotone α) (γ : PosReal) :
    ContractingWith (Real.toNNReal (1 / (α * (γ : ℝ) + 1))) (resolventMap A hA_max γ) := by
  let αγ : PosReal := ⟨α * (γ : ℝ), mul_pos hA_strong.pos γ.2⟩
  have hscaled : ((γ : ℝ) • A).IsStronglyMonotone (αγ : ℝ) := by
    -- The Chapter 23 resolvent estimate applies after rescaling the graph by `γ`.
    simpa [αγ, mul_comm] using hA_strong.smul_posReal γ
  have hK : (1 / ((αγ : ℝ) + 1)) ∈ Set.Ioo (0 : ℝ) 1 := inv_one_add_mem_Ioo_zero_one αγ
  have hK_nonneg : 0 ≤ 1 / (α * (γ : ℝ) + 1) := by
    exact le_of_lt (by simpa [αγ, mul_comm] using hK.1)
  -- The resolvent witnesses are the singleton graph points produced by maximality.
  refine ⟨by simpa [Real.toNNReal_of_nonneg hK_nonneg, αγ, mul_comm] using hK.2, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hx : resolventMap A hA_max γ x ∈ J[((γ : ℝ) • A)] x := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA_max γ x]
    simp
  have hy : resolventMap A hA_max γ y ∈ J[((γ : ℝ) • A)] y := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA_max γ y]
    simp
  have hdist :
      ‖resolventMap A hA_max γ x - resolventMap A hA_max γ y‖ ≤
        (1 / ((αγ : ℝ) + 1)) * ‖x - y‖ :=
    norm_sub_le_inv_one_add_mul_norm_sub_of_mem_resolvent αγ hscaled hx hy
  have hcoef :
      (Real.toNNReal (1 / (α * (γ : ℝ) + 1)) : ℝ) = 1 / ((αγ : ℝ) + 1) := by
    rw [Real.toNNReal_of_nonneg hK_nonneg]
    simp [αγ]
  calc
    dist (resolventMap A hA_max γ x) (resolventMap A hA_max γ y) =
        ‖resolventMap A hA_max γ x - resolventMap A hA_max γ y‖ := by
          rw [dist_eq_norm]
    _ ≤ (1 / ((αγ : ℝ) + 1)) * ‖x - y‖ := hdist
    _ = (Real.toNNReal (1 / (α * (γ : ℝ) + 1)) : ℝ) * dist x y := by
          rw [hcoef, dist_eq_norm]

/-- Helper for Proposition 26.16: the canonical resolvent map is nonexpansive because firm
nonexpansiveness implies the norm bound `‖Tx - Ty‖ ≤ ‖x - y‖`. -/
theorem resolventMap_lipschitzWith_one
    {A : SetValuedOperator H H} (hA_max : Maximal IsMonotone A) (γ : PosReal) :
    LipschitzWith 1 (resolventMap A hA_max γ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hfirm :
      ‖resolventMap A hA_max γ x - resolventMap A hA_max γ y‖ ^ 2 +
          ‖(x - resolventMap A hA_max γ x) - (y - resolventMap A hA_max γ y)‖ ^ 2 ≤
        ‖x - y‖ ^ 2 := by
    -- Corollary 23.11 gives the firm resolvent inequality on the whole space.
    exact (firmlyNonexpansiveOn_iff.1 (resolventMap_firmlyNonexpansiveOn_univ A hA_max γ))
      x (by simp) y (by simp)
  have hsq :
      ‖resolventMap A hA_max γ x - resolventMap A hA_max γ y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [hfirm]
  have hdist :
      ‖resolventMap A hA_max γ x - resolventMap A hA_max γ y‖ ≤ ‖x - y‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  simpa [dist_eq_norm, one_mul] using hdist

/-- Helper for Proposition 26.16: if `B` is `β`-cocoercive and `γ < 2β`, then the residual map
`Id - γ B` is nonexpansive on `D`. -/
theorem idSubGammaBLipschitzWith_one_of_cocoercive
    {D : Set H} {B : D → H}
    (β γ : PosReal) (hB_coco : CocoerciveOn (β : ℝ) D B) (hγ_lt : (γ : ℝ) < 2 * (β : ℝ)) :
    LipschitzWith 1 (fun x : D ↦ (x : H) - (γ : ℝ) • B x) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hcoco :
      (β : ℝ) * ‖B x - B y‖ ^ 2 ≤ ⟪(x : H) - y, B x - B y⟫_ℝ := hB_coco.ineq x y
  have hnorm :
      ‖((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)‖ ^ 2 =
        ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ⟪(x : H) - y, B x - B y⟫_ℝ +
          (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 := by
    have hrewrite :
        (((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)) =
          ((x : H) - y) - (γ : ℝ) • (B x - B y) := by
      rw [smul_sub]
      abel_nf
    calc
      ‖((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)‖ ^ 2
          = ‖((x : H) - y) - (γ : ℝ) • (B x - B y)‖ ^ 2 := by rw [hrewrite]
      _ = ‖(x : H) - y‖ ^ 2 -
            2 * ⟪(x : H) - y, (γ : ℝ) • (B x - B y)⟫_ℝ +
            ‖(γ : ℝ) • (B x - B y)‖ ^ 2 := by
              simpa using norm_sub_sq_real ((x : H) - y) ((γ : ℝ) • (B x - B y))
      _ = ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ⟪(x : H) - y, B x - B y⟫_ℝ +
            (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 := by
              rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg γ.2.le]
              ring
  have hsq :
      ‖((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
    have hinner_term :
        -2 * (γ : ℝ) * ⟪(x : H) - y, B x - B y⟫_ℝ ≤
          -2 * (γ : ℝ) * ((β : ℝ) * ‖B x - B y‖ ^ 2) := by
      nlinarith [hcoco, γ.2]
    have hbound :
        ‖((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ((β : ℝ) * ‖B x - B y‖ ^ 2) +
            (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 := by
      rw [hnorm]
      linarith
    have hcoef_nonpos : (γ : ℝ) ^ 2 - 2 * (γ : ℝ) * (β : ℝ) ≤ 0 := by
      nlinarith [hγ_lt, γ.2, β.2]
    calc
      ‖((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)‖ ^ 2
          ≤ ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ((β : ℝ) * ‖B x - B y‖ ^ 2) +
              (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 := hbound
      _ = ‖(x : H) - y‖ ^ 2 + ((γ : ℝ) ^ 2 - 2 * (γ : ℝ) * (β : ℝ)) * ‖B x - B y‖ ^ 2 := by
            ring
      _ ≤ ‖(x : H) - y‖ ^ 2 := by
            have hsq_nonneg : 0 ≤ ‖B x - B y‖ ^ 2 := sq_nonneg ‖B x - B y‖
            nlinarith
  have hdist :
      ‖((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)‖ ≤ ‖(x : H) - y‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hdist

/-- Helper for Proposition 26.16: the forward-backward resolvent step always lands back in `D`
because the resolvent range is `A.dom` and `A.dom ⊆ D`. -/
theorem forwardBackwardStep_mem_domain
    {D : Set H} {A : SetValuedOperator H H} {B : D → H}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (γ : PosReal) (x : D) :
    resolventMap A hA_max γ ((x : H) - (γ : ℝ) • B x) ∈ D := by
  -- The resolvent image lies in `A.dom`, then the domain hypothesis returns it to `D`.
  have hx_dom :
      resolventMap A hA_max γ ((x : H) - (γ : ℝ) • B x) ∈ A.dom := by
    rw [← range_resolvent_smul_eq_dom A γ, SetValuedOperator.mem_range_iff]
    refine ⟨(x : H) - (γ : ℝ) • B x, ?_⟩
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA_max γ
      ((x : H) - (γ : ℝ) • B x)]
    simp
  exact hA_dom hx_dom

/-- Helper for Proposition 26.16: the constrained forward-backward step defines a self-map of
`D`. -/
def forwardBackwardSelfMap
    (D : Set H) (A : SetValuedOperator H H) (B : D → H)
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (γ : PosReal) : D → D :=
  fun x ↦
    ⟨resolventMap A hA_max γ ((x : H) - (γ : ℝ) • B x),
      forwardBackwardStep_mem_domain (D := D) (A := A) (B := B) hA_max hA_dom γ x⟩

/-- Helper for Proposition 26.16: on points of `D`, primal inclusion membership is equivalent to
the graph condition `-B z ∈ A z`. -/
theorem mem_primalInclusionSolution_iff_neg_mem
    {D : Set H} {A : SetValuedOperator H H} {B : D → H} (z : D) :
    ((z : H) ∈ primal_inclusion_solution_set A (ofFunction D B)) ↔ -B z ∈ A z := by
  rw [mem_primal_inclusion_solution_set, ofFunction_apply_of_mem D B z.2, Set.mem_add]
  constructor
  · intro hz
    rcases hz with ⟨a, ha, b, hb, hab⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    have ha_eq : a = -B z := by
      simpa [eq_neg_iff_add_eq_zero] using hab
    simpa [ha_eq] using ha
  · intro hz
    refine ⟨-B z, hz, B z, by simp, ?_⟩
    abel_nf

/-- Helper for Proposition 26.16: every primal inclusion solution belongs to the constraint set
`D`. -/
theorem primalInclusionSolution_mem_domain
    {D : Set H} {A : SetValuedOperator H H} {B : D → H} {z : H}
    (hz : z ∈ primal_inclusion_solution_set A (ofFunction D B)) :
    z ∈ D := by
  by_contra hzD
  have hzero : (0 : H) ∈ (∅ : Set H) := by
    simpa [mem_primal_inclusion_solution_set, ofFunction_apply_of_not_mem D B hzD] using hz
  simpa using hzero

/-- Helper for Proposition 26.16: fixed points of the constrained forward-backward self-map are
exactly primal inclusion solutions. -/
theorem isFixedPt_forwardBackwardSelfMap_iff_mem_primalInclusionSolution
    {D : Set H} {A : SetValuedOperator H H} {B : D → H}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (γ : PosReal) (z : D) :
    Function.IsFixedPt (forwardBackwardSelfMap D A B hA_max hA_dom γ) z ↔
      ((z : H) ∈ primal_inclusion_solution_set A (ofFunction D B)) := by
  constructor
  · intro hzfix
    -- Coercing the fixed-point equation exposes the resolvent identity in the ambient space.
    have hEq :
        resolventMap A hA_max γ ((z : H) - (γ : ℝ) • B z) = z := by
      exact congrArg Subtype.val hzfix.eq
    have hneg : -B z ∈ A z := by
      exact (resolventMap_sub_smul_eq_iff_neg_mem A hA_max γ (z : H) (B z)).1 hEq
    exact (mem_primalInclusionSolution_iff_neg_mem (D := D) (A := A) (B := B) z).2 hneg
  · intro hz
    -- The primal inclusion gives the graph witness needed to rebuild the fixed-point equation.
    have hneg : -B z ∈ A z :=
      (mem_primalInclusionSolution_iff_neg_mem (D := D) (A := A) (B := B) z).1 hz
    have hEq :
        resolventMap A hA_max γ ((z : H) - (γ : ℝ) • B z) = z := by
      exact (resolventMap_sub_smul_eq_iff_neg_mem A hA_max γ (z : H) (B z)).2 hneg
    show forwardBackwardSelfMap D A B hA_max hA_dom γ z = z
    apply Subtype.ext
    simpa [forwardBackwardSelfMap] using hEq

/-- Helper for Proposition 26.16: a forward-backward orbit is exactly the iterate sequence of the
constrained forward-backward self-map on `D`. -/
theorem forwardBackwardOrbit_eq_iterate_selfMap
    {D : Set H} {A : SetValuedOperator H H} {B : D → H}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (γ : PosReal) {x : ℕ → D} (hOrbit : IsForwardBackwardOrbit D A B γ x) :
    ∀ n : ℕ, x n = (forwardBackwardSelfMap D A B hA_max hA_dom γ)^[n] (x 0) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n hn =>
      -- Rewrite one orbit step by the resolvent realizer, then substitute the iterate formula.
      apply Subtype.ext
      calc
        ((x (n + 1) : D) : H) =
            resolventMap A hA_max γ ((x n : H) - (γ : ℝ) • B (x n)) := by
              simpa using hOrbit.step_eq_resolventMap hA_max n
        _ =
            resolventMap A hA_max γ
              ((((forwardBackwardSelfMap D A B hA_max hA_dom γ)^[n] (x 0) : D) : H) -
                (γ : ℝ) • B ((forwardBackwardSelfMap D A B hA_max hA_dom γ)^[n] (x 0))) := by
              simpa [hn]
        _ =
            (((forwardBackwardSelfMap D A B hA_max hA_dom γ)
              ((forwardBackwardSelfMap D A B hA_max hA_dom γ)^[n] (x 0)) : D) : H) := by
              rfl
        _ =
            (((forwardBackwardSelfMap D A B hA_max hA_dom γ)^[n + 1] (x 0) : D) : H) := by
              rw [Function.iterate_succ_apply']

/-- Helper for Proposition 26.16: in case (ii), the residual step `Id - γ B` satisfies the
textbook squared-distance estimate `(26.64)` on `D`. -/
theorem idSubGammaB_norm_sq_le_of_ofFunction_isStronglyMonotone_of_lipschitz
    {D : Set H} {B : D → H}
    (α β γ : PosReal) (hB_strong : (ofFunction D B).IsStronglyMonotone (α : ℝ))
    (hB_lipschitz : LipschitzWith (Real.toNNReal (β : ℝ)) B)
    (x y : D) :
    ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2 ≤
      (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)) * ‖(x : H) - y‖ ^ 2 := by
  have hx_mem : B x ∈ ofFunction D B x := by
    rw [ofFunction_apply_of_mem D B x.2]
    simp
  have hy_mem : B y ∈ ofFunction D B y := by
    rw [ofFunction_apply_of_mem D B y.2]
    simp
  have hstrong_inner :
      (α : ℝ) * ‖(x : H) - y‖ ^ 2 ≤ ⟪(x : H) - y, B x - B y⟫_ℝ := by
    -- Strong monotonicity is applied to the graph witnesses coming from `ofFunction`.
    simpa using hB_strong.ineq hx_mem hy_mem
  have hLip_norm :
      ‖B x - B y‖ ≤ (β : ℝ) * ‖(x : H) - y‖ := by
    -- Rewrite the Lipschitz bound from `dist` on the subtype to ambient norms.
    have hβ_max : max (β : ℝ) 0 = (β : ℝ) := max_eq_left β.2.le
    simpa [Subtype.dist_eq, dist_eq_norm, one_mul, hβ_max] using hB_lipschitz.dist_le_mul x y
  have hLip_sq :
      ‖B x - B y‖ ^ 2 ≤ (β : ℝ) ^ 2 * ‖(x : H) - y‖ ^ 2 := by
    have hsq :=
      (sq_le_sq₀ (norm_nonneg (B x - B y))
        (mul_nonneg β.2.le (norm_nonneg ((x : H) - y)))).2 hLip_norm
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hnorm :
      ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2 =
        ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ⟪(x : H) - y, B x - B y⟫_ℝ +
          (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 := by
    have hrewrite :
        (((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y)) =
          ((x : H) - y) - (γ : ℝ) • (B x - B y) := by
      rw [smul_sub]
      abel_nf
    calc
      ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2
          = ‖((x : H) - y) - (γ : ℝ) • (B x - B y)‖ ^ 2 := by rw [hrewrite]
      _ = ‖(x : H) - y‖ ^ 2 -
            2 * ⟪(x : H) - y, (γ : ℝ) • (B x - B y)⟫_ℝ +
            ‖(γ : ℝ) • (B x - B y)‖ ^ 2 := by
              simpa using norm_sub_sq_real ((x : H) - y) ((γ : ℝ) • (B x - B y))
      _ = ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ⟪(x : H) - y, B x - B y⟫_ℝ +
            (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 := by
              rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg γ.2.le]
              ring
  -- The textbook estimate is exactly the strong-monotonicity lower bound plus the Lipschitz upper
  -- bound inserted into the expanded square.
  have hbound :
      ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2 ≤
        ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ((α : ℝ) * ‖(x : H) - y‖ ^ 2) +
          (γ : ℝ) ^ 2 * ((β : ℝ) ^ 2 * ‖(x : H) - y‖ ^ 2) := by
    have hinner_term :
        -2 * (γ : ℝ) * ⟪(x : H) - y, B x - B y⟫_ℝ ≤
          -2 * (γ : ℝ) * ((α : ℝ) * ‖(x : H) - y‖ ^ 2) := by
      nlinarith [hstrong_inner, γ.2]
    have hsq_term :
        (γ : ℝ) ^ 2 * ‖B x - B y‖ ^ 2 ≤
          (γ : ℝ) ^ 2 * ((β : ℝ) ^ 2 * ‖(x : H) - y‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hLip_sq (sq_nonneg (γ : ℝ))
    rw [hnorm]
    linarith
  calc
    ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2
        ≤ ‖(x : H) - y‖ ^ 2 - 2 * (γ : ℝ) * ((α : ℝ) * ‖(x : H) - y‖ ^ 2) +
            (γ : ℝ) ^ 2 * ((β : ℝ) ^ 2 * ‖(x : H) - y‖ ^ 2) := hbound
    _ = (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)) * ‖(x : H) - y‖ ^ 2 := by
          ring

/-- Helper for Proposition 26.16: in case (ii), the residual step `Id - γ B` is Lipschitz on
`D` with the factor from the source proof. -/
theorem idSubGammaBLipschitzWith_of_ofFunction_isStronglyMonotone_of_lipschitz
    {D : Set H} {B : D → H}
    (α β γ : PosReal) (hα_le_β : (α : ℝ) ≤ (β : ℝ))
    (hB_strong : (ofFunction D B).IsStronglyMonotone (α : ℝ))
    (hB_lipschitz : LipschitzWith (Real.toNNReal (β : ℝ)) B)
    (hγ_lt : (γ : ℝ) < 2 * (α : ℝ) / (β : ℝ) ^ 2) :
    LipschitzWith
      (Real.toNNReal
        (Real.sqrt (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2))))
      (fun x : D ↦ (x : H) - (γ : ℝ) • B x) := by
  let δ : ℝ := 1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)
  have hβsq_pos : 0 < (β : ℝ) ^ 2 := by
    nlinarith [β.2]
  have hcore_pos : 0 < 2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2 := by
    have hscaled' : (γ : ℝ) * (β : ℝ) ^ 2 < 2 * (α : ℝ) := by
      exact (lt_div_iff₀ hβsq_pos).1 hγ_lt
    exact sub_pos.mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled')
  have hprod_pos : 0 < (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) := by
    exact mul_pos γ.2 hcore_pos
  have hαsq_le_βsq : (α : ℝ) ^ 2 ≤ (β : ℝ) ^ 2 := by
    nlinarith [hα_le_β, α.2, β.2]
  have hprod_mul_le : (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) * (β : ℝ) ^ 2 ≤
      (α : ℝ) ^ 2 := by
    have hsq_nonneg : 0 ≤ (((β : ℝ) ^ 2) * (γ : ℝ) - (α : ℝ)) ^ 2 := by positivity
    nlinarith
  have hprod_le_one : (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) ≤ 1 := by
    have hprod_le_alpha : (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) ≤
        (α : ℝ) ^ 2 / (β : ℝ) ^ 2 := by
      exact (le_div_iff₀ hβsq_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hprod_mul_le)
    have hαdiv_le_one : (α : ℝ) ^ 2 / (β : ℝ) ^ 2 ≤ 1 := by
      exact (div_le_iff₀ hβsq_pos).2 (by simpa using hαsq_le_βsq)
    exact le_trans hprod_le_alpha hαdiv_le_one
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    exact sub_nonneg.mpr hprod_le_one
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    exact sub_lt_self _ hprod_pos
  have hsqrt_nonneg : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hsq :
      ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2 ≤
        δ * ‖(x : H) - y‖ ^ 2 := by
    simpa [δ] using
      idSubGammaB_norm_sq_le_of_ofFunction_isStronglyMonotone_of_lipschitz
        α β γ hB_strong hB_lipschitz x y
  have hdist :
      ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ≤
        Real.sqrt δ * ‖(x : H) - y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hsqrt_nonneg (norm_nonneg ((x : H) - y)))).1
    calc
      ‖(((x : H) - (γ : ℝ) • B x) - ((y : H) - (γ : ℝ) • B y))‖ ^ 2
          ≤ δ * ‖(x : H) - y‖ ^ 2 := hsq
      _ = (Real.sqrt δ * ‖(x : H) - y‖) ^ 2 := by
            rw [pow_two, mul_pow, Real.sq_sqrt hδ_nonneg, pow_two]
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul, δ,
    Real.toNNReal_of_nonneg hsqrt_nonneg] using hdist

/-- Helper for Proposition 26.16: composing the residual step with the resolvent produces a
contraction of the constrained forward-backward self-map. -/
theorem forwardBackwardSelfMap_contractingWith_of_lipschitz
    {D : Set H} {A : SetValuedOperator H H} {B : D → H} {ρ σ : NNReal}
    (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D) (γ : PosReal)
    (hres : LipschitzWith ρ (resolventMap A hA_max γ))
    (hstep : LipschitzWith σ (fun x : D ↦ (x : H) - (γ : ℝ) • B x))
    (hρσ : ρ * σ < 1) :
    ContractingWith (ρ * σ) (forwardBackwardSelfMap D A B hA_max hA_dom γ) := by
  refine ⟨hρσ, ?_⟩
  have hcomp :
      LipschitzWith (ρ * σ)
        (fun x : D ↦ resolventMap A hA_max γ ((x : H) - (γ : ℝ) • B x)) :=
    hres.comp hstep
  -- The subtype-valued self-map has the same metric expression as its ambient representative.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [forwardBackwardSelfMap, Subtype.dist_eq, dist_eq_norm] using hcomp.dist_le_mul x y

/-- Helper for Proposition 26.16: the case-(ii) residual factor `√(1 - γ (2α - γβ²))` lies in
`[0, 1)`. -/
theorem forwardBackwardResidualSqrtFactor_lt_one
    (α β γ : PosReal) (hα_le_β : (α : ℝ) ≤ (β : ℝ))
    (hγ_lt : (γ : ℝ) < 2 * (α : ℝ) / (β : ℝ) ^ 2) :
    0 ≤ Real.sqrt (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)) ∧
      Real.sqrt (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)) < 1 := by
  let δ : ℝ := 1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)
  have hβsq_pos : 0 < (β : ℝ) ^ 2 := by
    nlinarith [β.2]
  have hcore_pos : 0 < 2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2 := by
    have hscaled : (γ : ℝ) * (β : ℝ) ^ 2 < 2 * (α : ℝ) := by
      exact (lt_div_iff₀ hβsq_pos).1 hγ_lt
    exact sub_pos.mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  have hprod_pos : 0 < (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) := by
    exact mul_pos γ.2 hcore_pos
  have hαsq_le_βsq : (α : ℝ) ^ 2 ≤ (β : ℝ) ^ 2 := by
    nlinarith [hα_le_β, α.2, β.2]
  have hprod_mul_le :
      (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) * (β : ℝ) ^ 2 ≤
        (α : ℝ) ^ 2 := by
    have hsq_nonneg : 0 ≤ (((β : ℝ) ^ 2) * (γ : ℝ) - (α : ℝ)) ^ 2 := by positivity
    nlinarith
  have hprod_le_one : (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) ≤ 1 := by
    have hprod_le_alpha :
        (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2) ≤
          (α : ℝ) ^ 2 / (β : ℝ) ^ 2 := by
      exact (le_div_iff₀ hβsq_pos).2
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hprod_mul_le)
    have hαdiv_le_one : (α : ℝ) ^ 2 / (β : ℝ) ^ 2 ≤ 1 := by
      exact (div_le_iff₀ hβsq_pos).2 (by simpa using hαsq_le_βsq)
    exact le_trans hprod_le_alpha hαdiv_le_one
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    exact sub_nonneg.mpr hprod_le_one
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    exact sub_lt_self _ hprod_pos
  constructor
  · exact Real.sqrt_nonneg δ
  · -- The scalar bound is the last ingredient needed to package the case-(ii) contraction.
    rw [Real.sqrt_lt hδ_nonneg zero_le_one]
    simpa [δ] using hδ_lt_one

/-- Helper for Proposition 26.16: a contraction on the constrained forward-backward self-map
induces the ambient primal-solution existence, uniqueness, convergence, and linear rate. -/
theorem forwardBackwardOrbit_linearRate_of_contractingSelfMap
    {D : Set H} {A : SetValuedOperator H H} {B : D → H} {ρ : NNReal}
    (hD_closed : IsClosed D) (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (γ : PosReal) {x : ℕ → D}
    (hcontract : ContractingWith ρ (forwardBackwardSelfMap D A B hA_max hA_dom γ))
    (hOrbit : IsForwardBackwardOrbit D A B γ x) :
    ∃ z ∈ primal_inclusion_solution_set A (ofFunction D B),
      Tendsto (fun n ↦ x n : ℕ → H) atTop (𝓝 z) ∧
        primal_inclusion_solution_set A (ofFunction D B) = ({z} : Set H) ∧
        ∀ n : ℕ, dist z (x n) ≤ (ρ : ℝ) ^ n * dist z (x 0) := by
  letI : Nonempty D := ⟨x 0⟩
  letI : CompleteSpace D := hD_closed.completeSpace_coe
  let T := forwardBackwardSelfMap D A B hA_max hA_dom γ
  have hcontractT : ContractingWith ρ T := by
    simpa [T] using hcontract
  let zD : D := hcontractT.fixedPoint T
  have hzD_fixed : Function.IsFixedPt T zD := by
    simpa [zD] using hcontractT.fixedPoint_isFixedPt
  have hz :
      ((zD : D) : H) ∈ primal_inclusion_solution_set A (ofFunction D B) := by
    -- Route correction: transport the Banach fixed point to the ambient primal solution once.
    simpa [T] using
      (isFixedPt_forwardBackwardSelfMap_iff_mem_primalInclusionSolution
        (D := D) (A := A) (B := B) hA_max hA_dom γ zD).1 hzD_fixed
  have hsingleton :
      primal_inclusion_solution_set A (ofFunction D B) = ({((zD : D) : H)} : Set H) := by
    ext y
    constructor
    · intro hy
      let yD : D := ⟨y, primalInclusionSolution_mem_domain hy⟩
      have hy_mem :
          ((yD : D) : H) ∈ primal_inclusion_solution_set A (ofFunction D B) := by
        simpa [yD] using hy
      have hy_fixed : Function.IsFixedPt T yD := by
        simpa [T] using
          (isFixedPt_forwardBackwardSelfMap_iff_mem_primalInclusionSolution
            (D := D) (A := A) (B := B) hA_max hA_dom γ yD).2 hy_mem
      have hy_eq : yD = zD := hcontractT.fixedPoint_unique hy_fixed
      rw [Set.mem_singleton_iff]
      exact congrArg Subtype.val hy_eq
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hz
  have hiter : ∀ n : ℕ, x n = T^[n] (x 0) := by
    simpa [T] using forwardBackwardOrbit_eq_iterate_selfMap hA_max hA_dom γ hOrbit
  have hsub_tendsto : Tendsto (fun n ↦ x n : ℕ → D) atTop (𝓝 zD) := by
    have hiter_eq : (fun n ↦ x n : ℕ → D) = fun n ↦ T^[n] (x 0) := funext hiter
    rw [hiter_eq]
    simpa [zD] using hcontractT.tendsto_iterate_fixedPoint (x 0)
  have htendsto :
      Tendsto (fun n ↦ x n : ℕ → H) atTop (𝓝 (((zD : D) : H))) := by
    simpa using (continuous_subtype_val.tendsto zD).comp hsub_tendsto
  have hrate :
      ∀ n : ℕ, dist (((zD : D) : H)) (x n) ≤ (ρ : ℝ) ^ n * dist (((zD : D) : H)) (x 0) := by
    intro n
    -- Rewrite the orbit as iterates, then use the contraction estimate on `T^[n]`.
    have hdist :=
      (hcontractT.toLipschitzWith.iterate n).dist_le_mul (x 0) zD
    calc
      dist (((zD : D) : H)) (x n)
          = dist (((T^[n] zD : D) : H)) (((T^[n] (x 0) : D) : H)) := by
              rw [(hcontractT.fixedPoint_isFixedPt.iterate n).eq, hiter n]
      _ = dist (((T^[n] (x 0) : D) : H)) (((T^[n] zD : D) : H)) := by rw [dist_comm]
      _ ≤ (ρ : ℝ) ^ n * dist (((x 0 : D) : H)) (((zD : D) : H)) := by
            simpa [Subtype.dist_eq, dist_eq_norm] using hdist
      _ = (ρ : ℝ) ^ n * dist (((zD : D) : H)) (x 0) := by rw [dist_comm]
  exact ⟨((zD : D) : H), hz, htendsto, hsingleton, hrate⟩

/-- Cocoercive-case helper for the constrained forward-backward linear convergence statement. -/
theorem forwardBackwardOrbit_linearRate_of_isStronglyMonotone_of_cocoercive
    {D : Set H} {A : SetValuedOperator H H} {B : D → H}
    (hD_closed : IsClosed D) (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (α β γ : PosReal)
    (hA_strong : A.IsStronglyMonotone (α : ℝ))
    (hB_coco : CocoerciveOn (β : ℝ) D B) (hγ_lt : (γ : ℝ) < 2 * (β : ℝ))
    {x : ℕ → D} (hOrbit : IsForwardBackwardOrbit D A B γ x) :
    ∃ z ∈ primal_inclusion_solution_set A (ofFunction D B),
      Tendsto (fun n ↦ x n : ℕ → H) atTop (𝓝 z) ∧
        primal_inclusion_solution_set A (ofFunction D B) = ({z} : Set H) ∧
        ∀ n : ℕ,
          dist z (x n) ≤ (1 / ((α : ℝ) * (γ : ℝ) + 1)) ^ n * dist z (x 0) := by
  have hres :=
    resolventMap_contractingWith_of_isStronglyMonotone hA_max hA_strong γ
  have hstep :=
    idSubGammaBLipschitzWith_one_of_cocoercive β γ hB_coco hγ_lt
  have hcontract :
      ContractingWith (Real.toNNReal (1 / ((α : ℝ) * (γ : ℝ) + 1)))
        (forwardBackwardSelfMap D A B hA_max hA_dom γ) := by
    -- Route correction: build the contraction once and delegate all Banach transport to the
    -- shared helper.
    simpa [mul_one] using
      forwardBackwardSelfMap_contractingWith_of_lipschitz
        (D := D) (A := A) (B := B) hA_max hA_dom γ hres.toLipschitzWith hstep
          (by simpa [mul_one] using hres.1)
  have hρ_nonneg : 0 ≤ 1 / ((α : ℝ) * (γ : ℝ) + 1) := by
    have hαγ_pos : 0 < (α : ℝ) * (γ : ℝ) := mul_pos α.2 γ.2
    have hden_pos : 0 < (α : ℝ) * (γ : ℝ) + 1 := by nlinarith
    exact le_of_lt (one_div_pos.mpr hden_pos)
  rcases forwardBackwardOrbit_linearRate_of_contractingSelfMap
      (D := D) (A := A) (B := B) hD_closed hA_max hA_dom γ hcontract hOrbit with
    ⟨z, hz, hzlim, hsingle, hrate⟩
  refine ⟨z, hz, hzlim, hsingle, ?_⟩
  intro n
  let r : ℝ := 1 / ((α : ℝ) * (γ : ℝ) + 1)
  have hr_nonneg : 0 ≤ r := hρ_nonneg
  have hrate' : dist z (x n) ≤ (max r 0) ^ n * dist z (x 0) := by
    simpa [r, Real.toNNReal] using hrate n
  calc
    dist z (x n) ≤ (max r 0) ^ n * dist z (x 0) := hrate'
    _ = r ^ n * dist z (x 0) := by rw [max_eq_left hr_nonneg]
    _ = (1 / ((α : ℝ) * (γ : ℝ) + 1)) ^ n * dist z (x 0) := by rfl

/-- Lipschitz-case helper for the constrained forward-backward linear convergence statement. -/
theorem forwardBackwardOrbit_linearRate_of_ofFunction_isStronglyMonotone_of_lipschitz
    {D : Set H} {A : SetValuedOperator H H} {B : D → H}
    (hD_closed : IsClosed D) (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (α β γ : PosReal)
    (hα_le_β : (α : ℝ) ≤ (β : ℝ))
    (hB_strong : (ofFunction D B).IsStronglyMonotone (α : ℝ))
    (hB_lipschitz : LipschitzWith (Real.toNNReal (β : ℝ)) B)
    (hγ_lt : (γ : ℝ) < 2 * (α : ℝ) / (β : ℝ) ^ 2) {x : ℕ → D}
    (hOrbit : IsForwardBackwardOrbit D A B γ x) :
    ∃ z ∈ primal_inclusion_solution_set A (ofFunction D B),
      Tendsto (fun n ↦ x n : ℕ → H) atTop (𝓝 z) ∧
        primal_inclusion_solution_set A (ofFunction D B) = ({z} : Set H) ∧
        ∀ n : ℕ,
          dist z (x n) ≤
            (Real.sqrt
                (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2))) ^ n *
              dist z (x 0) := by
  let δ : ℝ := 1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)
  have hres := resolventMap_lipschitzWith_one hA_max γ
  have hstep :=
    idSubGammaBLipschitzWith_of_ofFunction_isStronglyMonotone_of_lipschitz
      α β γ hα_le_β hB_strong hB_lipschitz hγ_lt
  have hsqrt :=
    forwardBackwardResidualSqrtFactor_lt_one α β γ hα_le_β hγ_lt
  have hcontract :
      ContractingWith (Real.toNNReal (Real.sqrt δ))
        (forwardBackwardSelfMap D A B hA_max hA_dom γ) := by
    -- The resolvent is nonexpansive, so only the residual factor needs the strict `< 1` input.
    simpa [δ, one_mul] using
      forwardBackwardSelfMap_contractingWith_of_lipschitz
        (D := D) (A := A) (B := B) hA_max hA_dom γ hres hstep (by simpa [δ] using hsqrt.2)
  simpa [δ, Real.toNNReal_of_nonneg hsqrt.1] using
    forwardBackwardOrbit_linearRate_of_contractingSelfMap
      (D := D) (A := A) (B := B) hD_closed hA_max hA_dom γ hcontract hOrbit

/-- Proposition 26.16.

Let `D` be a nonempty closed subset of `H`, let `A : H → 2^H` be maximally monotone with
`A.dom ⊆ D`, let `B : D → H`, let `α, β ∈ ℝ_{++}`, and let `γ ∈ ℝ_{++}`. Suppose either

1. `A` is `α`-strongly monotone, `B` is `β`-cocoercive, and `γ ∈ ]0, 2β[`, or
2. `α ≤ β`, `ofFunction D B` is `α`-strongly monotone, `B` is `β`-Lipschitz, and
   `γ ∈ ]0, 2α / β^2[`.

If `x : ℕ → D` satisfies the forward-backward recursion
`x_{n+1} ∈ J_{γ A} (x_n - γ B x_n)`, then `x` converges linearly to the unique point of
`zer (A + B)`, formalized by `primal_inclusion_solution_set A (ofFunction D B)`. -/
theorem forwardBackwardOrbit_linearlyConverges_to_unique_primalInclusionSolution
    {D : Set H} {A : SetValuedOperator H H} {B : D → H}
    (hD_closed : IsClosed D) (hA_max : Maximal IsMonotone A) (hA_dom : A.dom ⊆ D)
    (α β γ : PosReal)
    (hCases :
      (A.IsStronglyMonotone (α : ℝ) ∧ CocoerciveOn (β : ℝ) D B ∧ (γ : ℝ) < 2 * (β : ℝ)) ∨
      ((α : ℝ) ≤ (β : ℝ) ∧ (ofFunction D B).IsStronglyMonotone (α : ℝ) ∧
        LipschitzWith (Real.toNNReal (β : ℝ)) B ∧
        (γ : ℝ) < 2 * (α : ℝ) / (β : ℝ) ^ 2))
    {x : ℕ → D} (hOrbit : IsForwardBackwardOrbit D A B γ x) :
    ∃ z ∈ primal_inclusion_solution_set A (ofFunction D B),
      ∃ ρ : ℝ,
        0 ≤ ρ ∧
        ρ < 1 ∧
        Tendsto (fun n ↦ x n : ℕ → H) atTop (𝓝 z) ∧
        primal_inclusion_solution_set A (ofFunction D B) = ({z} : Set H) ∧
        ∀ n : ℕ, dist z (x n) ≤ ρ ^ n * dist z (x 0) := by
  rcases hCases with hCase1 | hCase2
  · rcases hCase1 with ⟨hA_strong, hB_coco, hγ_lt⟩
    rcases forwardBackwardOrbit_linearRate_of_isStronglyMonotone_of_cocoercive
        (D := D) (A := A) (B := B) hD_closed hA_max hA_dom α β γ hA_strong hB_coco hγ_lt hOrbit
      with ⟨z, hz, hzlim, hsingle, hrate⟩
    refine ⟨z, hz, 1 / ((α : ℝ) * (γ : ℝ) + 1), ?_, ?_, hzlim, hsingle, hrate⟩
    · have hαγ_pos : 0 < (α : ℝ) * (γ : ℝ) := mul_pos α.2 γ.2
      have hden_pos : 0 < (α : ℝ) * (γ : ℝ) + 1 := by nlinarith
      exact le_of_lt (one_div_pos.mpr hden_pos)
    · have hden_gt_one : 1 < (α : ℝ) * (γ : ℝ) + 1 := by
        have hαγ_pos : 0 < (α : ℝ) * (γ : ℝ) := mul_pos α.2 γ.2
        nlinarith
      simpa [one_div] using inv_lt_one_of_one_lt₀ hden_gt_one
  · rcases hCase2 with ⟨hα_le_β, hB_strong, hB_lipschitz, hγ_lt⟩
    rcases forwardBackwardOrbit_linearRate_of_ofFunction_isStronglyMonotone_of_lipschitz
        (D := D) (A := A) (B := B) hD_closed hA_max hA_dom α β γ
        hα_le_β hB_strong hB_lipschitz hγ_lt hOrbit with
      ⟨z, hz, hzlim, hsingle, hrate⟩
    have hsqrt := forwardBackwardResidualSqrtFactor_lt_one α β γ hα_le_β hγ_lt
    refine ⟨z, hz,
      Real.sqrt (1 - (γ : ℝ) * (2 * (α : ℝ) - (γ : ℝ) * (β : ℝ) ^ 2)),
      hsqrt.1, hsqrt.2, hzlim, hsingle, hrate⟩

end Hilbert

end

end SetValuedOperator
