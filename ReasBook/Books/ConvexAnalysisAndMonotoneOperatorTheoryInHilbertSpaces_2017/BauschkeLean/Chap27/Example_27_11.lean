import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import BauschkeLean.Chap20.Corollary_20_50
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap23.Corollary_23_37
import BauschkeLean.Chap27.LaxMilgramQuadraticObjective
import BauschkeLean.Chap27.Proposition_27_8

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced mathlib's `LaxMilgram` owners for coercive bounded
-- bilinear forms. Here the boundedness clause from `(27.11)` is encoded by
-- `B : H →L[ℝ] H →L[ℝ] ℝ`, while the coercivity clause is encoded by `IsCoercive B`.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A point `xbar` solves the Stampacchia variational inequality on `C` for the bounded bilinear
form `B` and the continuous linear functional `ℓ` when it is feasible and satisfies the source
inequality against every feasible comparison point. -/
def SolvesStampacchiaVariationalInequality
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (C : Set H) (xbar : H) : Prop :=
  xbar ∈ C ∧ ∀ y ∈ C, B xbar (y - xbar) ≥ ℓ (y - xbar)

namespace SolvesStampacchiaVariationalInequality

theorem mem
    {B : H →L[ℝ] H →L[ℝ] ℝ} {ℓ : H →L[ℝ] ℝ} {C : Set H} {xbar : H}
    (hxbar : SolvesStampacchiaVariationalInequality B ℓ C xbar) :
    xbar ∈ C :=
  hxbar.1

theorem inequality
    {B : H →L[ℝ] H →L[ℝ] ℝ} {ℓ : H →L[ℝ] ℝ} {C : Set H} {xbar : H}
    (hxbar : SolvesStampacchiaVariationalInequality B ℓ C xbar) :
    ∀ y ∈ C, B xbar (y - xbar) ≥ ℓ (y - xbar) :=
  hxbar.2

end SolvesStampacchiaVariationalInequality

section CompleteSpacePart

variable [CompleteSpace H]

/-- Helper for Example 27.11: the affine single-valued operator associated with the bounded
bilinear form `B` and the linear functional `ℓ`. -/
def stampacchiaAffineMap
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) : H → H :=
  fun x ↦ InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B x -
    (InnerProductSpace.toDual ℝ H).symm ℓ

/-- Helper for Example 27.11: subtracting two affine representatives cancels the Riesz shift and
leaves only the bilinear operator applied to the difference. -/
@[simp] lemma stampacchiaAffineMap_sub
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (x y : H) :
    stampacchiaAffineMap B ℓ x - stampacchiaAffineMap B ℓ y =
      InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B (x - y) := by
  -- Cancel the common Riesz representative of `ℓ` and use linearity of `B♯`.
  simp [stampacchiaAffineMap, map_sub]

/-- Helper for Example 27.11: the strong-monotonicity pairing for the affine representative is the
coercive quadratic form `B (x - y) (x - y)`. -/
lemma inner_sub_stampacchiaAffineMap_sub_eq
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (x y : H) :
    ⟪x - y, stampacchiaAffineMap B ℓ x - stampacchiaAffineMap B ℓ y⟫_ℝ =
      B (x - y) (x - y) := by
  -- Rewrite the affine difference through `B♯` and then evaluate the Riesz pairing.
  rw [stampacchiaAffineMap_sub, real_inner_comm,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- Helper for Example 27.11: the normal-cone inequality for `stampacchiaAffineMap B ℓ x` is
exactly the textbook Stampacchia gap `B x (y - x) - ℓ (y - x)`. -/
lemma inner_sub_stampacchiaAffineMap_eq_neg_gap
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (x y : H) :
    ⟪x - y, stampacchiaAffineMap B ℓ x⟫_ℝ =
      -(B x (y - x) - ℓ (y - x)) := by
  -- Expand the affine map and rewrite both inner products through the Riesz representatives.
  have hsub : x - y = -(y - x) := by
    abel
  calc
    ⟪x - y, stampacchiaAffineMap B ℓ x⟫_ℝ
        = ⟪x - y, InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B x⟫_ℝ -
            ⟪x - y, (InnerProductSpace.toDual ℝ H).symm ℓ⟫_ℝ := by
              simp [stampacchiaAffineMap, inner_sub_right]
    _ = B x (x - y) - ℓ (x - y) := by
          rw [real_inner_comm, InnerProductSpace.continuousLinearMapOfBilin_apply,
            real_inner_comm, InnerProductSpace.toDual_symm_apply]
          rfl
    _ = -(B x (y - x) - ℓ (y - x)) := by
          rw [hsub, (B x).map_neg, ℓ.map_neg]
          ring

/-- Helper for Example 27.11: solving the Stampacchia variational inequality is equivalent to
being a zero of `stampacchiaAffineMap B ℓ + N[C]`. -/
lemma solvesStampacchiaVariationalInequality_iff_memZerosNormalConeAddAffine
    {C : Set H} (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) {x : H} :
    SolvesStampacchiaVariationalInequality B ℓ C x ↔
      x ∈ ((stampacchiaAffineMap B ℓ).toSetValuedOperator +
        (Set.normalCone C : SetValuedOperator H H)).zeros := by
  constructor
  · rintro ⟨hxC, hineq⟩
    -- Encode the Stampacchia inequality as the normal-cone condition `-A x ∈ N[C] x`.
    rw [SetValuedOperator.mem_zeros_iff]
    change 0 ∈ Function.toSetValuedOperator (stampacchiaAffineMap B ℓ) x + Set.normalCone C x
    rw [Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨stampacchiaAffineMap B ℓ x, by simp, -(stampacchiaAffineMap B ℓ x), ?_, by simp⟩
    rw [Set.normalCone_of_mem hxC]
    refine (innerSupremumOn_sub_singleton_le_zero_iff
      (C := C) (u := -(stampacchiaAffineMap B ℓ x)) (p := x)).2 ?_
    intro y hyC
    have hgap : 0 ≤ B x (y - x) - ℓ (y - x) := by
      linarith [hineq y hyC]
    have hpair :
        ⟪y - x, -(stampacchiaAffineMap B ℓ x)⟫_ℝ =
          -(B x (y - x) - ℓ (y - x)) := by
      have hsub : y - x = -(x - y) := by
        abel
      calc
        ⟪y - x, -(stampacchiaAffineMap B ℓ x)⟫_ℝ
            = ⟪x - y, stampacchiaAffineMap B ℓ x⟫_ℝ := by
                rw [hsub, inner_neg_left, inner_neg_right]
                ring
        _ = -(B x (y - x) - ℓ (y - x)) :=
            inner_sub_stampacchiaAffineMap_eq_neg_gap B ℓ x y
    rw [hpair]
    linarith
  · intro hxzero
    -- Read a zero of `A + N[C]` as the normal-cone witness `-A x ∈ N[C] x`.
    rw [SetValuedOperator.mem_zeros_iff] at hxzero
    change 0 ∈ Function.toSetValuedOperator (stampacchiaAffineMap B ℓ) x + Set.normalCone C x at hxzero
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hxzero
    rcases hxzero with ⟨u, hu, v, hv, huv⟩
    have hu' : u = stampacchiaAffineMap B ℓ x := by
      simpa using hu
    subst u
    have hv' : v = -(stampacchiaAffineMap B ℓ x) := by
      have hv'' : stampacchiaAffineMap B ℓ x = -v := by
        simpa using eq_neg_of_add_eq_zero_left huv
      have hv''' : -(stampacchiaAffineMap B ℓ x) = v := by
        simpa using congrArg Neg.neg hv''
      exact hv'''.symm
    by_cases hxC : x ∈ C
    · refine ⟨hxC, ?_⟩
      rw [hv', Set.normalCone_of_mem hxC] at hv
      have hnormal :
          ∀ y ∈ C, ⟪y - x, -(stampacchiaAffineMap B ℓ x)⟫_ℝ ≤ 0 :=
        (innerSupremumOn_sub_singleton_le_zero_iff
          (C := C) (u := -(stampacchiaAffineMap B ℓ x)) (p := x)).1 hv
      intro y hyC
      have hpair :
          ⟪y - x, -(stampacchiaAffineMap B ℓ x)⟫_ℝ =
            -(B x (y - x) - ℓ (y - x)) := by
        have hsub : y - x = -(x - y) := by
          abel
        calc
          ⟪y - x, -(stampacchiaAffineMap B ℓ x)⟫_ℝ
              = ⟪x - y, stampacchiaAffineMap B ℓ x⟫_ℝ := by
                  rw [hsub, inner_neg_left, inner_neg_right]
                  ring
          _ = -(B x (y - x) - ℓ (y - x)) :=
              inner_sub_stampacchiaAffineMap_eq_neg_gap B ℓ x y
      have hnonpos : -(B x (y - x) - ℓ (y - x)) ≤ 0 := by
        simpa [hpair] using hnormal y hyC
      linarith
    · rw [hv', Set.normalCone_of_not_mem hxC] at hv
      simp at hv

/-- Helper for Example 27.11: the affine representative inherits strong monotonicity from the
coercivity lower bound on `B`. -/
lemma stampacchiaAffineMap_isStronglyMonotone
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) {α : ℝ} (hα_pos : 0 < α)
    (hα : ∀ z : H, α * ‖z‖ * ‖z‖ ≤ B z z) :
    ((stampacchiaAffineMap B ℓ).toSetValuedOperator).IsStronglyMonotone α := by
  refine ⟨hα_pos, ?_⟩
  intro x u y v hu hv
  -- Singleton-valued fibers reduce strong monotonicity to the coercive lower bound on `B`.
  simp only [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu hv
  subst u v
  calc
    α * ‖x - y‖ ^ 2 = α * ‖x - y‖ * ‖x - y‖ := by ring
    _ ≤ B (x - y) (x - y) := hα (x - y)
    _ = ⟪x - y, stampacchiaAffineMap B ℓ x - stampacchiaAffineMap B ℓ y⟫_ℝ :=
      (inner_sub_stampacchiaAffineMap_sub_eq B ℓ x y).symm

/-- Helper for Example 27.11: adding the monotone normal cone preserves the coercive strong
monotonicity modulus of the affine representative. -/
lemma affineAddNormalCone_isStronglyMonotone
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) {α : ℝ} (hα_pos : 0 < α)
    (hα : ∀ z : H, α * ‖z‖ * ‖z‖ ≤ B z z) :
    (((stampacchiaAffineMap B ℓ).toSetValuedOperator) +
      (Set.normalCone C : SetValuedOperator H H)).IsStronglyMonotone α := by
  refine ⟨hα_pos, ?_⟩
  intro x u y v hu hv
  -- Split both sum-operator witnesses and combine strong monotonicity with monotonicity.
  rcases Set.mem_add.mp hu with ⟨uA, huA, uN, huN, rfl⟩
  rcases Set.mem_add.mp hv with ⟨vA, hvA, vN, hvN, rfl⟩
  have hA :
      α * ‖x - y‖ ^ 2 ≤ ⟪x - y, uA - vA⟫_ℝ :=
    (stampacchiaAffineMap_isStronglyMonotone B ℓ hα_pos hα).ineq huA hvA
  have hNmono :
      SetValuedOperator.IsMonotone (Set.normalCone C : SetValuedOperator H H) :=
    (Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex).1
  have hN : 0 ≤ ⟪x - y, uN - vN⟫_ℝ := hNmono huN hvN
  have hsplit :
      ⟪x - y, (uA + uN) - (vA + vN)⟫_ℝ =
        ⟪x - y, uA - vA⟫_ℝ + ⟪x - y, uN - vN⟫_ℝ := by
    have hdecomp : (uA + uN) - (vA + vN) = (uA - vA) + (uN - vN) := by
      abel
    rw [hdecomp, inner_add_right]
  calc
    α * ‖x - y‖ ^ 2 ≤ ⟪x - y, uA - vA⟫_ℝ := hA
    _ ≤ ⟪x - y, uA - vA⟫_ℝ + ⟪x - y, uN - vN⟫_ℝ := by linarith
    _ = ⟪x - y, (uA + uN) - (vA + vN)⟫_ℝ := hsplit.symm

end CompleteSpacePart

/-- Helper for Example 27.11: the quadratic-affine objective has the expected line expansion along
the segment from `x` to `y`. -/
lemma laxMilgramQuadraticObjective_lineDiff
    (B : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ)
    (hB_symm : ∀ x y : H, B x y = B y x) (x y : H) (t : ℝ) :
    laxMilgramQuadraticObjective B ℓ (x + t • (y - x)) -
      laxMilgramQuadraticObjective B ℓ x =
        t * (B x (y - x) - ℓ (y - x)) +
          (t ^ 2 / 2 : ℝ) * B (y - x) (y - x) := by
  -- Expand the quadratic form and the linear term along the affine line.
  simp [laxMilgramQuadraticObjective, map_add, map_sub, map_smul, hB_symm, mul_add, add_mul,
    mul_assoc, pow_two]
  ring

/-- Helper for Example 27.11: for symmetric `B` with `B z z ≥ 0`, constrained minimizers of the
quadratic objective are exactly solutions of the Stampacchia variational inequality. -/
lemma memArgminOnQuadraticObjective_iff_solvesStampacchia_of_symmetric_nonneg
    {C : Set H} (hC_convex : Convex ℝ C) (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hB_nonneg : ∀ z : H, 0 ≤ B z z) (ℓ : H →L[ℝ] ℝ)
    (hB_symm : ∀ x y : H, B x y = B y x) {xbar : H} :
    xbar ∈ Argmin[C] (laxMilgramQuadraticObjective B ℓ).toEReal.asEReal ↔
      SolvesStampacchiaVariationalInequality B ℓ C xbar := by
  constructor
  · intro hxarg
    rw [ERealFunction.mem_argminOn_iff] at hxarg
    rcases hxarg with ⟨hxbarC, hxmin⟩
    rw [isMinOn_iff] at hxmin
    refine ⟨hxbarC, ?_⟩
    intro y hyC
    -- Route correction: prove the VI directly from one-dimensional minimization along the segment
    -- `[xbar, y]`, instead of routing through a completeness-dependent subdifferential API.
    by_contra hgap
    let gap : ℝ := B xbar (y - xbar) - ℓ (y - xbar)
    let q : ℝ := B (y - xbar) (y - xbar)
    have hgap_neg : gap < 0 := by
      dsimp [gap]
      linarith
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact hB_nonneg (y - xbar)
    have hbound_pos : 0 < -gap / (q + 1) := by
      have hnum : 0 < -gap := by
        dsimp [gap] at hgap_neg ⊢
        linarith
      have hden : 0 < q + 1 := by
        dsimp [q] at hq_nonneg ⊢
        linarith
      exact div_pos hnum hden
    let s : ℝ := min 1 (-gap / (q + 1))
    have hs_pos : 0 < s := by
      dsimp [s]
      exact lt_min (by norm_num) hbound_pos
    have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
    have hs_le_one : s ≤ 1 := by
      dsimp [s]
      exact min_le_left _ _
    have hs_le_bound : s ≤ -gap / (q + 1) := by
      dsimp [s]
      exact min_le_right _ _
    have hzC' : (1 - s) • xbar + s • y ∈ C :=
      hC_convex hxbarC hyC (sub_nonneg.mpr hs_le_one) hs_nonneg (by ring)
    have hzC : xbar + s • (y - xbar) ∈ C := by
      -- Move to the convex-combination normal form required by `Convex`.
      have hcomb :
          xbar + s • (y - xbar) = (1 - s) • xbar + s • y := by
        calc
          xbar + s • (y - xbar) = AffineMap.lineMap xbar y s := by
            simpa [add_comm] using (AffineMap.lineMap_apply_module' xbar y s).symm
          _ = (1 - s) • xbar + s • y := AffineMap.lineMap_apply_module xbar y s
      rw [hcomb]
      exact hzC'
    have hzmin :
        laxMilgramQuadraticObjective B ℓ xbar ≤
          laxMilgramQuadraticObjective B ℓ (xbar + s • (y - xbar)) :=
      by
        have hzminE :
            (((laxMilgramQuadraticObjective B ℓ xbar) : ℝ) : EReal) ≤
              (((laxMilgramQuadraticObjective B ℓ (xbar + s • (y - xbar))) : ℝ) : EReal) := by
          simpa using hxmin _ hzC
        exact_mod_cast hzminE
    have hs_bound' : s * (q + 1) ≤ -gap := by
      have hden : 0 < q + 1 := by
        linarith
      exact (le_div_iff₀ hden).mp hs_le_bound
    have hcore_neg : gap + (s / 2) * q < 0 := by
      nlinarith [hgap_neg, hq_nonneg, hs_nonneg, hs_bound']
    have hdiff_neg :
        laxMilgramQuadraticObjective B ℓ (xbar + s • (y - xbar)) -
          laxMilgramQuadraticObjective B ℓ xbar < 0 := by
      have hcore_neg' :
          B xbar (y - xbar) - ℓ (y - xbar) +
            (s / 2) * B (y - xbar) (y - xbar) < 0 := by
        simpa [gap, q, hB_symm xbar y] using hcore_neg
      rw [laxMilgramQuadraticObjective_lineDiff B ℓ hB_symm xbar y s]
      nlinarith [hs_pos, hcore_neg']
    linarith
  · intro hxsol
    rw [ERealFunction.mem_argminOn_iff]
    refine ⟨hxsol.1, ?_⟩
    rw [isMinOn_iff]
    intro y hyC
    -- Evaluate the quadratic objective difference at `t = 1` and use the VI plus nonnegativity.
    have hgap : 0 ≤ B xbar (y - xbar) - ℓ (y - xbar) := by
      linarith [hxsol.2 y hyC]
    have hquad : 0 ≤ B (y - xbar) (y - xbar) := hB_nonneg (y - xbar)
    have hline :
        laxMilgramQuadraticObjective B ℓ y -
          laxMilgramQuadraticObjective B ℓ xbar =
            (B xbar (y - xbar) - ℓ (y - xbar)) +
              ((1 : ℝ) / 2) * B (y - xbar) (y - xbar) := by
      simpa using laxMilgramQuadraticObjective_lineDiff B ℓ hB_symm xbar y 1
    have hdiff_nonneg :
        0 ≤ laxMilgramQuadraticObjective B ℓ y -
          laxMilgramQuadraticObjective B ℓ xbar := by
      rw [hline]
      nlinarith
    have hymin : laxMilgramQuadraticObjective B ℓ xbar ≤ laxMilgramQuadraticObjective B ℓ y := by
      linarith
    have hyminE :
        (((laxMilgramQuadraticObjective B ℓ xbar) : ℝ) : EReal) ≤
          (((laxMilgramQuadraticObjective B ℓ y) : ℝ) : EReal) := by
      exact_mod_cast hymin
    simpa using hyminE

/-- Helper for Example 27.11: coercivity makes Stampacchia solutions unique. -/
lemma eq_of_solvesStampacchiaVariationalInequality_of_isCoercive
    {C : Set H} (B : H →L[ℝ] H →L[ℝ] ℝ) (hB_coercive : IsCoercive B) (ℓ : H →L[ℝ] ℝ)
    {x y : H} (hx : SolvesStampacchiaVariationalInequality B ℓ C x)
    (hy : SolvesStampacchiaVariationalInequality B ℓ C y) :
    x = y := by
  rcases hB_coercive with ⟨α, hα_pos, hα⟩
  have hxineq : ℓ (y - x) ≤ B x (y - x) := hx.2 y hy.1
  have hyineq : B y (y - x) ≤ ℓ (y - x) := by
    have htmp : B y (x - y) ≥ ℓ (x - y) := hy.2 x hx.1
    have hneg : B y (x - y) = -B y (y - x) := by
      rw [show x - y = -(y - x) by abel, map_neg]
    have hnegℓ : ℓ (x - y) = -ℓ (y - x) := by
      rw [show x - y = -(y - x) by abel, map_neg]
    linarith
  have hB_nonpos : B (x - y) (x - y) ≤ 0 := by
    have hrewrite : B (x - y) (y - x) = -B (x - y) (x - y) := by
      rw [show y - x = -(x - y) by abel, map_neg]
    have hxy : 0 ≤ B (x - y) (y - x) := by
      have hrewrite' : B (x - y) (y - x) = B x (y - x) - B y (y - x) := by
        calc
          B (x - y) (y - x) = B (x - y) y - B (x - y) x := by
            rw [(B (x - y)).map_sub]
          _ = (B x y - B y y) - (B x x - B y x) := by
            simp [map_sub]
          _ = B x (y - x) - B y (y - x) := by
            rw [(B x).map_sub, (B y).map_sub]
            ring
      calc
        B (x - y) (y - x) = B x (y - x) - B y (y - x) := hrewrite'
        _ ≥ 0 := by linarith [hxineq, hyineq]
    rw [hrewrite] at hxy
    linarith
  have hnorm_zero : ‖x - y‖ = 0 := by
    have hcoer : α * ‖x - y‖ * ‖x - y‖ ≤ B (x - y) (x - y) := hα (x - y)
    have hleft : 0 ≤ α * ‖x - y‖ * ‖x - y‖ := by
      positivity
    have hsq_zero : α * ‖x - y‖ * ‖x - y‖ = 0 := by
      linarith
    have hsq_zero' : ‖x - y‖ * ‖x - y‖ = 0 := by
      nlinarith [hα_pos, hsq_zero]
    nlinarith [hsq_zero']
  exact sub_eq_zero.mp <| norm_eq_zero.mp hnorm_zero

section CompleteSpaceExistence

variable [CompleteSpace H]

/-- Example 27.11 (1): if `B` is a coercive bounded bilinear form on a real Hilbert space `H`,
if `C` is a nonempty closed convex subset of `H`, and if `ℓ` is a continuous linear functional on
`H`, then the Stampacchia variational inequality on `C` has a unique solution. -/
theorem existsUnique_solution_stampacchiaVariationalInequality_of_nonempty_isClosed_convex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB_coercive : IsCoercive B) (ℓ : H →L[ℝ] ℝ) :
    ∃! xbar : H, SolvesStampacchiaVariationalInequality B ℓ C xbar := by
  rcases hB_coercive with ⟨α, hα_pos, hα⟩
  let A : H → H := stampacchiaAffineMap B ℓ
  have hA_mono : A.toSetValuedOperator.IsMonotone :=
    (stampacchiaAffineMap_isStronglyMonotone B ℓ hα_pos hα).isMonotone
  have hA_cont : Continuous A := by
    -- The affine representative is continuous as a continuous linear map plus a constant shift.
    simpa [A, stampacchiaAffineMap] using
      (InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) B).continuous.sub continuous_const
  let T : C → H := fun x ↦ A x
  have hT_cont : Continuous T := by
    -- Restrict the ambient continuous representative to the subtype `C`.
    simpa [T] using hA_cont.comp continuous_subtype_val
  have hA_eq : ∀ x, ∀ hx : x ∈ C, A.toSetValuedOperator x = ({T ⟨x, hx⟩} : Set H) := by
    intro x hx
    simp [A, T, Function.toSetValuedOperator_apply]
  have hsum_max :
      Maximal SetValuedOperator.IsMonotone
        (A.toSetValuedOperator + (Set.normalCone C : SetValuedOperator H H)) := by
    simpa [A] using
      SetValuedOperator.add_normalCone_isMaximallyMonotone_of_monotone_of_eq_singleton_continuous
        hC_nonempty hC_closed hC_convex A.toSetValuedOperator hA_mono T hA_eq hT_cont
  have hsum_strong :
      (A.toSetValuedOperator + (Set.normalCone C : SetValuedOperator H H)).IsStronglyMonotone α :=
    affineAddNormalCone_isStronglyMonotone hC_nonempty hC_closed hC_convex B ℓ hα_pos hα
  obtain ⟨xbar, hxbar_zero, hzeros⟩ :=
    SetValuedOperator.exists_mem_zeros_eq_singleton_of_maximal_of_isStronglyMonotone
      (A.toSetValuedOperator + (Set.normalCone C : SetValuedOperator H H))
      hsum_max hsum_strong
  refine ⟨xbar, ?_, ?_⟩
  · -- Translate the singleton zero-set witness back to the source VI formulation.
    simpa [A] using
      (solvesStampacchiaVariationalInequality_iff_memZerosNormalConeAddAffine
        (C := C) B ℓ (x := xbar)).2 hxbar_zero
  · intro y hy
    have hy_zero :
        y ∈ (A.toSetValuedOperator + (Set.normalCone C : SetValuedOperator H H)).zeros := by
      simpa [A] using
        (solvesStampacchiaVariationalInequality_iff_memZerosNormalConeAddAffine
          (C := C) B ℓ (x := y)).1 hy
    have hy_single : y ∈ ({xbar} : Set H) := by
      simpa [hzeros] using hy_zero
    simpa using Set.mem_singleton_iff.mp hy_single

end CompleteSpaceExistence

/-- Example 27.11 (2): if `C` is convex and `B` is a symmetric coercive bounded bilinear form,
then `xbar` solves the Stampacchia variational inequality on `C` if and only if `xbar` is the
unique minimizer over `C` of the quadratic-affine functional `x ↦ (1 / 2) B(x, x) - ℓ(x)`. The
nonemptiness and closedness assumptions from clause `(1)` are existence hypotheses and are
redundant for this pointwise equivalence, and completeness is likewise unused by the pointwise
argmin characterization, so those assumptions are omitted here. -/
theorem solves_stampacchiaVariationalInequality_iff_argminOn_eq_singleton_of_symmetric
    {C : Set H} (hC_convex : Convex ℝ C) (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hB_coercive : IsCoercive B) (ℓ : H →L[ℝ] ℝ) (hB_symm : ∀ x y : H, B x y = B y x)
    {xbar : H} :
    SolvesStampacchiaVariationalInequality B ℓ C xbar ↔
      Argmin[C] (laxMilgramQuadraticObjective B ℓ).toEReal.asEReal = {xbar} := by
  rcases hB_coercive with ⟨α, hα_pos, hα⟩
  have hB_coercive' : IsCoercive B := ⟨α, hα_pos, hα⟩
  have hB_nonneg : ∀ z : H, 0 ≤ B z z := by
    intro z
    have hz : α * ‖z‖ * ‖z‖ ≤ B z z := hα z
    have hleft : 0 ≤ α * ‖z‖ * ‖z‖ := by
      positivity
    linarith
  have hmem (x : H) :
      x ∈ Argmin[C] (laxMilgramQuadraticObjective B ℓ).toEReal.asEReal ↔
        SolvesStampacchiaVariationalInequality B ℓ C x := by
    simpa using
      (memArgminOnQuadraticObjective_iff_solvesStampacchia_of_symmetric_nonneg
        hC_convex B hB_nonneg ℓ hB_symm (xbar := x))
  constructor
  · intro hx
    -- Use the pointwise membership equivalence together with coercive uniqueness.
    ext y
    constructor
    · intro hy
      have hy_sol : SolvesStampacchiaVariationalInequality B ℓ C y := (hmem y).mp hy
      exact Set.mem_singleton_iff.mpr <|
        eq_of_solvesStampacchiaVariationalInequality_of_isCoercive
          (C := C) B hB_coercive' ℓ (x := xbar) (y := y) hx hy_sol |>.symm
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using (hmem xbar).mpr hx
  · intro hx
    have hxarg : xbar ∈ Argmin[C] (laxMilgramQuadraticObjective B ℓ).toEReal.asEReal := by
      simpa [hx] using (show xbar ∈ ({xbar} : Set H) by simp)
    exact (hmem xbar).mp hxarg

/-- Companion to Example 27.11 (2): in the symmetric case, the source variational-inequality
solution predicate is equivalent to direct membership in the canonical constrained argmin owner
for the quadratic-affine objective. The standing existence/uniqueness hypotheses are trimmed to
the convexity and quadratic nonnegativity needed for the direct membership statement, and no
completeness hypothesis is required. -/
theorem
    solves_stampacchiaVariationalInequality_iff_mem_argminOn_objective_of_symmetric
    {C : Set H} (hC_convex : Convex ℝ C)
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB_nonneg : ∀ z : H, 0 ≤ B z z) (ℓ : H →L[ℝ] ℝ)
    (hB_symm : ∀ x y : H, B x y = B y x) {xbar : H} :
    SolvesStampacchiaVariationalInequality B ℓ C xbar ↔
      xbar ∈ Argmin[C] (laxMilgramQuadraticObjective B ℓ).toEReal.asEReal := by
  -- Reuse the quadratic line-expansion characterization proved once for clause `(2)`.
  simpa [iff_comm] using
    (memArgminOnQuadraticObjective_iff_solvesStampacchia_of_symmetric_nonneg
      hC_convex B hB_nonneg ℓ hB_symm (xbar := xbar))
