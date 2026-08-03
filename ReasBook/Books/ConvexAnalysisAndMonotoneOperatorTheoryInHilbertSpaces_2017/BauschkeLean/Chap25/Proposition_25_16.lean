import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap02.Definition_2_23
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap04.Corollary_4_5
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap20.Example_20_15
import BauschkeLean.Chap20.Example_20_16
import BauschkeLean.Chap20.Example_20_54
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap25.Definition_25_10

open scoped InnerProduct InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

noncomputable section

section RealHilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 25.16 is the Brézis-Haraux equivalence for bounded linear maps.
- `core/canonical`: the two ambient owners are `CocoerciveOn` and
  `SetValuedOperator.IsThreeStarMonotone`.
- `bridge/view`: whole-space bounded linear maps enter those owners through the canonical
  singleton-valued bridge `ContinuousLinearMap.toSetValuedOperator` and the `Set.univ`
  specialization of `CocoerciveOn`. -/

/-- Helper for Proposition 25.16: on `Set.univ`, cocoercivity of a bounded linear map is
equivalent to the pointwise quadratic inequality obtained by specializing at `y = 0`. -/
lemma cocoerciveOn_univ_iff_quadratic_form
    (A : H →L[ℝ] H) {β : ℝ} :
    CocoerciveOn β (Set.univ : Set H) (fun x : Set.univ ↦ A x) ↔
      0 < β ∧ ∀ z : H, β * ‖A z‖ ^ (2 : ℕ) ≤ ⟪z, A z⟫_ℝ := by
  -- Unfold the `Set.univ` specialization, then specialize the pairwise inequality at `y = 0`.
  rw [CocoerciveOn]
  constructor
  · rintro ⟨hβ, hineq⟩
    refine ⟨hβ, ?_⟩
    intro z
    simpa using hineq ⟨z, by simp⟩ ⟨0, by simp⟩
  · rintro ⟨hβ, hineq⟩
    refine ⟨hβ, ?_⟩
    intro x y
    simpa [map_sub, real_inner_comm] using hineq ((x : H) - y)

/-- Helper for Proposition 25.16: the `β`-quadratic inequality for `A` is exactly the quadratic
clause from Corollary 4.5 applied to the scaled map `β • A`. -/
lemma scaled_quadratic_clause_iff
    (A : H →L[ℝ] H) (β : Set.Ioi (0 : ℝ)) :
    (∀ z : H, (β : ℝ) * ‖A z‖ ^ (2 : ℕ) ≤ ⟪z, A z⟫_ℝ) ↔
      ∀ z : H, ‖(((β : ℝ) • A) z)‖ ^ (2 : ℕ) ≤ ⟪z, ((β : ℝ) • A) z⟫_ℝ := by
  have hβpos : 0 < (β : ℝ) := β.2
  constructor
  · intro hquad z
    -- Multiply the source inequality by `β` so it matches the scaled quadratic clause.
    have hscaled :
        (β : ℝ) * ((β : ℝ) * ‖A z‖ ^ (2 : ℕ)) ≤ (β : ℝ) * ⟪z, A z⟫_ℝ :=
      mul_le_mul_of_nonneg_left (hquad z) hβpos.le
    simpa [ContinuousLinearMap.smul_apply, norm_smul, abs_of_pos hβpos,
      real_inner_smul_right, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
  · intro hquad z
    -- Rewrite the scaled quadratic clause back into the unscaled `β`-cocoercive form.
    have hscaled :
        (β : ℝ) * ((β : ℝ) * ‖A z‖ ^ (2 : ℕ)) ≤ (β : ℝ) * ⟪z, A z⟫_ℝ := by
      simpa [ContinuousLinearMap.smul_apply, norm_smul, abs_of_pos hβpos,
        real_inner_smul_right, pow_two, mul_assoc, mul_left_comm, mul_comm] using hquad z
    nlinarith [hβpos, hscaled]

/-- Helper for Proposition 25.16: for a fixed positive parameter, whole-space cocoercivity is
preserved by taking adjoints. -/
lemma cocoerciveOn_univ_adjoint_iff
    (A : H →L[ℝ] H) (β : Set.Ioi (0 : ℝ)) :
    CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ A x) ↔
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ (A†) x) := by
  have hforward :
      ∀ B : H →L[ℝ] H,
        CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ B x) →
          CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ (B†) x) := by
    intro B hB
    rw [cocoerciveOn_univ_iff_quadratic_form] at hB ⊢
    refine ⟨hB.1, ?_⟩
    have hscaledB :
        ∀ z : H, ‖(((β : ℝ) • B) z)‖ ^ (2 : ℕ) ≤ ⟪z, ((β : ℝ) • B) z⟫_ℝ :=
      (scaled_quadratic_clause_iff B β).mp hB.2
    have hfirmAdj :
        FirmlyNonexpansiveOn (Set.univ : Set H)
          (fun x : Set.univ ↦ (((β : ℝ) • B).adjoint) x) :=
      (List.TFAE.out
        (tfae_firmly_nonexpansive_adjoint_norm_quadratic ((β : ℝ) • B))
        2 3).mp hscaledB
    have hscaledAdj :
        ∀ z : H, ‖((((β : ℝ) • B).adjoint) z)‖ ^ (2 : ℕ) ≤
          ⟪z, (((β : ℝ) • B).adjoint) z⟫_ℝ :=
      (List.TFAE.out
        (tfae_firmly_nonexpansive_adjoint_norm_quadratic (((β : ℝ) • B).adjoint))
        0 2).mp hfirmAdj
    have hscaledAdj' :
        ∀ z : H, ‖(((β : ℝ) • (B†)) z)‖ ^ (2 : ℕ) ≤ ⟪z, ((β : ℝ) • (B†)) z⟫_ℝ := by
      simpa using hscaledAdj
    exact (scaled_quadratic_clause_iff (B†) β).mpr hscaledAdj'
  constructor
  · intro hA
    exact hforward A hA
  · intro hAadj
    simpa [ContinuousLinearMap.adjoint_adjoint] using hforward (A†) hAadj

/-- Helper for Proposition 25.16: the scalar `1` is a positive real number. -/
lemma one_mem_Ioi_zero : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
  simpa using (show 0 < (1 : ℝ) from one_pos)

/-- Helper for Proposition 25.16: the elementary one-variable quadratic bound
`a t - (β / 2) t² ≤ a² / (2β)` used in the Fitzpatrick estimate. -/
lemma linear_term_sub_quadratic_term_le
    {β a t : ℝ} (hβ : 0 < β) :
    a * t - (β / 2) * t ^ (2 : ℕ) ≤ a ^ (2 : ℕ) / (2 * β) := by
  -- Complete the square and let `nlinarith` clear the positive denominator `β`.
  have hβ2 : 0 < 2 * β := by positivity
  refine (le_div_iff₀ hβ2).2 ?_
  ring_nf
  nlinarith [sq_nonneg (a - β * t)]

/-- Helper for Proposition 25.16: whole-space cocoercivity bounds the Fitzpatrick function at
points of the form `(x, A y)` by the quadratic source estimate. -/
lemma fitzpatrick_apply_le_inv_two_mul_beta_of_cocoercive
    (A : H →L[ℝ] H)
    {β : ℝ} (hA_coco : CocoerciveOn β (Set.univ : Set H) (fun x : Set.univ ↦ A x))
    (x y : H) :
    F[A.toSetValuedOperator] (x, A y) ≤
      ((((‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)) / (2 * β) : ℝ)) : EReal) := by
  let βpos : Set.Ioi (0 : ℝ) := ⟨β, hA_coco.pos⟩
  have hA_quad :
      ∀ z : H, β * ‖A z‖ ^ (2 : ℕ) ≤ ⟪z, A z⟫_ℝ :=
    (cocoerciveOn_univ_iff_quadratic_form A).mp hA_coco |>.2
  have hAadj_coco :
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun z : Set.univ ↦ (A†) z) :=
    (cocoerciveOn_univ_adjoint_iff A βpos).mp hA_coco
  have hAadj_quad :
      ∀ z : H, β * ‖(A†) z‖ ^ (2 : ℕ) ≤ ⟪z, (A†) z⟫_ℝ :=
    (cocoerciveOn_univ_iff_quadratic_form (A†)).mp hAadj_coco |>.2
  rw [fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup]
  refine iSup_le fun z ↦ ?_
  -- Split the source supremand into the `A`-part and the `A†`-part from the textbook proof.
  have hz_diag :
      ⟪z, A z⟫_ℝ = ⟪z, (A†) z⟫_ℝ := by
    calc
      ⟪z, A z⟫_ℝ = ⟪A z, z⟫_ℝ := by rw [real_inner_comm]
      _ = ⟪z, (A†) z⟫_ℝ := by
        simpa using (ContinuousLinearMap.adjoint_inner_right (A := A) z z).symm
  have hz_cross :
      ⟪z, A y⟫_ℝ = ⟪(A†) z, y⟫_ℝ := by
    calc
      ⟪z, A y⟫_ℝ = ⟪A y, z⟫_ℝ := by rw [real_inner_comm]
      _ = ⟪y, (A†) z⟫_ℝ := by
        simpa using (ContinuousLinearMap.adjoint_inner_right (A := A) y z).symm
      _ = ⟪(A†) z, y⟫_ℝ := by rw [real_inner_comm]
  have hA_part :
      ⟪x, A z⟫_ℝ - (1 / 2 : ℝ) * ⟪z, A z⟫_ℝ ≤ ‖x‖ ^ (2 : ℕ) / (2 * β) := by
    have hinner_le : ⟪x, A z⟫_ℝ ≤ ‖x‖ * ‖A z‖ := real_inner_le_norm x (A z)
    have hquad_half :
        (β / 2) * ‖A z‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ⟪z, A z⟫_ℝ := by
      have hscaled := mul_le_mul_of_nonneg_left (hA_quad z) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
    have hlin :
        ‖x‖ * ‖A z‖ - (β / 2) * ‖A z‖ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) / (2 * β) :=
      linear_term_sub_quadratic_term_le (a := ‖x‖) (t := ‖A z‖) hA_coco.pos
    linarith
  have hAadj_part :
      ⟪(A†) z, y⟫_ℝ - (1 / 2 : ℝ) * ⟪z, (A†) z⟫_ℝ ≤ ‖y‖ ^ (2 : ℕ) / (2 * β) := by
    have hinner_le : ⟪(A†) z, y⟫_ℝ ≤ ‖(A†) z‖ * ‖y‖ := by
      simpa [mul_comm] using real_inner_le_norm ((A†) z) y
    have hquad_half :
        (β / 2) * ‖(A†) z‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ⟪z, (A†) z⟫_ℝ := by
      have hscaled :=
        mul_le_mul_of_nonneg_left (hAadj_quad z) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
    have hlin :
        ‖y‖ * ‖(A†) z‖ - (β / 2) * ‖(A†) z‖ ^ (2 : ℕ) ≤ ‖y‖ ^ (2 : ℕ) / (2 * β) :=
      linear_term_sub_quadratic_term_le (a := ‖y‖) (t := ‖(A†) z‖) hA_coco.pos
    linarith
  have hsum :
      ⟪z, A y⟫_ℝ + ⟪x, A z⟫_ℝ - ⟪z, A z⟫_ℝ ≤
        (‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)) / (2 * β) := by
    have hA_part' :
        ⟪x, A z⟫_ℝ - (1 / 2 : ℝ) * ⟪z, (A†) z⟫_ℝ ≤ ‖x‖ ^ (2 : ℕ) / (2 * β) := by
      simpa [hz_diag] using hA_part
    have hsum' := add_le_add hA_part' hAadj_part
    have hsum'' :
        ⟪(A†) z, y⟫_ℝ + ⟪x, A z⟫_ℝ - ⟪z, (A†) z⟫_ℝ ≤
          (‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)) / (2 * β) := by
      have hleft :
          (⟪x, A z⟫_ℝ - (1 / 2 : ℝ) * ⟪z, (A†) z⟫_ℝ) +
              (⟪(A†) z, y⟫_ℝ - (1 / 2 : ℝ) * ⟪z, (A†) z⟫_ℝ) =
            ⟪(A†) z, y⟫_ℝ + ⟪x, A z⟫_ℝ - ⟪z, (A†) z⟫_ℝ := by
        ring
      have hright :
          ‖x‖ ^ (2 : ℕ) / (2 * β) + ‖y‖ ^ (2 : ℕ) / (2 * β) =
            (‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)) / (2 * β) := by
        ring
      rw [← hleft, ← hright]
      exact hsum'
    calc
      ⟪z, A y⟫_ℝ + ⟪x, A z⟫_ℝ - ⟪z, A z⟫_ℝ
          = ⟪(A†) z, y⟫_ℝ + ⟪x, A z⟫_ℝ - ⟪z, (A†) z⟫_ℝ := by
              rw [hz_cross, hz_diag]
      _ ≤ (‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)) / (2 * β) := hsum''
  exact EReal.coe_le_coe_iff.2 hsum

/-- Helper for Proposition 25.16: the zero slice of the Fitzpatrick function is proper because
`(0, 0)` lies in the graph of the singleton-valued operator. -/
lemma fitzpatrick_zero_slice_isProper
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    ERealFunction.IsProper (fun x : H ↦ F[A.toSetValuedOperator] (x, 0)) := by
  have hA_graph : (gra A.toSetValuedOperator).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    exact (SetValuedOperator.mem_graph A.toSetValuedOperator 0 0).2
      (by simp [Function.toSetValuedOperator_apply])
  have hAop_mono : A.toSetValuedOperator.IsMonotone := by
    simpa [Function.toSetValuedOperator] using
      (LinearMap.toSetValuedOperator_isMonotone_iff A.toLinearMap).2 hA_mono
  refine ⟨?_, ?_⟩
  · intro x
    exact ne_of_gt
      (SetValuedOperator.fitzpatrickFunction_ne_bot_of_graph_nonempty A.toSetValuedOperator
        hA_graph (x, 0))
  · refine ⟨0, ?_⟩
    rw [ERealFunction.mem_dom_iff_ne_top]
    have hgraph0 : (0, 0) ∈ gra A.toSetValuedOperator := by
      exact (SetValuedOperator.mem_graph A.toSetValuedOperator 0 0).2
        (by simp [Function.toSetValuedOperator_apply])
    have hzero :
        F[A.toSetValuedOperator] (0, 0) = 0 := by
      simpa using
        SetValuedOperator.fitzpatrickFunction_eq_inner_of_mem_graph
          (A := A.toSetValuedOperator) hAop_mono hgraph0
    simp [hzero]

/-- Helper for Proposition 25.16: the zero slice `x ↦ F_A(x, 0)` belongs to `Γ₀(H)`. -/
lemma fitzpatrick_zero_slice_mem_gammaZero
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    ERealFunction.properIoi
        (fun x : H ↦ F[A.toSetValuedOperator] (x, 0))
        (fitzpatrick_zero_slice_isProper A hA_mono) ∈ Γ₀(H) := by
  let f :
      H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi
      (fun x : H ↦ F[A.toSetValuedOperator] (x, 0))
      (fitzpatrick_zero_slice_isProper A hA_mono)
  let FA :
      H × H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi
      (F[A.toSetValuedOperator])
      (SetValuedOperator.fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        (A := A.toSetValuedOperator)
        (by
          refine ⟨(0, 0), ?_⟩
          exact (SetValuedOperator.mem_graph A.toSetValuedOperator 0 0).2
            (by simp [Function.toSetValuedOperator_apply]))
        (by
          simpa [Function.toSetValuedOperator] using
            (LinearMap.toSetValuedOperator_isMonotone_iff A.toLinearMap).2 hA_mono))
  let L : H →L[ℝ] H × H := ContinuousLinearMap.inl ℝ H H
  have hFA_gamma : FA ∈ Γ₀(H × H) := by
    simpa [FA] using
      SetValuedOperator.fitzpatrickFunction_mem_gammaZero
        (A := A.toSetValuedOperator)
        (by
          refine ⟨(0, 0), ?_⟩
          exact (SetValuedOperator.mem_graph A.toSetValuedOperator 0 0).2
            (by simp [Function.toSetValuedOperator_apply]))
        (by
          simpa [Function.toSetValuedOperator] using
            (LinearMap.toSetValuedOperator_isMonotone_iff A.toLinearMap).2 hA_mono)
  rw [ERealFunction.mem_gammaZero_iff] at hFA_gamma ⊢
  constructor
  · -- Lower semicontinuity is stable under the continuous embedding `x ↦ (x, 0)`.
    simpa [f, FA, L, Function.comp] using hFA_gamma.1.comp L.continuous
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The graph point `(0, 0)` gives a finite zero-slice value, hence a domain witness.
      refine ⟨0, ?_⟩
      rw [ERealFunction.mem_effectiveDomain_iff]
      have hgraph0 : (0, 0) ∈ gra A.toSetValuedOperator := by
        exact (SetValuedOperator.mem_graph A.toSetValuedOperator 0 0).2
          (by simp [Function.toSetValuedOperator_apply])
      have hAop_mono : A.toSetValuedOperator.IsMonotone := by
        simpa [Function.toSetValuedOperator] using
          (LinearMap.toSetValuedOperator_isMonotone_iff A.toLinearMap).2 hA_mono
      have hzero :
          F[A.toSetValuedOperator] (0, 0) = 0 := by
        simpa using
          SetValuedOperator.fitzpatrickFunction_eq_inner_of_mem_graph
            (A := A.toSetValuedOperator) hAop_mono hgraph0
      simp [f, hzero]
    · intro x hx y hy α hα hα_lt_one
      have hx' : L x ∈ ERealFunction.effectiveDomain FA := by
        simpa [f, FA, L, Function.comp, ERealFunction.mem_effectiveDomain_iff] using hx
      have hy' : L y ∈ ERealFunction.effectiveDomain FA := by
        simpa [f, FA, L, Function.comp, ERealFunction.mem_effectiveDomain_iff] using hy
      -- Jensen convexity on `H × H` restricts to the linear slice `u = 0`.
      simpa [f, FA, L, Function.comp, map_add, map_smul] using
        hFA_gamma.2.ineq hx' hy' hα hα_lt_one

/-- Helper for Proposition 25.16: a uniform bound on the zero slice over a ball yields the
quadratic estimate `⟪x, A y⟫² ≤ 4 μ ⟪y, A y⟫`. -/
lemma pairing_sq_le_of_zero_slice_ball_bound
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone)
    {μ ρ : ℝ}
    (hμ :
      ∀ {x : H}, x ∈ Metric.ball (0 : H) ρ →
        F[A.toSetValuedOperator] (x, 0) ≤ (μ : EReal))
    {x y : H} (hx : x ∈ Metric.ball (0 : H) ρ) :
    ⟪x, A y⟫_ℝ ^ (2 : ℕ) ≤ 4 * μ * ⟪y, A y⟫_ℝ := by
  let a : ℝ := ⟪x, A y⟫_ℝ
  let c : ℝ := ⟪y, A y⟫_ℝ
  have hc_nonneg : 0 ≤ c := by
    simpa [c, real_inner_comm] using hA_mono y
  have hquad : ∀ t : ℝ, a * t - c * t ^ (2 : ℕ) ≤ μ := by
    intro t
    have hfitz : F[A.toSetValuedOperator] (x, 0) ≤ (μ : EReal) := hμ hx
    rw [fitzpatrickFunction_toSetValuedOperator_apply_eq_iSup] at hfitz
    have hcand :
        (((⟪t • y, (0 : H)⟫_ℝ + ⟪x, A (t • y)⟫_ℝ - ⟪t • y, A (t • y)⟫_ℝ : ℝ) :
          EReal)) ≤ (μ : EReal) := by
      exact le_trans
        (le_iSup
          (fun z : H ↦
            (((⟪z, (0 : H)⟫_ℝ + ⟪x, A z⟫_ℝ - ⟪z, A z⟫_ℝ : ℝ) : EReal)))
          (t • y))
        hfitz
    have hcand_real :
        ⟪t • y, (0 : H)⟫_ℝ + ⟪x, A (t • y)⟫_ℝ - ⟪t • y, A (t • y)⟫_ℝ ≤ μ := by
      exact_mod_cast hcand
    simpa [a, c, inner_zero_right, map_smul, real_inner_smul_left, real_inner_smul_right,
      pow_two, mul_assoc, mul_left_comm, mul_comm] using hcand_real
  by_cases hc : c = 0
  · by_cases ha : a = 0
    · simp [a, c, ha, hc]
    · have hspec := hquad ((μ + 1) / a)
      have hspec_eq : a * ((μ + 1) / a) = μ + 1 := by
        field_simp [ha]
      rw [hc, hspec_eq, zero_mul, sub_zero] at hspec
      linarith
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc)
    have hspec := hquad (a / (2 * c))
    have hspec_eq : a * (a / (2 * c)) - c * ((a / (2 * c)) ^ (2 : ℕ)) = a ^ (2 : ℕ) / (4 * c) := by
      field_simp [hc_pos.ne']
      ring
    rw [hspec_eq] at hspec
    have hfourc_pos : 0 < 4 * c := by positivity
    have hbound : a ^ (2 : ℕ) ≤ 4 * μ * c := by
      have := (div_le_iff₀ hfourc_pos).mp hspec
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    simpa [a, c] using hbound

/-- Helper for Proposition 25.16: the source `(ii) → (i)` bound makes every pair
`(x, A y)` belong to the Fitzpatrick domain, hence yields `3*` monotonicity. -/
lemma isThreeStarMonotone_of_cocoerciveOn_univ
    (A : H →L[ℝ] H)
    {β : ℝ} (hA_coco : CocoerciveOn β (Set.univ : Set H) (fun x : Set.univ ↦ A x)) :
    A.toSetValuedOperator.IsThreeStarMonotone := by
  rw [SetValuedOperator.isThreeStarMonotone_iff]
  rintro ⟨x, u⟩ ⟨_, hu_range⟩
  rw [ERealFunction.mem_dom_iff_ne_top]
  rcases (SetValuedOperator.mem_range_iff A.toSetValuedOperator u).1 hu_range with ⟨y, hy⟩
  have hu_eq : u = A y := by
    simpa [Function.toSetValuedOperator_apply] using hy
  -- The finite upper bound from cocoercivity puts every `(x, A y)` in the Fitzpatrick domain.
  rw [hu_eq]
  exact ne_of_lt <|
    lt_of_le_of_lt
      (fitzpatrick_apply_le_inv_two_mul_beta_of_cocoercive A hA_coco x y)
      (EReal.coe_lt_top _)

/-- Helper for Proposition 25.16: `3*` monotonicity forces the packaged zero slice
`x ↦ F_A(x, 0)` to have full effective domain. -/
lemma fitzpatrick_zero_slice_effectiveDomain_eq_univ_of_isThreeStarMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone)
    (hthree : A.toSetValuedOperator.IsThreeStarMonotone) :
    ERealFunction.effectiveDomain
        (ERealFunction.properIoi
          (fun x : H ↦ F[A.toSetValuedOperator] (x, 0))
          (fitzpatrick_zero_slice_isProper A hA_mono)) =
      Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    -- Every `x` lies in the operator domain, and `0 = A 0` supplies the range witness.
    rw [ERealFunction.mem_effectiveDomain_iff, ERealFunction.properIoi_apply]
    have hx_dom : x ∈ A.toSetValuedOperator.dom := by
      rw [SetValuedOperator.mem_dom_iff]
      refine ⟨A x, ?_⟩
      simp [Function.toSetValuedOperator_apply]
    have hzero_range : (0 : H) ∈ A.toSetValuedOperator.range := by
      rw [ContinuousLinearMap.toSetValuedOperator_range]
      exact ⟨0, by simp⟩
    have hpair_dom :
        (x, (0 : H)) ∈ A.toSetValuedOperator.dom ×ˢ A.toSetValuedOperator.range :=
      ⟨hx_dom, hzero_range⟩
    simpa using hthree.subset_dom_fitzpatrickFunction hpair_dom

/-- Helper for Proposition 25.16: Corollary 8.39 turns `3*` monotonicity into a finite upper
bound for the zero slice on a neighborhood of the origin. -/
lemma zero_slice_local_upper_bound_of_isThreeStarMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone)
    (hthree : A.toSetValuedOperator.IsThreeStarMonotone) :
    ∃ ρ μ : ℝ, 0 < ρ ∧ 0 < μ ∧
      ∀ x ∈ Metric.ball (0 : H) ρ, F[A.toSetValuedOperator] (x, 0) ≤ (μ : EReal) := by
  let f0 : H → Set.Ioi (⊥ : EReal) :=
    ERealFunction.properIoi
      (fun x : H ↦ F[A.toSetValuedOperator] (x, 0))
      (fitzpatrick_zero_slice_isProper A hA_mono)
  have hf0_gamma : f0 ∈ Γ₀(H) := by
    simpa [f0] using fitzpatrick_zero_slice_mem_gammaZero A hA_mono
  rw [ERealFunction.mem_gammaZero_iff] at hf0_gamma
  have heff : ERealFunction.effectiveDomain f0 = Set.univ := by
    simpa [f0] using
      fitzpatrick_zero_slice_effectiveDomain_eq_univ_of_isThreeStarMonotone
        A hA_mono hthree
  have hcont_points :
      {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ ERealFunction.effectiveDomain f0 ∧
        ContinuousAt (fun y : H ↦ (f0 y : EReal).toReal) x} =
        interior (ERealFunction.effectiveDomain f0) := by
    exact
      ERealFunction.continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
        f0 hf0_gamma.2 (Or.inr (Or.inl hf0_gamma.1))
  have hzero_cont :
      (0 : H) ∈ {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ ERealFunction.effectiveDomain f0 ∧
        ContinuousAt (fun y : H ↦ (f0 y : EReal).toReal) x} := by
    rw [hcont_points, heff]
    simp
  rcases hzero_cont with ⟨ρ0, hρ0, hball_dom0, hcont0⟩
  have hupper_nhds :
      Set.Iio (((f0 0 : EReal).toReal) + 1) ∈ nhds (((f0 0 : EReal).toReal) : ℝ) := by
    exact Iio_mem_nhds (by linarith)
  have hevent_upper :
      ∀ᶠ y : H in nhds (0 : H), (f0 y : EReal).toReal < ((f0 0 : EReal).toReal + 1) := by
    exact hcont0 hupper_nhds
  rcases Metric.mem_nhds_iff.mp hevent_upper with ⟨σ, hσ, hσball⟩
  let ρ : ℝ := min ρ0 σ
  let μ : ℝ := max 1 (((f0 0 : EReal).toReal) + 1)
  refine ⟨ρ, μ, by simpa [ρ] using lt_min hρ0 hσ, by
    dsimp [μ]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hx_dist : dist x (0 : H) < ρ := by
    simpa [ρ, Metric.mem_ball] using hx
  have hxρ : x ∈ Metric.ball (0 : H) ρ0 := by
    simpa [Metric.mem_ball] using lt_of_lt_of_le hx_dist (by simp [ρ])
  have hxσ : x ∈ Metric.ball (0 : H) σ := by
    simpa [Metric.mem_ball] using lt_of_lt_of_le hx_dist (by simp [ρ])
  have hx_dom : x ∈ ERealFunction.effectiveDomain f0 := hball_dom0 hxρ
  have hx_top : (f0 x : EReal) ≠ ⊤ := by
    exact ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp hx_dom)
  have hx_bot : (f0 x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f0 x : EReal) from (f0 x).2)
  have hreal_le : (f0 x : EReal).toReal ≤ μ := by
    dsimp [μ]
    exact le_trans (le_of_lt (hσball hxσ)) (le_max_right _ _)
  have hEReal_le : (f0 x : EReal) ≤ (μ : EReal) := by
    rw [show (f0 x : EReal) = (((f0 x : EReal).toReal : ℝ) : EReal) by
      exact (EReal.coe_toReal hx_top hx_bot).symm]
    exact_mod_cast hreal_le
  simpa [f0] using hEReal_le

/-- Helper for Proposition 25.16: a zero-slice ball bound produces the positive quadratic-form
constant from the textbook discriminant argument. -/
lemma exists_pos_quadratic_form_of_zero_slice_ball_bound
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone)
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ)
    (hbound :
      ∀ x ∈ Metric.ball (0 : H) ρ, F[A.toSetValuedOperator] (x, 0) ≤ (μ : EReal)) :
    ∃ β : Set.Ioi (0 : ℝ), ∀ y : H, (β : ℝ) * ‖A y‖ ^ (2 : ℕ) ≤ ⟪y, A y⟫_ℝ := by
  have hβpos : 0 < ρ ^ (2 : ℕ) / (16 * μ) := by
    have hden : 0 < 16 * μ := by
      positivity
    exact div_pos (pow_pos hρ _) hden
  refine ⟨⟨ρ ^ (2 : ℕ) / (16 * μ), hβpos⟩, ?_⟩
  intro y
  by_cases hAy : A y = 0
  · -- The kernel case is immediate because both sides vanish.
    simp [hAy]
  · let c : ℝ := (ρ / 2) / ‖A y‖
    let x : H := c • A y
    have hAy_norm_pos : 0 < ‖A y‖ := norm_pos_iff.mpr hAy
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hx_ball : x ∈ Metric.ball (0 : H) ρ := by
      -- Route correction: use the strict interior point `((ρ / 2) / ‖A y‖) • A y`.
      rw [Metric.mem_ball, dist_eq_norm]
      calc
        ‖x - 0‖ = ‖x‖ := by
          simp
        _ = c * ‖A y‖ := by
          simpa [x, norm_smul, Real.norm_of_nonneg hc_pos.le]
        _ = ρ / 2 := by
          dsimp [c]
          field_simp [hAy_norm_pos.ne']
        _ < ρ := by
          linarith
    have hsq_le :
        ⟪x, A y⟫_ℝ ^ (2 : ℕ) ≤ 4 * μ * ⟪y, A y⟫_ℝ := by
      exact
        pairing_sq_le_of_zero_slice_ball_bound A hA_mono
          (μ := μ) (ρ := ρ) (hμ := fun {z} hz ↦ hbound z hz)
          (x := x) (y := y) hx_ball
    have hinner_x :
        ⟪x, A y⟫_ℝ = (ρ / 2) * ‖A y‖ := by
      calc
        ⟪x, A y⟫_ℝ = c * ⟪A y, A y⟫_ℝ := by
          simpa [x] using (real_inner_smul_left (A y) (A y) c)
        _ = c * ‖A y‖ ^ (2 : ℕ) := by
          rw [real_inner_self_eq_norm_sq]
        _ = (ρ / 2) * ‖A y‖ := by
          dsimp [c]
          field_simp [hAy_norm_pos.ne']
    have hcoef_le :
        (ρ ^ (2 : ℕ) / 4) * ‖A y‖ ^ (2 : ℕ) ≤ 4 * μ * ⟪y, A y⟫_ℝ := by
      rw [hinner_x] at hsq_le
      nlinarith
    have hcleared :
        ρ ^ (2 : ℕ) * ‖A y‖ ^ (2 : ℕ) ≤ 16 * μ * ⟪y, A y⟫_ℝ := by
      nlinarith
    have hden_pos : 0 < 16 * μ := by
      positivity
    have hdiv :
        (ρ ^ (2 : ℕ) * ‖A y‖ ^ (2 : ℕ)) / (16 * μ) ≤ ⟪y, A y⟫_ℝ :=
      (div_le_iff₀ hden_pos).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcleared)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Proposition 25.16: a `3*`-monotone bounded linear operator admits a positive
cocoercivity parameter on the whole space. -/
lemma exists_pos_cocoerciveOn_univ_of_isThreeStarMonotone
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone)
    (hthree : A.toSetValuedOperator.IsThreeStarMonotone) :
    ∃ β : Set.Ioi (0 : ℝ),
      CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ A x) := by
  -- Package the source route as: zero-slice `Γ₀` continuity, local ball bound, then the
  -- quadratic-form inequality that is equivalent to whole-space cocoercivity.
  rcases zero_slice_local_upper_bound_of_isThreeStarMonotone A hA_mono hthree with
    ⟨ρ, μ, hρ, hμ, hbound⟩
  rcases exists_pos_quadratic_form_of_zero_slice_ball_bound A hA_mono hρ hμ hbound with
    ⟨β, hquad⟩
  refine ⟨β, ?_⟩
  exact (cocoerciveOn_univ_iff_quadratic_form A).2 ⟨β.2, hquad⟩

/-- Proposition 25.16: if a bounded linear operator `A` on a real Hilbert space is monotone, then
for some `β : Set.Ioi (0 : ℝ)` the following are equivalent: `A` is `3*`-monotone, `A` is
`β`-cocoercive, `A†` is `β`-cocoercive, and `A†` is `3*`-monotone. -/
theorem exists_pos_tfae_threeStarMonotone_cocoercive_adjoint
    (A : H →L[ℝ] H) (hA_mono : A.toLinearMap.IsMonotone) :
    ∃ β : Set.Ioi (0 : ℝ),
      let Aop := A.toSetValuedOperator
      let AadjOp := A†.toSetValuedOperator
      List.TFAE
        [Aop.IsThreeStarMonotone,
          CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ A x),
          CocoerciveOn (β : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ (A†) x),
          AadjOp.IsThreeStarMonotone] := by
  have hAadj_mono : A†.toLinearMap.IsMonotone :=
    (ContinuousLinearMap.isMonotone_iff_adjoint_isMonotone A).mp hA_mono
  by_cases hthree : A.toSetValuedOperator.IsThreeStarMonotone
  · rcases exists_pos_cocoerciveOn_univ_of_isThreeStarMonotone A hA_mono hthree with
      ⟨β, hβcocoA⟩
    refine ⟨β, ?_⟩
    dsimp
    -- In the positive branch, choose the parameter supplied by the source `(i) → (ii)` route.
    tfae_have 1 → 2 := by
      intro _
      exact hβcocoA
    tfae_have 2 → 3 := by
      intro hβcoco
      exact (cocoerciveOn_univ_adjoint_iff A β).mp hβcoco
    tfae_have 3 → 4 := by
      intro hβcocoAdj
      exact isThreeStarMonotone_of_cocoerciveOn_univ (A†) hβcocoAdj
    tfae_have 4 → 1 := by
      intro hthreeAdj
      -- Route correction: recover clause `(i)` for `A` by first running `(i) → (ii)` on `A†`.
      rcases exists_pos_cocoerciveOn_univ_of_isThreeStarMonotone (A†) hAadj_mono hthreeAdj with
        ⟨γ, hγcocoAdj⟩
      have hγcocoA :
          CocoerciveOn (γ : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ A x) :=
        (cocoerciveOn_univ_adjoint_iff A γ).mpr hγcocoAdj
      exact isThreeStarMonotone_of_cocoerciveOn_univ A hγcocoA
    tfae_finish
  · let β : Set.Ioi (0 : ℝ) := ⟨1, one_mem_Ioi_zero⟩
    refine ⟨β, ?_⟩
    dsimp
    -- In the negative branch, clause `(i)` is false, so only the reverse cycle needs work.
    tfae_have 1 → 2 := by
      intro hfalse
      exact False.elim (hthree hfalse)
    tfae_have 2 → 3 := by
      intro hβcoco
      exact (cocoerciveOn_univ_adjoint_iff A β).mp hβcoco
    tfae_have 3 → 4 := by
      intro hβcocoAdj
      exact isThreeStarMonotone_of_cocoerciveOn_univ (A†) hβcocoAdj
    tfae_have 4 → 1 := by
      intro hthreeAdj
      rcases exists_pos_cocoerciveOn_univ_of_isThreeStarMonotone (A†) hAadj_mono hthreeAdj with
        ⟨γ, hγcocoAdj⟩
      have hγcocoA :
          CocoerciveOn (γ : ℝ) (Set.univ : Set H) (fun x : Set.univ ↦ A x) :=
        (cocoerciveOn_univ_adjoint_iff A γ).mpr hγcocoAdj
      exact isThreeStarMonotone_of_cocoerciveOn_univ A hγcocoA
    tfae_finish

end RealHilbert

end

end ContinuousLinearMap
