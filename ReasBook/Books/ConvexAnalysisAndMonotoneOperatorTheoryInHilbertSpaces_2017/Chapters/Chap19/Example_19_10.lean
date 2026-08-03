import Mathlib
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Example_12_21
import BauschkeLean.Chap12.Example_12_25
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap19.Proposition_19_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section NonemptyBridge

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: membership in `sri (L '' C - D)` implies membership in `L '' C - D`, so
-- `0 = L x - d` for some `x ∈ C` and `d ∈ D`; in particular `x` witnesses `C.Nonempty`.
private theorem nonempty_of_zero_mem_sri_image_sub_left
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (L '' C - D)) :
    C.Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨Lx, hLx, _, _, _⟩
  rcases hLx with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

end NonemptyBridge

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Example 19.10 is the constrained best-approximation problem on
  `C ∩ L ⁻¹' D`.
- `core/canonical`: the owner theorem is
  `argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator`.
- `bridge/view`: specialize the owner theorem to `φ = ι[C]` and `ψ = ι[D]`, then rewrite the
  resulting proximity operator as the metric projection `P[C, hC]` and the conjugate of `ι[D]`
  as the support function `σ[D]`.
-/

variable {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable {D : Set K} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
variable (z : H) (L : H →L[ℝ] K)
variable (hsri : (0 : K) ∈ sri (L '' C - D))

local notation "hC_cheb" =>
  isChebyshev_of_nonempty_isClosed_convex
    (nonempty_of_zero_mem_sri_image_sub_left C D L hsri) hC_closed hC_convex

local notation "P_C" => P[C, hC_cheb]
local notation "feasibleSet" => C ∩ L ⁻¹' D
local notation "primalObj" => fun x : H ↦ ‖x - z‖
local notation "halfSqObj" =>
  fun x : H ↦ ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))
local notation "dualObj" =>
  fun v : K ↦
    ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
      ((((1 / 2 : ℝ) * (Metric.infDist (z - L.adjoint v) C) ^ 2 : ℝ) : EReal))) +
        σ[D] v

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 19.10: the strong-relative-interior hypothesis produces a feasible point
for the constraint set `C ∩ L ⁻¹' D`. -/
private lemma exists_mem_and_image_mem_of_zero_mem_sri_image_sub :
    (hsri : (0 : K) ∈ sri (L '' C - D)) →
    ∃ x, x ∈ C ∧ L x ∈ D := by
  intro hsri
  -- Membership in `sri (L '' C - D)` first gives actual membership in `L '' C - D`.
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨y, hy, d, hd, hyd⟩
  -- Unpack the image witness and use `y - d = 0` to show `L x = d ∈ D`.
  rcases hy with ⟨x, hx, rfl⟩
  have hLd : L x = d := sub_eq_zero.mp hyd
  have hLxD : L x ∈ D := hLd ▸ hd
  exact ⟨x, hx, hLxD⟩

/-- Helper for Example 19.10: the indicator of a nonempty closed convex set belongs to `Γ₀`. -/
private lemma indicator_mem_gammaZero_of_nonempty_isClosed_convex_local
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) :
    ι[S] ∈ Γ₀(X) := by
  -- Closedness gives lower semicontinuity of the indicator, and convexity gives convexity of its
  -- effective domain.
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[S]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed S).2 hS_closed
  have hdom : effectiveDomain (ι[S]) = S := by
    ext y
    by_cases hy : y ∈ S
    · simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
    · simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hdom] using hS_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyS : y ∈ S := by
    simpa [hdom] using hy
  have hzS : z ∈ S := by
    simpa [hdom] using hz
  have hayzS : a • y + (1 - a) • z ∈ S :=
    hS_convex hyS hzS ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyS, hzS, hayzS]

omit [CompleteSpace K] in
/-- Helper for Example 19.10: the proximity operator of the indicator of `C` is the metric
projection onto `C`. -/
private theorem proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex_local
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty) (hC_gamma : ι[C] ∈ Γ₀(H)) :
    Prox[ι[C], hC_gamma] = P_C := by
  -- The general indicator/projection identification already gives exactly this specialization.
  have hcheb_eq :
      isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex = hC_cheb := by
    apply Subsingleton.elim
  simpa using
    (proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex).trans (by rw [hcheb_eq])

omit [CompleteSpace K] in
/-- Helper for Example 19.10: the conjugate of the indicator of `D` is its support function. -/
private lemma conjugate_indicator_eq_supportFunction_local :
    ((ι[D]).asEReal)∗ = σ[D] := by
  -- This is exactly Example 13.3(i).
  simpa using conjugate_indicator_eq_supportFunction D

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 19.10: the unit Moreau envelope of the indicator of `C` is the half
squared distance to `C`. -/
private lemma unit_moreauEnvelope_indicator_eq_half_sq_infDist
    (hC_nonempty : C.Nonempty) (x : H) :
    ({}^[(1 : PosReal)] ι[C]) x =
      ((((1 / 2 : ℝ) * Metric.infDist x C ^ 2 : ℝ) : EReal)) := by
  -- Start from the general indicator Moreau-envelope formula at parameter `1`.
  have hmoreau :=
    congrFun (indicator_moreauEnvelope_eq_scaled_sq_infEDist C (1 : PosReal)) x
  have hdist_top : (Metric.infEDist x C : EReal) ≠ ⊤ := by
    intro htop
    rcases hC_nonempty with ⟨y, hy⟩
    exact ne_top_of_le_ne_top (edist_ne_top x y) (Metric.infEDist_le_edist_of_mem hy)
      (by simpa using htop)
  have hsq :
      (Metric.infEDist x C : EReal) ^ 2 / (2 : EReal) =
        (((Metric.infDist x C ^ 2) / 2 : ℝ) : EReal) := by
    rw [pow_two, ← EReal.coe_toReal hdist_top (by simp : (Metric.infEDist x C : EReal) ≠ ⊥),
      ← EReal.coe_toReal hdist_top (by simp : (Metric.infEDist x C : EReal) ≠ ⊥),
      show (2 : EReal) = ((2 : ℝ) : EReal) by rfl, ← EReal.coe_mul, ← EReal.coe_div]
    simp [Metric.infDist, pow_two]
  calc
    ({}^[(1 : PosReal)] ι[C]) x
        = (Metric.infEDist x C : EReal) ^ 2 / (2 * ((1 : PosReal) : ℝ) : EReal) := hmoreau
    _ = (Metric.infEDist x C : EReal) ^ 2 / (2 : EReal) := by
      norm_num
    _ = (((Metric.infDist x C ^ 2) / 2 : ℝ) : EReal) := hsq
    _ = ((((1 / 2 : ℝ) * Metric.infDist x C ^ 2 : ℝ) : EReal)) := by
      congr 1
      ring

/-- Helper for Example 19.10: after specializing Proposition 19.5 to `φ = ι[C]` and
`ψ = ι[D]`, the owner dual objective is exactly the textbook dual objective. -/
private lemma specialized_dual_owner_eq_dualObj
    (hsri : (0 : K) ∈ sri (L '' C - D))
    (_hC_gamma : ι[C] ∈ Γ₀(H)) (hD_gamma : ι[D] ∈ Γ₀(K)) :
    (fun v : K ↦
      ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
        ({}^[(1 : PosReal)] ι[C]) (z - L.adjoint v)) +
          (((ι[D])∗[hD_gamma] v : EReal))) = dualObj := by
  -- Rewrite the conjugate of `ι[D]` as the support function and the Moreau term as squared
  -- distance to `C`.
  rcases exists_mem_and_image_mem_of_zero_mem_sri_image_sub (L := L) hsri with
    ⟨x0, hx0C, _⟩
  have hC_nonempty : C.Nonempty := ⟨x0, hx0C⟩
  have hconj :
      (fun v : K ↦ (((ι[D])∗[hD_gamma] v : EReal))) = fun v : K ↦ (σ[D] v : EReal) := by
    ext v
    calc
      (((ι[D])∗[hD_gamma] v : EReal)) = ((ι[D]).asEReal∗ v) := by
        rw [gammaZeroConjugate_apply]
      _ = (σ[D] v : EReal) := by
        simpa using congrFun (conjugate_indicator_eq_supportFunction_local (D := D)) v
  funext v
  have hconj_v : (((ι[D])∗[hD_gamma] v : EReal)) = (σ[D] v : EReal) := by
    simpa using congrFun hconj v
  calc
    ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
        ({}^[(1 : PosReal)] ι[C]) (z - L.adjoint v)) +
          (((ι[D])∗[hD_gamma] v : EReal))
      = ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
          ((((1 / 2 : ℝ) * Metric.infDist (z - L.adjoint v) C ^ 2 : ℝ) : EReal))) +
            (σ[D] v : EReal) := by
          rw [unit_moreauEnvelope_indicator_eq_half_sq_infDist
            (C := C) (hC_nonempty := hC_nonempty) (x := z - L.adjoint v), hconj_v]
    _ = dualObj v := by
      rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 19.10: the specialized owner primal objective is the half squared-distance
objective plus the indicator of the feasible set `C ∩ L ⁻¹' D`. -/
private lemma specialized_primal_owner_eq_halfSqDist_add_indicator_feasibleSet :
    (fun x : H ↦
      (ι[C] x : EReal) + (ι[D] (L x) : EReal) +
        ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))) =
      fun x : H ↦ halfSqObj x + (ι[feasibleSet] x : EReal) := by
  -- Split on feasibility in `C` and in `D` to normalize both indicator presentations.
  funext x
  have hhalf_ne_bot :
      ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ :=
    EReal.coe_ne_bot ((1 / 2 : ℝ) * ‖x - z‖ ^ 2)
  by_cases hxC : x ∈ C
  · by_cases hxD : L x ∈ D
    · simp [indicator_apply, Set.mem_inter_iff, Set.mem_preimage, hxC, hxD]
    · have hxfeasible : x ∉ feasibleSet := by
        simp [Set.mem_inter_iff, Set.mem_preimage, hxC, hxD]
      have hleft :
          (⊤ : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) = ⊤ :=
        EReal.top_add_of_ne_bot hhalf_ne_bot
      have hright :
          ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) + ⊤ = ⊤ :=
        EReal.add_top_of_ne_bot hhalf_ne_bot
      have htop_comm :
          (⊤ : EReal) + (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 =
            (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 + ⊤ := by
        calc
          (⊤ : EReal) + (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 = ⊤ := by
            simpa [one_div, EReal.coe_mul, EReal.coe_pow] using hleft
          _ = (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 + ⊤ := by
            simpa [one_div, EReal.coe_mul, EReal.coe_pow] using hright.symm
      simpa [indicator_apply, hxfeasible, hxC, hxD, one_div, EReal.coe_mul,
        EReal.coe_pow] using htop_comm
  · by_cases hxD : L x ∈ D
    · have hxfeasible : x ∉ feasibleSet := by
        simp [Set.mem_inter_iff, Set.mem_preimage, hxC, hxD]
      have hleft :
          (⊤ : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) = ⊤ :=
        EReal.top_add_of_ne_bot hhalf_ne_bot
      have hright :
          ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) + ⊤ = ⊤ :=
        EReal.add_top_of_ne_bot hhalf_ne_bot
      have htop_comm :
          (⊤ : EReal) + (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 =
            (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 + ⊤ := by
        calc
          (⊤ : EReal) + (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 = ⊤ := by
            simpa [one_div, EReal.coe_mul, EReal.coe_pow] using hleft
          _ = (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 + ⊤ := by
            simpa [one_div, EReal.coe_mul, EReal.coe_pow] using hright.symm
      simpa [indicator_apply, hxfeasible, hxC, hxD, one_div, EReal.coe_mul,
        EReal.coe_pow] using htop_comm
    · have hxfeasible : x ∉ feasibleSet := by
        simp [Set.mem_inter_iff, Set.mem_preimage, hxC, hxD]
      have hleft :
          (⊤ : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) = ⊤ :=
        EReal.top_add_of_ne_bot hhalf_ne_bot
      have hright :
          ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) + ⊤ = ⊤ :=
        EReal.add_top_of_ne_bot hhalf_ne_bot
      have htop_comm :
          (⊤ : EReal) + (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 =
            (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 + ⊤ := by
        calc
          (⊤ : EReal) + (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 = ⊤ := by
            simpa [one_div, EReal.coe_mul, EReal.coe_pow] using hleft
          _ = (↑(2⁻¹ : ℝ) : EReal) * (↑‖x - z‖ : EReal) ^ 2 + ⊤ := by
            simpa [one_div, EReal.coe_mul, EReal.coe_pow] using hright.symm
      simpa [indicator_apply, hxfeasible, hxC, hxD, one_div, EReal.coe_mul,
        EReal.coe_pow] using htop_comm

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 19.10: after replacing the indicator functions by their effective
domains, the owner regularity condition is exactly the textbook `sri` hypothesis. -/
private lemma zero_mem_sri_image_effectiveDomain_indicator_sub :
    (hsri : (0 : K) ∈ sri (L '' C - D)) →
    (0 : K) ∈ sri (L '' effectiveDomain (ι[C]) - effectiveDomain (ι[D])) := by
  intro hsri
  -- Route correction: isolate the indicator-domain rewrite once so both theorem proofs use the
  -- same source-faithful regularity bridge.
  simpa [effectiveDomain_indicator] using hsri

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 19.10: on the feasible set, minimizing `‖x - z‖` is equivalent to
minimizing `(1 / 2) ‖x - z‖²`. -/
private lemma argminOn_norm_eq_argminOn_half_sqDist :
    Argmin[feasibleSet] primalObj = Argmin[feasibleSet] halfSqObj := by
  ext x
  constructor
  · intro hx
    rcases mem_argminOn_iff.mp hx with ⟨hx_feasible, hx_min⟩
    refine mem_argminOn_iff.mpr ⟨hx_feasible, ?_⟩
    -- Convert norm minimization into squared-norm minimization by monotonicity on `ℝ≥0`.
    rw [isMinOn_iff] at hx_min ⊢
    intro y hy_feasible
    have hxy : ‖x - z‖ ≤ ‖y - z‖ := by
      exact_mod_cast hx_min y hy_feasible
    have hxy_sq : (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖y - z‖ ^ 2 := by
      nlinarith [hxy, norm_nonneg (x - z), norm_nonneg (y - z)]
    exact_mod_cast hxy_sq
  · intro hx
    rcases mem_argminOn_iff.mp hx with ⟨hx_feasible, hx_min⟩
    refine mem_argminOn_iff.mpr ⟨hx_feasible, ?_⟩
    -- The same monotonicity argument recovers the original norm objective.
    rw [isMinOn_iff] at hx_min ⊢
    intro y hy_feasible
    have hxy_sq : (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖y - z‖ ^ 2 := by
      exact_mod_cast hx_min y hy_feasible
    have hxy : ‖x - z‖ ≤ ‖y - z‖ := by
      nlinarith [hxy_sq, norm_nonneg (x - z), norm_nonneg (y - z)]
    exact_mod_cast hxy

-- Proof sketch: apply Proposition 19.5 with `φ = ι_C`, `ψ = ι_D`, and `r = 0`. Rewrite the dual
-- objective by the indicator Moreau-envelope formula and the conjugate of an indicator as a
-- support function. Then identify the proximal point of `ι_C` with the metric projection onto
-- `C`, and use that minimizing `‖x - z‖` over the feasible set is equivalent to minimizing
-- `(1 / 2) ‖x - z‖²`.
include hC_closed hC_convex hD_closed hD_convex hsri in
/-- Example 19 10: if `C` and `D` are closed convex subsets of real Hilbert spaces and
`0 ∈ sri (L(C) - D)`, then the dual problem
`v ↦ (1 / 2) ‖z - L^* v‖² - (1 / 2) d_C(z - L^* v)² + σ[D] v` has a solution. -/
theorem argmin_bestApproximationDual_nonempty :
    (Argmin dualObj).Nonempty := by
  rcases exists_mem_and_image_mem_of_zero_mem_sri_image_sub (L := L) hsri with
    ⟨x0, hx0C, hx0D⟩
  have hC_nonempty : C.Nonempty := ⟨x0, hx0C⟩
  have hD_nonempty : D.Nonempty := ⟨L x0, hx0D⟩
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local C hC_nonempty hC_closed hC_convex
  have hD_gamma : ι[D] ∈ Γ₀(K) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local D hD_nonempty hD_closed hD_convex
  obtain ⟨howner_nonempty, _⟩ :=
    argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator
      (φ := ι[C]) (hφ := hC_gamma) (hψ := hD_gamma) (z := z) (r := (0 : K)) (L := L)
      (zero_mem_sri_image_effectiveDomain_indicator_sub
        (L := L) hsri)
  rcases howner_nonempty with ⟨w, hw0⟩
  have hw :
      w ∈ Argmin
        (fun v : K ↦
          ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
            ({}^[(1 : PosReal)] ι[C]) (z - L.adjoint v)) +
              (((ι[D])∗[hD_gamma] v : EReal))) := by
    -- The specialized owner dual objective has no linear term because `r = 0`.
    simpa using hw0
  have hw_textbook : w ∈ Argmin dualObj := by
    -- Rewrite the owner dual surface into the textbook formula.
    rw [(specialized_dual_owner_eq_dualObj
      (C := C) (D := D) (z := z) (L := L) hsri hC_gamma hD_gamma)] at hw
    exact hw
  exact ⟨w, hw_textbook⟩

include hC_closed hC_convex hD_closed hD_convex hsri in
/-- Projection formula for Example 19 10: if `v` solves the dual problem above, then the unique
minimizer of `‖x - z‖`
over `x ∈ C` with `L x ∈ D` is `P_C (z - L^* v)`. -/
theorem argminOn_norm_eq_singleton_projectionPoint_of_mem_dualArgmin
    {v : K} (hv : v ∈ Argmin dualObj) :
    Argmin[feasibleSet] primalObj =
      ({P_C (z - L.adjoint v)} : Set H) := by
  rcases exists_mem_and_image_mem_of_zero_mem_sri_image_sub (L := L) hsri with
    ⟨x0, hx0C, hx0D⟩
  have hC_nonempty : C.Nonempty := ⟨x0, hx0C⟩
  have hD_nonempty : D.Nonempty := ⟨L x0, hx0D⟩
  have hx0_feasible : x0 ∈ feasibleSet := ⟨hx0C, hx0D⟩
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local C hC_nonempty hC_closed hC_convex
  have hD_gamma : ι[D] ∈ Γ₀(K) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex_local D hD_nonempty hD_closed hD_convex
  have hv_owner :
      v ∈ Argmin
        (fun u : K ↦
          ((((1 / 2 : ℝ) * ‖z - L.adjoint u‖ ^ 2 : ℝ) : EReal) -
            ({}^[(1 : PosReal)] ι[C]) (z - L.adjoint u)) +
              (((ι[D])∗[hD_gamma] u : EReal))) := by
    -- Translate the textbook dual minimizer back to the specialized owner objective.
    rw [(specialized_dual_owner_eq_dualObj
      (C := C) (D := D) (z := z) (L := L) hsri hC_gamma hD_gamma).symm] at hv
    exact hv
  have hv_owner0 :
      v ∈ Argmin
        (fun u : K ↦
          ((((1 / 2 : ℝ) * ‖z - L.adjoint u‖ ^ 2 : ℝ) : EReal) -
            ({}^[(1 : PosReal)] ι[C]) (z - L.adjoint u)) +
              (((ι[D])∗[hD_gamma] u : EReal)) +
                (((⟪u, (0 : K)⟫_ℝ : ℝ) : EReal))) := by
    -- Reinsert the vanishing linear term so that Proposition 19.5 applies verbatim.
    simpa using hv_owner
  obtain ⟨_, hprimal_singleton⟩ :=
    argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator
      (φ := ι[C]) (hφ := hC_gamma) (hψ := hD_gamma) (z := z) (r := (0 : K)) (L := L)
      (zero_mem_sri_image_effectiveDomain_indicator_sub
        (L := L) hsri)
  have hprox_raw :
      Prox[ι[C], hC_gamma] =
        P[C, isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex] := by
    simpa using
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex
  have hcheb_eq :
      isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex = hC_cheb := by
    apply Subsingleton.elim
  have hprox :
      Prox[ι[C], hC_gamma] = P_C := by
    -- Replace the generic Chebyshev witness by the local one from the `sri` hypothesis.
    simpa [hcheb_eq] using hprox_raw
  have howner_primal_raw :
      Argmin
          (fun x : H ↦
            (ι[C] x : EReal) + (ι[D] (L x - (0 : K)) : EReal) +
              ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))) =
        ({Prox[ι[C], hC_gamma] (z - L.adjoint v)} : Set H) := by
    exact hprimal_singleton hv_owner0
  have howner_primal :
      Argmin (fun x : H ↦ halfSqObj x + (ι[feasibleSet] x : EReal)) =
        ({P_C (z - L.adjoint v)} : Set H) := by
    -- Rewrite the owner primal surface into the feasible-set indicator presentation.
    rw [show
        (fun x : H ↦
          (ι[C] x : EReal) + (ι[D] (L x - (0 : K)) : EReal) +
            ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))) =
          fun x : H ↦ halfSqObj x + (ι[feasibleSet] x : EReal) by
          simpa [sub_zero] using
            (specialized_primal_owner_eq_halfSqDist_add_indicator_feasibleSet
              (C := C) (D := D) (z := z) (L := L)),
      hprox] at howner_primal_raw
    simpa using howner_primal_raw
  have hhalf_not_bot : ∀ x ∉ feasibleSet, halfSqObj x ≠ ⊥ := by
    -- The half squared-distance objective is real-valued.
    intro x _
    change ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥
    exact EReal.coe_ne_bot ((1 / 2 : ℝ) * ‖x - z‖ ^ 2)
  have hargminOn_halfSq :
      Argmin[feasibleSet] halfSqObj =
        feasibleSet ∩ Argmin (fun x : H ↦ halfSqObj x + (ι[feasibleSet] x : EReal)) :=
    argminOn_eq_inter_argmin_add_indicator (f := halfSqObj) feasibleSet hhalf_not_bot
  have hp_global :
      P_C (z - L.adjoint v) ∈
        Argmin (fun x : H ↦ halfSqObj x + (ι[feasibleSet] x : EReal)) := by
    rw [howner_primal]
    exact Set.mem_singleton _
  have hp_feasible : P_C (z - L.adjoint v) ∈ feasibleSet := by
    -- Compare the singleton minimizer against the finite value at the feasible witness `x0`.
    rw [mem_argmin_iff, isMinOn_univ_iff] at hp_global
    by_contra hp_not_feasible
    have hp_top :
        (halfSqObj (P_C (z - L.adjoint v)) + (ι[feasibleSet] (P_C (z - L.adjoint v)) : EReal)) =
          ⊤ := by
      have hhalf_ne_bot :
          ((((1 / 2 : ℝ) * ‖P_C (z - L.adjoint v) - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ :=
        EReal.coe_ne_bot ((1 / 2 : ℝ) * ‖P_C (z - L.adjoint v) - z‖ ^ 2)
      have hindicator_top :
          (ι[feasibleSet] (P_C (z - L.adjoint v)) : EReal) = ⊤ := by
        simp [hp_not_feasible]
      rw [hindicator_top]
      exact EReal.add_top_of_ne_bot hhalf_ne_bot
    have hx0_finite :
        (halfSqObj x0 + (ι[feasibleSet] x0 : EReal)) ≠ ⊤ := by
      have hhalf_ne_top :
          ((((1 / 2 : ℝ) * ‖x0 - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊤ :=
        EReal.coe_ne_top ((1 / 2 : ℝ) * ‖x0 - z‖ ^ 2)
      have hindicator_zero : (ι[feasibleSet] x0 : EReal) = 0 := by
        simp [hx0_feasible]
      rw [hindicator_zero, add_zero]
      exact hhalf_ne_top
    have hmin :
        (halfSqObj (P_C (z - L.adjoint v)) + (ι[feasibleSet] (P_C (z - L.adjoint v)) : EReal)) ≤
          (halfSqObj x0 + (ι[feasibleSet] x0 : EReal)) :=
      hp_global x0
    rw [hp_top] at hmin
    exact hx0_finite (top_le_iff.mp hmin)
  have hargminOn_halfSq_singleton :
      Argmin[feasibleSet] halfSqObj = ({P_C (z - L.adjoint v)} : Set H) := by
    -- The singleton owner minimizer is already feasible, so the constrained and global
    -- indicatorized minimizers coincide.
    rw [hargminOn_halfSq, howner_primal]
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hp_feasible, Set.mem_singleton _⟩
  -- Replace the half squared-distance minimizers by the norm minimizers from the textbook.
  rw [argminOn_norm_eq_argminOn_half_sqDist
    (C := C) (D := D) (z := z) (L := L)]
  exact hargminOn_halfSq_singleton

end PrimalSolutionsViaDualSolutions

end ERealFunction
