import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap04.Corollary_4_13
import BauschkeLean.Chap04.Proposition_4_4
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Example_13_6
import BauschkeLean.Chap14.Corollary_14_8
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.Proposition_12_28
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Remark_16_28
import BauschkeLean.Chap16.Theorem_16_58
import BauschkeLean.Chap27.Proposition_27_5
import BauschkeLean.Chap27.Theorem_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set Function
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_completeSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Corollary 19.7 is the fixed-point reformulation of the equality-constrained
  proximal problem.
- `core/canonical`: the proximal owners are `proximalObjective φ z` and `Prox[φ, hφ]`; the
  equality-constraint owner is `equalityConstraintPerturbation f L r` from Proposition 19.21.
- `bridge/view`: the sampled upstream owners are Proposition 12.28 for firm nonexpansiveness of
  `Prox[φ, hφ]`, Corollary 4.13 for adjoint compression, Proposition 19.21 for the equality
  constraint owner, and Proposition 19.5 for the proximal specialization. The source-facing map
  `proximalConstraintDualMap` is the textbook affine fixed-point map whose fixed points encode the
  equality constraint on the associated proximal point; the residual-map view stays derived rather
  than driving the public surface. -/

/-- The dual fixed-point map associated with the linearly constrained proximal problem from
Corollary 19.7. -/
abbrev proximalConstraintDualMap
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) : K → K :=
  fun v ↦ v - r + L (Prox[φ, hφ] (z - L.adjoint v))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 19 7: on the effective domain, the proximal objective is the
corresponding finite real-valued expression. -/
private theorem proximalObjective_eq_coe_toReal_add_quadratic_of_mem_effectiveDomain
    {φ : H → Set.Ioi (⊥ : EReal)} (z x : H) (hx : x ∈ effectiveDomain φ) :
    proximalObjective φ z x =
      (((φ x : EReal).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ 2 : ℝ) : EReal) := by
  -- On the effective domain, `φ x` is finite, so the proximal objective is just a finite
  -- `EReal` coercion of the usual real-valued formula.
  have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (φ x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ x : EReal) from (φ x).2)
  rw [proximalObjective, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
  simp

/-
The effective-domain test is purely order-theoretic, so the ambient Hilbert-space structure is
not part of this helper's API.
-/
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 19 7: outside the effective domain, the proximal objective equals `⊤`. -/
private theorem proximalObjective_eq_top_of_not_mem_effectiveDomain
    {φ : H → Set.Ioi (⊥ : EReal)} (z x : H) (hx : x ∉ effectiveDomain φ) :
    proximalObjective φ z x = ⊤ := by
  -- Outside the effective domain, the function value is already `⊤`, and the finite quadratic
  -- term does not change that.
  have hx_top : (φ x : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
  rw [proximalObjective, hx_top, EReal.top_add_coe]

omit [CompleteSpace K] in
/-- Helper for Corollary 19 7: translating a strong-relative-interior point to the origin turns
the regularity set into the difference with the singleton base point. -/
private theorem zero_mem_sri_sub_singleton_of_mem_sri
    {C : Set K} {y : K} (hy : y ∈ sri C) :
    (0 : K) ∈ sri (C - ({y} : Set K)) := by
  rcases Set.mem_strongRelativeInterior_iff.mp hy with ⟨hyC, hcone⟩
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨?_, ?_⟩
  · refine Set.mem_sub.mpr ?_
    exact ⟨y, hyC, y, by simp, sub_self y⟩
  · simpa using hcone

omit [CompleteSpace K] in
/-- Helper for Corollary 19 7: reflecting a convex set through the origin reflects its conic
hull. -/
private theorem cone_neg_eq_neg_cone
    {C : Set K} (hC_convex : Convex ℝ C) :
    cone (-C) = -cone C := by
  calc
    cone (-C) = ((hC_convex.neg.toCone (-C) : ConvexCone ℝ K) : Set K) := by
      simpa [Set.cone_def] using (convexCone_hull_eq_toCone (E := K) hC_convex.neg)
    _ = -(((hC_convex.toCone C : ConvexCone ℝ K) : Set K)) := by
      symm
      exact neg_toCone_eq_toCone_neg hC_convex
    _ = -cone C := by
      rw [show cone C = ((hC_convex.toCone C : ConvexCone ℝ K) : Set K) by
        simpa [Set.cone_def] using (convexCone_hull_eq_toCone (E := K) hC_convex)]

omit [CompleteSpace K] in
/-- Helper for Corollary 19 7: reflecting a strong-relative-interior set at the origin preserves
the origin strong-relative-interior witness. -/
private theorem zero_mem_sri_neg_of_zero_mem_sri
    {C : Set K} (hC_convex : Convex ℝ C) (hzero : (0 : K) ∈ sri C) :
    (0 : K) ∈ sri (-C) := by
  rcases Set.mem_strongRelativeInterior_iff.mp hzero with ⟨hzero_mem, hcone_eq⟩
  have hneg_nonempty : (-C : Set K).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [Set.mem_neg] using hzero_mem
  refine
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      (E := K) hneg_nonempty hC_convex.neg).2 ?_
  calc
    cone (-C) = -cone C := cone_neg_eq_neg_cone (K := K) hC_convex
    _ = -(((Submodule.span ℝ C).topologicalClosure : Submodule ℝ K) : Set K) := by
      simpa using congrArg Neg.neg hcone_eq
    _ = (((Submodule.span ℝ C).topologicalClosure : Submodule ℝ K) : Set K) := by
      ext x
      constructor
      · intro hx
        simpa using ((Submodule.span ℝ C).topologicalClosure.neg_mem hx)
      · intro hx
        exact ((Submodule.span ℝ C).topologicalClosure.neg_mem hx)
    _ = (((Submodule.span ℝ (-C)).topologicalClosure : Submodule ℝ K) : Set K) := by
      simp [Submodule.span_neg]

/-- Helper for Corollary 19 7: taking the product with `univ` preserves a strong-relative-
interior witness at the origin. -/
private theorem zero_mem_sri_prod_univ_of_zero_mem_sri
    {S : Set H} (hS_convex : Convex ℝ S) (hsri : (0 : H) ∈ sri S) :
    (0 : H × K) ∈ sri (S ×ˢ (Set.univ : Set K)) := by
  have hzeroS : (0 : H) ∈ S := (Set.mem_strongRelativeInterior_iff.mp hsri).1
  have hS_nonempty : S.Nonempty := ⟨0, hzeroS⟩
  have hconeS :
      cone S = ((Submodule.span ℝ S).topologicalClosure : Set H) := by
    exact
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        hS_nonempty hS_convex).1 hsri
  have hcone_prod :
      cone (S ×ˢ (Set.univ : Set K)) = cone S ×ˢ (Set.univ : Set K) := by
    rw [cone_eq_toCone_of_convex (H := H × K) (hS_convex.prod convex_univ)]
    ext p
    constructor
    · intro hp
      rcases (Convex.mem_toCone (hS_convex.prod convex_univ)).1 hp with ⟨a, ha, q, hq, rfl⟩
      rcases hq with ⟨hqS, -⟩
      refine ⟨?_, by simp⟩
      rw [cone_eq_toCone_of_convex (H := H) hS_convex]
      exact (Convex.mem_toCone hS_convex).2 ⟨a, ha, q.1, hqS, rfl⟩
    · rintro ⟨hp, -⟩
      rw [cone_eq_toCone_of_convex (H := H) hS_convex] at hp
      rcases (Convex.mem_toCone hS_convex).1 hp with ⟨a, ha, x, hx, hax⟩
      refine (Convex.mem_toCone (hS_convex.prod convex_univ)).2 ?_
      refine ⟨a, ha, (x, a⁻¹ • p.2), ?_, ?_⟩
      · exact ⟨hx, by simp⟩
      · ext <;> simp [hax, ha.ne', smul_smul]
  have hspan_le :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) ≤
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    simpa [Submodule.span_univ] using
      (Submodule.span_prod_le (R := ℝ) S (Set.univ : Set K))
  have hspan_ge :
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) ≤
        Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := by
    have hsubset :
        LinearMap.inl ℝ H K '' S ∪ LinearMap.inr ℝ H K '' (Set.univ : Set K) ⊆
          S ×ˢ (Set.univ : Set K) := by
      intro p hp
      rcases hp with hp | hp
      · rcases hp with ⟨x, hx, rfl⟩
        exact ⟨hx, by simp⟩
      · rcases hp with ⟨y, -, rfl⟩
        exact ⟨hzeroS, by simp⟩
    calc
      (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) =
          Submodule.span ℝ
            (LinearMap.inl ℝ H K '' S ∪ LinearMap.inr ℝ H K '' (Set.univ : Set K)) := by
              symm
              simpa [Submodule.span_univ] using
                (LinearMap.span_inl_union_inr (R := ℝ) (M := H) (M₂ := K)
                  (s := S) (t := (Set.univ : Set K)))
      _ ≤ Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) := Submodule.span_mono hsubset
  have hspan_eq :
      Submodule.span ℝ (S ×ˢ (Set.univ : Set K)) =
        (Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) := by
    exact le_antisymm hspan_le hspan_ge
  have hclosure_prod :
      ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (H × K)) =
        (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ (Set.univ : Set K)) := by
    rw [hspan_eq]
    change closure (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) : Set (H × K))) =
      (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ (Set.univ : Set K))
    have hprod_set :
        (((Submodule.span ℝ S).prod (⊤ : Submodule ℝ K) : Set (H × K))) =
          ((Submodule.span ℝ S : Set H) ×ˢ (Set.univ : Set K)) := by
      rfl
    rw [hprod_set, closure_prod_eq]
    simp
  have hcone_eq :
      cone (S ×ˢ (Set.univ : Set K)) =
        ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (H × K)) := by
    calc
      cone (S ×ˢ (Set.univ : Set K)) = cone S ×ˢ (Set.univ : Set K) := hcone_prod
      _ = (((Submodule.span ℝ S).topologicalClosure : Set H) ×ˢ (Set.univ : Set K)) := by
            rw [hconeS]
      _ = ((Submodule.span ℝ (S ×ˢ (Set.univ : Set K))).topologicalClosure : Set (H × K)) := by
            symm
            exact hclosure_prod
  exact
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      ⟨(0 : H × K), by simp [hzeroS]⟩
      (hS_convex.prod convex_univ)).2 hcone_eq

omit [CompleteSpace H] in
/-- Helper for Corollary 19 7: proximal points of a `Γ₀` function lie in its effective domain. -/
private theorem mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) {x p : H}
    (hp : IsProxPoint φ x p) :
    p ∈ effectiveDomain φ := by
  -- Unfold proximality to the minimizing property of the proximal objective and compare against
  -- one finite witness from the nonempty effective domain of `φ`.
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  rcases hφ.2.nonempty with ⟨q, hq⟩
  have hobj_q_ne_top : proximalObjective φ x q ≠ ⊤ := by
    rw [proximalObjective_eq_coe_toReal_add_quadratic_of_mem_effectiveDomain x q hq]
    exact EReal.coe_ne_top _
  by_contra hp_dom
  have hobj_p_top : proximalObjective φ x p = ⊤ :=
    proximalObjective_eq_top_of_not_mem_effectiveDomain x p hp_dom
  have hpq : proximalObjective φ x p ≤ proximalObjective φ x q := hp q
  rw [hobj_p_top] at hpq
  exact hobj_q_ne_top (top_le_iff.mp hpq)

/-- Helper for Corollary 19 7: among feasible points, the proximal point improves the objective
by the standard quadratic defect. -/
private theorem proximalObjective_add_quadratic_defect_le_of_isProxPoint_and_constraint
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) {v : K} {p y : H}
    (hp : IsProxPoint φ (z - L.adjoint v) p)
    (hp_feas : L p = r) (hy_feas : L y = r) :
    proximalObjective φ z p +
        ((((1 / 2 : ℝ) * ‖y - p‖ ^ 2 : ℝ) : EReal)) ≤
      proximalObjective φ z y := by
  by_cases hy : y ∈ effectiveDomain φ
  · -- First convert the proximal variational inequality at `z - L^* v` into a real inequality.
    have hp_dom : p ∈ effectiveDomain φ :=
      mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hφ hp
    have hp_top : (φ p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hp_bot : (φ p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (φ p : EReal) from (φ p).2)
    have hy_top : (φ y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (φ y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (φ y : EReal) from (φ y).2)
    have hprox_var :
        (⟪y - p, (z - L.adjoint v) - p⟫_ℝ : EReal) + (φ p : EReal) ≤ (φ y : EReal) :=
      (isProxPoint_iff_forall_inner_add_le φ hφ.2 (z - L.adjoint v) p).1 hp y
    have hvar_real :
        ⟪y - p, (z - L.adjoint v) - p⟫_ℝ + (φ p : EReal).toReal ≤
          (φ y : EReal).toReal := by
      have hcast :
          (((⟪y - p, (z - L.adjoint v) - p⟫_ℝ + (φ p : EReal).toReal : ℝ) : EReal)) ≤
            (((φ y : EReal).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_toReal hp_top hp_bot, ← EReal.coe_toReal hy_top hy_bot,
          ← EReal.coe_add] at hprox_var
        exact hprox_var
      exact_mod_cast hcast
    have hfiber :
        inner ℝ (y - p) ((z - L.adjoint v) - p) = inner ℝ (y - p) (z - p) := by
      have hLy : L (y - p) = 0 := by
        rw [map_sub, hy_feas, hp_feas, sub_self]
      have hadj : inner ℝ (y - p) (L.adjoint v) = 0 := by
        calc
          inner ℝ (y - p) (L.adjoint v) = inner ℝ (L (y - p)) v := by
            rw [ContinuousLinearMap.adjoint_inner_right]
          _ = 0 := by simp [hLy]
      calc
        inner ℝ (y - p) ((z - L.adjoint v) - p)
            = inner ℝ (y - p) ((z - p) - L.adjoint v) := by abel_nf
        _ = inner ℝ (y - p) (z - p) - inner ℝ (y - p) (L.adjoint v) := by
              rw [inner_sub_right]
        _ = inner ℝ (y - p) (z - p) := by simp [hadj]
    have hbase_real :
        inner ℝ (y - p) (z - p) + (φ p : EReal).toReal ≤ (φ y : EReal).toReal := by
      simpa [hfiber] using hvar_real
    have hnorm :
        ‖z - y‖ ^ 2 =
          ‖z - p‖ ^ 2 - 2 * inner ℝ (y - p) (z - p) + ‖y - p‖ ^ 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, real_inner_comm] using
        (norm_sub_sq_real (z - p) (y - p))
    have hobj_real :
        (φ p : EReal).toReal + (1 / 2 : ℝ) * ‖z - p‖ ^ 2 +
            (1 / 2 : ℝ) * ‖y - p‖ ^ 2 ≤
          (φ y : EReal).toReal + (1 / 2 : ℝ) * ‖z - y‖ ^ 2 := by
      -- The feasible-fiber cancellation turns the proximal inequality into the desired defect.
      nlinarith [hbase_real, hnorm]
    have hcast :
        (((φ p : EReal).toReal + (1 / 2 : ℝ) * ‖z - p‖ ^ 2 +
            (1 / 2 : ℝ) * ‖y - p‖ ^ 2 : ℝ) :
            EReal) ≤
          (((φ y : EReal).toReal + (1 / 2 : ℝ) * ‖z - y‖ ^ 2 : ℝ) : EReal) := by
      exact_mod_cast hobj_real
    -- Finally rewrite both proximal objectives into their finite real representatives.
    rw [proximalObjective_eq_coe_toReal_add_quadratic_of_mem_effectiveDomain z p hp_dom,
      proximalObjective_eq_coe_toReal_add_quadratic_of_mem_effectiveDomain z y hy]
    rw [← EReal.coe_add]
    convert hcast using 1
  · -- Outside the effective domain, the comparison objective is `⊤`,
    -- so the defect estimate is automatic.
    rw [proximalObjective_eq_top_of_not_mem_effectiveDomain z y hy]
    exact le_top

-- Proof sketch: unfold `proximalConstraintDualMap`, rewrite fixed-point membership as
-- `v - r + L (Prox_φ (z - L^* v)) = v`, and rearrange the equality.
/-- A vector is a fixed point of the Corollary 19.7 dual map exactly when its associated proximal
point satisfies the linear constraint `Lx = r`. -/
@[simp] theorem mem_fixedPoints_proximalConstraintDualMap_iff
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) {v : K} :
    v ∈ fixedPoints (proximalConstraintDualMap φ hφ z r L) ↔
      L (Prox[φ, hφ] (z - L.adjoint v)) = r := by
  rw [Function.mem_fixedPoints_iff, proximalConstraintDualMap]
  constructor
  · intro hv
    have hv' : (v + L (Prox[φ, hφ] (z - L.adjoint v))) - r = v := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hv
    rw [sub_eq_iff_eq_add] at hv'
    exact add_left_cancel <| by simpa [add_assoc, add_left_comm, add_comm] using hv'
  · intro hv
    rw [hv]
    abel_nf

/-- Helper for Corollary 19 7: the dual map is `Id` minus the gradient term
`v ↦ r - L (Prox[φ, hφ] (z - L.adjoint v))`. -/
private theorem proximalConstraintDualMap_eq_id_sub_gradientTerm
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) :
    proximalConstraintDualMap φ hφ z r L =
      fun v ↦ v - (r - L (Prox[φ, hφ] (z - L.adjoint v))) := by
  -- Unfold the dual map and regroup it as `Id - ∇d`.
  funext v
  simp [proximalConstraintDualMap, sub_eq_add_neg]
  abel_nf

omit [CompleteSpace K] in
/-- Helper for Corollary 19 7: translating a firmly nonexpansive map by a constant preserves firm
nonexpansiveness, since pairwise differences are unchanged. -/
private theorem add_const_firmlyNonexpansive
    {T : K → K} (c : K) (hT : FirmlyNonexpansive T) :
    FirmlyNonexpansive (fun x ↦ c + T x) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner] at hT ⊢
  intro x y
  -- Constant translations do not change pairwise displacements,
  -- so the firm inequality is unchanged.
  have hdiff : (c + T x) - (c + T y) = T x - T y := by
    abel_nf
  simpa [hdiff] using hT x y

omit [CompleteSpace H] in
/-- Helper for Corollary 19 7: proximal points of a `Γ₀` function satisfy the pairwise firm
inequality. -/
private theorem prox_point_pairwise_firm_inequality_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) {x y p q : H}
    (hp : IsProxPoint φ x p) (hq : IsProxPoint φ y q) :
    ‖p - q‖ ^ (2 : ℕ) ≤ inner ℝ (p - q) (x - y) := by
  have hp_dom : p ∈ effectiveDomain φ :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hφ hp
  have hq_dom : q ∈ effectiveDomain φ :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hφ hq
  have hp_top : (φ p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
  have hp_bot : (φ p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ p : EReal) from (φ p).2)
  have hq_top : (φ q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq_dom)
  have hq_bot : (φ q : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ q : EReal) from (φ q).2)
  have hpq_ereal :
      (⟪q - p, x - p⟫_ℝ : EReal) + (φ p : EReal) ≤ (φ q : EReal) :=
    (isProxPoint_iff_forall_inner_add_le φ hφ.2 x p).1 hp q
  have hpq :
      ⟪q - p, x - p⟫_ℝ + (φ p : EReal).toReal ≤ (φ q : EReal).toReal := by
    have hcast :
        (((⟪q - p, x - p⟫_ℝ + (φ p : EReal).toReal : ℝ) : EReal)) ≤
          (((φ q : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hp_top hp_bot, ← EReal.coe_toReal hq_top hq_bot,
        ← EReal.coe_add] at hpq_ereal
      exact hpq_ereal
    exact_mod_cast hcast
  have hqp_ereal :
      (⟪p - q, y - q⟫_ℝ : EReal) + (φ q : EReal) ≤ (φ p : EReal) :=
    (isProxPoint_iff_forall_inner_add_le φ hφ.2 y q).1 hq p
  have hqp :
      ⟪p - q, y - q⟫_ℝ + (φ q : EReal).toReal ≤ (φ p : EReal).toReal := by
    have hcast :
        (((⟪p - q, y - q⟫_ℝ + (φ q : EReal).toReal : ℝ) : EReal)) ≤
          (((φ p : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hq_top hq_bot, ← EReal.coe_toReal hp_top hp_bot,
        ← EReal.coe_add] at hqp_ereal
      exact hqp_ereal
    exact_mod_cast hcast
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hsub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hqpd : q - p = -d := by
    dsimp [d]
    abel_nf
  have hrewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by rw [hqpd]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by rw [hsub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hsum
  have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d] using hfinal

/-- Helper for Corollary 19.7: the signed translated proximal map
`x ↦ -Prox[φ, hφ] (z - x)` is firmly nonexpansive. -/
private theorem neg_proximityOperator_sub_const_firmlyNonexpansive_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) (z : H) :
    FirmlyNonexpansive (fun x : H ↦ -Prox[φ, hφ] (z - x)) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  have hp :
      IsProxPoint φ (z - y) (Prox[φ, hφ] (z - y)) := by
    exact
      proximityOperator_isProxPoint
        φ
        (hasUniqueProxPoint_of_mem_gammaZero φ hφ)
        (z - y)
  have hq :
      IsProxPoint φ (z - x) (Prox[φ, hφ] (z - x)) := by
    exact
      proximityOperator_isProxPoint
        φ
        (hasUniqueProxPoint_of_mem_gammaZero φ hφ)
        (z - x)
  have hfirm :
      ‖Prox[φ, hφ] (z - y) - Prox[φ, hφ] (z - x)‖ ^ (2 : ℕ) ≤
        inner ℝ (Prox[φ, hφ] (z - y) - Prox[φ, hφ] (z - x)) ((z - y) - (z - x)) :=
    prox_point_pairwise_firm_inequality_of_mem_gammaZero (hφ := hφ) hp hq
  have hfirm' :
      ‖-Prox[φ, hφ] (z - x) + Prox[φ, hφ] (z - y)‖ ^ (2 : ℕ) ≤
        inner ℝ (-Prox[φ, hφ] (z - x) + Prox[φ, hφ] (z - y)) ((z - y) - (z - x)) := by
    simpa [sub_eq_add_neg, add_comm] using hfirm
  have hxy : (z - y) - (z - x) = x - y := by
    abel_nf
  simpa [hxy] using hfirm'

/-- Helper for Corollary 19.7: compressing the signed translated proximal map through `L.adjoint`
preserves firm nonexpansiveness when `‖L‖ ≤ 1`. -/
private theorem compressed_negative_proximityOperator_firmlyNonexpansive
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) :
    FirmlyNonexpansive (fun v : K ↦ -L (Prox[φ, hφ] (z - L.adjoint v))) := by
  have hKernel :
      FirmlyNonexpansiveOn (Set.univ : Set H)
        (fun x : Set.univ ↦ -Prox[φ, hφ] (z - x)) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      neg_proximityOperator_sub_const_firmlyNonexpansive_of_mem_gammaZero (hφ := hφ) z
  have hAdj : ‖L.adjoint‖ ≤ 1 := by
    simpa [ContinuousLinearMap.adjoint.norm_map] using hL
  have hCompressed :
      FirmlyNonexpansiveOn (Set.univ : Set K)
        (fun v : Set.univ ↦
          (((L.adjoint).adjoint) ∘ (fun x : H ↦ -Prox[φ, hφ] (z - x)) ∘ L.adjoint) v) := by
    -- Corollary 4.13 applies to the whole-space signed proximal kernel composed with `L.adjoint`.
    simpa using
      adjoint_comp_firmlyNonexpansive_of_norm_le_one
        (H := K) (K := H)
        (T := fun x : H ↦ -Prox[φ, hφ] (z - x))
        hKernel L.adjoint hAdj
  simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ, Function.comp,
    ContinuousLinearMap.adjoint_adjoint] using hCompressed

/-- Helper for Corollary 19.7: the dual gradient term
`v ↦ r - L (Prox[φ, hφ] (z - L.adjoint v))` is firmly nonexpansive. -/
private theorem proximal_constraint_gradient_term_firmlyNonexpansive
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) :
    FirmlyNonexpansive (fun v : K ↦ r - L (Prox[φ, hφ] (z - L.adjoint v))) := by
  have hCompressed :
      FirmlyNonexpansive (fun v : K ↦ -L (Prox[φ, hφ] (z - L.adjoint v))) :=
    compressed_negative_proximityOperator_firmlyNonexpansive (hφ := hφ) z L hL
  -- Adding the constant `r` recovers the gradient term without changing pairwise displacements.
  simpa [sub_eq_add_neg] using
    add_const_firmlyNonexpansive
      (T := fun v : K ↦ -L (Prox[φ, hφ] (z - L.adjoint v))) r hCompressed

-- Proof sketch: `Prox_φ` is firmly nonexpansive by Proposition 12.28. Corollary 4.13 transfers
-- firm nonexpansiveness to the gradient term `v ↦ r - L (Prox_φ (z - L^* v))`, so the displayed
-- map is the corresponding `Id - ∇d` operator.
/-- Corollary 19.7 (1): if `φ ∈ Γ₀(ℋ)`, `‖L‖ ≤ 1`, and `r ∈ sri (L (dom φ))`,
then the map `v ↦ v - r + L (Prox_φ (z - L^* v))` is firmly nonexpansive. -/
theorem proximalConstraintDualMap_firmlyNonexpansive_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1)
    (hsri : r ∈ sri (L '' effectiveDomain φ)) :
    FirmlyNonexpansive (proximalConstraintDualMap φ hφ z r L) := by
  -- Route correction: the previously attempted source route through the shifted map
  -- `x ↦ Prox[φ, hφ] (z - x)` is false in general, so clause `(1)` must be rebuilt from the
  -- correct owner/sign convention before the `Id - ∇d` argument can be completed.
  let _ := hsri
  have hGradient :
      FirmlyNonexpansive (fun v : K ↦ r - L (Prox[φ, hφ] (z - L.adjoint v))) :=
    proximal_constraint_gradient_term_firmlyNonexpansive (hφ := hφ) z r L hL
  have hGradientOn :
      FirmlyNonexpansiveOn (Set.univ : Set K)
        (fun v : Set.univ ↦ r - L (Prox[φ, hφ] (z - L.adjoint v))) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using hGradient
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  -- Rewrite the fixed-point map as the residual of the firmly nonexpansive gradient term.
  rw [proximalConstraintDualMap_eq_id_sub_gradientTerm]
  simpa [residualMap] using
    (firmlyNonexpansiveOn_residualMap_iff
      (Set.univ : Set K)
      (fun v : Set.univ ↦ r - L (Prox[φ, hφ] (z - L.adjoint v)))).2 hGradientOn

attribute [local instance] prod_pseudoMetricSpace_l2
attribute [local instance] prod_normedAddCommGroup_l2
attribute [local instance] prod_normedSpace_l2
attribute [local instance] prod_completeSpace_l2
attribute [local instance] prod_innerProductSpace_l2

/-- Helper for Corollary 19 7: the product map `x ↦ (L x, x)` packages the equality constraint
and the quadratic term into a single composite objective. -/
private abbrev constraintProductMap
    (L : H →L[ℝ] K) : H →L[ℝ] K × H :=
  L.prod (ContinuousLinearMap.id ℝ H)

/-- Helper for Corollary 19 7: the shifted half-squared norm `x ↦ ‖x - z‖² / 2` remains in
`Γ₀(H)`. -/
private abbrev shiftedHalfSquaredNorm
    (z : H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ halfSquaredNorm (-z + x)

/-- Helper for Corollary 19 7: the product-space penalty combines the equality indicator on the
first coordinate with the shifted half-squared norm on the second. -/
private abbrev equalityConstraintQuadraticPenalty
    (z : H) (r : K) : K × H → Set.Ioi (⊥ : EReal) :=
  ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) ∘ ContinuousLinearMap.fst ℝ K H) +
    (shiftedHalfSquaredNorm (H := H) z ∘ ContinuousLinearMap.snd ℝ K H)

/-- Helper for Corollary 19 7: the shifted half-squared norm has full effective domain. -/
private theorem mem_effectiveDomain_shiftedHalfSquaredNorm
    (z x : H) :
    x ∈ effectiveDomain (shiftedHalfSquaredNorm (H := H) z) := by
  rw [mem_effectiveDomain_iff]
  rw [shiftedHalfSquaredNorm, halfSquaredNorm_apply]
  exact EReal.coe_lt_top _

/-- Helper for Corollary 19 7: the product-space equality-and-quadratic penalty belongs to
`Γ₀(K × H)`. -/
private theorem equalityConstraintQuadraticPenalty_mem_gammaZero
    (z : H) (r : K) :
    equalityConstraintQuadraticPenalty (H := H) z r ∈ Γ₀(K × H) := by
  have hindicator :
      (ι[{r}] : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
    exact
      indicator_mem_gammaZero_of_nonempty_isClosed_convex
        ⟨r, by simp⟩
        isClosed_singleton
        (convex_singleton r)
  have hshift :
      shiftedHalfSquaredNorm (H := H) z ∈ Γ₀(H) := by
    simpa [shiftedHalfSquaredNorm] using
      translate_mem_gammaZero
        (hf := halfSquaredNorm_mem_gammaZero (H := H))
        (-z)
  have hfst :
      ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) ∘ ContinuousLinearMap.fst ℝ K H) ∈ Γ₀(K × H) := by
    refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty
      (ι[{r}])
      hindicator
      (ContinuousLinearMap.fst ℝ K H)
      ?_
    refine ⟨r, ?_, ?_⟩
    · exact ⟨(r, 0), by simp⟩
    · simpa [effectiveDomain_indicator]
  have hsnd :
      (shiftedHalfSquaredNorm (H := H) z ∘ ContinuousLinearMap.snd ℝ K H) ∈ Γ₀(K × H) := by
    refine comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty
      (shiftedHalfSquaredNorm (H := H) z)
      hshift
      (ContinuousLinearMap.snd ℝ K H)
      ?_
    refine ⟨z, ?_, mem_effectiveDomain_shiftedHalfSquaredNorm (H := H) z z⟩
    exact ⟨(0, z), by simp⟩
  refine pointwiseAdd_mem_gammaZero
    ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) ∘ ContinuousLinearMap.fst ℝ K H)
    (shiftedHalfSquaredNorm (H := H) z ∘ ContinuousLinearMap.snd ℝ K H)
    hfst
    hsnd
    ?_
  refine ⟨(r, z), ?_, ?_⟩
  · change r ∈ effectiveDomain (ι[{r}] : K → Set.Ioi (⊥ : EReal))
    simpa [effectiveDomain_indicator]
  · simpa using mem_effectiveDomain_shiftedHalfSquaredNorm (H := H) z z

/-- Helper for Corollary 19 7: the product-space penalty is finite exactly on
`{r} × univ`. -/
private theorem effectiveDomain_equalityConstraintQuadraticPenalty
    (z : H) (r : K) :
    effectiveDomain (equalityConstraintQuadraticPenalty (H := H) z r) =
      ({r} : Set K) ×ˢ (Set.univ : Set H) := by
  ext p
  constructor
  · intro hpdom
    by_cases hp : p.1 = r
    · exact ⟨hp, by simp⟩
    · exfalso
      rw [mem_effectiveDomain_iff] at hpdom
      have htop : (equalityConstraintQuadraticPenalty (H := H) z r p : EReal) = ⊤ := by
        have hsnd_ne_bot :
            ((shiftedHalfSquaredNorm (H := H) z p.2 : Set.Ioi (⊥ : EReal)) : EReal) ≠ ⊥ := by
          exact ne_of_gt (shiftedHalfSquaredNorm (H := H) z p.2).2
        calc
          (equalityConstraintQuadraticPenalty (H := H) z r p : EReal)
              = (((ι[{r}] : K → Set.Ioi (⊥ : EReal)) p.1 : EReal) +
                  ((shiftedHalfSquaredNorm (H := H) z p.2 : Set.Ioi (⊥ : EReal)) : EReal)) := by
                    rfl
          _ = ⊤ + ((shiftedHalfSquaredNorm (H := H) z p.2 : Set.Ioi (⊥ : EReal)) : EReal) := by
                simp [hp]
          _ = ⊤ := EReal.top_add_of_ne_bot hsnd_ne_bot
      rw [htop] at hpdom
      exact (lt_irrefl (⊤ : EReal)) hpdom
  · rintro ⟨hp, -⟩
    rw [mem_effectiveDomain_iff]
    subst hp
    have hp2 : p.2 ∈ effectiveDomain (shiftedHalfSquaredNorm (H := H) z) :=
      mem_effectiveDomain_shiftedHalfSquaredNorm (H := H) z p.2
    rw [mem_effectiveDomain_iff] at hp2
    simpa [equalityConstraintQuadraticPenalty, Function.comp] using hp2

/-- Helper for Corollary 19 7: subtracting the graph of `x ↦ (L x, x)` from `{r} × univ`
collapses to the first-coordinate difference paired with an unconstrained second coordinate. -/
private theorem effectiveDomain_equalityConstraintQuadraticPenalty_sub_image
    {φ : H → Set.Ioi (⊥ : EReal)} (z : H) (r : K) (L : H →L[ℝ] K) :
    effectiveDomain (equalityConstraintQuadraticPenalty (H := H) z r) -
        constraintProductMap (H := H) (K := K) L '' effectiveDomain φ =
      (effectiveDomain (ι[{r}] : K → Set.Ioi (⊥ : EReal)) - L '' effectiveDomain φ) ×ˢ
        (Set.univ : Set H) := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_sub.mp hp with ⟨a, ha, b, hb, hab⟩
    rcases hb with ⟨x, hx, rfl⟩
    refine ⟨?_, by simp⟩
    refine Set.mem_sub.mpr ?_
    refine ⟨r, ?_, L x, ⟨x, hx, rfl⟩, ?_⟩
    · simp [effectiveDomain_indicator]
    · have hfst : a.1 = r := by
        simpa [effectiveDomain_equalityConstraintQuadraticPenalty (H := H) z r] using ha
      simpa [constraintProductMap, hfst] using congrArg Prod.fst hab
  · intro hp
    rcases hp with ⟨hp1, hp2⟩
    rcases Set.mem_sub.mp hp1 with ⟨y, hy, b, hb, hyb⟩
    rcases hb with ⟨x, hx, rfl⟩
    have hy' : y = r := by
      simpa [effectiveDomain_indicator] using hy
    refine Set.mem_sub.mpr ?_
    refine ⟨(r, p.2 + x), ?_, constraintProductMap (H := H) (K := K) L x, ?_, ?_⟩
    · simpa [effectiveDomain_equalityConstraintQuadraticPenalty (H := H) z r]
    · exact ⟨x, hx, rfl⟩
    · ext
      · simpa [hy'] using hyb
      · simp

/-- Helper for Corollary 19 7: the adjoint of `x ↦ (L x, x)` is `w ↦ L^* w.1 + w.2`. -/
private theorem constraintProductMap_adjoint_apply
    (L : H →L[ℝ] K) (w : K × H) :
    (constraintProductMap (H := H) (K := K) L).adjoint w =
      L.adjoint w.1 + w.2 := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  calc
    ⟪constraintProductMap (H := H) (K := K) L x, w⟫_ℝ
        = ⟪L x, w.1⟫_ℝ + ⟪x, w.2⟫_ℝ := by
            rfl
    _ = ⟪x, L.adjoint w.1⟫_ℝ + ⟪x, w.2⟫_ℝ := by
          rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪x, L.adjoint w.1 + w.2⟫_ℝ := by
          rw [inner_add_right]

/-- Helper for Corollary 19 7: the subdifferential of the half-squared norm is the singleton
containing the base point. -/
private theorem mem_subdifferential_halfSquaredNorm_iff
    {x u : H} :
    u ∈ (∂ (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) x ↔ u = x := by
  have hdom : (effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_effectiveDomain_iff]
    simpa [halfSquaredNorm_apply] using (EReal.coe_lt_top (0 : ℝ))
  constructor
  · intro hu
    have hfy :
        ((halfSquaredNorm x : EReal) + (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal∗ u) =
          ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq
        (f := (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) hdom x u).1 hu
    rw [fenchelConjugate_halfSquaredNorm] at hfy
    have hfy_real : (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2 = ⟪x, u⟫_ℝ := by
      norm_num [halfSquaredNorm_apply] at hfy
      exact_mod_cast hfy
    have hsq : ‖x - u‖ ^ 2 = 0 := by
      have hnorm := norm_sub_sq_real x u
      nlinarith
    have hnorm0 : ‖x - u‖ = 0 := by
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa [norm_sub_rev] using hnorm0))
  · intro hu
    subst u
    apply (mem_subdifferential_iff_fenchel_young_eq
      (f := (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) hdom x x).2
    rw [fenchelConjugate_halfSquaredNorm, Function.asEReal_apply, halfSquaredNorm_apply]
    have hreal : (‖x‖ ^ 2) / 2 + (‖x‖ ^ 2) / 2 = ⟪x, x⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]
      ring
    exact_mod_cast hreal

/-- Helper for Corollary 19 7: any product-space subgradient of the equality-and-quadratic
penalty lies at a feasible point and has quadratic component `x - z`. -/
private theorem feasibility_and_quadratic_component_of_mem_subdifferential
    (z : H) (r : K) (L : H →L[ℝ] K) {x : H} {w : K × H}
    (hw : w ∈ (∂ (equalityConstraintQuadraticPenalty (H := H) z r)) (L x, x)) :
    L x = r ∧ w.2 = x - z := by
  let qz : H → Set.Ioi (⊥ : EReal) := shiftedHalfSquaredNorm (H := H) z
  have hpenalty :
      equalityConstraintQuadraticPenalty (H := H) z r ∈ Γ₀(K × H) :=
    equalityConstraintQuadraticPenalty_mem_gammaZero (H := H) (K := K) z r
  have hdom_sub :
      (L x, x) ∈ SetValuedOperator.dom
        (∂ (equalityConstraintQuadraticPenalty (H := H) z r)) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨w, hw⟩
  have hdom :
      (L x, x) ∈ effectiveDomain (equalityConstraintQuadraticPenalty (H := H) z r) :=
    subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hpenalty hdom_sub
  have hfeas : L x = r := by
    simpa [effectiveDomain_equalityConstraintQuadraticPenalty (H := H) z r] using hdom
  have hsecond :
      w.2 ∈ (∂ qz) x := by
    rw [mem_subdifferential_iff]
    intro y
    have hineq := (mem_subdifferential_iff
      (f := equalityConstraintQuadraticPenalty (H := H) z r)
      (x := (L x, x)) (u := w)).1 hw (L x, y)
    have hinner :
        (⟪(L x, y) - (L x, x), w⟫_ℝ : EReal) = (⟪y - x, w.2⟫_ℝ : EReal) := by
      have hinner_real : ⟪(L x, y) - (L x, x), w⟫_ℝ = ⟪y - x, w.2⟫_ℝ := by
        calc
          ⟪(L x, y) - (L x, x), w⟫_ℝ = ⟪(0, y - x), w⟫_ℝ := by
            simp
          _ = ⟪(0 : K), w.1⟫_ℝ + ⟪y - x, w.2⟫_ℝ := by
                rfl
          _ = ⟪y - x, w.2⟫_ℝ := by simp
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hinner_real
    calc
      (⟪y - x, w.2⟫_ℝ : EReal) + (qz x : EReal)
          = (⟪(L x, y) - (L x, x), w⟫_ℝ : EReal) +
              (equalityConstraintQuadraticPenalty (H := H) z r (L x, x) : EReal) := by
                rw [hinner]
                simp [qz, equalityConstraintQuadraticPenalty, hfeas]
      _ ≤ (equalityConstraintQuadraticPenalty (H := H) z r (L x, y) : EReal) := hineq
      _ = (qz y : EReal) := by
            simp [qz, equalityConstraintQuadraticPenalty, hfeas]
  have hsecond' :
      w.2 ∈ (∂ (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) (x - z) := by
    simpa [qz, sub_eq_add_neg, add_comm] using
      (mem_subdifferential_translate_iff
        (f := (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))
        (x0 := -z) (z := x) (u := w.2)).1 hsecond
  have hw2 : w.2 = x - z := by
    exact (mem_subdifferential_halfSquaredNorm_iff (x := x - z) (u := w.2)).1 hsecond'
  exact ⟨hfeas, hw2⟩

-- Proof sketch: specialize the equality-constraint owner from Proposition 19.21 to
-- `f = proximalObjective φ z`, and use the proximal specialization from Proposition 19.5 to
-- identify the corresponding dual solutions with fixed points via
-- `mem_fixedPoints_proximalConstraintDualMap_iff`.
/-- Corollary 19.7 (2): if `φ ∈ Γ₀(ℋ)`, `‖L‖ ≤ 1`, and `r ∈ sri (L (dom φ))`,
then the fixed-point set of `v ↦ v - r + L (Prox_φ (z - L^* v))` is nonempty. -/
theorem fixedPoints_proximalConstraintDualMap_nonempty_of_mem_sri_image_effectiveDomain
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K)
    (hL : ‖L‖ ≤ 1)
    (hsri : r ∈ sri (L '' effectiveDomain φ)) :
    (fixedPoints (proximalConstraintDualMap φ hφ z r L)).Nonempty := by
  let _ := hL
  let ψ0 : K → Set.Ioi (⊥ : EReal) := ι[{(0 : K)}]
  let g0 : K → Set.Ioi (⊥ : EReal) := fun y ↦ ψ0 (y - r)
  have hψ0 : ψ0 ∈ Γ₀(K) := by
    -- Encode the zero fiber with a singleton indicator.
    simpa [ψ0] using
      indicator_mem_gammaZero_of_nonempty_isClosed_convex
        (C := ({(0 : K)} : Set K))
        ⟨0, by simp⟩
        isClosed_singleton
        (convex_singleton (0 : K))
  have hg0_eq : g0 = ι[{r}] := by
    funext y
    by_cases hy : y = r
    · subst hy
      apply Subtype.ext
      simp [g0, ψ0]
    · have hy0 : y - r ≠ 0 := by
        exact sub_ne_zero.mpr hy
      apply Subtype.ext
      simp [g0, ψ0, hy, hy0]
  have hg0 : g0 ∈ Γ₀(K) := by
    simpa [hg0_eq] using
      indicator_mem_gammaZero_of_nonempty_isClosed_convex
        (C := ({r} : Set K))
        ⟨r, by simp⟩
        isClosed_singleton
        (convex_singleton r)
  have hsri0 : (0 : K) ∈ sri (effectiveDomain g0 - L '' effectiveDomain φ) := by
    let C : Set K := L '' effectiveDomain φ
    have htranslate : (0 : K) ∈ sri (C - ({r} : Set K)) :=
      zero_mem_sri_sub_singleton_of_mem_sri (C := C) (y := r) hsri
    have hC_convex : Convex ℝ C := hφ.2.convex_effectiveDomain.linear_image L.toLinearMap
    have hreflect : (0 : K) ∈ sri (-(C - ({r} : Set K))) :=
      zero_mem_sri_neg_of_zero_mem_sri (K := K) (hC_convex.sub (convex_singleton r)) htranslate
    have hneg_eq : -(C - ({r} : Set K)) = ({r} : Set K) - C := by
      ext x
      constructor <;> intro hx <;>
        simpa [Set.mem_neg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
    have hsri_singleton : (0 : K) ∈ sri (({r} : Set K) - C) := by
      rwa [← hneg_eq]
    simpa [C, hg0_eq, effectiveDomain_indicator] using hsri_singleton
  rcases (Set.mem_strongRelativeInterior_iff.mp hsri).1 with ⟨x0, hx0, hLx0⟩
  have hrange : (Set.range L ∩ effectiveDomain g0).Nonempty := by
    refine ⟨r, ?_, ?_⟩
    · exact ⟨x0, hLx0⟩
    · simpa [hg0_eq, effectiveDomain_indicator]
  have hg0_comp : g0 ∘ L ∈ Γ₀(H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty g0 hg0 L hrange
  have hsum : φ + g0 ∘ L ∈ Γ₀(H) := by
    refine pointwiseAdd_mem_gammaZero φ (g0 ∘ L) hφ hg0_comp ?_
    refine ⟨x0, hx0, ?_⟩
    rw [mem_effectiveDomain_iff]
    simpa [Function.comp, hg0_eq, hLx0]
  let p0 : H := Prox[φ + g0 ∘ L, hsum] z
  have hp0_argmin :
      p0 ∈ Argmin
        (compositePrimalObjective
          φ
          (equalityConstraintQuadraticPenalty (H := H) z r)
          (constraintProductMap (H := H) (K := K) L)) := by
    have hobj_eq :
        compositePrimalObjective
            φ
            (equalityConstraintQuadraticPenalty (H := H) z r)
            (constraintProductMap (H := H) (K := K) L) =
          proximalObjective (φ + g0 ∘ L) z := by
      funext x
      have hnorm0 : ‖x + -z‖ = ‖z - x‖ := by
        simpa [sub_eq_add_neg] using norm_sub_rev x z
      have hnorm : ‖x + -z‖ ^ 2 = ‖z - x‖ ^ 2 := by
        exact congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hnorm0
      simp [compositePrimalObjective, equalityConstraintQuadraticPenalty, constraintProductMap,
        shiftedHalfSquaredNorm, proximalObjective, hg0_eq, halfSquaredNorm_apply, hnorm,
        add_assoc, add_left_comm, add_comm]
    have hp0_prox : p0 ∈ Argmin (proximalObjective (φ + g0 ∘ L) z) := by
      simpa [IsProxPoint, proximalPoints, p0] using
        proximityOperator_isProxPoint
          (φ + g0 ∘ L)
          (hasUniqueProxPoint_of_mem_gammaZero (φ + g0 ∘ L) hsum)
          z
    simpa [hobj_eq] using hp0_prox
  have hargmin_nonempty :
      (Argmin
        (compositePrimalObjective
          φ
          (equalityConstraintQuadraticPenalty (H := H) z r)
          (constraintProductMap (H := H) (K := K) L))).Nonempty := ⟨p0, hp0_argmin⟩
  have hS_convex :
      Convex ℝ (effectiveDomain g0 - L '' effectiveDomain φ) := by
    simpa [hg0_eq, effectiveDomain_indicator] using
      (convex_singleton r).sub (hφ.2.convex_effectiveDomain.linear_image L.toLinearMap)
  have hsri_prod :
      (0 : K × H) ∈ sri
        ((effectiveDomain g0 - L '' effectiveDomain φ) ×ˢ (Set.univ : Set H)) :=
    zero_mem_sri_prod_univ_of_zero_mem_sri (K := H) hS_convex hsri0
  have hregular :
      CompositePrimalObjectiveRegularity
        φ
        (equalityConstraintQuadraticPenalty (H := H) z r)
        (constraintProductMap (H := H) (K := K) L) := by
    refine CompositePrimalObjectiveRegularity.zero_mem_sri ?_
    rw [effectiveDomain_equalityConstraintQuadraticPenalty_sub_image (φ := φ) z r L]
    simpa [hg0_eq, effectiveDomain_indicator] using hsri_prod
  have hzeros_nonempty :
      (((∂ φ) +
          ContinuousLinearMap.adjointImageSubdifferential
            (constraintProductMap (H := H) (K := K) L)
            (equalityConstraintQuadraticPenalty (H := H) z r)).zeros).Nonempty := by
    exact
      zeros_subdifferential_sum_nonempty_of_nonempty_argmin_and_regular
        (hf := hφ)
        (hg := equalityConstraintQuadraticPenalty_mem_gammaZero (H := H) (K := K) z r)
        (L := constraintProductMap (H := H) (K := K) L)
        hargmin_nonempty
        hregular
  rcases hzeros_nonempty with ⟨p, hpzero⟩
  rcases
      (mem_zeros_subdifferential_sum_iff_exists_mem_subdifferential
        (L := constraintProductMap (H := H) (K := K) L)).1 hpzero with
    ⟨w, hw, hsub⟩
  have hwdata :
      L p = r ∧ w.2 = p - z :=
    feasibility_and_quadratic_component_of_mem_subdifferential
      (H := H) (K := K) z r L hw
  have hsub_phi :
      z - L.adjoint w.1 - p ∈ (∂ φ) p := by
    simpa [constraintProductMap_adjoint_apply (H := H) (K := K) L w, hwdata.2,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  have hp_eq : p = Prox[φ, hφ] (z - L.adjoint w.1) := by
    exact
      (eq_proximityOperator_iff_sub_mem_subdifferential
        (hf := hφ) (x := z - L.adjoint w.1) (p := p)).2 hsub_phi
  refine ⟨w.1, ?_⟩
  apply (mem_fixedPoints_proximalConstraintDualMap_iff hφ z r L).2
  simpa [hp_eq] using hwdata.1

/-- Helper for Corollary 19 7: a feasible proximal point is the unique constrained minimizer of
`proximalObjective φ z`. -/
private theorem argminOn_proximalObjective_eq_singleton_of_isProxPoint_and_constraint
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) {v : K} {p : H}
    (hp : IsProxPoint φ (z - L.adjoint v) p) (hp_feas : L p = r) :
    Argmin[L ⁻¹' {r}] (proximalObjective φ z) = ({p} : Set H) := by
  let p0 : H := p
  have hp0 : IsProxPoint φ (z - L.adjoint v) p0 := by
    simpa [p0] using hp
  have hp0_feas : L p0 = r := by
    simpa [p0] using hp_feas
  ext y
  constructor
  · intro hy
    rcases mem_argminOn_iff.mp hy with ⟨hy_mem, hy_min⟩
    rw [isMinOn_iff] at hy_min
    have hy_feas : L y = r := by
      simpa [Set.mem_preimage, Set.mem_singleton_iff] using hy_mem
    have hdefect :
        proximalObjective φ z p0 +
            ((((1 / 2 : ℝ) * ‖y - p0‖ ^ 2 : ℝ) : EReal)) ≤
          proximalObjective φ z y :=
      proximalObjective_add_quadratic_defect_le_of_isProxPoint_and_constraint
        hφ z r L hp0 hp0_feas hy_feas
    have hy_le_hp : proximalObjective φ z y ≤ proximalObjective φ z p0 := by
      have hp0_mem : p0 ∈ L ⁻¹' {r} := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hp0_feas
      exact hy_min p0 hp0_mem
    have hp_dom : p0 ∈ effectiveDomain φ :=
      mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero hφ hp0
    have hsq_nonpos : (1 / 2 : ℝ) * ‖y - p0‖ ^ 2 ≤ 0 := by
      have hcollapse :
          proximalObjective φ z p0 +
              ((((1 / 2 : ℝ) * ‖y - p0‖ ^ 2 : ℝ) : EReal)) ≤
            proximalObjective φ z p0 := le_trans hdefect hy_le_hp
      rw [
        proximalObjective_eq_coe_toReal_add_quadratic_of_mem_effectiveDomain z p0 hp_dom
      ] at hcollapse
      rw [← EReal.coe_add] at hcollapse
      have hcollapse_real :
          (φ p0 : EReal).toReal + (1 / 2 : ℝ) * ‖z - p0‖ ^ 2 +
              (1 / 2 : ℝ) * ‖y - p0‖ ^ 2 ≤
            (φ p0 : EReal).toReal + (1 / 2 : ℝ) * ‖z - p0‖ ^ 2 := by
        exact_mod_cast hcollapse
      nlinarith
    have hsq_zero : ‖y - p0‖ ^ 2 = 0 := by
      have hsq_nonneg : 0 ≤ ‖y - p0‖ ^ 2 := by positivity
      nlinarith
    have hnorm_zero : ‖y - p0‖ = 0 := by
      nlinarith
    have hy_eq_p0 : y = p0 := sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
    rw [Set.mem_singleton_iff]
    simpa [p0] using hy_eq_p0
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rcases hy with rfl
    refine mem_argminOn_iff.mpr ⟨?_, ?_⟩
    · simpa using hp_feas
    · change IsMinOn (proximalObjective φ z) (L ⁻¹' {r}) _
      rw [isMinOn_iff]
      intro y' hy'_mem
      have hy'_feas : L y' = r := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy'_mem
      have hdefect :=
        proximalObjective_add_quadratic_defect_le_of_isProxPoint_and_constraint
          hφ z r L hp0 hp0_feas hy'_feas
      have hsq_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖y' - p0‖ ^ 2 := by
        positivity
      have hsq_nonneg_ereal :
          (0 : EReal) ≤ ((((1 / 2 : ℝ) * ‖y' - p0‖ ^ 2 : ℝ) : EReal)) := by
        exact_mod_cast hsq_nonneg
      have hbase :
          proximalObjective φ z p0 ≤
            proximalObjective φ z p0 +
              ((((1 / 2 : ℝ) * ‖y' - p0‖ ^ 2 : ℝ) : EReal)) := by
        exact le_add_of_nonneg_right hsq_nonneg_ereal
      exact le_trans hbase hdefect

-- Proof sketch: use Proposition 19.21 to express the equality-constrained primal problem for
-- `proximalObjective φ z`, then apply the proximal specialization from Proposition 19.5. A fixed
-- point gives the feasibility relation `L (Prox_φ (z - L^* v)) = r` by
-- `mem_fixedPoints_proximalConstraintDualMap_iff`.
/-- Corollary 19.7 (3): if `φ ∈ Γ₀(ℋ)`, `‖L‖ ≤ 1`, and `r ∈ sri (L (dom φ))`,
then for every fixed point `v` of `v ↦ v - r + L (Prox_φ (z - L^* v))`, the unique
minimizer of `proximalObjective φ z` subject to `Lx = r` is `Prox_φ (z - L^* v)`. -/
theorem argminOn_proximalObjective_eq_singleton_of_mem_fixedPoints_proximalConstraintDualMap
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1)
    (hsri : r ∈ sri (L '' effectiveDomain φ)) {v : K}
    (hv : v ∈ fixedPoints (proximalConstraintDualMap φ hφ z r L)) :
    Argmin[L ⁻¹' {r}] (proximalObjective φ z) =
      ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := by
  let _ := hL
  let _ := hsri
  -- The fixed-point equation is exactly the linear feasibility condition for the proximal point.
  have hv_feas :
      L (Prox[φ, hφ] (z - L.adjoint v)) = r :=
    (mem_fixedPoints_proximalConstraintDualMap_iff hφ z r L).1 hv
  have hprox :
      IsProxPoint φ (z - L.adjoint v) (Prox[φ, hφ] (z - L.adjoint v)) := by
    exact
      proximityOperator_isProxPoint
        φ
        (hasUniqueProxPoint_of_mem_gammaZero φ hφ)
        (z - L.adjoint v)
  exact
    argminOn_proximalObjective_eq_singleton_of_isProxPoint_and_constraint
      hφ z r L hprox hv_feas

end PrimalSolutionsViaDualSolutions

end ERealFunction
