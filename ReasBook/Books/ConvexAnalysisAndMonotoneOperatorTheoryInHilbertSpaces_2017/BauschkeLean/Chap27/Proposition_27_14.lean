import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap06.Proposition_6_4
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Proposition_17_31
import BauschkeLean.Chap27.Theorem_27_2

open Set
open InnerProductSpace
open ContinuousLinearMap
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section AffineConstraints

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 27.14 is the equality-constrained minimization criterion
  `min { f x | L x = r }`.
- `core/canonical`: the local owner ingredients are the Chapter 27 composite optimality system
  from Theorem 27.2 and the Chapter 19 equality-constraint perturbation surface.
- `bridge/view`: this file keeps the constrained `Argmin[...]` formulation, the affine-objective
  consequence for a chosen multiplier witness, and the Gâteaux-gradient specialization.
-/

-- Semantic search note: `lean_leansearch` only surfaced generic calculus Lagrange-multiplier
-- results, so the verified project-facing owners for this file are the Chapter 19
-- equality-constraint perturbation API and the Chapter 27 subdifferential optimality system.

/-- Helper for Proposition 27.14: the singleton equality constraint `ι[{r}]` satisfies the
Chapter 27 `0 ∈ sri (dom g - L(dom f))` regularity hypothesis as soon as `r ∈ sri (L(dom f))`. -/
lemma zero_mem_sri_singletonIndicator_sub_image_of_mem_sri_image
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) {r : K} (hsri : r ∈ sri (L '' effectiveDomain f)) :
    (0 : K) ∈
      sri
        (effectiveDomain (ι[{r}] : K → Set.Ioi (⊥ : EReal)) - L '' effectiveDomain f) := by
  let S : Set K := L '' effectiveDomain f
  let A : Set K := S - ({r} : Set K)
  have hS_convex : Convex ℝ S := by
    -- The image of the effective domain of a `Γ₀` function under a linear map stays convex.
    exact (mem_gammaZero_iff.mp hf).2.convex_effectiveDomain.linear_image L.toLinearMap
  have hA_convex : Convex ℝ A := by
    -- Translating a convex set by the singleton `{r}` preserves convexity.
    simpa [A] using hS_convex.sub (convex_singleton r)
  have hzeroA : (0 : K) ∈ sri A := by
    -- Recenter the strong-relative-interior witness from `r` to the origin.
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hrS, hcone⟩
    refine Set.mem_strongRelativeInterior_iff.mpr ⟨?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨r, hrS, r, by simp, sub_self r⟩
    · simpa [A, sub_singleton_zero_eq_self] using hcone
  have hA_nonempty : A.Nonempty := ⟨0, (Set.mem_strongRelativeInterior_iff.mp hzeroA).1⟩
  have hneg_cone :
      cone (-A) = ((Submodule.span ℝ (-A)).topologicalClosure : Set K) := by
    have hA_cone :
        cone A = ((Submodule.span ℝ A).topologicalClosure : Set K) :=
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        hA_nonempty hA_convex).1 hzeroA
    calc
      cone (-A) = -cone A := by
        calc
          cone (-A) = ((hA_convex.neg.toCone (-A) : ConvexCone ℝ K) : Set K) := by
            simpa [Set.cone_def] using
              (convexCone_hull_eq_toCone (E := K) hA_convex.neg)
          _ = -(((hA_convex.toCone A : ConvexCone ℝ K) : Set K)) := by
            symm
            exact neg_toCone_eq_toCone_neg hA_convex
          _ = -cone A := by
            rw [show cone A = ((hA_convex.toCone A : ConvexCone ℝ K) : Set K) by
              simpa [Set.cone_def] using (convexCone_hull_eq_toCone (E := K) hA_convex)]
      _ = -((Submodule.span ℝ A).topologicalClosure : Set K) := by
        rw [hA_cone]
      _ = ((Submodule.span ℝ A).topologicalClosure : Set K) := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_neg] at hx
          simpa using ((Submodule.span ℝ A).topologicalClosure.neg_mem hx)
        · intro hx
          rw [Set.mem_neg]
          exact ((Submodule.span ℝ A).topologicalClosure.neg_mem hx)
      _ = ((Submodule.span ℝ (-A)).topologicalClosure : Set K) := by
        simp [Submodule.span_neg]
  have hzero_negA : (0 : K) ∈ sri (-A) := by
    -- Reflecting a centered `sri` witness preserves the Chapter 6 cone/closed-span criterion.
    refine
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        (by
          refine ⟨0, ?_⟩
          rw [Set.mem_neg]
          simpa using (Set.mem_strongRelativeInterior_iff.mp hzeroA).1)
        hA_convex.neg).2 hneg_cone
  have hset :
      -A = effectiveDomain (ι[{r}] : K → Set.Ioi (⊥ : EReal)) - L '' effectiveDomain f := by
    -- The reflected translate `-(S - {r})` is exactly the source-facing difference `{r} - S`.
    ext x
    constructor
    · intro hx
      rw [Set.mem_neg] at hx
      rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, hyz⟩
      refine Set.mem_sub.mpr ?_
      exact ⟨z, by simpa [effectiveDomain_indicator] using hz, y, hy,
        by
          have hxy : z - y = x := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hyz
          exact hxy⟩
    · intro hx
      rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, hxz⟩
      rw [Set.mem_neg]
      exact Set.mem_sub.mpr ⟨z, hz, y, by simpa [effectiveDomain_indicator] using hy,
        by
          have hxy : z - y = -x := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hxz
          exact hxy⟩
  -- The singleton-indicator domain is `{r}`, and `{r} - S` is the negation of `S - {r}`.
  simpa [hset] using hzero_negA

/-- Helper for Proposition 27.14: the singleton indicator has a subgradient at `u` exactly when
`u` equals the constrained value `r`. -/
lemma mem_subdifferential_singletonIndicator_iff
    {r u v : K} :
    v ∈ (∂ (ι[{r}] : K → Set.Ioi (⊥ : EReal))) u ↔ u = r := by
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    -- Testing the subgradient inequality at the feasible point `r` rules out every infeasible `u`.
    by_contra hur
    have htop_le_zero : (⊤ : EReal) ≤ 0 := by
      have hineq := hu r
      have hu_top : ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) u : EReal) = ⊤ := by
        simp [indicator_apply, hur]
      have hr_zero : ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) r : EReal) = 0 := by
        simp [indicator_apply]
      have hleft :
          (⟪r - u, v⟫_ℝ : EReal) + ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) u : EReal) = ⊤ := by
        rw [hu_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      calc
        (⊤ : EReal)
            = (⟪r - u, v⟫_ℝ : EReal) + ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) u : EReal) := by
                exact hleft.symm
        _ ≤ ((ι[{r}] : K → Set.Ioi (⊥ : EReal)) r : EReal) := hineq
        _ = 0 := hr_zero
    have hcontra : ¬ ((⊤ : EReal) ≤ 0) := by
      simp
    exact hcontra htop_le_zero
  · intro hur
    subst hur
    -- At the feasible point, the indicator is `0`, and all infeasible comparison points give `⊤`.
    intro y
    by_cases hy : y = u
    · subst hy
      simp
    · have hy_top : ((ι[{u}] : K → Set.Ioi (⊥ : EReal)) y : EReal) = ⊤ := by
        simp [indicator_apply, hy]
      have hu_zero : ((ι[{u}] : K → Set.Ioi (⊥ : EReal)) u : EReal) = 0 := by
        simp [indicator_apply]
      calc
        (⟪y - u, v⟫_ℝ : EReal) + ((ι[{u}] : K → Set.Ioi (⊥ : EReal)) u : EReal)
            = (⟪y - u, v⟫_ℝ : EReal) := by rw [hu_zero, add_zero]
        _ ≤ ⊤ := le_top
        _ = ((ι[{u}] : K → Set.Ioi (⊥ : EReal)) y : EReal) := by
              symm
              exact hy_top

section CompleteAffineConstraints

variable [CompleteSpace H] [CompleteSpace K]

/-- First clause of Proposition 27.14: under `r ∈ sri (L (dom f))`, a point `xbar`
solves the constrained problem `min { f x | L x = r }` if and only if it is feasible
and there exists `vbar` with `-L^* vbar ∈ ∂ f xbar`. -/
theorem mem_argminOn_linear_fiber_iff_exists_neg_adjoint_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    {r : K} (hsri : r ∈ sri (L '' effectiveDomain f)) {xbar : H} :
    xbar ∈ Argmin[L ⁻¹' {r}] f.asEReal ↔
      L xbar = r ∧ ∃ vbar : K, -L.adjoint vbar ∈ (∂ f) xbar := by
  let g : K → Set.Ioi (⊥ : EReal) := ι[{r}]
  have hg : g ∈ Γ₀(K) := by
    -- Package the singleton equality constraint as a canonical `Γ₀` penalty.
    refine indicator_mem_gammaZero_of_nonempty_isClosed_convex ?_ isClosed_singleton ?_
    · exact ⟨r, by simp⟩
    · exact convex_singleton r
  have hregular : CompositePrimalObjectiveRegularity f g L := by
    -- The source `sri` hypothesis is exactly the Chapter 27 regularity branch for `g = ι[{r}]`.
    exact CompositePrimalObjectiveRegularity.zero_mem_sri
      (zero_mem_sri_singletonIndicator_sub_image_of_mem_sri_image
        (hf := hf) L hsri)
  have hobj :
      compositePrimalObjective f g L =
        f.asEReal + (ι[L ⁻¹' ({r} : Set K)]).asEReal := by
    -- Rewriting the singleton penalty along `L` exposes the textbook linear-fiber indicator.
    funext x
    by_cases hx : L x = r
    · simp [g, compositePrimalObjective_apply, indicator_apply, hx]
    · simp [g, compositePrimalObjective_apply, indicator_apply, hx]
  have hconstrained :
      Argmin[L ⁻¹' ({r} : Set K)] f.asEReal =
        (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
    -- The penalized global argmin becomes the constrained argmin after
    -- intersecting with the feasible fiber.
    calc
      Argmin[L ⁻¹' ({r} : Set K)] f.asEReal =
          (L ⁻¹' ({r} : Set K)) ∩ Argmin (f.asEReal + (ι[L ⁻¹' ({r} : Set K)]).asEReal) := by
            simpa using
              argminOn_eq_inter_argmin_add_indicator
                (f := f.asEReal) (C := L ⁻¹' ({r} : Set K))
                (fun x _ ↦ by
                  exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2))
      _ = (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
            simp [hobj]
  constructor
  · intro hx
    -- First move from the constrained argmin surface to the Chapter 27 composite objective.
    have hxconstrained :
        xbar ∈ (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
      simpa [hconstrained] using hx
    have hzero :
        xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L g).zeros := by
      exact
        (mem_argmin_compositePrimalObjective_iff_mem_zeros_subdifferential_sum_of_regular
          (hf := hf) (hg := hg) L hregular).1 hxconstrained.2
    rcases
        (mem_zeros_subdifferential_sum_iff_exists_mem_subdifferential
          (f := f) (g := g) L (xbar := xbar)).1 hzero with
      ⟨vbar, hvbar, hsub⟩
    -- The singleton-indicator subgradient collapses to the feasibility equation `L xbar = r`.
    exact ⟨(mem_subdifferential_singletonIndicator_iff (r := r) (u := L xbar) (v := vbar)).1 hvbar,
      ⟨vbar, hsub⟩⟩
  · rintro ⟨hfeas, ⟨vbar, hsub⟩⟩
    have hvbar : vbar ∈ (∂ g) (L xbar) := by
      -- Once feasibility holds, every multiplier lies in the subdifferential of `ι[{r}]`.
      simpa [g] using
        (mem_subdifferential_singletonIndicator_iff (r := r) (u := L xbar) (v := vbar)).2 hfeas
    have hzero :
        xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L g).zeros := by
      exact
        (mem_zeros_subdifferential_sum_iff_exists_mem_subdifferential
          (f := f) (g := g) L (xbar := xbar)).2
          ⟨vbar, hvbar, hsub⟩
    have harg :
        xbar ∈ Argmin (compositePrimalObjective f g L) := by
      exact
        (mem_argmin_compositePrimalObjective_iff_mem_zeros_subdifferential_sum_of_regular
          (hf := hf) (hg := hg) L hregular).2 hzero
    -- Reassemble the constrained argmin by combining feasibility with the global penalized argmin.
    have hxconstrained :
        xbar ∈ (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
      refine ⟨?_, harg⟩
      simpa using hfeas
    simpa [hconstrained] using hxconstrained

end CompleteAffineConstraints

/-- Helper for Proposition 27.14: adding the finite affine term `⟪y, u⟫` to the
subgradient inequality for `-u` collapses the left side to `⟪x, u⟫`. -/
lemma inner_add_inner_sub_neg_eq_inner
    (x y u : H) :
    ((⟪y, u⟫_ℝ : EReal) + (⟪y - x, -u⟫_ℝ : EReal)) = (⟪x, u⟫_ℝ : EReal) := by
  -- Route correction: isolate the only nontrivial affine normalization once at the real level,
  -- then coerce the finished identity to `EReal`.
  have hreal : ⟪y, u⟫_ℝ + ⟪y - x, -u⟫_ℝ = ⟪x, u⟫_ℝ := by
    rw [inner_neg_right, inner_sub_left]
    ring
  exact_mod_cast hreal

/-- Helper for Proposition 27.14: a negative subgradient at `xbar` makes `xbar` a global
minimizer of the affine tilt `x ↦ f x + ⟪x, u⟫`. -/
lemma mem_argmin_affineObjective_of_neg_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {xbar u : H}
    (hsub : -u ∈ (∂ f) xbar) :
    xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪x, u⟫_ℝ : EReal)) := by
  -- Rewrite both optimality surfaces to pointwise inequalities before adding the common affine
  -- term to the subgradient inequality.
  rw [mem_argmin_iff, isMinOn_univ_iff]
  rw [mem_subdifferential_iff] at hsub
  intro y
  have hshift' :
      (⟪y, u⟫_ℝ : EReal) + ((⟪y - xbar, -u⟫_ℝ : EReal) + (f xbar : EReal)) ≤
        (⟪y, u⟫_ℝ : EReal) + (f y : EReal) := by
    exact add_le_add_right (hsub y) (⟪y, u⟫_ℝ : EReal)
  have hshift :
      (⟪y, u⟫_ℝ : EReal) + ((⟪y - xbar, -u⟫_ℝ : EReal) + (f xbar : EReal)) ≤
        (⟪y, u⟫_ℝ : EReal) + (f y : EReal) := by
    simpa [add_assoc, add_left_comm, add_comm] using hshift'
  -- Normalize the left-hand side and commute the right-hand side into the target affine objective.
  calc
    (f xbar : EReal) + (⟪xbar, u⟫_ℝ : EReal)
        = (⟪y, u⟫_ℝ : EReal) + ((⟪y - xbar, -u⟫_ℝ : EReal) + (f xbar : EReal)) := by
            rw [← add_assoc, inner_add_inner_sub_neg_eq_inner]
            simp [add_comm]
    _ ≤ (⟪y, u⟫_ℝ : EReal) + (f y : EReal) := hshift
    _ = (f y : EReal) + (⟪y, u⟫_ℝ : EReal) := by
          rw [add_comm]

section CompleteAffineObjective

variable [CompleteSpace H] [CompleteSpace K]

/-- Proposition 27.14: if `xbar` is feasible and `vbar` satisfies the subgradient
condition `-L^* vbar ∈ ∂ f xbar`, then `vbar` is the textbook
Lagrange-multiplier witness for `xbar`, and `xbar` minimizes the affine
objective `x ↦ f x + ⟪x, L^* vbar⟫`. -/
theorem mem_argmin_affineObjective_of_eq_and_neg_adjoint_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K)
    {r : K} {xbar : H} {vbar : K} (hfeas : L xbar = r)
    (hsub : -L.adjoint vbar ∈ (∂ f) xbar) :
    xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪x, L.adjoint vbar⟫_ℝ : EReal)) := by
  -- Route correction: the feasibility equation is part of the textbook package, but the affine
  -- objective minimality follows directly from the negative-subgradient condition.
  let _ := hfeas
  -- Specialize the general affine-tilt lemma to the adjoint multiplier direction `L.adjoint vbar`.
  simpa using
    (mem_argmin_affineObjective_of_neg_mem_subdifferential
      (f := f) (xbar := xbar) (u := L.adjoint vbar) hsub)

end CompleteAffineObjective

section CompleteAffineConstraints

variable [CompleteSpace H] [CompleteSpace K]

/-- Gradient specialization of Proposition 27.14: if `f` is Gâteaux differentiable at the feasible
effective-domain
point `xbar` with gradient `gradf`, then clause `(1)` becomes the feasibility condition together
with `gradf = -L^* vbar` for some multiplier `vbar`. -/
theorem mem_argminOn_linear_fiber_iff_exists_eq_neg_adjoint_of_hasGateauxDerivativeAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    {r : K} (hsri : r ∈ sri (L '' effectiveDomain f))
    {xbar gradf : H} (hxbar : xbar ∈ effectiveDomain f)
    (hgrad :
      HasGateauxDerivativeAt
        (fun z : H ↦ (f z : EReal).toReal)
        (toDualMap ℝ H gradf) xbar) :
    xbar ∈ Argmin[L ⁻¹' {r}] f.asEReal ↔
      L xbar = r ∧ ∃ vbar : K, gradf = -L.adjoint vbar := by
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  constructor
  · intro hx
    -- First use clause `(1)` to get the KKT subgradient system.
    rcases
        (mem_argminOn_linear_fiber_iff_exists_neg_adjoint_mem_subdifferential
          (hf := hf) L hsri (xbar := xbar)).1 hx with
      ⟨hfeas, ⟨vbar, hsub⟩⟩
    have hsingleton :
        (∂ f) xbar = ({gradf} : Set H) :=
      @ERealFunction.subdifferential_eq_singleton_of_hasGateauxDerivativeAt
        H _ _ f xbar hxbar gradf hgrad
    have hgrad_eq' : -L.adjoint vbar = gradf := by
      -- Gâteaux differentiability collapses the subdifferential to the singleton `{gradf}`.
      simpa [hsingleton] using hsub
    exact ⟨hfeas, ⟨vbar, hgrad_eq'.symm⟩⟩
  · rintro ⟨hfeas, ⟨vbar, hgrad_eq⟩⟩
    have hsub : -L.adjoint vbar ∈ (∂ f) xbar := by
      -- The gradient witness is itself a subgradient, so the equality `gradf = -L^* vbar`
      -- supplies the KKT inclusion from clause `(1)`.
      have hgrad_sub : gradf ∈ (∂ f) xbar :=
        gateauxGradient_mem_subdifferential f hconv hxbar gradf hgrad
      simpa [hgrad_eq] using hgrad_sub
    exact
      (mem_argminOn_linear_fiber_iff_exists_neg_adjoint_mem_subdifferential
        (hf := hf) L hsri (xbar := xbar)).2
        ⟨hfeas, ⟨vbar, hsub⟩⟩

end CompleteAffineConstraints

end AffineConstraints

end ERealFunction
