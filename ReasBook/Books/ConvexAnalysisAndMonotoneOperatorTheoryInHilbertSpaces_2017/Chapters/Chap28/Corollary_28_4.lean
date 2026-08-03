import BauschkeLean.Chap02.Lemma_2_41
import BauschkeLean.Chap03.Corollary_3_22
import BauschkeLean.Chap04.Proposition_4_19
import BauschkeLean.Chap06.Proposition_6_4
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap19.Theorem_19_1
import BauschkeLean.Chap26.Proposition_26_1
import BauschkeLean.Chap26.Proposition_26_12
import BauschkeLean.Chap29.Example_29_17

open Filter
open Set
open SetValuedOperator
open EuclideanGeometry
open scoped InnerProductSpace Pointwise Topology

noncomputable section

universe u v

namespace ERealFunction

-- Semantic recall: the source recursion `(28.16)` is preserved through direct public owners for
-- the four iterate families `yₙ`, `xₙ`, `pₙ`, and `qₙ`. The core convergence engine is the
-- Chapter 26 Douglas--Rachford orbit on `(N[affineFiber L r], ∂ f)`, while Proposition 29.2
-- supplies the affine-fiber projector formula needed to recover the source update surface.

section DouglasRachfordLinearFiber

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
private theorem singleton_nonempty (r : K) : ({r} : Set K).Nonempty :=
  ⟨r, by simp⟩

omit [CompleteSpace K] in
/-- Helper for Corollary 28.4: the singleton indicator `ι[{r}]` belongs to `Γ₀(K)`. -/
private theorem singletonIndicator_mem_gammaZero (r : K) :
    (ι[{r}] : K → Set.Ioi (⊥ : EReal)) ∈ Γ₀(K) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ (((ι[{r}] : K → Set.Ioi (⊥ : EReal)) y : EReal))) := by
    simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed ({r} : Set K)).2 isClosed_singleton
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by
    refine ⟨r, ?_⟩
    simp [effectiveDomain_indicator]
  , fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hy_singleton : y ∈ ({r} : Set K) := by
    simpa [effectiveDomain_indicator] using hy
  have hz_singleton : z ∈ ({r} : Set K) := by
    simpa [effectiveDomain_indicator] using hz
  have hayz_singleton : a • y + (1 - a) • z ∈ ({r} : Set K) :=
    (convex_singleton r) hy_singleton hz_singleton ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hy_singleton, hz_singleton, hayz_singleton]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Corollary 28.4: the singleton indicator `ι[{r}]` satisfies the Chapter 27
regularity hypothesis as soon as `r ∈ sri (L '' effectiveDomain f)`. -/
private theorem zeroMemSriSingletonIndicatorSubImageOfMemSriImage
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) {r : K} (hsri : r ∈ sri (L '' effectiveDomain f)) :
    (0 : K) ∈
      sri
        (effectiveDomain (ι[{r}] : K → Set.Ioi (⊥ : EReal)) - L '' effectiveDomain f) := by
  let S : Set K := L '' effectiveDomain f
  let A : Set K := S - ({r} : Set K)
  have hS_convex : Convex ℝ S := by
    exact (mem_gammaZero_iff.mp hf).2.convex_effectiveDomain.linear_image L.toLinearMap
  have hA_convex : Convex ℝ A := by
    simpa [A] using hS_convex.sub (convex_singleton r)
  have hzeroA : (0 : K) ∈ sri A := by
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hrS, hcone⟩
    refine Set.mem_strongRelativeInterior_iff.mpr ?_
    refine ⟨?_, ?_⟩
    · exact Set.mem_sub.mpr ⟨r, hrS, r, by simp, sub_self r⟩
    · simpa [A, sub_singleton_zero_eq_self] using hcone
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    exact (Set.mem_strongRelativeInterior_iff.mp hzeroA).1
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
    refine
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        (by
          refine ⟨0, ?_⟩
          rw [Set.mem_neg]
          simpa using (Set.mem_strongRelativeInterior_iff.mp hzeroA).1)
        hA_convex.neg).2 hneg_cone
  have hset :
      -A = effectiveDomain (ι[{r}] : K → Set.Ioi (⊥ : EReal)) - L '' effectiveDomain f := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_neg] at hx
      rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, hyz⟩
      refine Set.mem_sub.mpr ?_
      refine ⟨z, ?_, y, hy, ?_⟩
      · simpa [effectiveDomain_indicator] using hz
      · have hxy : z - y = x := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            congrArg Neg.neg hyz
        exact hxy
    · intro hx
      rcases Set.mem_sub.mp hx with ⟨y, hy, z, hz, hxz⟩
      rw [Set.mem_neg]
      refine Set.mem_sub.mpr ?_
      refine ⟨z, hz, y, ?_, ?_⟩
      · simpa [effectiveDomain_indicator] using hy
      · have hxy : z - y = -x := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            congrArg Neg.neg hxz
        exact hxy
  simpa [hset] using hzero_negA

omit [CompleteSpace K] in
/-- Helper for Corollary 28.4: the singleton indicator has a subgradient at `u` exactly when
`u = r`. -/
private theorem memSubdifferentialSingletonIndicatorIff
    {r u v : K} :
    v ∈ (∂ (ι[{r}] : K → Set.Ioi (⊥ : EReal))) u ↔ u = r := by
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
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
            exact hy_top.symm

/-- Helper for Corollary 28.4: minimizing `f` on `affineFiber L r` is equivalent to feasibility
and the KKT condition `∃ vbar, -L^* vbar ∈ ∂ f xbar`. -/
private theorem linearFiberArgminIffExistsNegAdjointMemSubdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    {r : K} (hsri : r ∈ sri (L '' effectiveDomain f))
    {xbar : H} :
    xbar ∈ Argmin[L ⁻¹' {r}] f.asEReal ↔
      L xbar = r ∧ ∃ vbar : K, -L.adjoint vbar ∈ (∂ f) xbar := by
  let g : K → Set.Ioi (⊥ : EReal) := ι[{r}]
  have hg : g ∈ Γ₀(K) := by
    simpa [g] using singletonIndicator_mem_gammaZero r
  have hsri_zero :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) := by
    exact zeroMemSriSingletonIndicatorSubImageOfMemSriImage (hf := hf) L hsri
  obtain ⟨v, hv_argmin, hstrong_v⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      f hf g hg L hsri_zero
  have hv_value : compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hv_argmin)
  have hstrong :
      compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
    rw [← hv_value]
    exact hstrong_v
  have hobj :
      compositePrimalObjective f g L =
        f.asEReal + (ι[L ⁻¹' ({r} : Set K)]).asEReal := by
    funext x
    by_cases hx : L x = r
    · simp [g, compositePrimalObjective_apply, indicator_apply, hx]
    · simp [g, compositePrimalObjective_apply, indicator_apply, hx]
  have hconstrained :
      Argmin[L ⁻¹' ({r} : Set K)] f.asEReal =
        (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
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
    have hxconstrained :
        xbar ∈ (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
      simpa [hconstrained] using hx
    have htfae := primal_dual_solution_tfae_for_composite_objective hf hg L xbar v
    have hiff := List.TFAE.out htfae 0 1
    have hsubpair : -L.adjoint v ∈ (∂ f) xbar ∧ v ∈ (∂ g) (L xbar) := by
      exact hiff.1 ⟨hxconstrained.2, hv_argmin, hstrong⟩
    exact
      ⟨(memSubdifferentialSingletonIndicatorIff (r := r) (u := L xbar) (v := v)).1 hsubpair.2,
        ⟨v, hsubpair.1⟩⟩
  · rintro ⟨hfeas, ⟨v, hsub⟩⟩
    have hv_sub : v ∈ (∂ g) (L xbar) := by
      simpa [g] using
        (memSubdifferentialSingletonIndicatorIff (r := r) (u := L xbar) (v := v)).2 hfeas
    have htfae := primal_dual_solution_tfae_for_composite_objective hf hg L xbar v
    have hiff := List.TFAE.out htfae 1 0
    have harg :
        xbar ∈ Argmin (compositePrimalObjective f g L) :=
      (hiff.1 ⟨hsub, hv_sub⟩).1
    have hxconstrained :
        xbar ∈ (L ⁻¹' ({r} : Set K)) ∩ Argmin (compositePrimalObjective f g L) := by
      refine ⟨?_, harg⟩
      simpa using hfeas
    simpa [hconstrained] using hxconstrained

private theorem linearFiber_nonempty_of_comp_adjoint_eq_smul_id
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K)) :
    (affineFiber L r).Nonempty := by
  refine ⟨(μ : ℝ)⁻¹ • L.adjoint r, ?_⟩
  rw [mem_affineFiber, ContinuousLinearMap.map_smul]
  have happly := congrArg (fun T : K →L[ℝ] K ↦ T r) hscalar
  have hLLstar : L (L.adjoint r) = (μ : ℝ) • r := by
    simpa using happly
  calc
    (μ : ℝ)⁻¹ • L (L.adjoint r) = (μ : ℝ)⁻¹ • ((μ : ℝ) • r) := by rw [hLLstar]
    _ = r := by
      simp [smul_smul, inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from ne_of_gt μ.2)]

private theorem linearFiber_isChebyshev
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K)) :
    IsChebyshev (affineFiber L r) :=
  isChebyshev_of_nonempty_isClosed_convex
    (linearFiber_nonempty_of_comp_adjoint_eq_smul_id L r μ hscalar)
    (affineFiber_isClosed L r) (affineFiber_convex L r)

/-- Helper for Corollary 28.4: the orthogonal projector onto `affineFiber L r` is the explicit
affine correction `x + μ⁻¹ • L^*(r - L x)`. -/
private theorem projectionPoint_affineFiber_eq_affineCorrection
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (x : H) :
    P[affineFiber L r, linearFiber_isChebyshev L r μ hscalar] x =
      x + (μ : ℝ)⁻¹ • L.adjoint (r - L x) := by
  obtain ⟨z, hz⟩ := linearFiber_nonempty_of_comp_adjoint_eq_smul_id L r μ hscalar
  let C : AffineSubspace ℝ H := AffineSubspace.mk' z L.ker
  have hz_eq : L z = r := mem_affineFiber.mp hz
  have hC_set : (C : Set H) = affineFiber L r := by
    ext w
    change L (w - z) = 0 ↔ L w = r
    rw [ContinuousLinearMap.map_sub]
    constructor
    · intro hw
      have hwz : L w = L z := sub_eq_zero.mp hw
      simpa [hz_eq] using hwz
    · intro hw
      have hwz : L w = L z := by simpa [hz_eq] using hw
      exact sub_eq_zero.mpr hwz
  have hC_nonempty : (C : Set H).Nonempty := by
    refine ⟨z, ?_⟩
    change L (z - z) = 0
    simp
  have hC_closed : IsClosed (C : Set H) := by
    simpa [hC_set] using affineFiber_isClosed L r
  let hC_cheb : IsChebyshev (C : Set H) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  let p : H := x + (μ : ℝ)⁻¹ • L.adjoint (r - L x)
  have hp_mem : p ∈ (C : Set H) := by
    have hp_fiber : p ∈ affineFiber L r := by
      simp only [p, mem_affineFiber, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
      have happly := congrArg (fun T : K →L[ℝ] K ↦ T (r - L x)) hscalar
      have hLLstar : L (L.adjoint (r - L x)) = (μ : ℝ) • (r - L x) := by
        simpa using happly
      calc
        L x + (μ : ℝ)⁻¹ • L (L.adjoint (r - L x))
            = L x + (μ : ℝ)⁻¹ • ((μ : ℝ) • (r - L x)) := by rw [hLLstar]
        _ = r := by
          simp [smul_smul, inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from ne_of_gt μ.2)]
    simpa [hC_set, p] using hp_fiber
  have hLadj_orth : L.adjoint (r - L x) ∈ L.kerᗮ := by
    refine (Submodule.mem_orthogonal' L.ker _).2 ?_
    intro u hu
    have hLu : L u = 0 := LinearMap.mem_ker.mp hu
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hLu]
  have hp_orth : x - p ∈ C.directionᗮ := by
    have hneg : -((μ : ℝ)⁻¹ • L.adjoint (r - L x)) ∈ L.kerᗮ := by
      exact (L.kerᗮ).neg_mem ((L.kerᗮ).smul_mem _ hLadj_orth)
    simpa [C, p, AffineSubspace.direction_mk', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hneg
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hp_proj : (orthogonalProjection C x : H) = p := by
    refine (coe_orthogonalProjection_eq_iff_mem (s := C) (p := x) (q := p)).2 ?_
    exact ⟨hp_mem, hp_orth⟩
  have hp_point : P[(C : Set H), hC_cheb] x = p := by
    exact
      (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed x).trans hp_proj
  simpa [hC_set, p] using hp_point

/-- Helper for Corollary 28.4: a fixed point of the reflected Douglas--Rachford map for
`(N[C], B)` identifies `P_C y` with `resolventMap B hB γ y`. -/
private theorem affineProjector_eq_resolventLimit_of_fixedPoint
    {C : AffineSubspace ℝ H} (hC_nonempty : (C : Set H).Nonempty)
    (hC_closed : IsClosed (C : Set H))
    {B : SetValuedOperator H H} (hNC : Maximal SetValuedOperator.IsMonotone N[(C : Set H)])
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (γ : PosReal) {y : H}
    (hy_fix :
      y ∈ Function.fixedPoints (reflectedResolventComposition N[(C : Set H)] B hNC hB γ)) :
    P[(C : Set H), isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex] y =
      resolventMap B hB γ y := by
  let hC : IsChebyshev (C : Set H) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  let x : H := resolventMap B hB γ y
  have hy_fix_dr :
      y ∈ Function.fixedPoints
        (douglasRachfordOperator (resolventMap N[(C : Set H)] hNC γ) (resolventMap B hB γ)) := by
    rw [fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      N[(C : Set H)] B hNC hB γ]
    exact hy_fix
  have hx_proj : P[(C : Set H), hC] ((2 : ℝ) • x - y) = x := by
    have hy_eq :
        douglasRachfordOperator (resolventMap N[(C : Set H)] hNC γ) (resolventMap B hB γ) y = y :=
      hy_fix_dr
    have hres_eq : resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) = x := by
      have hcore :
          resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) + y - x = y := by
        simpa [x, douglasRachfordOperator_apply] using hy_eq
      have hsum :
          resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) + y = y + x :=
        sub_eq_iff_eq_add.mp hcore
      have hsum' :
          resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) + y = x + y := by
        simpa [add_comm] using hsum
      exact add_right_cancel hsum'
    rw [resolventMap_normalConeAffine_eq_projectionPoint
      (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
      (hNC := hNC) (γ := γ) ((2 : ℝ) • x - y)] at hres_eq
    exact hres_eq
  have hx_mem : x ∈ (C : Set H) := by
    simpa [hx_proj] using projectionPoint_mem (C : Set H) hC ((2 : ℝ) • x - y)
  have hy_orth : y - x ∈ C.directionᗮ := by
    have hx_proj_orth : (orthogonalProjection C ((2 : ℝ) • x - y) : H) = x := by
      rw [← projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed ((2 : ℝ) • x - y)]
      simpa using hx_proj
    have hchar := (coe_orthogonalProjection_eq_iff_mem
      (s := C) (p := ((2 : ℝ) • x - y)) (q := x)).mp hx_proj_orth
    rcases hchar with ⟨_, horth⟩
    have horth' : x - y ∈ C.directionᗮ := by
      simpa [vsub_eq_sub, sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm] using horth
    have hneg : -(x - y) ∈ C.directionᗮ := Submodule.neg_mem _ horth'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
  have hy_proj : P[(C : Set H), hC] y = x := by
    have hy_proj_orth : (orthogonalProjection C y : H) = x := by
      refine (coe_orthogonalProjection_eq_iff_mem (s := C) (p := y) (q := x)).2 ?_
      exact ⟨hx_mem, hy_orth⟩
    simpa [x] using
      (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed y).trans hy_proj_orth
  simpa [hC] using hy_proj

/-- Helper for Corollary 28.4: the affine projector along the Douglas--Rachford orbit converges
weakly to `resolventMap B hB γ y` once the orbit itself converges weakly to a fixed point `y`. -/
private theorem affineProjector_tendsto_weakly
    {C : AffineSubspace ℝ H} (hC_nonempty : (C : Set H).Nonempty)
    (hC_closed : IsClosed (C : Set H))
    {B : SetValuedOperator H H} (hNC : Maximal SetValuedOperator.IsMonotone N[(C : Set H)])
    (hB : Maximal SetValuedOperator.IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 y : H)
    (hy_fix :
      y ∈ Function.fixedPoints (reflectedResolventComposition N[(C : Set H)] B hNC hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ H
          (P[(C : Set H), isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex]
            (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n)))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
  let hC : IsChebyshev (C : Set H) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hproj_weak :
      WeaklyContinuous (fun x : (Set.univ : Set H) ↦ P[(C : Set H), hC] x) :=
    projectionPoint_weaklyContinuous_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed
  have hproj_tendsto :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (P[(C : Set H), hC]
              (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n)))
        atTop (𝓝 (toWeakSpace ℝ H (P[(C : Set H), hC] y))) := by
    exact
      (weaklyContinuous_iff_forall_net_tendsto.mp hproj_weak)
        (fun n ↦ ⟨douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n, by simp⟩)
        ⟨y, by simp⟩
        (by simpa using hy_tendsto)
  have hy_proj :
      P[(C : Set H), hC] y = resolventMap B hB γ y :=
    affineProjector_eq_resolventLimit_of_fixedPoint hC_nonempty hC_closed hNC hB γ hy_fix
  simpa [hC, hy_proj] using hproj_tendsto

/-- The Douglas--Rachford `y`-orbit from Corollary 28.4, realized canonically as the Chapter 26
Douglas--Rachford iteration for the pair `(N[affineFiber L r], ∂ f)`. -/
def linearFiberDouglasRachfordIteration
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  douglasRachfordIteration
    N[affineFiber L r] (∂ f)
    (Set.normalCone_isMaximallyMonotone
      (linearFiber_nonempty_of_comp_adjoint_eq_smul_id L r μ hscalar)
      (affineFiber_isClosed L r) (affineFiber_convex L r))
    (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)
    γ lam y0

/-- The proximal sequence `xₙ = Prox_{γ f}(yₙ)` from `(28.16)`. -/
def linearFiberDouglasRachfordPrimalSequence
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦ Prox[γ, f, hf] (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n)

/-- The affine-fiber projection sequence `pₙ = P[affineFiber L r] (yₙ)` from `(28.16)`. -/
def linearFiberDouglasRachfordProjectedSequence
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦
    linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n +
      (μ : ℝ)⁻¹ •
        L.adjoint
          (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n))

/-- The auxiliary affine-fiber projection sequence `qₙ = P[affineFiber L r] (xₙ)` from
`(28.16)`. -/
def linearFiberDouglasRachfordAuxiliaryProjectionSequence
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦
    linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n +
      (μ : ℝ)⁻¹ •
        L.adjoint
          (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n))

section IterateCompanions

variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
variable (L : H →L[ℝ] K) (r : K) (μ : PosReal)
variable (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
variable (γ : PosReal) (lam : ℕ → ℝ) (y0 : H)

/-- The canonical `y`-orbit starts at the prescribed initial point. -/
@[simp] theorem linearFiberDouglasRachfordIteration_zero :
    linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 0 = y0 := by
  simp [linearFiberDouglasRachfordIteration, douglasRachfordIteration]

/-- The canonical `x`-sequence is the source proximal step `xₙ = Prox_{γ f}(yₙ)`. -/
@[simp] theorem linearFiberDouglasRachfordPrimalSequence_eq_prox (n : ℕ) :
    linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n =
      Prox[γ, f, hf] (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n) := by
  rfl

/-- Proposition 29.2 rewrites the source iterate `pₙ` as the explicit affine correction
`yₙ + μ⁻¹ L^*(r - L yₙ)`. -/
theorem linearFiberDouglasRachfordProjectedSequence_eq_affineCorrection (n : ℕ) :
    linearFiberDouglasRachfordProjectedSequence hf L r μ hscalar γ lam y0 n =
      linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n +
        (μ : ℝ)⁻¹ •
          L.adjoint
            (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n)) := by
  rfl

/-- Proposition 29.2 likewise rewrites the source iterate `qₙ` as the explicit affine correction
`xₙ + μ⁻¹ L^*(r - L xₙ)`. -/
theorem linearFiberDouglasRachfordAuxiliaryProjectionSequence_eq_affineCorrection (n : ℕ) :
    linearFiberDouglasRachfordAuxiliaryProjectionSequence hf L r μ hscalar γ lam y0 n =
      linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n +
        (μ : ℝ)⁻¹ •
          L.adjoint
            (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n)) := by
  rfl

/-- Each projected iterate `pₙ` lies in the affine fiber `affineFiber L r`. -/
theorem linearFiberDouglasRachfordProjectedSequence_mem_affineFiber (n : ℕ) :
    linearFiberDouglasRachfordProjectedSequence hf L r μ hscalar γ lam y0 n ∈
      affineFiber L r := by
  rw [linearFiberDouglasRachfordProjectedSequence_eq_affineCorrection, mem_affineFiber,
    ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
  have happly := congrArg
    (fun T : K →L[ℝ] K ↦
      T (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n)))
    hscalar
  have hLLstar :
      L
          (L.adjoint
            (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n))) =
        (μ : ℝ) • (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n)) := by
    simpa using happly
  calc
    L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n) +
        (μ : ℝ)⁻¹ •
          L
            (L.adjoint
              (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n)))
        =
        L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n) +
          (μ : ℝ)⁻¹ •
            ((μ : ℝ) •
              (r - L (linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n))) := by
              rw [hLLstar]
    _ = r := by
      simp [smul_smul, inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from ne_of_gt μ.2)]

/-- Each auxiliary projected iterate `qₙ` lies in the affine fiber `affineFiber L r`. -/
theorem linearFiberDouglasRachfordAuxiliaryProjectionSequence_mem_affineFiber (n : ℕ) :
    linearFiberDouglasRachfordAuxiliaryProjectionSequence hf L r μ hscalar γ lam y0 n ∈
      affineFiber L r := by
  rw [linearFiberDouglasRachfordAuxiliaryProjectionSequence_eq_affineCorrection, mem_affineFiber,
    ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
  have happly := congrArg
    (fun T : K →L[ℝ] K ↦
      T (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n)))
    hscalar
  have hLLstar :
      L
          (L.adjoint
            (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n))) =
        (μ : ℝ) •
          (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n)) := by
    simpa using happly
  calc
    L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n) +
        (μ : ℝ)⁻¹ •
          L
            (L.adjoint
              (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n)))
        =
        L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n) +
          (μ : ℝ)⁻¹ •
            ((μ : ℝ) •
              (r - L (linearFiberDouglasRachfordPrimalSequence hf L r μ hscalar γ lam y0 n))) := by
              rw [hLLstar]
    _ = r := by
      simp [smul_smul, inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from ne_of_gt μ.2)]

end IterateCompanions

/-- Corollary 28.4: let `f ∈ Γ₀(H)` and `L : H →L[ℝ] K`. Assume `L ∘L L* = μ • Id`
for some `μ ∈ ℝ_{++}`, assume `r ∈ sri (L (dom f))`, and assume the equality-constrained
problem `minimize f x` subject to `L x = r` has a solution. Let `lam` take values in
`[0, 2]` with `∑ λ_n (2 - λ_n) = +∞`, let `γ ∈ ℝ_{++}`, and let
`yₙ`, `xₙ`, `pₙ`, `qₙ`
be the direct iterate families from `(28.16)`. Then `(pₙ)` converges weakly to a solution
of the constrained problem, represented here by a point of
`Argmin[affineFiber L r] f.asEReal`. -/
theorem linearFiberDouglasRachford_exists_weakLimit_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K) (r : K) (μ : PosReal)
    (hscalar : L.comp L.adjoint = (μ : ℝ) • (1 : K →L[ℝ] K))
    (hsri : r ∈ sri (L '' effectiveDomain f))
    (hargmin : (Argmin[affineFiber L r] f.asEReal).Nonempty)
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : H) :
    ∃ xbar ∈ Argmin[affineFiber L r] f.asEReal,
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (linearFiberDouglasRachfordProjectedSequence hf L r μ hscalar γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H xbar)) := by
  let hA : Maximal SetValuedOperator.IsMonotone N[affineFiber L r] :=
    Set.normalCone_isMaximallyMonotone
      (linearFiber_nonempty_of_comp_adjoint_eq_smul_id L r μ hscalar)
      (affineFiber_isClosed L r) (affineFiber_convex L r)
  have hB : Maximal SetValuedOperator.IsMonotone (∂ f) :=
    subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
  obtain ⟨z, hz⟩ := linearFiber_nonempty_of_comp_adjoint_eq_smul_id L r μ hscalar
  let C : AffineSubspace ℝ H := AffineSubspace.mk' z L.ker
  have hz_eq : L z = r := mem_affineFiber.mp hz
  have hC_set : (C : Set H) = affineFiber L r := by
    ext w
    change L (w - z) = 0 ↔ L w = r
    rw [ContinuousLinearMap.map_sub]
    constructor
    · intro hw
      have hwz : L w = L z := sub_eq_zero.mp hw
      simpa [hz_eq] using hwz
    · intro hw
      have hwz : L w = L z := by simpa [hz_eq] using hw
      exact sub_eq_zero.mpr hwz
  have hC_nonempty : (C : Set H).Nonempty := by
    refine ⟨z, ?_⟩
    change L (z - z) = 0
    simp
  have hC_closed : IsClosed (C : Set H) := by
    simpa [hC_set] using affineFiber_isClosed L r
  let hC : IsChebyshev (C : Set H) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  have hNC : Maximal SetValuedOperator.IsMonotone N[(C : Set H)] := by
    simpa [hC_set] using hA
  have hzero : (primal_inclusion_solution_set N[(C : Set H)] (∂ f)).Nonempty := by
    rcases hargmin with ⟨x, hx⟩
    rcases
        (linearFiberArgminIffExistsNegAdjointMemSubdifferential
          (hf := hf) L hsri).1 hx with
      ⟨hx_fiber, v, hv⟩
    have hxC : x ∈ (C : Set H) := by
      simpa [hC_set] using hx_fiber
    refine ⟨x, ?_⟩
    refine
      (mem_primal_inclusion_solution_set_normalCone_affine_iff_exists_mem_orthogonal
        C
        (∂ f)).2 ?_
    have horth : -L.adjoint v ∈ L.kerᗮ := by
      refine (Submodule.mem_orthogonal' L.ker (-L.adjoint v)).2 ?_
      intro u hu
      have hLu : L u = 0 := LinearMap.mem_ker.mp hu
      rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
      simp [hLu]
    refine ⟨hxC, -L.adjoint v, ?_, hv⟩
    simpa [C, AffineSubspace.direction_mk'] using horth
  rcases
      (SetValuedOperator.douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
        (A := N[(C : Set H)]) (B := ∂ f) hNC hB (γ := γ) (lam := lam) (y0 := y0)
        hzero hlam hdiv) with
    ⟨y, hy_fix, hy_tendsto⟩
  let xbar : H := resolventMap (∂ f) hB γ y
  have hxbar_primal : xbar ∈ primal_inclusion_solution_set N[(C : Set H)] (∂ f) := by
    rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      N[(C : Set H)] (∂ f) hNC hB γ]
    exact ⟨y, hy_fix, rfl⟩
  have hxbar_argmin : xbar ∈ Argmin[affineFiber L r] f.asEReal := by
    rcases
        (mem_primal_inclusion_solution_set_normalCone_affine_iff_exists_mem_orthogonal
          C
          (∂ f)).1 hxbar_primal with
      ⟨hxbarC, u, hu_orth_C, hu_sub⟩
    have hu_orth : u ∈ L.kerᗮ := by
      simpa [C, AffineSubspace.direction_mk'] using hu_orth_C
    have hu_eq :
        u = (μ : ℝ)⁻¹ • L.adjoint (L u) := by
      let d : H := (μ : ℝ)⁻¹ • L.adjoint (L u) - u
      have hd_ker : d ∈ L.ker := by
        change L d = 0
        simp only [d, ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
        have happly := congrArg (fun T : K →L[ℝ] K ↦ T (L u)) hscalar
        have hLLstar : L (L.adjoint (L u)) = (μ : ℝ) • L u := by
          simpa using happly
        simp [hLLstar, smul_smul, inv_mul_cancel₀ (show (μ : ℝ) ≠ 0 from ne_of_gt μ.2)]
      have hLadj_orth : L.adjoint (L u) ∈ L.kerᗮ := by
        refine (Submodule.mem_orthogonal' L.ker _).2 ?_
        intro w hw
        have hLw : L w = 0 := LinearMap.mem_ker.mp hw
        rw [ContinuousLinearMap.adjoint_inner_left]
        simp [hLw]
      have hd_orth : d ∈ L.kerᗮ := by
        exact (L.kerᗮ).sub_mem ((L.kerᗮ).smul_mem _ hLadj_orth) hu_orth
      have hd_zero : d = 0 := by
        have hd_inner : ⟪d, d⟫_ℝ = 0 :=
          (Submodule.mem_orthogonal' L.ker d).1 hd_orth d hd_ker
        exact inner_self_eq_zero.mp hd_inner
      exact (sub_eq_zero.mp hd_zero).symm
    have hsub : -L.adjoint (-((μ : ℝ)⁻¹ • L u)) ∈ (∂ f) xbar := by
      have hEq : -L.adjoint (-((μ : ℝ)⁻¹ • L u)) = u := by
        calc
          -L.adjoint (-((μ : ℝ)⁻¹ • L u))
              = -(-((μ : ℝ)⁻¹ • L.adjoint (L u))) := by
                  simp
          _ = (μ : ℝ)⁻¹ • L.adjoint (L u) := by simp
          _ = u := hu_eq.symm
      rw [hEq]
      exact hu_sub
    refine
      (linearFiberArgminIffExistsNegAdjointMemSubdifferential
        (hf := hf) L hsri).2 ?_
    refine ⟨?_, ⟨-((μ : ℝ)⁻¹ • L u), hsub⟩⟩
    simpa [hC_set] using hxbarC
  have hproj_tendsto :
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (P[(C : Set H), hC]
              (douglasRachfordIteration N[(C : Set H)] (∂ f) hNC hB γ lam y0 n)))
        atTop (𝓝 (toWeakSpace ℝ H xbar)) := by
    simpa [xbar] using
      affineProjector_tendsto_weakly hC_nonempty hC_closed hNC hB γ lam y0 y hy_fix hy_tendsto
  refine ⟨xbar, hxbar_argmin, ?_⟩
  have hseq :
      ∀ n : ℕ,
        linearFiberDouglasRachfordProjectedSequence hf L r μ hscalar γ lam y0 n =
          P[(C : Set H), hC]
            (douglasRachfordIteration N[(C : Set H)] (∂ f) hNC hB γ lam y0 n) := by
    intro n
    rw [linearFiberDouglasRachfordProjectedSequence_eq_affineCorrection]
    rw [← projectionPoint_affineFiber_eq_affineCorrection
      (L := L) (r := r) (μ := μ) (hscalar := hscalar)
      (x := linearFiberDouglasRachfordIteration hf L r μ hscalar γ lam y0 n)]
    simp [linearFiberDouglasRachfordIteration, hC_set]
  simpa [hseq] using hproj_tendsto

end DouglasRachfordLinearFiber

end ERealFunction
