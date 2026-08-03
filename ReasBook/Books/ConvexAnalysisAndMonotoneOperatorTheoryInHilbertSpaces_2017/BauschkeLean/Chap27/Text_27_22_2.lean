import BauschkeLean.Chap01.Text_1_0_16
import BauschkeLean.Chap10.Definition_10_7
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap13.Example_13_6
import BauschkeLean.Chap18.Remark_18_21
import BauschkeLean.Chap15.Proposition_15_7
import BauschkeLean.Chap27.Corollary_27_3
import BauschkeLean.Chap27.Theorem_27_23

open Filter Set
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

noncomputable section

universe u

namespace ERealFunction

section Regularization

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall note: the canonical Chapter 27 owners for this text are the pointwise-sum
-- argmin/subdifferential criterion from `Corollary_27_3` and the Tikhonov convergence theorem
-- `tendsto_argmin_add_posReal_smul_of_closedBall_uniformlyConvex`, both specialized to
-- `g = halfSquaredNorm`.

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem mem_effectiveDomain_posReal_smul_iff
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ effectiveDomain (γ • f) ↔ x ∈ effectiveDomain f := by
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, posReal_smul_apply, lt_top_iff_ne_top,
    lt_top_iff_ne_top]
  constructor
  · intro hγf htop
    exact hγf (by simpa [htop] using EReal.coe_mul_top_of_pos γ.2)
  · intro hf
    rw [EReal.mul_ne_top]
    exact ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
      Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hf⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem halfSquaredNorm_coercive :
    Coercive ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal) := by
  refine
    (coercive_iff_bounded_lowerLevelSet
      ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)).2 ?_
  intro ξ
  refine (Metric.isBounded_iff_subset_closedBall (0 : H)).2 ?_
  let R : ℝ := max 1 (2 * |ξ| + 1)
  refine ⟨R, ?_⟩
  intro x hx
  rw [mem_lowerLevelSet_iff] at hx
  have hxreal : ‖x‖ ^ 2 / 2 ≤ ξ := by
    have hcast :
        ((halfSquaredNorm x : Set.Ioi (⊥ : EReal)) : EReal) ≤ ((ξ : ℝ) : EReal) := by
      simpa [Function.asEReal_apply] using hx
    have hcast' : ((((1 / 2 : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal)) ≤ ((ξ : ℝ) : EReal) := by
      simpa [halfSquaredNorm_apply] using hcast
    have hreal' : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ξ := by
      exact_mod_cast hcast'
    nlinarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hnorm
  have hnorm' : ¬ ‖x‖ ≤ R := by
    simpa using hnorm
  have hRlt : R < ‖x‖ := lt_of_not_ge hnorm'
  have hnorm_ge_one : 1 ≤ ‖x‖ := le_trans (le_max_left 1 (2 * |ξ| + 1)) hRlt.le
  have habs_lt : 2 * |ξ| + 1 < ‖x‖ := lt_of_le_of_lt (le_max_right 1 (2 * |ξ| + 1)) hRlt
  have hξ_twice : 2 * ξ < ‖x‖ := by
    nlinarith [le_abs_self ξ, habs_lt]
  have hnorm_sq_ge : ‖x‖ ≤ ‖x‖ ^ 2 := by
    nlinarith [hnorm_ge_one, sq_nonneg ‖x‖]
  have hξ_lt : ξ < ‖x‖ ^ 2 / 2 := by
    nlinarith [hξ_twice, hnorm_sq_ge]
  exact (not_lt_of_ge hxreal) hξ_lt

omit [CompleteSpace H] in
private theorem halfSquaredNorm_uniformlyConvexOn_closedBall_slice
    (c : H) {r : ℝ} (hr : 0 ≤ r)
    (hC_nonempty :
      (Metric.closedBall c r ∩
        effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))).Nonempty) :
    ∃ φ : NNReal → EReal,
      UniformlyConvexOn halfSquaredNorm
        (Metric.closedBall c r ∩
          effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) φ := by
  let _ := hr
  let g : H → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
  have hstrong : StrongConvexOn (Set.univ : Set H) (1 : ℝ) g := by
    rw [strongConvexOn_iff_convex]
    simpa [g, sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (convexOn_const (0 : ℝ) convex_univ :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun _ : H ↦ (0 : ℝ)))
  have huniform : UniformlyConvex g.toEReal (strongConvexityModulus (1 : ℝ)) := by
    have hstrongly : StronglyConvex g.toEReal (1 : ℝ) :=
      StrongConvexOn.toStronglyConvex (by norm_num) hstrong
    exact hstrongly.uniformlyConvex
  have hhalf : g.toEReal = (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) := by
    ext x
    change (((‖x‖ ^ 2 / 2 : ℝ) : EReal)) = (halfSquaredNorm x : EReal)
    rw [halfSquaredNorm_apply]
  have hslice :
      UniformlyConvexOn g.toEReal
        (Metric.closedBall c r ∩ effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)))
        (strongConvexityModulus (1 : ℝ)) := by
    refine ⟨hC_nonempty, ?_, huniform.uniformlyConvexOn.monotone,
      huniform.uniformlyConvexOn.modulus_eq_zero_iff, ?_⟩
    · intro x hx
      simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy α hα0 hα1
      simpa [Function.effectiveDomain_toEReal] using
        huniform.uniformlyConvexOn.gap_le (by simp [Function.effectiveDomain_toEReal])
          (by simp [Function.effectiveDomain_toEReal]) hα0 hα1
  refine ⟨strongConvexityModulus (1 : ℝ), ?_⟩
  simpa [hhalf] using hslice

omit [CompleteSpace H] in
private theorem mem_subdifferential_halfSquaredNorm_iff
    {x u : H} :
    u ∈ (∂ (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) x ↔ u = x := by
  have hdom : (effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_effectiveDomain_iff]
    simp
  constructor
  · intro hu
    have hfy :
        (halfSquaredNorm x : EReal) +
            (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal∗ u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq
        (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) hdom x u).1 hu
    rw [fenchelConjugate_halfSquaredNorm] at hfy
    have hfy_real : (1 / 2 : ℝ) * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2 = ⟪x, u⟫_ℝ := by
      norm_num at hfy
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
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) hdom x x).2
    rw [fenchelConjugate_halfSquaredNorm, Function.asEReal_apply, halfSquaredNorm_apply]
    have hreal : (‖x‖ ^ 2) / 2 + (‖x‖ ^ 2) / 2 = ⟪x, x⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]
      ring
    exact_mod_cast hreal

omit [CompleteSpace H] in
@[simp] private theorem subdifferential_halfSquaredNorm_apply_local (x : H) :
    (∂ (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) x = ({x} : Set H) := by
  ext u
  rw [Set.mem_singleton_iff, mem_subdifferential_halfSquaredNorm_iff]

omit [CompleteSpace H] in
private theorem halfSquaredNorm_pointwiseAddRegularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    PointwiseAddRegularity f ((⟨ε, hε.1⟩ : PosReal) • halfSquaredNorm) := by
  refine PointwiseAddRegularity.zero_mem_sri ?_
  have hhalf_dom :
      effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)) = (Set.univ : Set H) := by
    ext x
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    simp
  have hdom :
      effectiveDomain
          (((⟨ε, hε.1⟩ : PosReal) • halfSquaredNorm : H → Set.Ioi (⊥ : EReal))) =
        (Set.univ : Set H) := by
    ext x
    rw [mem_effectiveDomain_posReal_smul_iff]
    rw [hhalf_dom]
  rw [hdom]
  have hsub : ((Set.univ : Set H) - effectiveDomain f) = Set.univ :=
    by
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        rcases hf.2.nonempty with ⟨y, hy⟩
        exact Set.mem_sub.mpr ⟨x + y, by simp, y, hy, by abel⟩
  rw [hsub, Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

/-- Text 27.22.2 (1): when the regularizer is `g = (1 / 2)‖·‖²`, minimizing
`f + ε g` is equivalent to the Tikhonov inclusion
`0 ∈ ∂ f(xε) + ε xε`. -/
theorem mem_argmin_add_posReal_smul_halfSquaredNorm_iff_zero_mem_subdifferential_add_singleton_smul
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {xε : H} :
    xε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • halfSquaredNorm).asEReal ↔
      0 ∈ (∂ f) xε + ({ε • xε} : Set H) := by
  let εpos : PosReal := ⟨ε, hε.1⟩
  have hregular : PointwiseAddRegularity f (εpos • halfSquaredNorm) :=
    halfSquaredNorm_pointwiseAddRegularity hf hε
  have hargmin :
      xε ∈ Argmin (f + εpos • halfSquaredNorm).asEReal ↔
        xε ∈ ((∂ f) + (∂ (εpos • halfSquaredNorm))).zeros := by
    simpa using
      (mem_argmin_add_iff_mem_zeros_subdifferential_add_of_regularity
        hf (smul_mem_gammaZero halfSquaredNorm halfSquaredNorm_mem_gammaZero εpos) hregular)
  rw [hargmin, SetValuedOperator.mem_zeros_iff,
    subdifferential_posReal_smul_eq_smul halfSquaredNorm εpos,
    SetValuedOperator.add_smul_apply, subdifferential_halfSquaredNorm_apply_local]
  simp [Set.smul_set_singleton, εpos]

/-- Text 27.22.2 (1), companion form: the Tikhonov inclusion is equivalent to the direct
subgradient condition `-(ε • xε) ∈ ∂ f(xε)`. -/
theorem mem_argmin_add_posReal_smul_halfSquaredNorm_iff_neg_smul_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {xε : H} :
    xε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • halfSquaredNorm).asEReal ↔
      -(ε • xε) ∈ (∂ f) xε := by
  rw [mem_argmin_add_posReal_smul_halfSquaredNorm_iff_zero_mem_subdifferential_add_singleton_smul
    hf hε]
  constructor
  · rw [Set.mem_add]
    rintro ⟨u, hu, v, hv, huv⟩
    rw [Set.mem_singleton_iff] at hv
    subst v
    have hu_eq : u = -(ε • xε) := by
      simpa using eq_neg_of_add_eq_zero_left huv
    simpa [hu_eq] using hu
  · intro hu
    rw [Set.mem_add]
    exact ⟨-(ε • xε), hu, ε • xε, by simp, by simp⟩

/-- Text 27.22.2 (2): if `x0` is the minimum-norm minimizer of `f`, then every Tikhonov
minimizer curve converges to `x0` as `ε ↓ 0` through `]0,1[`. -/
theorem tendsto_argmin_add_posReal_smul_halfSquaredNorm_to_minimum_norm_minimizer
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {x0 : H} (hx0 : x0 ∈ Argmin[Argmin f.asEReal] halfSquaredNorm.asEReal)
    {xε : ℝ → H}
    (hxε :
      ∀ {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
        xε ε ∈ Argmin (f + (⟨ε, hε.1⟩ : PosReal) • halfSquaredNorm).asEReal) :
    Tendsto xε (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) (𝓝 x0) := by
  have hfeas :
      (Argmin f.asEReal ∩
        effectiveDomain (halfSquaredNorm : H → Set.Ioi (⊥ : EReal))).Nonempty := by
    refine ⟨x0, (mem_argminOn_iff.mp hx0).1, ?_⟩
    rw [mem_effectiveDomain_iff, halfSquaredNorm_apply]
    exact EReal.coe_lt_top _
  exact
    tendsto_argmin_add_posReal_smul_of_closedBall_uniformlyConvex
      hf halfSquaredNorm_mem_gammaZero hfeas halfSquaredNorm_coercive
      (fun {c} {r} hr hnonempty ↦
        halfSquaredNorm_uniformlyConvexOn_closedBall_slice c hr hnonempty)
      hx0 hxε

end Regularization

end ERealFunction
