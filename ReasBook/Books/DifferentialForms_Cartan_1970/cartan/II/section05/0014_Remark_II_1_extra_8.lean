import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0012_Definition_II_1_extra_7»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {a b : E} {γ : Path a b} {ω : E → E →L[ℝ] F}
variable {D D₁ D₂ : Set E} {f g : C(I, F)}

/-- Helper for Cartan section05 0014_Remark_II_1_extra_8: two local primitives defined near the
same point differ by a constant on a smaller ball around that point. -/
private theorem local_sub_eq_const_on_ball_of_common_primitive
    {U V : Set E} {z₀ : E} {F₁ F₂ : E → F}
    (hU : IsOpen U) (hV : IsOpen V) (hzU : z₀ ∈ U) (hzV : z₀ ∈ V)
    (hF₁ : IsPrimitiveOn U ω F₁) (hF₂ : IsPrimitiveOn V ω F₂) :
    ∃ r : ℝ, 0 < r ∧ ∃ c : F,
      Set.EqOn (fun z ↦ F₂ z - F₁ z) (fun _ ↦ c) (Metric.ball z₀ r) := by
  -- Shrink to a ball inside the overlap so the standard constant-difference theorem applies.
  have hzUV : z₀ ∈ U ∩ V := ⟨hzU, hzV⟩
  rcases Metric.isOpen_iff.mp (hU.inter hV) z₀ hzUV with ⟨r, hr, hball⟩
  have hF₁_ball : IsPrimitiveOn (Metric.ball z₀ r) ω F₁ :=
    hF₁.mono fun z hz ↦ (hball hz).1
  have hF₂_ball : IsPrimitiveOn (Metric.ball z₀ r) ω F₂ :=
    hF₂.mono fun z hz ↦ (hball hz).2
  rcases IsPrimitiveOn.sub_eqOn_const_of_isOpen_isPreconnected
      (D := Metric.ball z₀ r) Metric.isOpen_ball (convex_ball z₀ r).isPreconnected
      hF₂_ball hF₁_ball with
    ⟨c, hc⟩
  exact ⟨r, hr, c, hc⟩

-- Proof sketch: compare the two local primitive witnesses at each parameter value on a common
-- codomain ball and pull the resulting constant-difference relation back along `γ`.
/-- Helper for Cartan section05 0014_Remark_II_1_extra_8: the difference of two primitives along
the same path is locally constant on the unit interval. -/
theorem IsPrimitiveAlongPath.sub_isLocallyConstant
    (hf : IsPrimitiveAlongPath ω D₁ γ f)
    (hg : IsPrimitiveAlongPath ω D₂ γ g) :
    IsLocallyConstant (fun t : I ↦ g t - f t) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro τ
  rcases hf.local_primitive τ with
    ⟨sf, hsf_open, hτsf, Uf, hUf_open, hγτUf, -, hγsf, F₁, hF₁, hEqf⟩
  rcases hg.local_primitive τ with
    ⟨sg, hsg_open, hτsg, Ug, hUg_open, hγτUg, -, hγsg, F₂, hF₂, hEqg⟩
  -- Compare the two codomain primitives on a common ball around `γ τ`.
  rcases local_sub_eq_const_on_ball_of_common_primitive hUf_open hUg_open hγτUf hγτUg hF₁ hF₂ with
    ⟨r, hr, c, hc⟩
  let s : Set I := (sf ∩ sg) ∩ γ ⁻¹' Metric.ball (γ τ) r
  have hs_open : IsOpen s := by
    refine (hsf_open.inter hsg_open).inter ?_
    exact γ.continuous.isOpen_preimage _ Metric.isOpen_ball
  have hτs : τ ∈ s := by
    refine ⟨⟨hτsf, hτsg⟩, Metric.mem_ball_self hr⟩
  have hτconst : g τ - f τ = c := by
    calc
      g τ - f τ = F₂ (γ τ) - F₁ (γ τ) := by
        rw [hEqg hτsg, hEqf hτsf]
        rfl
      _ = c := hc (Metric.mem_ball_self hr)
  refine ⟨s, hs_open, hτs, ?_⟩
  intro t ht
  have htsf : t ∈ sf := ht.1.1
  have htsg : t ∈ sg := ht.1.2
  have htball : γ t ∈ Metric.ball (γ τ) r := ht.2
  -- On the common neighborhood, both primitives pull back from codomain primitives whose
  -- difference is the same constant `c`.
  calc
    g t - f t = F₂ (γ t) - F₁ (γ t) := by
      rw [hEqg htsg, hEqf htsf]
      rfl
    _ = c := hc htball
    _ = g τ - f τ := hτconst.symm

-- Proof sketch: near an interior parameter value, the local primitive witness identifies
-- `Set.IccExtend zero_le_one f` with a codomain primitive composed with `γ.extend`, so the
-- derivative is obtained by the chain rule.
/-- Helper for Cartan section05 0014_Remark_II_1_extra_8: a primitive along `γ` has the expected
right derivative at every interior parameter where `γ.extend` is differentiable. -/
private theorem hasDerivWithinAt_iccExtend_of_localPrimitive
    (hf : IsPrimitiveAlongPath ω D γ f) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hγdiff : DifferentiableAt ℝ γ.extend x) :
    HasDerivWithinAt (Set.IccExtend zero_le_one f)
      (ω (γ.extend x) (deriv γ.extend x)) (Set.Ioi x) x := by
  let τ : I := ⟨x, Set.Ioo_subset_Icc_self hx⟩
  rcases hf.local_primitive τ with
    ⟨s, hs_open, hτs, U, -, hγτU, -, -, F₀, hF₀, hEqf⟩
  have hs_mem : s ∈ nhds τ := hs_open.mem_nhds hτs
  have hproj_mem :
      {y : ℝ | Set.projIcc 0 1 zero_le_one y ∈ s} ∈ nhds x := by
    have hs_proj : s ∈ nhds (Set.projIcc 0 1 zero_le_one x) := by
      simpa [τ, Set.projIcc_of_mem zero_le_one (Set.Ioo_subset_Icc_self hx)] using hs_mem
    exact continuous_projIcc.continuousAt.preimage_mem_nhds hs_proj
  have hEqNear :
      Set.IccExtend zero_le_one f =ᶠ[nhds x] fun y ↦ F₀ (γ.extend y) := by
    filter_upwards [hproj_mem] with y hy
    exact hEqf hy
  have hγxU : γ.extend x ∈ U := by
    simpa [τ, Path.extend_apply γ (Set.Ioo_subset_Icc_self hx)] using hγτU
  have hcomp :
      HasDerivAt (fun y ↦ F₀ (γ.extend y)) (ω (γ.extend x) (deriv γ.extend x)) x := by
    -- Apply the chain rule to the local codomain primitive and the differentiable path.
    simpa using (hF₀ (γ.extend x) hγxU).comp_hasDerivAt x hγdiff.hasDerivAt
  exact (hcomp.hasDerivWithinAt).congr_of_eventuallyEq
    (hEqNear.filter_mono nhdsWithin_le_nhds) <| by
      simpa [τ, Path.extend_apply γ (Set.Ioo_subset_Icc_self hx),
        Set.IccExtend_of_mem _ _ (Set.Ioo_subset_Icc_self hx)] using
        hEqf hτs

-- Proof sketch: choose a subdivision witnessing piecewise differentiability of `γ`, apply the
-- one-variable fundamental theorem on each subinterval using the local primitive supplied by
-- `hf`, and sum the resulting endpoint differences to obtain a telescoping series.
/-- Cartan section05 0014_Remark_II_1_extra_8 (Remark II.1-extra-8): if `γ` is piecewise
differentiable, the pullback of `ω` is integrable along `γ`, and `f` is a primitive of `ω` along
`γ`, then the curve integral of `ω` along `γ` is the endpoint difference `f 1 - f 0`. The source
text separates this from the purely topological endpoint-difference convention for continuous
paths. -/
theorem IsPrimitiveAlongPath.curveIntegral_eq_endpoint_sub
    [CompleteSpace F] (hf : IsPrimitiveAlongPath ω D γ f)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable) (hγ_integrable : CurveIntegrable ω γ) :
    ∫ᶜ z in γ, ω z = f 1 - f 0 := by
  rcases hγ_piecewise with ⟨n, subdiv, hsubdiv, h0, h1, hpiece⟩
  let a : ℕ → ℝ := fun k => if hk : k ≤ n + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  let β : ℕ → F := fun k => Set.IccExtend zero_le_one f (a k)
  have ha0 : a 0 = 0 := by
    simp [a, h0]
  have haLast : a (n + 1) = 1 := by
    simpa [a] using h1
  have hFcont : Continuous (Set.IccExtend zero_le_one f) := f.continuous.Icc_extend'
  have hpieceIntegrable :
      ∀ k < n + 1,
        IntervalIntegrable (curveIntegralFun ω γ) MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    have hk_le : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1_le : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt :
        subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩ < subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ := by
      exact hsubdiv (by simp)
    have hleft_nonneg : 0 ≤ subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩ := by
      rw [← h0]
      exact hsubdiv.monotone (by simp)
    have hright_le_one : subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ ≤ 1 := by
      rw [← h1]
      have hfin_le : (⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ : Fin (n + 2)) ≤ Fin.last (n + 1) := by
        change k + 1 ≤ n + 1
        exact hk1_le
      exact hsubdiv.monotone hfin_le
    have ha_k : a k = subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩ := by
      simp [a, hk_le]
    have ha_k1 : a (k + 1) = subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ := by
      simp [a, hk1_le]
    rw [ha_k, ha_k1]
    apply hγ_integrable.mono_set
    rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hlt.le]
    exact Set.Icc_subset_Icc hleft_nonneg hright_le_one
  have hpieceIntegral :
      ∀ k < n + 1, ∫ x in a k..a (k + 1), curveIntegralFun ω γ x = β (k + 1) - β k := by
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk_le : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1_le : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have ha_k : a k = subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩ := by
      simp [a, hk_le]
    have ha_k1 : a (k + 1) = subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ := by
      simp [a, hk1_le]
    have hlt :
        subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩ < subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ := by
      exact hsubdiv (by simp)
    have hleft_nonneg : 0 ≤ subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩ := by
      rw [← h0]
      exact hsubdiv.monotone (by simp)
    have hright_le_one : subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ ≤ 1 := by
      rw [← h1]
      have hfin_le : (⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ : Fin (n + 2)) ≤ Fin.last (n + 1) := by
        change k + 1 ≤ n + 1
        exact hk1_le
      exact hsubdiv.monotone hfin_le
    have hcont_piece :
        ContinuousOn (Set.IccExtend zero_le_one f) (Set.Icc (a k) (a (k + 1))) := by
      -- Global continuity immediately gives continuity on each subdivision interval.
      intro x hx
      exact hFcont.continuousAt.continuousWithinAt
    have hint_piece :
        IntervalIntegrable (curveIntegralFun ω γ) MeasureTheory.volume (a k) (a (k + 1)) :=
      hpieceIntegrable k hk
    have hderiv_piece :
        ∀ x ∈ Set.Ioo (a k) (a (k + 1)),
          HasDerivWithinAt (Set.IccExtend zero_le_one f)
            (curveIntegralFun ω γ x) (Set.Ioi x) x := by
      intro x hx
      have hx_sub :
          x ∈ Set.Ioo (subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩)
            (subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩) := by
        simpa [ha_k, ha_k1] using hx
      have hγdiffWithin :
          DifferentiableWithinAt ℝ γ.extend
            (Set.Icc (subdiv ⟨k, Nat.lt_succ_of_le hk_le⟩)
              (subdiv ⟨k + 1, Nat.lt_succ_of_le hk1_le⟩)) x :=
        (hpiece i).differentiableOn_one x (Set.Ioo_subset_Icc_self hx_sub)
      have hγdiff : DifferentiableAt ℝ γ.extend x :=
        hγdiffWithin.differentiableAt (Icc_mem_nhds hx_sub.1 hx_sub.2)
      have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor
        · exact lt_of_le_of_lt hleft_nonneg hx_sub.1
        · exact lt_of_lt_of_le hx_sub.2 hright_le_one
      have hlocal := hasDerivWithinAt_iccExtend_of_localPrimitive hf hx01 hγdiff
      have hcurve :
          curveIntegralFun ω γ x = ω (γ.extend x) (deriv γ.extend x) := by
        rw [curveIntegralFun_def]
        congr
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hx01.1 hx01.2)
      exact hlocal.congr_deriv hcurve.symm
    -- Evaluate the integral on one differentiable piece by the one-variable FTC.
    have hle : a k ≤ a (k + 1) := by
      rw [ha_k, ha_k1]
      exact hlt.le
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hle hcont_piece hderiv_piece hint_piece
  have hsum :
      ∑ k ∈ Finset.range (n + 1), ∫ x in a k..a (k + 1), curveIntegralFun ω γ x =
        ∫ x in a 0..a (n + 1), curveIntegralFun ω γ x := by
    exact intervalIntegral.sum_integral_adjacent_intervals hpieceIntegrable
  -- Sum the piecewise endpoint formulas and telescope the intermediate values.
  calc
    ∫ᶜ z in γ, ω z = ∫ x in 0..1, curveIntegralFun ω γ x := by
      rw [curveIntegral_def]
    _ = ∫ x in a 0..a (n + 1), curveIntegralFun ω γ x := by
      simp [ha0, haLast]
    _ = ∑ k ∈ Finset.range (n + 1), ∫ x in a k..a (k + 1), curveIntegralFun ω γ x := by
      symm
      exact hsum
    _ = ∑ k ∈ Finset.range (n + 1), (β (k + 1) - β k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact hpieceIntegral k (Finset.mem_range.mp hk)
    _ = β (n + 1) - β 0 := by
      simpa [β] using (Finset.sum_range_sub β (n + 1))
    _ = f 1 - f 0 := by
      simp [β, ha0, haLast]

-- Proof sketch: compare the endpoint differences attached to `f` and `g` on a common local cover
-- of `I`; on overlaps their difference is locally constant, hence constant on the connected unit
-- interval, so the endpoint jumps agree.
/-- The endpoint difference attached to a primitive along a continuous path is independent of the
chosen primitive. -/
theorem IsPrimitiveAlongPath.endpoint_sub_eq
    (hf : IsPrimitiveAlongPath ω D₁ γ f)
    (hg : IsPrimitiveAlongPath ω D₂ γ g) :
    f 1 - f 0 = g 1 - g 0 := by
  have hloc : IsLocallyConstant (fun t : I ↦ g t - f t) :=
    hf.sub_isLocallyConstant hg
  haveI : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc
  have hconst : g (0 : I) - f (0 : I) = g 1 - f 1 := by
    simpa using hloc.apply_eq_of_preconnectedSpace (0 : I) 1
  -- On the connected parameter interval, the difference `g - f` is constant, so the endpoint
  -- jumps agree after rearranging terms.
  have hswap : f 1 - g 1 = f 0 - g 0 := by
    calc
      f 1 - g 1 = -(g 1 - f 1) := by abel
      _ = -(g 0 - f 0) := by rw [← hconst]
      _ = f 0 - g 0 := by abel
  calc
    f 1 - f 0 = (f 1 - g 1) + (g 1 - f 0) := by abel
    _ = (f 0 - g 0) + (g 1 - f 0) := by rw [hswap]
    _ = g 1 - g 0 := by abel
