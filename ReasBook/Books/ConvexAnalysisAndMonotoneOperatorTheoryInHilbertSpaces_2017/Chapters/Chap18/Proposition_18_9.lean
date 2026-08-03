import Mathlib
import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap16.Proposition_16_37
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap17.Proposition_17_39.SelectionContinuity
import BauschkeLean.Chap17.Proposition_17_39.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open SetValuedOperator
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 18 9: a segment of subgradients at `x` becomes a segment inside the
domain of the subdifferential of the Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
lemma segment_subset_subdifferentialDom_gammaZeroConjugate_of_segment_subset_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u0 u1 : H}
    (hseg : segment ℝ u0 u1 ⊆ (∂ f) x) :
    segment ℝ u0 u1 ⊆ SetValuedOperator.dom (∂ (f∗[hf])) := by
  intro u hu
  -- Corollary 16.30 rewrites subgradients of `f` as inverse-graph points of `∂ f*`.
  rw [SetValuedOperator.mem_dom_iff]
  refine ⟨x, ?_⟩
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf]
  simpa [SetValuedOperator.mem_inverse_iff] using hseg hu

omit [CompleteSpace H] in
/-- Helper for Proposition 18 9: strict convexity of `f*` on the segment between two subgradients
at the same point forces those subgradients to agree. -/
lemma eq_of_mem_subdifferential_of_strictlyConvexOn_segment_gammaZeroConjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u0 u1 : H}
    (hu0 : u0 ∈ (∂ f) x) (hu1 : u1 ∈ (∂ f) x)
    (hstrictSeg : StrictlyConvexOn (f∗[hf]) (segment ℝ u0 u1)) :
    u0 = u1 := by
  by_contra hne
  -- Route correction: use the source segment argument, not a replacement differentiability test.
  have hseg : segment ℝ u0 u1 ⊆ (∂ f) x :=
    (convex_subdifferential f x).segment_subset hu0 hu1
  have htrace :=
    gammaZeroConjugate_eq_lineMap_on_segment_of_segment_subset_subdifferential
      (f := f) hf x u0 u1 hseg
  rcases htrace with ⟨hfin, haff⟩
  let m : H := AffineMap.lineMap u0 u1 (1 / 2 : ℝ)
  have hm_seg : m ∈ segment ℝ u0 u1 := by
    rw [segment_eq_image_lineMap]
    refine ⟨(1 / 2 : ℝ), ?_, rfl⟩
    constructor <;> norm_num
  have hu0_fin : u0 ∈ effectiveDomain (f∗[hf]) := hfin (left_mem_segment ℝ u0 u1)
  have hu1_fin : u1 ∈ effectiveDomain (f∗[hf]) := hfin (right_mem_segment ℝ u0 u1)
  have hm_fin : m ∈ effectiveDomain (f∗[hf]) := hfin hm_seg
  have hu0_top : (f∗[hf] u0 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu0_fin)
  have hu1_top : (f∗[hf] u1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hu1_fin)
  have hm_top : (f∗[hf] m : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hm_fin)
  have hu0_bot : (f∗[hf] u0 : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] u0).2
  have hu1_bot : (f∗[hf] u1 : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] u1).2
  have hm_bot : (f∗[hf] m : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] m).2
  have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hm_real :
      (f∗[hf] m : EReal).toReal =
        AffineMap.lineMap
          ((f∗[hf] u0 : EReal).toReal)
          ((f∗[hf] u1 : EReal).toReal)
          (1 / 2 : ℝ) := by
    simpa [m] using haff hhalf_mem
  have hm_eq :
      (f∗[hf] m : EReal) =
        (1 / 2 : EReal) * (f∗[hf] u1 : EReal) +
          (1 - (1 / 2 : ℝ) : EReal) * (f∗[hf] u0 : EReal) := by
    have hm_cast :
        (f∗[hf] m : EReal) =
          ((AffineMap.lineMap
            ((f∗[hf] u0 : EReal).toReal)
            ((f∗[hf] u1 : EReal).toReal)
            (1 / 2 : ℝ) : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hm_top hm_bot]
      exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hm_real
    calc
      (f∗[hf] m : EReal) =
          ((AffineMap.lineMap
            ((f∗[hf] u0 : EReal).toReal)
            ((f∗[hf] u1 : EReal).toReal)
            (1 / 2 : ℝ) : ℝ) : EReal) := hm_cast
      _ = (1 / 2 : EReal) * (f∗[hf] u1 : EReal) +
            (1 - (1 / 2 : ℝ) : EReal) * (f∗[hf] u0 : EReal) := by
            rw [← EReal.coe_toReal hu0_top hu0_bot, ← EReal.coe_toReal hu1_top hu1_bot]
            have hmid_real_value :
                AffineMap.lineMap
                    ((f∗[hf] u0 : EReal).toReal)
                    ((f∗[hf] u1 : EReal).toReal)
                    (1 / 2 : ℝ) =
                  (1 / 2 : ℝ) * (f∗[hf] u1 : EReal).toReal +
                    (1 - 1 / 2 : ℝ) * (f∗[hf] u0 : EReal).toReal := by
              simp [AffineMap.lineMap_apply_module, add_comm]
            simpa [EReal.coe_add, EReal.coe_mul] using
              congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hmid_real_value
  have hne' : u1 ≠ u0 := fun h => hne h.symm
  have hmid_lt :
      (f∗[hf] m : EReal) <
        (1 / 2 : EReal) * (f∗[hf] u1 : EReal) +
          (1 - (1 / 2 : ℝ) : EReal) * (f∗[hf] u0 : EReal) := by
    -- Strict convexity forbids equality at the midpoint of a nontrivial segment.
    simpa [m, AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
      hstrictSeg.ineq (right_mem_segment ℝ u0 u1) (left_mem_segment ℝ u0 u1) hne'
        (by norm_num) (by norm_num)
  exact (not_lt_of_ge hm_eq.ge) hmid_lt

/-- Helper for Proposition 18 9: interior effective-domain points have singleton subdifferential
fibers under the segmentwise strict-convexity hypothesis on `f*`. -/
lemma subdifferential_eq_singleton_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hstrict :
      ∀ ⦃C : Set H⦄, C.Nonempty → Convex ℝ C →
        C ⊆ SetValuedOperator.dom (∂ (f∗[hf])) →
        StrictlyConvexOn (f∗[hf]) C)
    {x : H} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ u : H, (∂ f) x = ({u} : Set H) := by
  -- Interior-domain points lie in `dom (∂ f)`, so a subgradient exists to serve as the singleton.
  rcases (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := x)).1
      (mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx) with ⟨u, hu⟩
  refine ⟨u, Set.Subset.antisymm ?_ ?_⟩
  · intro v hv
    -- The segment between two subgradients stays in `∂ f(x)`, hence strict convexity on its
    -- conjugate-domain image forces the endpoints to coincide.
    have hseg_sub : segment ℝ u v ⊆ (∂ f) x :=
      (convex_subdifferential f x).segment_subset hu hv
    have hseg_dom :
        segment ℝ u v ⊆ SetValuedOperator.dom (∂ (f∗[hf])) :=
      segment_subset_subdifferentialDom_gammaZeroConjugate_of_segment_subset_subdifferential
        hf hseg_sub
    have hstrictSeg : StrictlyConvexOn (f∗[hf]) (segment ℝ u v) :=
      hstrict ⟨u, left_mem_segment ℝ u v⟩ (convex_segment u v) hseg_dom
    exact Set.mem_singleton_iff.mpr
      (eq_of_mem_subdifferential_of_strictlyConvexOn_segment_gammaZeroConjugate
        hf hu hv hstrictSeg).symm
  · intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact hu

omit [CompleteSpace H] in
/-- Helper for Proposition 18 9: at finite values, the affine `EReal` subgradient inequality is
equivalent to the corresponding real inequality. -/
lemma ereal_affine_ineq_iff_inner_le_toReal_sub
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    (((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)) ↔
      (⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal)) := by
  -- This isolates the `EReal`-to-`toReal` transport once, so later quotient bounds stay readable.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsub :
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
        (f y : EReal) - (f x : EReal) := by
    -- Rewriting both finite `EReal` values through `toReal` turns the subtraction into a real one.
    calc
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
          (((f y : EReal).toReal : EReal) - (((f x : EReal).toReal : EReal))) := by
            rw [EReal.coe_sub]
      _ = (f y : EReal) - (f x : EReal) := by
        rw [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hx_top hx_bot]
  constructor
  · intro hineq
    -- Move `(f x : EReal)` to the right and then read the resulting finite inequality in `ℝ`.
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).2 hineq
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      simpa [hsub] using hsubineq
    exact_mod_cast hcast
  · intro hineq
    -- Cast the real inequality back to `EReal`, then undo the subtraction transport.
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hineq
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      simpa [hsub] using hcast
    exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).1 hsubineq

/-- Helper for Proposition 18 9: if the fiber `(∂ f) x` is a singleton, then every subgradient
selection converges weakly to that unique value along domain points approaching `x`. -/
lemma selection_values_tendsto_weak_of_singleton_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hsubx : (∂ f) x = ({u} : Set H))
    (G : Selection (∂ f)) (z : ℕ → (∂ f).dom)
    (hz :
      Tendsto z atTop
        (𝓝 ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩)) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (G (z n) : H)) atTop (𝓝 (toWeakSpace ℝ H u)) := by
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  have hxcont : ContinuousAtOnEffectiveDomain f x :=
    continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain hf hx
  have hz_base : Tendsto (fun n ↦ (z n : H)) atTop (𝓝 x) := by
    simpa [x0] using (continuous_subtype_val.tendsto x0).comp hz
  obtain ⟨ρ, hρpos, hρbounded⟩ :=
    subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain f hf.2 hxcont
  have htail : ∀ᶠ n in atTop, (z n : H) ∈ Metric.ball x ρ := by
    exact hz_base.eventually (Metric.ball_mem_nhds x hρpos)
  rcases eventually_atTop.mp htail with ⟨N, hN⟩
  let s0 : Set H := (fun n ↦ (G (z n) : H)) '' {n : ℕ | n < N}
  have hs0_finite : s0.Finite := by
    classical
    simpa [s0] using (Set.finite_lt_nat N).image (fun n ↦ (G (z n) : H))
  have hrange_subset :
      Set.range (fun n ↦ (G (z n) : H)) ⊆ s0 ∪ ⋃ y ∈ Metric.ball x ρ, (∂ f) y := by
    rintro v ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr <| Set.mem_iUnion.2 ⟨(z n : H),
        Set.mem_iUnion.2 ⟨hN n (Nat.le_of_not_lt hn), selection_apply_mem G (z n)⟩⟩
  have hbounded :
      Bornology.IsBounded (Set.range fun n ↦ (G (z n) : H)) := by
    exact (hs0_finite.isBounded.union hρbounded).subset hrange_subset
  have hcluster_eq :
      ∀ w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (G (z n) : H))
          (toWeakSpace ℝ H w) →
        w = u := by
    intro w hw
    rcases hw.exists_subseq_tendsto with ⟨φ, hφ, hφw⟩
    have hzφ : Tendsto (fun n ↦ z (φ n)) atTop (𝓝 x0) :=
      hz.comp hφ.tendsto_atTop
    have hzφ_base : Tendsto (fun n ↦ ((z (φ n)) : H)) atTop (𝓝 x) := by
      simpa [x0] using (continuous_subtype_val.tendsto x0).comp hzφ
    have hboundedSubseq :
        Bornology.IsBounded (Set.range fun n ↦ (G (z (φ n)) : H)) := by
      refine hbounded.subset ?_
      rintro v ⟨n, rfl⟩
      exact ⟨φ n, rfl⟩
    have hwmem : w ∈ (∂ f) x := by
      refine
        mem_subdifferential_of_tendsto_of_tendsto_toWeakSpace
          hf hzφ_base hφw hboundedSubseq ?_
      intro n
      exact selection_apply_mem G (z (φ n))
    have hw_single : w ∈ ({u} : Set H) := by
      rw [← hsubx]
      exact hwmem
    simpa using hw_single
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint
        (fun n ↦ (G (z n) : H))).2
        ⟨hbounded, fun y w hy hw ↦ by
          calc
            y = u := hcluster_eq y hy
            _ = w := (hcluster_eq w hw).symm⟩ with
    ⟨w, hw⟩
  have hw_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (G (z n) : H))
        (toWeakSpace ℝ H w) := by
    exact ⟨id, strictMono_id, by simpa using hw⟩
  have hw_eq : w = u := hcluster_eq w hw_cluster
  simpa [hw_eq] using hw

/-- Helper for Proposition 18 9: a weakly continuous subgradient selection at an interior
effective-domain point yields the Gâteaux derivative determined by its selected value at that
point. -/
lemma hasGateauxDerivativeAt_of_selection_weakContinuousAt_on_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f))
    (G : Selection (∂ f))
    (hG :
      SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x) :
    HasGateauxDerivativeAt (fun y ↦ (f y : EReal).toReal)
      (InnerProductSpace.toDualMap ℝ H
        (G ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩ : H)) x := by
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  refine
    (hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
      (C := Set.univ) (T := fun y ↦ (f y : EReal).toReal)
      (A := InnerProductSpace.toDualMap ℝ H (G x0 : H)) (x := x)).2 ?_
  refine ⟨hasRadialSegmentsAt_univ x, ?_⟩
  intro y
  rcases small_segment_subset_subdifferentialDom hf hx y with ⟨α0, hα0pos, hα0mem⟩
  let γ : ℝ → (∂ f).dom := fun α ↦
    if hα : α ∈ Set.Icc (0 : ℝ) α0 then
      ⟨x + α • y, hα0mem α hα⟩
    else
      x0
  have hγ_vals :
      (fun α ↦ (γ α : H)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun α : ℝ ↦ x + α • y := by
    have hIcc :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Icc (0 : ℝ) α0 := by
      have hlt :
          ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < α0 := by
        exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hα0pos)
      filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
      exact ⟨le_of_lt hαpos, hαlt.le⟩
    filter_upwards [hIcc] with α hα
    have hα' : 0 ≤ α ∧ α ≤ α0 := by
      simpa [Set.mem_Icc] using hα
    simp [γ, hα']
  have hγ_tendsto : Tendsto γ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 x0) := by
    apply tendsto_subtype_rng.2
    have hline_cont : Continuous fun α : ℝ ↦ x + α • y := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hline0 : Tendsto (fun α : ℝ ↦ x + α • y) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa using (hline_cont.continuousAt : ContinuousAt (fun α : ℝ ↦ x + α • y) 0).tendsto
    have hline :
        Tendsto (fun α : ℝ ↦ x + α • y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 x) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds hline0
    exact Filter.Tendsto.congr' hγ_vals.symm hline
  have hupper_tendsto :
      Tendsto (fun α : ℝ ↦ inner ℝ (G (γ α) : H) y)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (inner ℝ (G x0 : H) y)) := by
    -- Weak continuity is only used through the scalar coordinate `u ↦ ⟪u, y⟫`.
    exact
      ((weakSpace_continuous_inner_right (H := H) y).tendsto (toWeakSpace ℝ H (G x0 : H))).comp
        ((hG x0.2).tendsto.comp hγ_tendsto)
  have hlower :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        inner ℝ y (G x0 : H) ≤
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) := by
    have hIcc :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Icc (0 : ℝ) α0 := by
      have hlt :
          ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < α0 := by
        exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hα0pos)
      filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
      exact ⟨le_of_lt hαpos, hαlt.le⟩
    filter_upwards [self_mem_nhdsWithin, hIcc] with α hαpos hα
    have hxeff : x ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf x0.2
    have hαeff : x + α • y ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf (hα0mem α hα)
    have hsub :
        inner ℝ ((x + α • y) - x) (G x0 : H) ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      exact
        (ereal_affine_ineq_iff_inner_le_toReal_sub hxeff hαeff).1
          ((mem_subdifferential_iff (f := f) (x := x) (u := (G x0 : H))).1
            (selection_apply_mem G x0) (x + α • y))
    have hscaled :
        α * inner ℝ y (G x0 : H) ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      simpa [sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
        inner_add_left, inner_smul_left, inner_sub_left] using hsub
    exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hscaled)
  have hupper :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) ≤
          inner ℝ (G (γ α) : H) y := by
    have hIcc :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Icc (0 : ℝ) α0 := by
      have hlt :
          ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < α0 := by
        exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hα0pos)
      filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
      exact ⟨le_of_lt hαpos, hαlt.le⟩
    filter_upwards [self_mem_nhdsWithin, hIcc] with α hαpos hα
    have hxeff : x ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf x0.2
    have hγα : γ α = ⟨x + α • y, hα0mem α hα⟩ := by
      have hα' : 0 ≤ α ∧ α ≤ α0 := by
        simpa [Set.mem_Icc] using hα
      apply Subtype.ext
      simp [γ, hα']
    have hαeff : x + α • y ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf (hα0mem α hα)
    have hsub :
        inner ℝ (x - (x + α • y)) (G (γ α) : H) ≤
          (f x : EReal).toReal - (f (x + α • y) : EReal).toReal := by
      exact
        (ereal_affine_ineq_iff_inner_le_toReal_sub hαeff hxeff).1
          ((mem_subdifferential_iff (f := f) (x := x + α • y) (u := (G (γ α) : H))).1
            (by simpa [hγα] using selection_apply_mem G (γ α)) x)
    have hscaled :
        (f (x + α • y) : EReal).toReal - (f x : EReal).toReal ≤
          α * inner ℝ (G (γ α) : H) y := by
      have hsub' :
          -(α * inner ℝ (G (γ α) : H) y) ≤
            (f x : EReal).toReal - (f (x + α • y) : EReal).toReal := by
        simpa [real_inner_comm, sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
          inner_add_left, inner_smul_left, inner_sub_left] using hsub
      linarith
    exact (div_le_iff₀ hαpos).2 (by simpa [mul_comm] using hscaled)
  have hlower' :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ((InnerProductSpace.toDualMap ℝ H (G x0 : H)) y) ≤
          (1 / α) • ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) := by
    simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm, div_eq_mul_inv, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hlower
  have hupper' :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (1 / α) • ((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) ≤
          inner ℝ (G (γ α) : H) y := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper_tendsto hlower' hupper'

omit [CompleteSpace H] in
/-- Helper for Proposition 18 9: a whole-space Gâteaux derivative restricts to the interior of the
effective domain because that set is open around the base point. -/
lemma hasGateauxDerivativeWithinAt_of_hasGateauxDerivativeAt_on_interior
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {A : H →L[ℝ] ℝ}
    (hx : x ∈ interior (effectiveDomain f))
    (hA : HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) A x) :
    HasGateauxDerivativeWithinAt
      (fun z ↦ (f z : EReal).toReal) A (interior (effectiveDomain f)) x := by
  -- Only the radial-segment witness changes when passing from the whole space to an open subset.
  have hnhds : interior (effectiveDomain f) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  refine ⟨HasRadialSegmentsAt.of_mem_nhds hnhds, ?_⟩
  exact hA.2

/-- Helper for Proposition 18 9: for a function in `Γ₀(H)`, continuity on the effective domain
and a singleton subdifferential at `x` should force the finite-valued representative to have the
corresponding Gâteaux derivative at `x`. -/
lemma
    hasGateauxDerivativeAt_of_singleton_subdifferential_on_interior
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f)) (hsub : (∂ f) x = ({u} : Set H)) :
    HasGateauxDerivativeAt
      (fun z ↦ (f z : EReal).toReal) (InnerProductSpace.toDualMap ℝ H u) x := by
  classical
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  let hnonempty : ∀ z : (∂ f).dom, Nonempty ((∂ f) z) := fun z ↦ by
    rcases (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := (z : H))).1 z.2 with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  let G : Selection (∂ f) := fun z ↦ Classical.choice (hnonempty z)
  have hxu : (G x0 : H) = u := by
    have hmem : (G x0 : H) ∈ (∂ f) x := selection_apply_mem G x0
    have hsingle : (G x0 : H) ∈ ({u} : Set H) := by
      simpa [hsub] using hmem
    simpa using hsingle
  have hG :
      SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x := by
    intro hxdom
    have hxeq : (⟨x, hxdom⟩ : (∂ f).dom) = x0 := by
      apply Subtype.ext
      rfl
    have hcont0 :
        ContinuousAt (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x0 := by
      apply Filter.tendsto_of_seq_tendsto
      intro z hz
      simpa [x0, hxu] using
        selection_values_tendsto_weak_of_singleton_subdifferential hf hx hsub G z hz
    simpa [x0, hxeq] using hcont0
  have hderiv :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H (G x0 : H)) x :=
    hasGateauxDerivativeAt_of_selection_weakContinuousAt_on_interior_effectiveDomain hf hx G hG
  simpa [hxu] using hderiv

-- Proof sketch: fix `x ∈ interior (effectiveDomain f)`. Proposition 17.39 gives continuity of
-- `f` on the effective domain at `x` and nonemptiness of `(∂ f) x`. The strict-convexity
-- hypothesis on every nonempty convex subset of `dom (∂ f*)` forces `(∂ f) x` to be a singleton
-- by the segment argument above. Proposition 17.31 then yields a whole-space Gâteaux derivative,
-- and openness of `interior (effectiveDomain f)` converts it to the required within-set form.
/-- Proposition 18 9: if `f ∈ Γ₀(H)` and the Fenchel conjugate `f*`,
represented by `f∗[hf]`, is strictly convex on every nonempty convex subset of `dom (∂ f*)`,
then the finite-valued representative of `f` is Gâteaux differentiable on
`interior (effectiveDomain f)`. -/
theorem gateauxDifferentiableOn_interior_effectiveDomain_of_strictlyConvexOn_every_nonempty_convex_subset_subdifferentialDom_gammaZeroConjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hstrict :
      ∀ ⦃C : Set H⦄, C.Nonempty → Convex ℝ C →
        C ⊆ SetValuedOperator.dom (∂ (f∗[hf])) →
        StrictlyConvexOn (f∗[hf]) C) :
    GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := by
  intro x hx
  rcases subdifferential_eq_singleton_of_mem_interior_effectiveDomain hf hstrict hx with
    ⟨u, hsub⟩
  have hgateaux :
      HasGateauxDerivativeAt
        (fun z ↦ (f z : EReal).toReal) (InnerProductSpace.toDualMap ℝ H u) x := by
    -- The proved segment argument closes the singleton step; only the `Γ₀` derivative bridge
    -- remains to finish the source route.
    exact
      hasGateauxDerivativeAt_of_singleton_subdifferential_on_interior
          hf hx hsub
  refine ⟨InnerProductSpace.toDualMap ℝ H u, ?_⟩
  -- The target is a within-set differentiability statement on the open interior effective domain.
  exact hasGateauxDerivativeWithinAt_of_hasGateauxDerivativeAt_on_interior hx hgateaux

end DifferentiabilityAndStrictConvexity

end ERealFunction
