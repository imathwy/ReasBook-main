import Mathlib
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap01.Text_1_0_14
import BauschkeLean.Chap02.Fact_2_35
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Proposition_17_31
import BauschkeLean.Chap17.Proposition_17_39.Index

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open InnerProductSpace
open scoped InnerProductSpace Topology

universe u

namespace SetValuedOperator

section SelectionContinuity

variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*}
variable {Z : Type*} [TopologicalSpace Z]

/-- A map on the domain of a set-valued operator is continuous at `x` when it is continuous at
each subtype point over `x`. Actual selections are the main source of such maps, but the codomain
may also be changed by a canonical view such as `toWeakSpace`. -/
def SelectionContinuousAt (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) : Prop :=
  ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩

/-- Unfolding `SelectionContinuousAt` gives continuity of the map on the operator domain at each
subtype point over `x`. -/
theorem selectionContinuousAt_iff
    (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) :
    SelectionContinuousAt A T x ↔
      ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩ :=
  Iff.rfl

end SelectionContinuity

end SetValuedOperator

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

open SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 17 39: at finite values, the affine `EReal` subgradient inequality is
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

/-- Helper for Proposition 17 39: every subgradient at an interior effective-domain point is
dominated by the Gâteaux gradient on each direction. -/
lemma subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u gradf y : H}
    (hx : x ∈ interior (effectiveDomain f)) (hu : u ∈ (∂ f) x)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    ⟪y, u⟫_ℝ ≤ ⟪y, gradf⟫_ℝ := by
  have hxeff : x ∈ effectiveDomain f := interior_subset hx
  rcases small_segment_subset_subdifferentialDom hf hx y with ⟨α0, hα0pos, hα0mem⟩
  have hquot_tendsto :
      Tendsto
        (fun α : ℝ ↦
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪y, gradf⟫_ℝ) := by
    -- The Gâteaux derivative identifies the limiting one-sided secant slope in direction `y`.
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, real_inner_comm]
      using hgrad.tendsto_directionalDifferenceQuotient y
  have hquot_ge :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ⟪y, u⟫_ℝ ≤
          (((f (x + α • y) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) := by
    have hIcc :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α ∈ Set.Icc (0 : ℝ) α0 := by
      have hlt :
          ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < α0 := by
        exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hα0pos)
      filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
      exact ⟨le_of_lt hαpos, hαlt.le⟩
    filter_upwards [self_mem_nhdsWithin, hIcc] with α hαpos hα
    have hαeff :
        x + α • y ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf (hα0mem α hα)
    have hsub :
        inner ℝ ((x + α • y) - x) u ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      exact
        (ereal_affine_ineq_iff_inner_le_toReal_sub hxeff hαeff).1
          ((mem_subdifferential_iff (f := f) (x := x) (u := u)).1 hu (x + α • y))
    have hscaled :
        α * inner ℝ y u ≤
          (f (x + α • y) : EReal).toReal - (f x : EReal).toReal := by
      -- Expand the segment step to isolate the scalar factor `α`.
      simpa [sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
        inner_add_left, inner_smul_left, inner_sub_left] using hsub
    exact (le_div_iff₀ hαpos).2 (by simpa [mul_comm] using hscaled)
  -- Passing the subgradient inequality to the limit compares `u` with the Gâteaux gradient.
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hquot_tendsto hquot_ge

/-- Helper for Proposition 17 39: at an interior effective-domain point, Gâteaux
differentiability forces the subdifferential to be a singleton. -/
lemma subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x gradf : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeAt
        (fun z ↦ (f z : EReal).toReal) (InnerProductSpace.toDualMap ℝ H gradf) x) :
    (∂ f) x = ({gradf} : Set H) := by
  have hgrad_mem :
      gradf ∈ (∂ f) x := by
    exact
      gateauxGradient_mem_subdifferential f hf.2 (interior_subset hx) gradf hgrad
  apply Set.Subset.antisymm
  · intro u hu
    have hu_eq : u = gradf := by
      apply ext_inner_left ℝ
      intro y
      have hy_le :
          ⟪y, u⟫_ℝ ≤ ⟪y, gradf⟫_ℝ := by
        exact
          subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
            hf hx hu hgrad
      have hneg_le :
          ⟪-y, u⟫_ℝ ≤ ⟪-y, gradf⟫_ℝ := by
        exact
          subgradient_inner_le_gateauxGradient_of_mem_interior_effectiveDomain
            hf hx hu hgrad
      have hy_ge :
          ⟪y, gradf⟫_ℝ ≤ ⟪y, u⟫_ℝ := by
        simpa using hneg_le
      exact le_antisymm hy_le hy_ge
    simp [hu_eq]
  · intro u hu
    rw [Set.mem_singleton_iff] at hu
    simpa [hu] using hgrad_mem

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 17 39: outside the effective domain, an extended-real-valued function
takes the value `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∉ effectiveDomain f) :
    (f y : EReal) = ⊤ := by
  exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))

/-- Helper for Proposition 17 39: strong convergence of base points and weak convergence of
subgradients preserve subdifferential membership once the subgradients stay bounded. -/
lemma mem_subdifferential_of_tendsto_of_tendsto_toWeakSpace
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xSeq uSeq : ℕ → H} {x u : H}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hub : Bornology.IsBounded (Set.range uSeq))
    (hsub : ∀ n, uSeq n ∈ (∂ f) (xSeq n)) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro y
  have hycoord0 :
      Tendsto (fun n ↦ inner ℝ (uSeq n) (y - x)) atTop (𝓝 (inner ℝ u (y - x))) := by
    simpa using ((weakSpace_continuous_inner_right (H := H) (y - x)).tendsto
      (toWeakSpace ℝ H u)).comp hu
  have hycoord :
      Tendsto (fun n ↦ inner ℝ (y - x) (uSeq n)) atTop (𝓝 (inner ℝ (y - x) u)) := by
    simpa [real_inner_comm] using hycoord0
  obtain ⟨R, hR⟩ := hub.subset_closedBall (0 : H)
  have hu_bound : ∀ n, ‖uSeq n‖ ≤ R := by
    intro n
    have hun : uSeq n ∈ Metric.closedBall (0 : H) R := hR (Set.mem_range_self n)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hun
  have hx_zero : Tendsto (fun n ↦ x - xSeq n) atTop (𝓝 (0 : H)) := by
    have hx_zero' : Tendsto (fun n ↦ x - xSeq n) atTop (𝓝 (x - x)) :=
      tendsto_const_nhds.sub hx
    simpa using hx_zero'
  have hbound_zero : Tendsto (fun n ↦ ‖x - xSeq n‖ * R) atTop (𝓝 0) := by
    have hnorm_zero : Tendsto (fun n ↦ ‖x - xSeq n‖) atTop (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : H)).comp hx_zero
    simpa [zero_mul] using hnorm_zero.mul_const R
  have hcross :
      Tendsto (fun n ↦ inner ℝ (x - xSeq n) (uSeq n)) atTop (𝓝 0) := by
    have hneg_zero : Tendsto (fun n ↦ -(‖x - xSeq n‖ * R)) atTop (𝓝 0) := by
      simpa using hbound_zero.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hneg_zero hbound_zero ?_ ?_
    · intro n
      have habs : |⟪x - xSeq n, uSeq n⟫_ℝ| ≤ ‖x - xSeq n‖ * R := by
        calc
          |⟪x - xSeq n, uSeq n⟫_ℝ| ≤ ‖x - xSeq n‖ * ‖uSeq n‖ :=
            abs_real_inner_le_norm _ _
          _ ≤ ‖x - xSeq n‖ * R := by
              gcongr
              exact hu_bound n
      calc
        -(‖x - xSeq n‖ * R) ≤ -|⟪x - xSeq n, uSeq n⟫_ℝ| := by linarith
        _ ≤ ⟪x - xSeq n, uSeq n⟫_ℝ := by
            exact neg_abs_le _
    · intro n
      calc
        ⟪x - xSeq n, uSeq n⟫_ℝ ≤ |⟪x - xSeq n, uSeq n⟫_ℝ| := le_abs_self _
        _ ≤ ‖x - xSeq n‖ * R := by
            calc
              |⟪x - xSeq n, uSeq n⟫_ℝ| ≤ ‖x - xSeq n‖ * ‖uSeq n‖ :=
                abs_real_inner_le_norm _ _
              _ ≤ ‖x - xSeq n‖ * R := by
                  gcongr
                  exact hu_bound n
  have hinner :
      Tendsto (fun n ↦ inner ℝ (y - xSeq n) (uSeq n)) atTop (𝓝 (inner ℝ (y - x) u)) := by
    have hsplit :
        (fun n ↦ inner ℝ (y - xSeq n) (uSeq n)) =
          fun n ↦ inner ℝ (y - x) (uSeq n) + inner ℝ (x - xSeq n) (uSeq n) := by
      funext n
      have hdecomp : y - xSeq n = (y - x) + (x - xSeq n) := by
        abel
      rw [hdecomp, inner_add_left]
    rw [hsplit]
    simpa using hycoord.add hcross
  have hinner_ereal :
      Tendsto
        (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
        atTop
        (𝓝 (((inner ℝ (y - x) u : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.tendsto _ |>.comp hinner
  have hvalue :
      (f x : EReal) ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop := by
    calc
      (f x : EReal) ≤ Filter.liminf (fun z ↦ (f z : EReal)) (𝓝 x) :=
            LowerSemicontinuousAt.le_liminf (hf.1.lowerSemicontinuousAt x)
      _ ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop :=
            Filter.liminf_le_liminf_of_le hx
  have hsum :
      Filter.liminf
          (fun n ↦
            (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal)))
          atTop ≤
        (f y : EReal) := by
    have hsup :
        Filter.limsup
            (fun n ↦
              (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal)))
            atTop ≤
          (f y : EReal) :=
      Filter.limsup_le_of_le
        (by isBoundedDefault)
        (Eventually.of_forall fun n ↦
          (mem_subdifferential_iff (f := f) (x := xSeq n) (u := uSeq n)).1 (hsub n) y)
    exact
      le_trans
        (Filter.liminf_le_limsup
          (u := fun n ↦
            (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal))))
        hsup
  calc
    ((inner ℝ (y - x) u : ℝ) : EReal) + (f x : EReal)
        = Filter.liminf
            (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
            atTop +
          (f x : EReal) := by
            rw [hinner_ereal.liminf_eq]
    _ ≤ Filter.liminf
          (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
          atTop +
        Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop := by
          gcongr
    _ ≤ Filter.liminf
          (fun n ↦
            (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) + (f (xSeq n) : EReal)))
          atTop := by
            simpa using
              (EReal.le_liminf_add :
                Filter.liminf
                    (fun n ↦ ((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal))
                    atTop +
                  Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop ≤
                Filter.liminf
                    (fun n ↦
                      (((inner ℝ (y - xSeq n) (uSeq n) : ℝ) : EReal) +
                        (f (xSeq n) : EReal)))
                    atTop)
    _ ≤ (f y : EReal) := hsum

/-- Helper for Proposition 17 39: if the subdifferential at `x` is the singleton `{u}`, then any
selection evaluated along a domain sequence converging to `x` converges weakly to `u`. -/
lemma selection_values_tendsto_weak_of_subdifferential_eq_singleton
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hsubx : (∂ f) x = ({u} : Set H))
    (G : Selection (∂ f)) (z : ℕ → (∂ f).dom)
    (hz :
      Tendsto z atTop
        (𝓝 ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩)) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (G (z n) : H)) atTop (𝓝 (toWeakSpace ℝ H u)) := by
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  have hxcont :
      ContinuousAtOnEffectiveDomain f x :=
    continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain hf hx
  have hz_base : Tendsto (fun n ↦ (z n : H)) atTop (𝓝 x) := by
    simpa [x0] using (continuous_subtype_val.tendsto x0).comp hz
  obtain ⟨ρ, hρpos, hρbounded⟩ :=
    subdifferential_ball_union_bounded_of_continuousAtOnEffectiveDomain f hf.2 hxcont
  have htail :
      ∀ᶠ n in atTop, (z n : H) ∈ Metric.ball x ρ := by
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
    have hzφ :
        Tendsto (fun n ↦ z (φ n)) atTop (𝓝 x0) :=
      hz.comp hφ.tendsto_atTop
    have hzφ_base :
        Tendsto (fun n ↦ ((z (φ n)) : H)) atTop (𝓝 x) := by
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

/-- Helper for Proposition 17 39: a weakly continuous selection at an interior effective-domain
point yields the Gâteaux derivative given by the selected subgradient at that point. -/
lemma hasGateauxDerivativeAt_of_selection_strongToWeakContinuousAt
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
      (fun α ↦ (γ α : H)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] fun α : ℝ ↦ x + α • y := by
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
  have hγ_tendsto :
      Tendsto γ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 x0) := by
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
    -- Weak continuity of the selection is only used through the continuous scalar coordinate
    -- `u ↦ ⟪u, y⟫`.
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
    have hxeff :
        x ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf x0.2
    have hαeff :
        x + α • y ∈ effectiveDomain f :=
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
    have hxeff :
        x ∈ effectiveDomain f :=
      subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf x0.2
    have hγα :
        γ α = ⟨x + α • y, hα0mem α hα⟩ := by
      have hα' : 0 ≤ α ∧ α ≤ α0 := by
        simpa [Set.mem_Icc] using hα
      apply Subtype.ext
      simp [γ, hα']
    have hαeff :
        x + α • y ∈ effectiveDomain f :=
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
  -- The quotient is squeezed between the fixed subgradient at `x` and the nearby selected
  -- subgradients, whose scalar coordinates converge back to the same limit.
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

-- Proof sketch: Proposition 17.31 identifies Gâteaux differentiability at `x` with singleton
-- subdifferential at `x`. Proposition 16.17 gives local boundedness and nonemptiness of nearby
-- subdifferentials on the interior effective domain, and Proposition 16.36 gives strong-weak
-- sequential closedness of `gra ∂ f`. These ingredients show that Gâteaux differentiability forces
-- every selection to converge weakly to the unique subgradient, while any weakly continuous
-- selection yields the directional-derivative inequalities needed to recover Gâteaux
-- differentiability.
/-- Proposition 17 39: for `f ∈ Γ₀(H)` and `x ∈ interior (effectiveDomain f)`, the following are
equivalent: (i) `x ↦ (f x : EReal).toReal` is Gâteaux differentiable at `x`; (ii) every selection
of `∂ f` is strong-to-weak continuous at `x`; (iii) there exists a selection of `∂ f` with the
same continuity property at `x`. -/
theorem gateauxDifferentiableAt_tfae_subdifferentialSelections_strongToWeakContinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    List.TFAE
      [GateauxDifferentiableAt (fun y ↦ (f y : EReal).toReal) x,
        ∀ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x,
        ∃ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x] := by
  let P1 :=
    GateauxDifferentiableAt (fun y ↦ (f y : EReal).toReal) x
  let P2 :=
    ∀ G : Selection (∂ f),
      SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x
  let P3 :=
    ∃ G : Selection (∂ f),
      SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x
  have h12 : P1 → P2 := by
    intro hgateaux G
    let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
    rcases hgateaux with ⟨A, hA⟩
    let u : H := (InnerProductSpace.toDual ℝ H).symm A
    have hAu0 :
        HasGateauxDerivativeAt
          (fun y ↦ (f y : EReal).toReal) (InnerProductSpace.toDual ℝ H u) x := by
      simpa [u] using hA
    have hAu :
        HasGateauxDerivativeAt
          (fun y ↦ (f y : EReal).toReal) (InnerProductSpace.toDualMap ℝ H u) x := by
      -- Convert the abstract linear functional to its Riesz representative before applying
      -- Proposition 17.31.
      simpa using hAu0
    have hsubx : (∂ f) x = ({u} : Set H) :=
      subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
        hf hx hAu
    have hGx : (G x0 : H) = u := by
      have hmem : (G x0 : H) ∈ (∂ f) x := selection_apply_mem G x0
      have hsingle : (G x0 : H) ∈ ({u} : Set H) := by
        simpa [hsubx] using hmem
      exact Set.mem_singleton_iff.mp hsingle
    have hcont0 :
        ContinuousAt (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x0 := by
      -- The domain subtype is first countable, so sequence convergence suffices here.
      apply Filter.tendsto_of_seq_tendsto
      intro z hz
      simpa [Function.comp, x0, hGx] using
        selection_values_tendsto_weak_of_subdifferential_eq_singleton hf hx hsubx G z hz
    intro hxdom
    have hxeq : (⟨x, hxdom⟩ : (∂ f).dom) = x0 := by
      apply Subtype.ext
      rfl
    simpa [x0, hxeq] using hcont0
  have h23 : P2 → P3 := by
    intro hall
    classical
    let hnonempty : ∀ z : (∂ f).dom, Nonempty ((∂ f) z) := fun z ↦ by
      rcases (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := (z : H))).1 z.2 with ⟨v, hv⟩
      exact ⟨⟨v, hv⟩⟩
    let G : Selection (∂ f) := fun z ↦ Classical.choice (hnonempty z)
    exact ⟨G, hall G⟩
  have h31 : P3 → P1 := by
    rintro ⟨G, hG⟩
    -- Route correction: recover the derivative directly from the directional quotient squeeze
    -- rather than trying to reconstruct singleton subdifferential fibers from one selection.
    refine ⟨InnerProductSpace.toDualMap ℝ H
      (G ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩), ?_⟩
    exact hasGateauxDerivativeAt_of_selection_strongToWeakContinuousAt hf hx G hG
  have hP12 : P1 ↔ P2 := by
    constructor
    · exact h12
    · intro h2
      exact h31 (h23 h2)
  have hP23 : P2 ↔ P3 := by
    constructor
    · exact h23
    · intro h3
      exact h12 (h31 h3)
  rw [List.tfae_cons_cons, List.tfae_cons_cons]
  refine ⟨hP12, ?_⟩
  refine ⟨hP23, ?_⟩
  exact List.tfae_singleton P3

end DifferentiabilityOfConvexFunctions

end ERealFunction
