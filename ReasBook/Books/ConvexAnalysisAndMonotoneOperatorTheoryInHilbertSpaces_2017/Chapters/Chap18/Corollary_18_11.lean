import BauschkeLean.Chap16.Proposition_16_37
import BauschkeLean.Chap02.Fact_2_35
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap16.Proposition_16_17
import BauschkeLean.Chap17.Proposition_17_39.SelectionContinuity
import BauschkeLean.Chap18.Proposition_18_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open SetValuedOperator
open scoped Gradient InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)}

/-- Helper for Corollary 18.11: a segment of subgradients at `x` lies in the subdifferential
domain of the Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
lemma segment_subset_subdifferentialDom_gammaZeroConjugate_of_segment_subset_subdifferential
    (hf : f ∈ Γ₀(H)) {x u0 u1 : H}
    (hseg : segment ℝ u0 u1 ⊆ (∂ f) x) :
    segment ℝ u0 u1 ⊆ SetValuedOperator.dom (∂ (f∗[hf])) := by
  intro u hu
  -- Corollary 16.30 transports subgradients of `f` to subgradients of `f*`.
  rw [SetValuedOperator.mem_dom_iff]
  refine ⟨x, ?_⟩
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf]
  simpa [SetValuedOperator.mem_inverse_iff] using hseg hu

/-- Helper for Corollary 18.11: strict convexity of `f*` on the segment between two subgradients
at the same point forces those subgradients to agree. -/
lemma eq_of_mem_subdifferential_of_strictlyConvexOn_segment_gammaZeroConjugate
    (hf : f ∈ Γ₀(H)) {x u0 u1 : H}
    (hu0 : u0 ∈ (∂ f) x) (hu1 : u1 ∈ (∂ f) x)
    (hstrictSeg : StrictlyConvexOn (f∗[hf]) (segment ℝ u0 u1)) :
    u0 = u1 := by
  by_contra hne
  -- The source route first shows that `f*` is affine on the whole subgradient segment.
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

/-- Helper for Corollary 18.11: the strict-convexity hypothesis on `dom (∂ f*)` makes every
interior subdifferential fiber of `f` a singleton. -/
lemma subdifferential_eq_singleton_of_mem_interior_effectiveDomain
    (hf : f ∈ Γ₀(H))
    (hstrict :
      ∀ ⦃C : Set H⦄, C.Nonempty → Convex ℝ C →
        C ⊆ SetValuedOperator.dom (∂ (f∗[hf])) →
        StrictlyConvexOn (f∗[hf]) C)
    {x : H} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ u : H, (∂ f) x = ({u} : Set H) := by
  -- Interior-domain points lie in `dom (∂ f)`, so a subgradient exists.
  rcases (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := x)).1
      (mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx) with ⟨u, hu⟩
  refine ⟨u, Set.Subset.antisymm ?_ ?_⟩
  · intro v hv
    have hseg_sub : segment ℝ u v ⊆ (∂ f) x :=
      (convex_subdifferential f x).segment_subset hu hv
    have hseg_dom :
        segment ℝ u v ⊆ SetValuedOperator.dom (∂ (f∗[hf])) :=
      segment_subset_subdifferentialDom_gammaZeroConjugate_of_segment_subset_subdifferential
        (f := f) hf hseg_sub
    have hstrictSeg : StrictlyConvexOn (f∗[hf]) (segment ℝ u v) :=
      hstrict ⟨u, left_mem_segment ℝ u v⟩ (convex_segment u v) hseg_dom
    exact Set.mem_singleton_iff.mpr
      (eq_of_mem_subdifferential_of_strictlyConvexOn_segment_gammaZeroConjugate
        (f := f) hf hu hv hstrictSeg).symm
  · intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact hu

omit [CompleteSpace H] in
/-- Helper for Corollary 18.11: a whole-space Gâteaux derivative restricts to
`interior (effectiveDomain f)` because that set is open around the base point. -/
lemma hasGateauxDerivativeWithinAt_of_hasGateauxDerivativeAt_on_interior
    {x : H} {A : H →L[ℝ] ℝ}
    (hx : x ∈ interior (effectiveDomain f))
    (hA : HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) A x) :
    HasGateauxDerivativeWithinAt
      (fun z ↦ (f z : EReal).toReal) A (interior (effectiveDomain f)) x := by
  have hnhds : interior (effectiveDomain f) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  refine ⟨HasRadialSegmentsAt.of_mem_nhds hnhds, ?_⟩
  exact hA.2

/-- Helper for Corollary 18.11: strong convergence of base points and weak convergence of
subgradients preserve subdifferential membership once the subgradients stay bounded. -/
lemma mem_subdifferential_of_tendsto_of_tendsto_toWeakSpace
    (hf : f ∈ Γ₀(H)) {xSeq uSeq : ℕ → H} {x u : H}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hub : Bornology.IsBounded (Set.range uSeq))
    (hsub : ∀ n, uSeq n ∈ (∂ f) (xSeq n)) :
    u ∈ (∂ f) x := by
  rw [mem_subdifferential_iff]
  intro y
  have hycoord0 :
      Tendsto (fun n ↦ inner ℝ (uSeq n) (y - x)) atTop (𝓝 (inner ℝ u (y - x))) := by
    simpa using
      ((weakSpace_continuous_inner_right (H := H) (y - x)).tendsto
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
        -(‖x - xSeq n‖ * R) ≤ -|⟪x - xSeq n, uSeq n⟫_ℝ| := by
          linarith
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

/-- Helper for Corollary 18.11: if the subdifferential at `x` is the singleton `{u}`, then any
selection evaluated along a domain sequence converging to `x` converges weakly to `u`. -/
lemma selection_values_tendsto_weak_of_subdifferential_eq_singleton
    (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hsubx : (∂ f) x = ({u} : Set H))
    (G : Selection (∂ f)) (z : ℕ → (∂ f).dom)
    (hz :
      Tendsto z atTop
        (𝓝 ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩)) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (G (z n) : H)) atTop (𝓝 (toWeakSpace ℝ H u)) := by
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  obtain ⟨ρ, hρpos, hρbounded⟩ :=
    subdifferential_ball_union_bounded_of_continuousPoint
      (f := f) hf.2
      (continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx)
  have hz_base : Tendsto (fun n ↦ (z n : H)) atTop (𝓝 x) := by
    simpa [x0] using (continuous_subtype_val.tendsto x0).comp hz
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

/-- Helper for Corollary 18.11: a weakly continuous selection at an interior effective-domain
point yields the Gâteaux derivative given by the selected subgradient at that point. -/
lemma hasGateauxDerivativeAt_of_selection_strongToWeakContinuousAt
    (hf : f ∈ Γ₀(H)) {x : H}
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
    -- Weak continuity of the selection is only used through the continuous scalar coordinate.
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

/-- Helper for Corollary 18.11: a singleton subdifferential at an interior effective-domain point
determines the corresponding Gâteaux derivative there. -/
lemma hasGateauxDerivativeAt_of_singleton_subdifferential_on_interior
    (hf : f ∈ Γ₀(H)) {x u : H}
    (hx : x ∈ interior (effectiveDomain f))
    (hsubx : (∂ f) x = ({u} : Set H)) :
    HasGateauxDerivativeAt
      (fun y ↦ (f y : EReal).toReal) (InnerProductSpace.toDualMap ℝ H u) x := by
  classical
  let hnonempty : ∀ z : (∂ f).dom, Nonempty ((∂ f) z) := fun z ↦ by
    rcases (SetValuedOperator.mem_dom_iff (A := ∂ f) (x := (z : H))).1 z.2 with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  let G : Selection (∂ f) := fun z ↦ Classical.choice (hnonempty z)
  let x0 : (∂ f).dom := ⟨x, mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf hx⟩
  have hGx : (G x0 : H) = u := by
    have hmem : (G x0 : H) ∈ (∂ f) x := selection_apply_mem G x0
    have hsingle : (G x0 : H) ∈ ({u} : Set H) := by
      simpa [hsubx] using hmem
    exact Set.mem_singleton_iff.mp hsingle
  have hcont0 :
      ContinuousAt (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x0 := by
    -- Sequence convergence on the subtype domain suffices for continuity at `x0`.
    apply Filter.tendsto_of_seq_tendsto
    intro z hz
    simpa [Function.comp, x0, hGx] using
      selection_values_tendsto_weak_of_subdifferential_eq_singleton hf hx hsubx G z hz
  have hG :
      SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x := by
    intro hxdom
    have hxeq : (⟨x, hxdom⟩ : (∂ f).dom) = x0 := by
      apply Subtype.ext
      rfl
    simpa [x0, hxeq] using hcont0
  have hderiv :
      HasGateauxDerivativeAt (fun y ↦ (f y : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H (G x0 : H)) x := by
    exact hasGateauxDerivativeAt_of_selection_strongToWeakContinuousAt hf hx G hG
  simpa [x0, hGx] using hderiv

/-- Helper for Corollary 18.11: the subdifferential domain of the Fenchel conjugate `f*`,
represented by `f∗[hf]`, is the range of the subdifferential of `f`. -/
lemma subdifferential_dom_gamma_zero_conjugate_eq_range_subdifferential
    (hf : f ∈ Γ₀(H)) :
    SetValuedOperator.dom (∂ (f∗[hf])) = SetValuedOperator.range (∂ f) := by
  -- Transport the conjugate subdifferential back to the inverse subdifferential of `f`.
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf]
  -- The domain of an inverse set-valued operator is the range of the original operator.
  ext u
  constructor
  · intro hu
    rcases (SetValuedOperator.mem_dom_iff ((∂ f).inverse) u).1 hu with ⟨x, hx⟩
    exact (SetValuedOperator.mem_range_iff (∂ f) u).2 ⟨x, by
      simpa [SetValuedOperator.mem_inverse_iff] using hx⟩
  · intro hu
    rcases (SetValuedOperator.mem_range_iff (∂ f) u).1 hu with ⟨x, hx⟩
    exact (SetValuedOperator.mem_dom_iff ((∂ f).inverse) u).2 ⟨x, by
      simpa [SetValuedOperator.mem_inverse_iff] using hx⟩

/-- Helper for Corollary 18.11: pointwise Gâteaux differentiability on
`interior (effectiveDomain f)` can be packaged into a single gradient field. -/
lemma exists_gateaux_gradient_field_on_interior_of_gateaux_differentiable_on
    (hdiff :
      GateauxDifferentiableOn
        (fun x ↦ (f x : EReal).toReal)
        (interior (effectiveDomain f))) :
    ∃ gradf : H → H,
      HasGateauxDerivativeOn
        (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ InnerProductSpace.toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)) := by
  classical
  let gradf : H → H := fun x ↦
    if hx : x ∈ interior (effectiveDomain f) then
      (InnerProductSpace.toDual ℝ H).symm (Classical.choose (hdiff x hx))
    else
      0
  refine ⟨gradf, ?_⟩
  intro x hx
  have hgrad_eq :
      InnerProductSpace.toDualMap ℝ H (gradf x) = Classical.choose (hdiff x hx) := by
    -- On the interior branch, the chosen vector represents the chosen derivative functional.
    change (InnerProductSpace.toDual ℝ H) (gradf x) = Classical.choose (hdiff x hx)
    simp [gradf, hx]
  -- Rewriting through the Riesz representation turns the pointwise derivative into the field form.
  simpa [hgrad_eq] using Classical.choose_spec (hdiff x hx)

/-- Helper for Corollary 18.11: the source identity `(18.31)` rewrites the conjugate
subdifferential domain as the image of any Gâteaux gradient field on
`interior (effectiveDomain f)`. -/
lemma subdifferential_dom_gamma_zero_conjugate_eq_gradient_image_of_hasGateauxDerivativeOn
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    {gradf : H → H}
    (hgrad :
      HasGateauxDerivativeOn
        (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ InnerProductSpace.toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f))) :
    SetValuedOperator.dom (∂ (f∗[hf])) = gradf '' interior (effectiveDomain f) := by
  -- Route correction: the source proof first identifies `dom (∂ f*)` with `ran (∂ f)`.
  rw [subdifferential_dom_gamma_zero_conjugate_eq_range_subdifferential (f := f) hf]
  -- Proposition 18.10 then turns that range into the gradient image under the domain hypothesis.
  simpa using
    (range_subdifferential_eq_gradientImage_of_hasGateauxDerivativeOn
      (f := f) (gradf := gradf) hf hdom hgrad)

/-- Helper for Corollary 18.11: under `dom (∂ f) = interior (effectiveDomain f)`, Gâteaux
differentiability on `interior (effectiveDomain f)` yields the source identity
`dom (∂ (f∗[hf])) = gradf '' interior (effectiveDomain f)`. -/
lemma exists_gateaux_gradient_field_with_subdifferential_dom_gamma_zero_conjugate_eq_image
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdiff :
      GateauxDifferentiableOn
        (fun x ↦ (f x : EReal).toReal)
        (interior (effectiveDomain f))) :
    ∃ gradf : H → H,
      HasGateauxDerivativeOn
        (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ InnerProductSpace.toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)) ∧
      SetValuedOperator.dom (∂ (f∗[hf])) = gradf '' interior (effectiveDomain f) := by
  rcases
      exists_gateaux_gradient_field_on_interior_of_gateaux_differentiable_on
        (f := f) hdiff with
    ⟨gradf, hgrad⟩
  refine ⟨gradf, hgrad, ?_⟩
  -- Equation `(18.31)` is now exactly the direct source-facing helper.
  exact
    subdifferential_dom_gamma_zero_conjugate_eq_gradient_image_of_hasGateauxDerivativeOn
      (f := f) hf hdom hgrad

/-- Corollary 18.11. Let `f ∈ Γ₀(H)` satisfy `dom (∂ f) = interior (effectiveDomain f)`.
Then the finite-valued representative of `f` is Gâteaux differentiable on
`interior (effectiveDomain f)` if and only if the Fenchel conjugate `f*`, represented by
`f∗[hf]`, is strictly convex on every nonempty convex subset of `dom (∂ f*)`. -/
theorem gateauxDifferentiableOn_interior_effectiveDomain_iff_strictlyConvexOn_conjugateSubdiffDom
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f)) :
    GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) ↔
      ∀ ⦃C : Set H⦄, C.Nonempty → Convex ℝ C →
        C ⊆ SetValuedOperator.dom (∂ (f∗[hf])) →
        StrictlyConvexOn (f∗[hf]) C := by
  constructor
  · intro hdiff C hC_nonempty hC_convex hC_subset
    rcases
        exists_gateaux_gradient_field_with_subdifferential_dom_gamma_zero_conjugate_eq_image
          (f := f) hf hdom hdiff with
      ⟨gradf, hgrad, himage⟩
    have hC_subset_image : C ⊆ gradf '' interior (effectiveDomain f) := by
      -- Equation `(18.31)` rewrites the conjugate subdifferential domain as the gradient image.
      simpa [himage] using hC_subset
    -- Proposition 18.10 now gives strict convexity on every nonempty convex subset of that image.
    exact
      gammaZeroConjugate_strictlyConvexOn_of_hasGateauxDerivativeOn
        (f := f) (hf := hf) (gradf := gradf) hgrad hC_nonempty hC_convex hC_subset_image
  · intro hstrict x hx
    rcases subdifferential_eq_singleton_of_mem_interior_effectiveDomain
        (f := f) hf hstrict hx with
      ⟨u, hsub⟩
    have hgateaux :
        HasGateauxDerivativeAt
          (fun z ↦ (f z : EReal).toReal) (InnerProductSpace.toDualMap ℝ H u) x := by
      -- The singleton fiber now determines the whole-space Gâteaux derivative at `x`.
      exact
        hasGateauxDerivativeAt_of_singleton_subdifferential_on_interior
          (f := f) hf hx hsub
    refine ⟨InnerProductSpace.toDualMap ℝ H u, ?_⟩
    -- Openness of `interior (effectiveDomain f)` turns that into the required within-set form.
    exact
      hasGateauxDerivativeWithinAt_of_hasGateauxDerivativeAt_on_interior
        (f := f) hx hgateaux

/-- Under the same hypotheses, if `f` is Gâteaux differentiable on
`interior (effectiveDomain f)`, then there exists a Gâteaux gradient field `gradf` on
`interior (effectiveDomain f)` whose image is exactly the owner domain
`dom (∂ (f∗[hf]))`. -/
theorem
    subdifferentialDom_gammaZeroConjugate_eq_gradientImage_of_gateauxDifferentiableOn
    (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdiff :
      GateauxDifferentiableOn
        (fun x ↦ (f x : EReal).toReal)
        (interior (effectiveDomain f))) :
    ∃ gradf : H → H,
      HasGateauxDerivativeOn
        (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ InnerProductSpace.toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)) ∧
      SetValuedOperator.dom (∂ (f∗[hf])) = gradf '' interior (effectiveDomain f) := by
  -- This is the formal equation `(18.31)` extracted from the source proof.
  exact
    exists_gateaux_gradient_field_with_subdifferential_dom_gamma_zero_conjugate_eq_image
      (f := f) hf hdom hdiff

end DifferentiabilityAndStrictConvexity

end ERealFunction
