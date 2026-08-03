import BauschkeLean.Chap09.Theorem_9_1
import BauschkeLean.Chap20.Proposition_20_37
import BauschkeLean.Chap20.Proposition_20_58

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace SetValuedOperator Topology
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section WeakGraphSequences

variable {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
variable {xSeq uSeq : ℕ → H} {x u : H}
variable (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
variable (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
variable (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))

/-- Helper for Corollary 20.59: weak convergence in a real pre-Hilbert space still forces a
norm-bounded range, by passing to the weak-star bidual and pulling the norm bound back through the
canonical isometric embedding. -/
private theorem bounded_range_of_tendsto_weakly_prehilbert
    {vSeq : ℕ → H} {v : H}
    (hv :
      Tendsto (fun n ↦ toWeakSpace ℝ H (vSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H v))) :
    Bornology.IsBounded (Set.range vSeq) := by
  let ySeq : ℕ → WeakDual ℝ (StrongDual ℝ H) := fun n ↦
    NormedSpace.inclusionInDoubleDualWeak ℝ H (toWeakSpace ℝ H (vSeq n))
  -- Transport weak convergence to the weak-star bidual, where Banach-Steinhaus yields boundedness.
  have hy :
      Tendsto ySeq atTop
        (𝓝 (NormedSpace.inclusionInDoubleDualWeak ℝ H (toWeakSpace ℝ H v))) := by
    simpa [ySeq] using
      ((NormedSpace.inclusionInDoubleDualWeak ℝ H).continuous.tendsto
        (toWeakSpace ℝ H v)).comp hv
  have hy_vN : Bornology.IsVonNBounded ℝ (Set.range ySeq) :=
    hy.isVonNBounded_range ℝ
  have hy_bounded : Bornology.IsBounded (Set.range ySeq) := by
    rw [WeakDual.isBounded_iff_isVonNBounded]
    exact hy_vN
  have hbidual_bounded :
      Bornology.IsBounded
        (Set.range fun n ↦ WeakDual.toStrongDual (ySeq n)) := by
    rw [← WeakDual.isBounded_toStrongDual_preimage_iff_isBounded]
    exact hy_bounded.subset <| by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  -- Pull the bidual bound back through the canonical linear isometry into the original space.
  refine
    ((NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := H)).antilipschitz.isBounded_preimage
      hbidual_bounded).subset ?_
  rintro z ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  ext l
  change StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ H (vSeq n)) l = l (vSeq n)
  simp [NormedSpace.dual_def]

/-- Helper for Corollary 20.59: coordinatewise weak convergence in `H` induces weak convergence of
the paired sequence in `H × H`. -/
private theorem weak_tendsto_pair_of_coordinatewise_weak_tendsto
    {xSeq uSeq : ℕ → H} {x u : H}
    (hxSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u))) :
    Tendsto (fun n ↦ toWeakSpace ℝ (WithLp 2 (H × H)) (WithLp.toLp 2 (xSeq n, uSeq n))) atTop
      (𝓝 (toWeakSpace ℝ (WithLp 2 (H × H)) (WithLp.toLp 2 (x, u)))) := by
  let e : WithLp 2 (H × H) ≃L[ℝ] H × H := WithLp.prodContinuousLinearEquiv 2 ℝ H H
  let pairToWeak :
      WeakSpace ℝ H × WeakSpace ℝ H → WeakSpace ℝ (WithLp 2 (H × H)) :=
    fun z ↦
      toWeakSpace ℝ (WithLp 2 (H × H))
        (WithLp.toLp 2 ((toWeakSpace ℝ H).symm z.1, (toWeakSpace ℝ H).symm z.2))
  have hpairToWeak : Continuous pairToWeak := by
    rw [continuous_iff_forall_weakDual_apply]
    intro l
    let Lprod : H × H →L[ℝ] ℝ :=
      WeakDual.toStrongDual l ∘L e.symm.toContinuousLinearMap
    let lfst : StrongDual ℝ H := Lprod ∘L ContinuousLinearMap.inl ℝ H H
    let lsnd : StrongDual ℝ H := Lprod ∘L ContinuousLinearMap.inr ℝ H H
    have hfst_eval :
        Continuous fun z : WeakSpace ℝ H × WeakSpace ℝ H ↦
          StrongDual.toWeakDual lfst ((toWeakSpace ℝ H).symm z.1) := by
      have hweak_eval :
          Continuous fun z : WeakSpace ℝ H ↦
            StrongDual.toWeakDual lfst ((toWeakSpace ℝ H).symm z) :=
        (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1 continuous_id
          (StrongDual.toWeakDual lfst)
      exact hweak_eval.comp continuous_fst
    have hsnd_eval :
        Continuous fun z : WeakSpace ℝ H × WeakSpace ℝ H ↦
          StrongDual.toWeakDual lsnd ((toWeakSpace ℝ H).symm z.2) := by
      have hweak_eval :
          Continuous fun z : WeakSpace ℝ H ↦
            StrongDual.toWeakDual lsnd ((toWeakSpace ℝ H).symm z) :=
        (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1 continuous_id
          (StrongDual.toWeakDual lsnd)
      exact hweak_eval.comp continuous_snd
    -- Split each product functional into its two coordinate evaluations.
    refine (hfst_eval.add hsnd_eval).congr ?_
    intro z
    simpa [pairToWeak, e, Lprod, lfst, lsnd, StrongDual.toWeakDual_apply,
      WeakDual.toStrongDual_apply, WithLp.prodContinuousLinearEquiv_symm_apply]
      using Lprod.comp_inl_add_comp_inr
          ((toWeakSpace ℝ H).symm z.1, (toWeakSpace ℝ H).symm z.2)
  have hprod :
      Tendsto (fun n ↦ (toWeakSpace ℝ H (xSeq n), toWeakSpace ℝ H (uSeq n))) atTop
        (𝓝 (toWeakSpace ℝ H x, toWeakSpace ℝ H u)) :=
    hxSeq.prodMk_nhds huSeq
  -- Compose the coordinatewise weak limit with the continuous pairing map.
  simpa [pairToWeak] using
    (hpairToWeak.tendsto (toWeakSpace ℝ H x, toWeakSpace ℝ H u)).comp hprod

/-- Helper for Corollary 20.59: weak lower semicontinuity of the Fitzpatrick function along a
weakly convergent graph sequence yields the `EReal` liminf inequality used in clause `(1)`. -/
private theorem fitzpatrick_liminf_of_weak_graph_sequence
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    {xSeq uSeq : ℕ → H} {x u : H}
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u))) :
    F[A] (x, u) ≤ liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop := by
  let hA_graph : (gra A).Nonempty := ⟨(xSeq 0, uSeq 0), hgraph 0⟩
  let hFA_proper : IsProper F[A] :=
    fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph (Maximal.isMonotone hA)
  let FA : H × H → Set.Ioi (⊥ : EReal) := properIoi (F[A]) hFA_proper
  let e : WithLp 2 (H × H) ≃L[ℝ] H × H := WithLp.prodContinuousLinearEquiv 2 ℝ H H
  let FAprod : WithLp 2 (H × H) → Set.Ioi (⊥ : EReal) := FA ∘ e
  have hFA_gamma : FA ∈ Γ₀(H × H) := by
    simpa [FA, hFA_proper] using
      fitzpatrickFunction_mem_gammaZero A hA_graph (Maximal.isMonotone hA)
  have hFAprod_gamma : FAprod ∈ Γ₀(WithLp 2 (H × H)) := by
    simpa [FAprod, e] using mem_gammaZero_comp_continuousLinearEquiv hFA_gamma e
  have htfae :
      List.TFAE
        [ (∀ ⦃pSeq : ℕ → WithLp 2 (H × H)⦄ ⦃p : WithLp 2 (H × H)⦄,
              Tendsto (fun n ↦ toWeakSpace ℝ (WithLp 2 (H × H)) (pSeq n)) atTop
                  (𝓝 (toWeakSpace ℝ (WithLp 2 (H × H)) p)) →
                FAprod.asEReal p ≤ liminf (FAprod.asEReal ∘ pSeq) atTop),
          (∀ ⦃pSeq : ℕ → WithLp 2 (H × H)⦄ ⦃p : WithLp 2 (H × H)⦄,
              Tendsto pSeq atTop (𝓝 p) →
                FAprod.asEReal p ≤ liminf (FAprod.asEReal ∘ pSeq) atTop),
          LowerSemicontinuous FAprod.asEReal,
          WeaklyLowerSemicontinuous FAprod.asEReal ] := by
    exact convex_lowerSemicontinuity_tfae
      (convex_epigraph_asEReal_of_mem_gammaZero hFAprod_gamma)
  have hweak_seq :
      ∀ ⦃pSeq : ℕ → WithLp 2 (H × H)⦄ ⦃p : WithLp 2 (H × H)⦄,
        Tendsto (fun n ↦ toWeakSpace ℝ (WithLp 2 (H × H)) (pSeq n)) atTop
            (𝓝 (toWeakSpace ℝ (WithLp 2 (H × H)) p)) →
          FAprod.asEReal p ≤ liminf (FAprod.asEReal ∘ pSeq) atTop := by
    exact (List.TFAE.out htfae 0 2).2 hFAprod_gamma.1
  -- Apply the weak sequential lower semicontinuity clause on the Hilbert-product model.
  simpa [FAprod, FA, hFA_proper, e, Function.comp, WithLp.prodContinuousLinearEquiv_apply] using
    hweak_seq
      (weak_tendsto_pair_of_coordinatewise_weak_tendsto hxSeq huSeq)

/-- Helper for Corollary 20.59: an eventual lower bound lets one move the liminf of a real
sequence through the coercion `ℝ → EReal`. -/
private theorem ereal_liminf_coe_eq
    {a : ℕ → ℝ}
    (hBoundedAbove : atTop.IsBoundedUnder (· ≤ ·) a)
    (hBoundedBelow : atTop.IsBoundedUnder (· ≥ ·) a) :
    (((liminf a atTop : ℝ) : ℝ) : EReal) = liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop := by
  simpa [Function.comp] using
    (Monotone.map_liminf_of_continuousAt (F := atTop) (f := fun r : ℝ ↦ (r : EReal))
      (fun x y h ↦ by simpa using h) a continuous_coe_real_ereal.continuousAt
      hBoundedAbove.isCoboundedUnder_ge hBoundedBelow)

/-- Helper for Corollary 20.59: bounded primal and dual ranges bound the inner-product sequence
both above and below. -/
private theorem inner_isBoundedUnder_of_bounded_ranges
    {xSeq uSeq : ℕ → H}
    (hx_bounded : Bornology.IsBounded (Set.range xSeq))
    (hu_bounded : Bornology.IsBounded (Set.range uSeq)) :
    atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) ∧
      atTop.IsBoundedUnder (· ≥ ·) (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) := by
  obtain ⟨Rx, hxR⟩ := hx_bounded.subset_closedBall (0 : H)
  obtain ⟨Ru, huR⟩ := hu_bounded.subset_closedBall (0 : H)
  let Cx : ℝ := max Rx 0
  let Cu : ℝ := max Ru 0
  refine ⟨?_, ?_⟩
  · refine isBoundedUnder_of ?_
    refine ⟨Cx * Cu, ?_⟩
    intro n
    have hx : ‖xSeq n‖ ≤ Cx := by
      calc
        ‖xSeq n‖ ≤ Rx := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hxR (Set.mem_range_self n)
        _ ≤ Cx := le_max_left _ _
    have hu : ‖uSeq n‖ ≤ Cu := by
      calc
        ‖uSeq n‖ ≤ Ru := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using huR (Set.mem_range_self n)
        _ ≤ Cu := le_max_left _ _
    calc
      ⟪xSeq n, uSeq n⟫_ℝ ≤ |⟪xSeq n, uSeq n⟫_ℝ| := le_abs_self _
      _ ≤ ‖xSeq n‖ * ‖uSeq n‖ := abs_real_inner_le_norm _ _
      _ ≤ Cx * Cu := mul_le_mul hx hu (norm_nonneg _) (le_max_right _ _)
  · refine isBoundedUnder_of ?_
    refine ⟨-(Cx * Cu), ?_⟩
    intro n
    have hx : ‖xSeq n‖ ≤ Cx := by
      calc
        ‖xSeq n‖ ≤ Rx := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hxR (Set.mem_range_self n)
        _ ≤ Cx := le_max_left _ _
    have hu : ‖uSeq n‖ ≤ Cu := by
      calc
        ‖uSeq n‖ ≤ Ru := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using huR (Set.mem_range_self n)
        _ ≤ Cu := le_max_left _ _
    have habs :
        |⟪xSeq n, uSeq n⟫_ℝ| ≤ Cx * Cu := by
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hx hu (norm_nonneg _) (le_max_right _ _))
    calc
      -(Cx * Cu) ≤ -|⟪xSeq n, uSeq n⟫_ℝ| := by linarith
      _ ≤ ⟪xSeq n, uSeq n⟫_ℝ := neg_abs_le _

/-- Helper for Corollary 20.59: an `EReal` liminf lower bound on a real sequence implies the
corresponding real liminf lower bound once the sequence is bounded below. -/
private theorem ereal_inner_liminf_to_real
    {a : ℕ → ℝ} {c : ℝ}
    (hBoundedAbove : atTop.IsBoundedUnder (· ≤ ·) a)
    (hBoundedBelow : atTop.IsBoundedUnder (· ≥ ·) a)
    (h :
      ((c : ℝ) : EReal) ≤ liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop) :
    c ≤ liminf a atTop := by
  have hcoe : (((liminf a atTop : ℝ) : ℝ) : EReal) =
      liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop :=
    ereal_liminf_coe_eq hBoundedAbove hBoundedBelow
  have h' : ((c : ℝ) : EReal) ≤ (((liminf a atTop : ℝ) : ℝ) : EReal) := by
    rw [hcoe]
    exact h
  exact_mod_cast h'

/- Source/core/bridge triage:
- `source-facing`: Corollary 20.59 records the weak-graph sequential consequences of the
  Fitzpatrick contact-set characterization.
- `core/canonical`: the owner abstractions are maximal monotonicity `Maximal IsMonotone A`, the
  Fitzpatrick owner `F[A]`, and the source-facing contact-set description
  `Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner`.
- `bridge/view`: the weak-space convergence hypotheses via `toWeakSpace ℝ H` are auxiliary
  topological transport data. Under `[CompleteSpace H]`, Proposition 20.38 upgrades this to the
  mixed weak-strong graph-closure owner `Maximal.graph_isSeqClosed_weakStrong`; the present
  corollary keeps the source-facing liminf/contact formulation that does not assume completeness.

Primitive data: maximal monotonicity, graph membership of the sequence terms, and weak
convergence of the primal and dual coordinates. Derived API: the liminf inequality for the
pairings, the resulting graph-membership criterion, and the convergence upgrade under the limsup
bound. -/

-- Semantic recall: no direct mathlib owner matched this weak-graph Fitzpatrick corollary, so we
-- keep the source-facing Chapter 20 statement shape and rely on the local maximal-monotone API.

-- Proof sketch: `hgraph` makes `gra A` nonempty, so Proposition 20.56 places the Fitzpatrick
-- owner `F[A]` in `Γ₀(H × H)`. Since `Γ₀` membership is the canonical owner for convex lower
-- semicontinuity, the weak liminf criterion from `WeaklyLowerSemicontinuousAt` applies to `F[A]`
-- along the weakly convergent sequence
-- `fun n ↦ (xSeq n, uSeq n)`. Rewrite the sequence values by
-- `fitzpatrickFunction_eq_inner_of_mem_graph`, and use
-- `Maximal.inner_le_fitzpatrickFunction hA x u` to compare the limit value with the pairing.
/-- Corollary 20.59 (1): if graph points `(x_n, u_n)` of a maximally monotone operator converge
weakly to `(x, u)`, then the pairing is weakly lower semicontinuous along the sequence:
`⟪x, u⟫ ≤ liminf_n ⟪x_n, u_n⟫`. -/
theorem Maximal.inner_le_liminf_inner_of_tendsto_weakly_seq
    (hA : Maximal IsMonotone A)
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    : ⟪x, u⟫_ℝ ≤ liminf (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop := by
  let a : ℕ → ℝ := fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ
  have hx_bounded : Bornology.IsBounded (Set.range xSeq) :=
    bounded_range_of_tendsto_weakly_prehilbert hxSeq
  have hu_bounded : Bornology.IsBounded (Set.range uSeq) :=
    bounded_range_of_tendsto_weakly_prehilbert huSeq
  have hBounds :
      atTop.IsBoundedUnder (· ≤ ·) a ∧ atTop.IsBoundedUnder (· ≥ ·) a :=
    inner_isBoundedUnder_of_bounded_ranges hx_bounded hu_bounded
  have hfitz :
      F[A] (x, u) ≤ liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop :=
    fitzpatrick_liminf_of_weak_graph_sequence hA hgraph hxSeq huSeq
  have hcontact :
      liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop =
        liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop := by
    refine Filter.liminf_congr ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa [a, pairing_apply] using
        fitzpatrickFunction_eq_inner_of_mem_graph
          (A := A) (Maximal.isMonotone hA) (hgraph n)
  have hinner_ereal :
      ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop := by
    calc
      ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F[A] (x, u) :=
        Maximal.inner_le_fitzpatrickFunction hA x u
      _ ≤ liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop := hfitz
      _ = liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop := hcontact
  -- Convert the `EReal` liminf inequality back to the target real liminf statement.
  exact ereal_inner_liminf_to_real hBounds.1 hBounds.2 hinner_ereal

-- Proof sketch: the weak-lower-semicontinuity argument from clause (1) gives
-- `F[A] (x, u) ≤ liminf_n ⟪xSeq n, uSeq n⟫`, while the graph hypothesis rewrites every sequence
-- value as a Fitzpatrick contact value. With the assumed liminf equality and
-- `Maximal.inner_le_fitzpatrickFunction hA x u`, we obtain
-- `F[A] (x, u) = ((⟪x, u⟫_ℝ : ℝ) : EReal)`. Rewriting the contact set by
-- `Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner` then yields `(x, u) ∈ gra A`.
/-- Corollary 20.59 (2): if the weakly convergent graph sequence satisfies
`liminf_n ⟪x_n, u_n⟫ = ⟪x, u⟫`, then the weak limit pair still belongs to `gra A`. -/
theorem Maximal.mem_graph_of_liminf_inner_eq_of_tendsto_weakly_seq
    (hA : Maximal IsMonotone A)
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hliminf : liminf (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop = ⟪x, u⟫_ℝ) :
    (x, u) ∈ gra A := by
  let a : ℕ → ℝ := fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ
  have hx_bounded : Bornology.IsBounded (Set.range xSeq) :=
    bounded_range_of_tendsto_weakly_prehilbert hxSeq
  have hu_bounded : Bornology.IsBounded (Set.range uSeq) :=
    bounded_range_of_tendsto_weakly_prehilbert huSeq
  have hBounds :
      atTop.IsBoundedUnder (· ≤ ·) a ∧ atTop.IsBoundedUnder (· ≥ ·) a :=
    inner_isBoundedUnder_of_bounded_ranges hx_bounded hu_bounded
  have hfitz :
      F[A] (x, u) ≤ liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop :=
    fitzpatrick_liminf_of_weak_graph_sequence hA hgraph hxSeq huSeq
  have hcontact :
      liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop =
        liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop := by
    refine Filter.liminf_congr ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa [a, pairing_apply] using
        fitzpatrickFunction_eq_inner_of_mem_graph
          (A := A) (Maximal.isMonotone hA) (hgraph n)
  have hfitz_le :
      F[A] (x, u) ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
    calc
      F[A] (x, u) ≤ liminf (fun n ↦ F[A] (xSeq n, uSeq n)) atTop := hfitz
      _ = liminf (fun n ↦ ((a n : ℝ) : EReal)) atTop := hcontact
      _ = (((liminf a atTop : ℝ) : ℝ) : EReal) := (ereal_liminf_coe_eq hBounds.1 hBounds.2).symm
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by simpa [a] using congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hliminf
  have hfitz_eq :
      F[A] (x, u) = pairing (x, u) := by
    apply le_antisymm
    · simpa [pairing_apply] using hfitz_le
    · exact Maximal.inner_le_fitzpatrickFunction hA x u
  -- The contact-set characterization from Proposition 20.58 identifies the graph.
  rw [Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner (A := A) hA]
  simpa using hfitz_eq

-- Proof sketch: clause (1) provides `⟪x, u⟫ ≤ liminf_n ⟪xSeq n, uSeq n⟫`, while the hypothesis
-- gives `limsup_n ⟪xSeq n, uSeq n⟫ ≤ ⟪x, u⟫`; hence liminf and limsup agree, so the real pairing
-- sequence converges to `⟪x, u⟫`.
/-- Corollary 20.59 (3): if moreover `limsup_n ⟪x_n, u_n⟫ ≤ ⟪x, u⟫`, then
`⟪x_n, u_n⟫ → ⟪x, u⟫`. -/
theorem Maximal.tendsto_inner_of_limsup_inner_le_of_tendsto_weakly_seq
    (hA : Maximal IsMonotone A)
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hlimsup : limsup (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop ≤ ⟪x, u⟫_ℝ) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  let a : ℕ → ℝ := fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ
  have hx_bounded : Bornology.IsBounded (Set.range xSeq) :=
    bounded_range_of_tendsto_weakly_prehilbert hxSeq
  have hu_bounded : Bornology.IsBounded (Set.range uSeq) :=
    bounded_range_of_tendsto_weakly_prehilbert huSeq
  have hBounds :
      atTop.IsBoundedUnder (· ≤ ·) a ∧ atTop.IsBoundedUnder (· ≥ ·) a :=
    inner_isBoundedUnder_of_bounded_ranges hx_bounded hu_bounded
  have hliminf :
      ⟪x, u⟫_ℝ ≤ liminf a atTop := by
    simpa [a] using
      Maximal.inner_le_liminf_inner_of_tendsto_weakly_seq
        (A := A) hA hgraph hxSeq huSeq
  -- Squeeze liminf and limsup at the common value `⟪x, u⟫`.
  simpa [a] using
    tendsto_of_le_liminf_of_limsup_le hliminf
      (by simpa [a] using hlimsup) hBounds.1 hBounds.2

-- Proof sketch: combine clause (3) with the liminf/limsup squeeze to obtain
-- `liminf_n ⟪xSeq n, uSeq n⟫ = ⟪x, u⟫`, then apply clause (2).
/-- Corollary 20.59 (4): under the same `limsup` bound, the weak limit pair belongs to `gra A`.
-/
theorem Maximal.mem_graph_of_limsup_inner_le_of_tendsto_weakly_seq
    (hA : Maximal IsMonotone A)
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hlimsup : limsup (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop ≤ ⟪x, u⟫_ℝ) :
    (x, u) ∈ gra A := by
  have hinner :
      Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) :=
    Maximal.tendsto_inner_of_limsup_inner_le_of_tendsto_weakly_seq hA hgraph hxSeq huSeq hlimsup
  -- Reuse clause `(2)` after identifying the liminf of a convergent real sequence with its limit.
  exact Maximal.mem_graph_of_liminf_inner_eq_of_tendsto_weakly_seq
    hA hgraph hxSeq huSeq hinner.liminf_eq

end WeakGraphSequences

end SetValuedOperator
