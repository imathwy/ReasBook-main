import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap20.Proposition_20_37
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap23.Proposition_23_38
import BauschkeLean.Chap23.Proposition_23_39

-- Semantic recall note: `lean_leansearch` only surfaced unrelated algebra-spectrum resolvent
-- theorems, so this item uses the verified local Chapter 23 owners `resolventMap` and `A.zeros`,
-- together with the Chapter 3 metric projection notation `P[...]`.

open scoped InnerProductSpace Pointwise SetValuedOperator Topology
open ERealFunction
open Filter

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 23.44 is phrased with the inverse parameter `γ` in the inclusion
  `0 ∈ A p + γ • (p - x)`.
- `core/canonical`: Chapter 23 already owns the resolvent as `J[((γ : ℝ) • A)]`, realized by
  `resolventMap A hA γ`.
- `bridge/view`: this file reexpresses the source-facing inverse-parameter formulation through the
  canonical owner by evaluating it at `γ⁻¹`. -/

/-- The `PosReal` filter expressing `γ ↓ 0` through `]0,1[`. -/
def atZeroRightWithinUnitInterval : Filter PosReal :=
  Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1))

/-- The inverse-parameter resolvent curve from Theorem 23.44, realized by evaluating the canonical
resolvent map at `γ⁻¹`. -/
noncomputable def inverseParameterResolventCurve
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H) : PosReal → H :=
  fun γ ↦ resolventMap A hA γ⁻¹ x

@[simp] theorem inverseParameterResolventCurve_apply
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H) (γ : PosReal) :
    inverseParameterResolventCurve A hA x γ = resolventMap A hA γ⁻¹ x :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 23.44: the source inclusion
`0 ∈ A p + ({γ • (p - x)} : Set H)` is exactly the graph condition
`(p, γ • (x - p)) ∈ gra A`. -/
private theorem zeroMem_add_singleton_smul_sub_iff_mem_graph
    (A : SetValuedOperator H H) (x : H) (γ : PosReal) (p : H) :
    0 ∈ A p + ({(γ : ℝ) • (p - x)} : Set H) ↔ (p, (γ : ℝ) • (x - p)) ∈ gra A := by
  rw [Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    rw [Set.mem_singleton_iff] at hv
    subst v
    rw [mem_graph]
    have hu_eq : u = (γ : ℝ) • (x - p) := by
      calc
        u = -((γ : ℝ) • (p - x)) := eq_neg_of_add_eq_zero_left huv
        _ = (γ : ℝ) • (x - p) := by
              simp [sub_eq_add_neg]
    exact hu_eq ▸ hu
  · intro hp
    rw [mem_graph] at hp
    refine ⟨(γ : ℝ) • (x - p), hp, (γ : ℝ) • (p - x), by simp, ?_⟩
    rw [← smul_add]
    simp

/-- Helper for Theorem 23.44: the canonical inverse-parameter resolvent point produces the graph
pair `(x_γ, γ • (x - x_γ)) ∈ gra A`. -/
private theorem inverseParameterResolventCurve_mem_graph
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H) (γ : PosReal) :
    (inverseParameterResolventCurve A hA x γ,
        (γ : ℝ) • (x - inverseParameterResolventCurve A hA x γ)) ∈ gra A := by
  -- Rewrite the chosen point as the singleton-valued resolvent member at parameter `γ⁻¹`.
  have hmem :
      inverseParameterResolventCurve A hA x γ ∈ J[(((γ⁻¹ : PosReal) : ℝ) • A)] x := by
    rw [inverseParameterResolventCurve_apply,
      resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ⁻¹ x]
    simp
  -- Proposition 23.2 supplies the graph criterion, and `(γ⁻¹)⁻¹ = γ` closes the bridge.
  simpa [inverseParameterResolventCurve_apply] using
    (mem_resolvent_smul_iff_mem_graph A γ⁻¹ x (inverseParameterResolventCurve A hA x γ)).1 hmem

/-- Helper for Theorem 23.44: every zero `z ∈ A.zeros` satisfies the source Fejér inequality
against the inverse-parameter resolvent curve. -/
private theorem norm_sq_sub_le_inner_sub_of_mem_zeros
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x z : H)
    (hz : z ∈ A.zeros) (γ : PosReal) :
    ‖inverseParameterResolventCurve A hA x γ - z‖ ^ 2 ≤
      ⟪inverseParameterResolventCurve A hA x γ - z, x - z⟫_ℝ := by
  let T : H → H := resolventMap A hA γ⁻¹
  have hz_mem : z ∈ J[(((γ⁻¹ : PosReal) : ℝ) • A)] z := by
    change z ∈ ({x : H | x ∈ J[(((γ⁻¹ : PosReal) : ℝ) • A)] x} : Set H)
    rw [fixedPointSet_resolvent_smul_eq_zeros (A := A) (γ := γ⁻¹)]
    exact hz
  have hz_fix : T z = z := by
    have hz_eq : z = resolventMap A hA γ⁻¹ z := by
      rw [← Set.mem_singleton_iff,
        ← resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ⁻¹ z]
      exact hz_mem
    simpa [T] using hz_eq.symm
  -- Firm nonexpansiveness of the resolvent realizes the textbook inequality directly.
  have hfirm :
      ∀ x y : H, ‖T x - T y‖ ^ 2 ≤ ⟪T x - T y, x - y⟫_ℝ :=
    resolvent_smul_firmlyNonexpansive_of_toSetValuedOperator_eq
      A hA γ⁻¹ T (resolventMap_toSetValuedOperator_eq A hA γ⁻¹)
  simpa [inverseParameterResolventCurve_apply, T, hz_fix] using hfirm x z

/-- Helper for Theorem 23.44: the Fejér inequality rewrites to the source sign condition
`⟪z - x_γ, x - x_γ⟫ ≤ 0`. -/
private theorem inner_sub_right_nonpos_of_mem_zeros
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x z : H)
    (hz : z ∈ A.zeros) (γ : PosReal) :
    ⟪z - inverseParameterResolventCurve A hA x γ,
      x - inverseParameterResolventCurve A hA x γ⟫_ℝ ≤ 0 := by
  let uγ := inverseParameterResolventCurve A hA x γ
  have hineq :
      ‖uγ - z‖ ^ 2 ≤ ⟪uγ - z, x - z⟫_ℝ :=
    norm_sq_sub_le_inner_sub_of_mem_zeros A hA x z hz γ
  -- Isolate the defect term `⟪uγ - z, x - uγ⟫` from the decomposition
  -- `x - z = (uγ - z) + (x - uγ)`.
  have hsplit :
      ⟪uγ - z, x - z⟫_ℝ =
        ‖uγ - z‖ ^ 2 + ⟪uγ - z, x - uγ⟫_ℝ := by
    have hdecomp : x - z = (uγ - z) + (x - uγ) := by
      abel_nf
    rw [hdecomp, inner_add_right, real_inner_self_eq_norm_sq]
  have hnonneg : 0 ≤ ⟪uγ - z, x - uγ⟫_ℝ := by
    rw [hsplit] at hineq
    linarith
  have hneg :
      ⟪z - uγ, x - uγ⟫_ℝ = -⟪uγ - z, x - uγ⟫_ℝ := by
    rw [show z - uγ = -(uγ - z) by abel_nf, inner_neg_left]
  linarith

/-- Helper for Theorem 23.44: bounded zero-right inverse-parameter resolvent sequences have all
their weak sequential cluster points in `A.zeros`. -/
private theorem mem_zeros_of_weakSequentialClusterPt_inverseParameterResolventCurve_seq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval)
    (hbounded :
      Bornology.IsBounded
        (Set.range fun n ↦ inverseParameterResolventCurve A hA x (γs n)))
    {y : H}
    (hy :
      IsSequentialClusterPt
        (fun n ↦ toWeakSpace ℝ H (inverseParameterResolventCurve A hA x (γs n)))
        (toWeakSpace ℝ H y)) :
    y ∈ A.zeros := by
  let u : ℕ → H := fun n ↦ inverseParameterResolventCurve A hA x (γs n)
  rcases hy.exists_subseq_tendsto with ⟨φ, hφ, hφ_tendsto⟩
  have hγs_zeroRight :
      Tendsto (fun n ↦ ((γs n : PosReal) : ℝ)) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) := by
    simpa [atZeroRightWithinUnitInterval] using hγs
  have hγφ_zero :
      Tendsto (fun n ↦ ((γs (φ n) : PosReal) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    exact (hγs_zeroRight.comp hφ.tendsto_atTop).trans nhdsWithin_le_nhds
  have huφ_bounded : Bornology.IsBounded (Set.range fun n ↦ u (φ n)) := by
    exact hbounded.subset (by rintro _ ⟨n, rfl⟩; exact ⟨φ n, rfl⟩)
  have hsub_bdd : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) (fun n ↦ ‖x - u (φ n)‖) := by
    classical
    let R : ℝ := Classical.choose (huφ_bounded.subset_closedBall (0 : H))
    have hR :
        Set.range (fun n ↦ u (φ n)) ⊆ Metric.closedBall (0 : H) R :=
      Classical.choose_spec (huφ_bounded.subset_closedBall (0 : H))
    refine Filter.isBoundedUnder_of ?_
    refine ⟨‖x‖ + R, fun m : ℕ ↦ ?_⟩
    have hRm : ‖u (φ m)‖ ≤ R := by
      have hmem : u (φ m) ∈ Metric.closedBall (0 : H) R := hR (Set.mem_range_self m)
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
    linarith [norm_sub_le x (u (φ m)), hRm]
  have hres_zero :
      Tendsto (fun n ↦ ((γs (φ n) : PosReal) : ℝ) • (x - u (φ n))) atTop (𝓝 (0 : H)) := by
    exact Filter.Tendsto.zero_smul_isBoundedUnder_le hγφ_zero hsub_bdd
  have hres_bounded :
      Bornology.IsBounded
        (Set.range fun n ↦ ((γs (φ n) : PosReal) : ℝ) • (x - u (φ n))) :=
    Metric.isBounded_range_of_tendsto _ hres_zero
  have hpair_bounded :
      Bornology.IsBounded
        (Set.range fun n ↦ (u (φ n), ((γs (φ n) : PosReal) : ℝ) • (x - u (φ n)))) := by
    refine (huφ_bounded.prod hres_bounded).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩
  have hgraph :
      ∀ n, (u (φ n), ((γs (φ n) : PosReal) : ℝ) • (x - u (φ n))) ∈ gra A := by
    intro n
    simpa [u] using inverseParameterResolventCurve_mem_graph A hA x (γs (φ n))
  -- Mixed weak-strong graph closedness places the cluster point back in `gra A`.
  have hmem : (y, (0 : H)) ∈ gra A :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_weakly_of_tendsto
      hA hgraph hpair_bounded hφ_tendsto hres_zero
  simpa [mem_zeros_iff, mem_graph] using hmem

/-- Helper for Theorem 23.44: a bounded zero-right inverse-parameter resolvent sequence forces
`A.zeros.Nonempty`. -/
private theorem zeros_nonempty_of_bounded_inverseParameterResolventCurve_seq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval)
    (hbounded :
      Bornology.IsBounded
        (Set.range fun n ↦ inverseParameterResolventCurve A hA x (γs n))) :
    A.zeros.Nonempty := by
  let u : ℕ → H := fun n ↦ inverseParameterResolventCurve A hA x (γs n)
  rcases bounded_sequence_has_weakly_convergent_subsequence u hbounded with
    ⟨y, φ, hφ, hy⟩
  have hy_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H y) :=
    ⟨φ, hφ, hy⟩
  exact
    ⟨y,
      mem_zeros_of_weakSequentialClusterPt_inverseParameterResolventCurve_seq
        A hA x hγs hbounded hy_cluster⟩

/-- Helper for Theorem 23.44: if `A.zeros.Nonempty`, every zero-right inverse-parameter
resolvent sequence converges strongly to the projection of `x` onto `A.zeros`. -/
private theorem tendsto_inverseParameterResolventCurve_of_zeroRightSeq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (hzero : A.zeros.Nonempty) {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval) :
    Tendsto (fun n ↦ inverseParameterResolventCurve A hA x (γs n)) atTop
      (nhds (P[A.zeros, Maximal.zeros_isChebyshev hA hzero] x)) := by
  let u : ℕ → H := fun n ↦ inverseParameterResolventCurve A hA x (γs n)
  let p := P[A.zeros, Maximal.zeros_isChebyshev hA hzero] x
  have hzero_nonempty := hzero
  rcases hzero with ⟨z0, hz0⟩
  have hnorm_le : ∀ n, ‖u n - z0‖ ≤ ‖x - z0‖ := by
    intro n
    have hsq :
        ‖u n - z0‖ ^ 2 ≤ ‖u n - z0‖ * ‖x - z0‖ := by
      exact
        (norm_sq_sub_le_inner_sub_of_mem_zeros A hA x z0 hz0 (γs n)).trans
          (real_inner_le_norm _ _)
    nlinarith [hsq, norm_nonneg (u n - z0), norm_nonneg (x - z0)]
  have hbounded : Bornology.IsBounded (Set.range u) := by
    refine
      (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall z0 ‖x - z0‖)).subset
        ?_
    rintro _ ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hnorm_le n
  have hp_char :
      p ∈ A.zeros ∧ ∀ z ∈ A.zeros, ⟪z - p, x - p⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (Maximal.zeros_isChebyshev hA hzero_nonempty) (Maximal.zeros_convex hA)).1 rfl
  have hcluster_eq :
      ∀ {y : H},
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H y) →
          y = p := by
    intro y hy
    have hy_mem : y ∈ A.zeros :=
      mem_zeros_of_weakSequentialClusterPt_inverseParameterResolventCurve_seq
        A hA x hγs hbounded hy
    rcases hy.exists_subseq_tendsto with ⟨φ, hφ, hφ_tendsto⟩
    have hweak_sub :
        Tendsto (fun n ↦ toWeakSpace ℝ H (u (φ n) - y)) atTop
          (𝓝 (toWeakSpace ℝ H (0 : H))) := by
      simpa [sub_eq_add_neg] using
        hφ_tendsto.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H y) atTop
            (𝓝 (toWeakSpace ℝ H y)))
    have hinner_zero :
        Tendsto (fun n ↦ ⟪u (φ n) - y, x - y⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
      simpa using
        (weakSpace_continuous_inner_right (x - y)).tendsto (toWeakSpace ℝ H (0 : H)) |>.comp
          hweak_sub
    have hsq_zero :
        Tendsto (fun n ↦ ‖u (φ n) - y‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      have hsq_le :
          ∀ n, ‖u (φ n) - y‖ ^ 2 ≤ ⟪u (φ n) - y, x - y⟫_ℝ := by
        intro n
        simpa [u] using
          norm_sq_sub_le_inner_sub_of_mem_zeros A hA x y hy_mem (γs (φ n))
      exact squeeze_zero (fun n ↦ by positivity) hsq_le hinner_zero
    have hnorm_zero :
        Tendsto (fun n ↦ ‖u (φ n) - y‖) atTop (𝓝 (0 : ℝ)) := by
      simpa [Real.sqrt_sq_eq_abs, Real.sqrt_zero, abs_of_nonneg (norm_nonneg _)] using
        hsq_zero.sqrt
    have hy_strong : Tendsto (fun n ↦ u (φ n)) atTop (𝓝 y) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa [u] using hnorm_zero
    have hy_inner :
        ∀ z ∈ A.zeros, ⟪z - y, x - y⟫_ℝ ≤ 0 := by
      intro z hz
      have hz_nonpos :
          ∀ n, ⟪z - u (φ n), x - u (φ n)⟫_ℝ ≤ 0 := by
        intro n
        simpa [u] using inner_sub_right_nonpos_of_mem_zeros A hA x z hz (γs (φ n))
      have hz_sub :
          Tendsto (fun n ↦ z - u (φ n)) atTop (𝓝 (z - y)) := by
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ z) atTop (𝓝 z)).sub hy_strong
      have hx_sub :
          Tendsto (fun n ↦ x - u (φ n)) atTop (𝓝 (x - y)) := by
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x)).sub hy_strong
      have hlimit :
          Tendsto (fun n ↦ ⟪z - u (φ n), x - u (φ n)⟫_ℝ) atTop
            (𝓝 ⟪z - y, x - y⟫_ℝ) := by
        simpa using Filter.Tendsto.inner hz_sub hx_sub
      exact le_of_tendsto_of_tendsto hlimit tendsto_const_nhds (Eventually.of_forall hz_nonpos)
    -- The strong subsequence limit satisfies the projection characterization, so it must be `p`.
    simpa [p] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (Maximal.zeros_isChebyshev hA hzero_nonempty) (Maximal.zeros_convex hA)).2
        ⟨hy_mem, hy_inner⟩
  have hunique :
      ∀ y z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H z) →
          y = z := by
    intro y z hy hz
    calc
      y = p := hcluster_eq hy
      _ = z := (hcluster_eq hz).symm
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with
    ⟨y, hy⟩
  have hy_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H y) :=
    ⟨id, strictMono_id, by simpa using hy⟩
  have hy_eq : y = p := hcluster_eq hy_cluster
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (toWeakSpace ℝ H p)) := by
    simpa [u, hy_eq] using hy
  have hweak_sub :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n - p)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [sub_eq_add_neg] using
      hweak.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H p) atTop
          (𝓝 (toWeakSpace ℝ H p)))
  have hinner_zero :
      Tendsto (fun n ↦ ⟪u n - p, x - p⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (weakSpace_continuous_inner_right (x - p)).tendsto (toWeakSpace ℝ H (0 : H)) |>.comp
        hweak_sub
  have hsq_zero :
      Tendsto (fun n ↦ ‖u n - p‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hsq_le : ∀ n, ‖u n - p‖ ^ 2 ≤ ⟪u n - p, x - p⟫_ℝ := by
      intro n
      simpa [u, p] using norm_sq_sub_le_inner_sub_of_mem_zeros A hA x p hp_char.1 (γs n)
    exact squeeze_zero (fun n ↦ by positivity) hsq_le hinner_zero
  have hnorm_zero : Tendsto (fun n ↦ ‖u n - p‖) atTop (𝓝 (0 : ℝ)) := by
    simpa [Real.sqrt_sq_eq_abs, Real.sqrt_zero, abs_of_nonneg (norm_nonneg _)] using
      hsq_zero.sqrt
  -- Weak convergence plus the Fejér estimate upgrade to the strong limit `p`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [u, p] using hnorm_zero

/-- Helper for Theorem 23.44: if `A.zeros = ∅`, every zero-right inverse-parameter resolvent
sequence has norm tending to `+∞`. -/
private theorem norm_tendsto_atTop_of_inverseParameterResolventCurve_zeroRightSeq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (hzero : A.zeros = ∅) {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval) :
    Tendsto (fun n ↦ ‖inverseParameterResolventCurve A hA x (γs n)‖) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro R
  by_cases hR_nonpos : R ≤ 0
  · exact Eventually.of_forall fun n ↦ hR_nonpos.trans (norm_nonneg _)
  · by_contra hR
    have hfreq :
        ∃ᶠ n in atTop, ‖inverseParameterResolventCurve A hA x (γs n)‖ < R := by
      exact (not_eventually.1 hR).mono fun _ hn ↦ lt_of_not_ge hn
    rcases Filter.exists_seq_forall_of_frequently hfreq with ⟨ns, hns, hnsR⟩
    have hbounded :
        Bornology.IsBounded
          (Set.range fun n ↦ inverseParameterResolventCurve A hA x (γs (ns n))) := by
      refine
        (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : H) R)).subset
          ?_
      rintro _ ⟨n, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using (hnsR n).le
    have hzeros :
        A.zeros.Nonempty :=
      zeros_nonempty_of_bounded_inverseParameterResolventCurve_seq A hA x
        (hγs.comp hns) hbounded
    have hfalse : False := by
      simp [hzero] at hzeros
    exact hfalse

/-- Theorem 23.44 (1): if `A : H → 2^H` is maximally monotone, `x : H`, and `γ ∈ ℝ_{++}`, then a
point `p` satisfies the source inclusion `0 ∈ A p + γ • (p - x)`, written on the set-valued
surface as `0 ∈ A p + ({(γ : ℝ) • (p - x)} : Set H)`, exactly when `p` is the canonical
inverse-parameter resolvent value `resolventMap A hA γ⁻¹ x`. -/
theorem resolventMap_isUnique_of_zero_mem_add_singleton_smul_sub
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (γ : PosReal) (p : H) :
    0 ∈ A p + ({(γ : ℝ) • (p - x)} : Set H) ↔ p = resolventMap A hA γ⁻¹ x := by
  constructor
  · intro hp
    -- Normalize the source inclusion to the resolvent graph criterion at parameter `γ⁻¹`.
    have hp_graph :
        (p, (((γ⁻¹ : PosReal) : ℝ)⁻¹) • (x - p)) ∈ gra A := by
      simpa using (zeroMem_add_singleton_smul_sub_iff_mem_graph A x γ p).1 hp
    have hp_mem :
        p ∈ J[(((γ⁻¹ : PosReal) : ℝ) • A)] x := by
      exact (mem_resolvent_smul_iff_mem_graph A γ⁻¹ x p).2 hp_graph
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ⁻¹ x] at hp_mem
    simpa using hp_mem
  · intro hp
    -- Rewrite the singleton resolvent value back to the source inclusion surface.
    have hp_mem :
        p ∈ J[(((γ⁻¹ : PosReal) : ℝ) • A)] x := by
      rw [hp, resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ⁻¹ x]
      simp
    exact
      (zeroMem_add_singleton_smul_sub_iff_mem_graph A x γ p).2 <|
        by
          simpa using (mem_resolvent_smul_iff_mem_graph A γ⁻¹ x p).1 hp_mem

/-- Theorem 23.44 (2): if `A : H → 2^H` is maximally monotone and `zer A ≠ ∅`, then the
inverse-parameter resolvent curve `γ ↦ resolventMap A hA γ⁻¹ x` converges to the metric
projection of `x` onto `A.zeros` as `γ ↓ 0` through `]0,1[`. -/
theorem tendsto_resolventMap_atZeroRight_of_zeros_nonempty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (hzero : A.zeros.Nonempty) :
    Filter.Tendsto (inverseParameterResolventCurve A hA x) atZeroRightWithinUnitInterval
      (nhds (P[A.zeros, Maximal.zeros_isChebyshev hA hzero] x)) :=
  by
    haveI : atZeroRightWithinUnitInterval.IsCountablyGenerated := by
      dsimp [atZeroRightWithinUnitInterval]
      infer_instance
    -- Reduce the filter statement to the zero-right sequence theorem.
    apply Filter.tendsto_of_seq_tendsto
    intro γs hγs
    simpa [Function.comp] using
      tendsto_inverseParameterResolventCurve_of_zeroRightSeq A hA x hzero hγs

/-- Theorem 23.44 (3): if `A : H → 2^H` is maximally monotone and `zer A = ∅`, then
`‖resolventMap A hA γ⁻¹ x‖ → +∞` as `γ ↓ 0` through `]0,1[`. -/
theorem norm_resolventMap_tendsto_atTop_atZeroRight_of_zeros_eq_empty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (hzero : A.zeros = ∅) :
    Filter.Tendsto (fun γ : PosReal ↦ ‖inverseParameterResolventCurve A hA x γ‖)
      atZeroRightWithinUnitInterval
      Filter.atTop := by
  haveI : atZeroRightWithinUnitInterval.IsCountablyGenerated := by
    dsimp [atZeroRightWithinUnitInterval]
    infer_instance
  -- Reduce divergence along the filter to the corresponding zero-right sequence statement.
  apply Filter.tendsto_of_seq_tendsto
  intro γs hγs
  change Tendsto (fun n : ℕ ↦ ‖inverseParameterResolventCurve A hA x (γs n)‖) atTop atTop
  exact norm_tendsto_atTop_of_inverseParameterResolventCurve_zeroRightSeq A hA x hzero hγs

end SetValuedOperator
