import BauschkeLean.Chap02.Lemma_2_42
import BauschkeLean.Chap02.Lemma_2_51
import BauschkeLean.Chap03.Corollary_3_35
import BauschkeLean.Chap08.Example_8_19
import BauschkeLean.Chap21.Corollary_21_14
import BauschkeLean.Chap23.Theorem_23_44

-- Semantic recall note: `lean_leansearch` only surfaced unrelated algebra-spectrum resolvent
-- theorems, so this item follows the verified local Chapter 23 owners `resolventMap` and
-- `A.zeros`, together with the Chapter 3 metric projection notation `P[...]`. The textbook
-- projector `P_{dom A}` is formalized on the closed convex set `closure A.dom`.

open scoped InnerProductSpace Pointwise SetValuedOperator Topology
open ERealFunction
open Filter

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 23.48: a maximally monotone operator has nonempty domain. This local
replacement avoids the broken `Corollary_21_20` import path while keeping the same mathematical
fact available to the proof. -/
private theorem dom_nonempty_of_maximal_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.dom.Nonempty := by
  -- If the domain were empty, the maximality test would force `(0, 0)` into the graph.
  by_contra hdom
  have hdom_empty : A.dom = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hdom ⟨x, hx⟩
  have hzero_mem : (0 : H) ∈ A (0 : H) := by
    refine (Maximal.mem_iff hA 0 0).2 ?_
    intro y v hv
    have hy_dom : y ∈ A.dom := (mem_dom_iff A y).2 ⟨v, hv⟩
    simp [hdom_empty] at hy_dom
  have hzero_dom : (0 : H) ∈ A.dom := (mem_dom_iff A 0).2 ⟨0, hzero_mem⟩
  exact hdom ⟨0, hzero_dom⟩

/-- Helper for Theorem 23.48: if `A : H → 2^H` is maximally monotone, then the closure of its
domain is Chebyshev. -/
theorem Maximal.closure_dom_isChebyshev
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    IsChebyshev (closure A.dom) := by
  exact
    isChebyshev_of_nonempty_isClosed_convex
      (Set.Nonempty.mono subset_closure (dom_nonempty_of_maximal_local A hA))
      isClosed_closure
      (convex_closure_dom_of_maximal A hA)

/-- Helper for Theorem 23.48: an eventual uniform distance bound from one point makes the whole
range of a sequence bounded. -/
private theorem bounded_range_of_eventually_norm_sub_le
    {H : Type u} [NormedAddCommGroup H]
    {u : ℕ → H} {z : H} {R : ℝ}
    (hR : ∀ᶠ n in atTop, ‖u n - z‖ ≤ R) :
    Bornology.IsBounded (Set.range u) := by
  rw [eventually_atTop] at hR
  rcases hR with ⟨N, hN⟩
  let s₀ : Set H := {y | ∃ n < N, u n = y}
  let s₁ : Set H := Set.range fun n : ℕ ↦ u (n + N)
  have hs₀_finite : s₀.Finite := by
    classical
    have hs₀_eq : s₀ = u '' {n : ℕ | n < N} := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
    rw [hs₀_eq]
    exact (Set.finite_lt_nat N).image u
  have hs₁_bounded : Bornology.IsBounded s₁ := by
    refine
      (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall z R)).subset ?_
    rintro y ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hN (n + N) (Nat.le_add_left N n)
  have hrange_subset : Set.range u ⊆ s₀ ∪ s₁ := by
    rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr ⟨n - N, by simp [Nat.sub_add_cancel (Nat.le_of_not_lt hn)]⟩
  exact (hs₀_finite.isBounded.union hs₁_bounded).subset hrange_subset

/-- Helper for Theorem 23.48: the canonical resolvent point realizes the graph pair
`(J_{γ A} x, γ⁻¹ • (x - J_{γ A} x)) ∈ gra A`. -/
private theorem resolventMap_mem_graph
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    (resolventMap A hA γ x, (γ : ℝ)⁻¹ • (x - resolventMap A hA γ x)) ∈ gra A := by
  -- The chosen resolvent point is the singleton-valued member of `J[γ • A] x`.
  have hmem :
      resolventMap A hA γ x ∈ J[((γ : ℝ) • A)] x := by
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x]
    simp
  exact (mem_resolvent_smul_iff_mem_graph A γ x (resolventMap A hA γ x)).1 hmem

/-- Helper for Theorem 23.48: squaring preserves the limsup of a bounded eventually nonnegative
real sequence. -/
private theorem sq_limsup_eq_limsup_sq_of_nonneg
    {a : ℕ → ℝ}
    (ha_nonneg : 0 ≤ᶠ[atTop] a)
    (ha_bdd : atTop.IsBoundedUnder (· ≤ ·) a) :
    (Filter.limsup a atTop) ^ 2 = Filter.limsup (fun n ↦ a n ^ 2) atTop := by
  let f : ℝ → ℝ := fun r ↦ max r 0 ^ 2
  have hf_mono : Monotone f := by
    intro r s hrs
    dsimp [f]
    have hmax : max r 0 ≤ max s 0 := max_le_max hrs le_rfl
    nlinarith [hmax, le_max_right r 0, le_max_right s 0]
  have hlimsup_nonneg : 0 ≤ Filter.limsup a atTop := by
    refine le_limsup_of_le ha_bdd ?_
    intro b hb
    rcases (hb.and ha_nonneg).exists with ⟨n, hn, hn'⟩
    exact hn'.trans hn
  have ha_cobdd : atTop.IsCoboundedUnder (· ≤ ·) a := by
    exact Filter.IsCoboundedUnder.of_frequently_ge (a := 0) ha_nonneg.frequently
  have hf_cont : ContinuousAt f (Filter.limsup a atTop) := by
    simpa [f] using ((continuous_id.max continuous_const).pow 2).continuousAt
  have hmap :
      f (Filter.limsup a atTop) = Filter.limsup (fun n ↦ f (a n)) atTop :=
    Monotone.map_limsup_of_continuousAt (F := atTop) (f := f) hf_mono a
      hf_cont ha_bdd ha_cobdd
  have hfg : ∀ᶠ n in atTop, f (a n) = a n ^ 2 := by
    refine ha_nonneg.mono ?_
    intro n hn
    have hn' : 0 ≤ a n := by simpa using hn
    simp [f, pow_two, max_eq_left hn']
  calc
    (Filter.limsup a atTop) ^ 2 = Filter.limsup (fun n ↦ f (a n)) atTop := by
      simpa [f, hlimsup_nonneg] using hmap
    _ = Filter.limsup (fun n ↦ a n ^ 2) atTop := Filter.limsup_congr hfg

/-- Helper for Theorem 23.48: squaring preserves the liminf of a bounded eventually nonnegative
real sequence. -/
private theorem sq_liminf_eq_liminf_sq_of_nonneg
    {a : ℕ → ℝ}
    (ha_nonneg : 0 ≤ᶠ[atTop] a)
    (ha_bdd : atTop.IsBoundedUnder (· ≤ ·) a) :
    (Filter.liminf a atTop) ^ 2 = Filter.liminf (fun n ↦ a n ^ 2) atTop := by
  let f : ℝ → ℝ := fun r ↦ max r 0 ^ 2
  have hf_mono : Monotone f := by
    intro r s hrs
    dsimp [f]
    have hmax : max r 0 ≤ max s 0 := max_le_max hrs le_rfl
    nlinarith [hmax, le_max_right r 0, le_max_right s 0]
  have ha_cobdd : atTop.IsCoboundedUnder (· ≥ ·) a := by
    exact ha_bdd.isCoboundedUnder_ge
  have ha_bddBelow : atTop.IsBoundedUnder (· ≥ ·) a :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0) ha_nonneg
  have hliminf_nonneg : 0 ≤ Filter.liminf a atTop := by
    exact le_liminf_of_le (hf := ha_cobdd) ha_nonneg
  have hf_cont : ContinuousAt f (Filter.liminf a atTop) := by
    simpa [f] using ((continuous_id.max continuous_const).pow 2).continuousAt
  have hmap :
      f (Filter.liminf a atTop) = Filter.liminf (fun n ↦ f (a n)) atTop :=
    Monotone.map_liminf_of_continuousAt (F := atTop) (f := f) hf_mono a
      hf_cont ha_cobdd ha_bddBelow
  have hfg : ∀ᶠ n in atTop, f (a n) = a n ^ 2 := by
    refine ha_nonneg.mono ?_
    intro n hn
    have hn' : 0 ≤ a n := by simpa using hn
    simp [f, pow_two, max_eq_left hn']
  calc
    (Filter.liminf a atTop) ^ 2 = Filter.liminf (fun n ↦ f (a n)) atTop := by
      simpa [f, hliminf_nonneg] using hmap
    _ = Filter.liminf (fun n ↦ a n ^ 2) atTop := Filter.liminf_congr hfg

/-- Helper for Theorem 23.48: the source inequality `(23.50)` on the canonical resolvent surface.
-/
private theorem resolventMap_normSq_sub_le_inner_add_mul_of_mem_graph
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (γ : PosReal) {y v : H} (hyv : (y, v) ∈ gra A) :
    ‖resolventMap A hA γ x - y‖ ^ 2 ≤
      ⟪resolventMap A hA γ x - y, x - y⟫_ℝ +
        (γ : ℝ) * ‖resolventMap A hA γ x - y‖ * ‖v‖ := by
  let u := resolventMap A hA γ x
  have hu_graph : (u, (γ : ℝ)⁻¹ • (x - u)) ∈ gra A := by
    simpa [u] using resolventMap_mem_graph A hA γ x
  -- Monotonicity compares the chosen resolvent graph point with the fixed graph point `(y, v)`.
  have hmono :
      0 ≤ ⟪u - y, (γ : ℝ)⁻¹ • (x - u) - v⟫_ℝ :=
    (isMonotone_iff A).1 hA.1 hu_graph hyv
  have hscaled :
      0 ≤
        (γ : ℝ) *
          ((((γ : ℝ)⁻¹ : ℝ) * ⟪u - y, x - u⟫_ℝ) - ⟪u - y, v⟫_ℝ) := by
    simpa [inner_sub_right, real_inner_smul_right] using mul_nonneg γ.2.le hmono
  have hbridge :
      0 ≤ ⟪u - y, x - u⟫_ℝ - (γ : ℝ) * ⟪u - y, v⟫_ℝ := by
    have hrew :
        (γ : ℝ) *
            ((((γ : ℝ)⁻¹ : ℝ) * ⟪u - y, x - u⟫_ℝ) - ⟪u - y, v⟫_ℝ) =
          ⟪u - y, x - u⟫_ℝ - (γ : ℝ) * ⟪u - y, v⟫_ℝ := by
      field_simp [γ.2.ne']
    simpa [hrew] using hscaled
  have hsplit :
      ⟪u - y, x - u⟫_ℝ =
        ⟪u - y, x - y⟫_ℝ - ‖u - y‖ ^ 2 := by
    have hdecomp : x - u = (x - y) - (u - y) := by
      abel_nf
    rw [hdecomp, inner_sub_right, real_inner_self_eq_norm_sq]
  have hmain :
      ‖u - y‖ ^ 2 ≤ ⟪u - y, x - y⟫_ℝ - (γ : ℝ) * ⟪u - y, v⟫_ℝ := by
    rw [hsplit] at hbridge
    linarith
  have hcross :
      ⟪u - y, x - y⟫_ℝ - (γ : ℝ) * ⟪u - y, v⟫_ℝ ≤
        ⟪u - y, x - y⟫_ℝ + (γ : ℝ) * ‖u - y‖ * ‖v‖ := by
    have hterm :
        -(γ : ℝ) * ⟪u - y, v⟫_ℝ ≤ (γ : ℝ) * ‖u - y‖ * ‖v‖ := by
      have hinner_lower : -(‖u - y‖ * ‖v‖) ≤ ⟪u - y, v⟫_ℝ :=
        (abs_le.mp (abs_real_inner_le_norm (u - y) v)).1
      have hinner_neg : -⟪u - y, v⟫_ℝ ≤ ‖u - y‖ * ‖v‖ := by
        linarith
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hinner_neg γ.2.le
    linarith
  exact hmain.trans hcross

/-- Helper for Theorem 23.48: every zero-right resolvent sequence is bounded. -/
private theorem bounded_range_resolventMap_of_zeroRightSeq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval) :
    Bornology.IsBounded (Set.range fun n ↦ resolventMap A hA (γs n) x) := by
  let u : ℕ → H := fun n ↦ resolventMap A hA (γs n) x
  rcases dom_nonempty_of_maximal_local A hA with ⟨y0, hy0_dom⟩
  rcases (mem_dom_iff A y0).1 hy0_dom with ⟨v0, hv0⟩
  have hγs_real :
      Tendsto (fun n ↦ ((γs n : PosReal) : ℝ)) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) := by
    simpa [atZeroRightWithinUnitInterval] using hγs
  have hlt_one : ∀ᶠ n in atTop, ((γs n : PosReal) : ℝ) < 1 := by
    have hmem :
        Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1) :=
      self_mem_nhdsWithin
    exact (hγs_real.eventually hmem).mono fun _ hn ↦ hn.2
  have hnorm_le :
      ∀ n, ‖u n - y0‖ ≤ ‖x - y0‖ + (γs n : ℝ) * ‖v0‖ := by
    intro n
    have hsq :
        ‖u n - y0‖ ^ 2 ≤ ‖u n - y0‖ * (‖x - y0‖ + (γs n : ℝ) * ‖v0‖) := by
      have hineq :=
        resolventMap_normSq_sub_le_inner_add_mul_of_mem_graph
          A hA x (γs n) (by simpa [mem_graph] using hv0)
      refine hineq.trans ?_
      have hinner := real_inner_le_norm (u n - y0) (x - y0)
      nlinarith [hinner, norm_nonneg (u n - y0), norm_nonneg (x - y0), norm_nonneg v0,
        (γs n).2.le]
    have ha_nonneg : 0 ≤ ‖u n - y0‖ := norm_nonneg _
    by_cases hzero : ‖u n - y0‖ = 0
    · simp [hzero]
      nlinarith [norm_nonneg (x - y0), norm_nonneg v0, (γs n).2.le]
    · have hpos : 0 < ‖u n - y0‖ := lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using hzero)
      have hmul :
          ‖u n - y0‖ * ‖u n - y0‖ ≤
            ‖u n - y0‖ * (‖x - y0‖ + (γs n : ℝ) * ‖v0‖) := by
        simpa [pow_two] using hsq
      exact le_of_mul_le_mul_left hmul hpos
  have hbound_eventually :
      ∀ᶠ n in atTop, ‖u n - y0‖ ≤ ‖x - y0‖ + ‖v0‖ := by
    filter_upwards [hlt_one] with n hn
    have hγ_le : ((γs n : PosReal) : ℝ) ≤ 1 := le_of_lt hn
    have hv_le : ((γs n : PosReal) : ℝ) * ‖v0‖ ≤ ‖v0‖ := by
      have hv_nonneg : 0 ≤ ‖v0‖ := norm_nonneg v0
      exact (mul_le_mul_of_nonneg_right hγ_le hv_nonneg).trans_eq (one_mul ‖v0‖)
    exact (hnorm_le n).trans (by linarith)
  exact bounded_range_of_eventually_norm_sub_le hbound_eventually

/-- Helper for Theorem 23.48: every weak sequential cluster point of a zero-right resolvent
sequence is the projection of `x` onto `closure A.dom`. -/
private theorem weakSequentialClusterPt_eq_projection_closureDom_of_zeroRightSeq
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval)
    {z : H}
    (hz :
      IsSequentialClusterPt
        (fun n ↦ toWeakSpace ℝ H (resolventMap A hA (γs n) x))
        (toWeakSpace ℝ H z)) :
    z = P[closure A.dom, Maximal.closure_dom_isChebyshev hA] x := by
  let u : ℕ → H := fun n ↦ resolventMap A hA (γs n) x
  have hbounded : Bornology.IsBounded (Set.range u) :=
    bounded_range_resolventMap_of_zeroRightSeq A hA x hγs
  have hu_dom : ∀ n, u n ∈ A.dom := by
    intro n
    refine (mem_dom_iff A (u n)).2 ?_
    refine ⟨(γs n : ℝ)⁻¹ • (x - u n), ?_⟩
    simpa [u, mem_graph] using resolventMap_mem_graph A hA (γs n) x
  rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφ_tendsto⟩
  have hz_mem_closure : z ∈ closure A.dom := by
    -- The weak limit of points in the closed convex set `closure A.dom` remains in that set.
    exact
      mem_of_tendsto_weakly_of_isClosed_convex
        (C := closure A.dom)
        isClosed_closure
        (convex_closure_dom_of_maximal A hA)
        (xₙ := fun n ↦ u (φ n))
        (x := z)
        (fun n ↦ subset_closure (hu_dom (φ n)))
        (by simpa [u] using hφ_tendsto)
  have huφ_bounded : Bornology.IsBounded (Set.range fun n ↦ u (φ n)) := by
    exact hbounded.subset (by rintro _ ⟨n, rfl⟩; exact ⟨φ n, rfl⟩)
  have hγs_real :
      Tendsto (fun n ↦ ((γs n : PosReal) : ℝ)) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) := by
    simpa [atZeroRightWithinUnitInterval] using hγs
  have hγφ_zero :
      Tendsto (fun n ↦ ((γs (φ n) : PosReal) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    exact (hγs_real.comp hφ.tendsto_atTop).trans nhdsWithin_le_nhds
  have hinner_dom :
      ∀ y ∈ A.dom, ⟪x - z, y - z⟫_ℝ ≤ 0 := by
    intro y hy
    rcases (mem_dom_iff A y).1 hy with ⟨v, hv⟩
    have hnorm_bdd :
        atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖u (φ n) - y‖) := by
      let R : ℝ := Classical.choose (huφ_bounded.subset_closedBall y)
      have hR : Set.range (fun n ↦ u (φ n)) ⊆ Metric.closedBall y R :=
        Classical.choose_spec (huφ_bounded.subset_closedBall y)
      refine Filter.isBoundedUnder_of ?_
      refine ⟨R, fun n ↦ ?_⟩
      have hmem : u (φ n) ∈ Metric.closedBall y R := hR (Set.mem_range_self n)
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hmem
    have hnorm_nonneg : 0 ≤ᶠ[atTop] fun n ↦ ‖u (φ n) - y‖ :=
      Eventually.of_forall fun n ↦ norm_nonneg _
    have hweak_sub :
        Tendsto (fun n ↦ toWeakSpace ℝ H (u (φ n) - y)) atTop
          (𝓝 (toWeakSpace ℝ H (z - y))) := by
      simpa [sub_eq_add_neg] using
        hφ_tendsto.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H y) atTop
            (𝓝 (toWeakSpace ℝ H y)))
    have hnorm_liminf :
        ‖z - y‖ ≤ Filter.liminf (fun n ↦ ‖u (φ n) - y‖) atTop :=
      norm_le_liminf_of_tendsto_weakly (fun n ↦ u (φ n) - y) (z - y) hweak_sub
    have hnormSq_liminf :
        ‖z - y‖ ^ 2 ≤ Filter.liminf (fun n ↦ ‖u (φ n) - y‖ ^ 2) atTop := by
      have hliminf_sq :
          (Filter.liminf (fun n ↦ ‖u (φ n) - y‖) atTop) ^ 2 =
            Filter.liminf (fun n ↦ ‖u (φ n) - y‖ ^ 2) atTop :=
        sq_liminf_eq_liminf_sq_of_nonneg hnorm_nonneg hnorm_bdd
      have hsq_le :
          ‖z - y‖ ^ 2 ≤ (Filter.liminf (fun n ↦ ‖u (φ n) - y‖) atTop) ^ 2 := by
        nlinarith [hnorm_liminf, norm_nonneg (z - y)]
      simpa [hliminf_sq] using hsq_le
    have hinner_tendsto :
        Tendsto (fun n ↦ ⟪u (φ n) - y, x - y⟫_ℝ) atTop (𝓝 ⟪z - y, x - y⟫_ℝ) := by
      simpa using
        (weakSpace_continuous_inner_right (x - y)).tendsto (toWeakSpace ℝ H (z - y)) |>.comp
          hweak_sub
    have hsmall_zero :
        Tendsto (fun n ↦ ((γs (φ n) : PosReal) : ℝ) * ‖u (φ n) - y‖ * ‖v‖) atTop (𝓝 0) := by
      have hprod_bdd :
          atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖u (φ n) - y‖ * ‖v‖) := by
        exact isBoundedUnder_le_mul_of_nonneg (Frequently.of_forall fun _ ↦ norm_nonneg _) hnorm_bdd
          (Eventually.of_forall fun _ ↦ norm_nonneg v)
          (Filter.isBoundedUnder_const : atTop.IsBoundedUnder (· ≤ ·) fun _ : ℕ ↦ ‖v‖)
      have hprod_norm_bdd :
          atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖‖u (φ n) - y‖ * ‖v‖‖) := by
        simpa [Function.comp, Real.norm_eq_abs, abs_of_nonneg, norm_nonneg] using hprod_bdd
      have hmul_zero :
          Tendsto (fun n ↦ ((γs (φ n) : PosReal) : ℝ) * (‖u (φ n) - y‖ * ‖v‖)) atTop (𝓝 0) :=
        Filter.Tendsto.zero_mul_isBoundedUnder_le hγφ_zero hprod_norm_bdd
      simpa [mul_assoc] using hmul_zero
    have hrhs_tendsto :
        Tendsto
          (fun n ↦
            ⟪u (φ n) - y, x - y⟫_ℝ +
              ((γs (φ n) : PosReal) : ℝ) * ‖u (φ n) - y‖ * ‖v‖)
          atTop
          (𝓝 ⟪z - y, x - y⟫_ℝ) := by
      simpa using hinner_tendsto.add hsmall_zero
    have hsq_bddBelow :
        atTop.IsBoundedUnder (· ≥ ·) (fun n ↦ ‖u (φ n) - y‖ ^ 2) := by
      refine Filter.isBoundedUnder_of_eventually_ge (a := 0) ?_
      exact Eventually.of_forall fun n : ℕ ↦ by
        simpa [pow_two] using mul_self_nonneg ‖u (φ n) - y‖
    have hliminf_le :
        Filter.liminf (fun n ↦ ‖u (φ n) - y‖ ^ 2) atTop ≤ ⟪z - y, x - y⟫_ℝ := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      have hrhs_eventually :
          ∀ᶠ n in atTop,
            ⟪u (φ n) - y, x - y⟫_ℝ +
                ((γs (φ n) : PosReal) : ℝ) * ‖u (φ n) - y‖ * ‖v‖ <
              ⟪z - y, x - y⟫_ℝ + ε := by
        exact hrhs_tendsto.eventually (Iio_mem_nhds <| by linarith)
      have hsq_eventually :
          ∀ᶠ n in atTop, ‖u (φ n) - y‖ ^ 2 ≤ ⟪z - y, x - y⟫_ℝ + ε := by
        refine (hrhs_eventually.and (Eventually.of_forall fun n ↦
          resolventMap_normSq_sub_le_inner_add_mul_of_mem_graph A hA x (γs (φ n))
            (by simpa [mem_graph] using hv))).mono ?_
        intro n hn
        exact hn.2.trans (le_of_lt hn.1)
      exact Filter.liminf_le_of_le hsq_bddBelow fun b hb ↦ by
        rcases (hb.and hsq_eventually).exists with ⟨n, hn, hn'⟩
        exact hn.trans hn'
    have hsq_le :
        ‖z - y‖ ^ 2 ≤ ⟪z - y, x - y⟫_ℝ := hnormSq_liminf.trans hliminf_le
    have hsplit :
        ⟪z - y, x - y⟫_ℝ = ‖z - y‖ ^ 2 + ⟪z - y, x - z⟫_ℝ := by
      have hdecomp : x - y = (z - y) + (x - z) := by
        abel_nf
      rw [hdecomp, inner_add_right, real_inner_self_eq_norm_sq]
    have hnonneg : 0 ≤ ⟪z - y, x - z⟫_ℝ := by
      rw [hsplit] at hsq_le
      linarith
    have hneg :
        ⟪x - z, y - z⟫_ℝ = -⟪z - y, x - z⟫_ℝ := by
      calc
        ⟪x - z, y - z⟫_ℝ = ⟪x - z, -(z - y)⟫_ℝ := by
          congr 2
          abel_nf
        _ = -⟪x - z, z - y⟫_ℝ := by rw [inner_neg_right]
        _ = -⟪z - y, x - z⟫_ℝ := by rw [real_inner_comm]
    linarith
  have hinner_closure :
      ∀ y ∈ closure A.dom, ⟪x - z, y - z⟫_ℝ ≤ 0 := by
    let S : Set H := {y : H | ⟪x - z, y - z⟫_ℝ ≤ 0}
    have hdom_subset : A.dom ⊆ S := by
      intro y hy
      exact hinner_dom y hy
    have hclosed : IsClosed S := by
      have hcont : Continuous fun y : H ↦ ⟪x - z, y - z⟫_ℝ :=
        continuous_const.inner (continuous_id.sub continuous_const)
      simpa [S] using isClosed_le hcont continuous_const
    have hclosure_subset : closure A.dom ⊆ S := closure_minimal hdom_subset hclosed
    intro y hy
    exact hclosure_subset hy
  -- The limit point satisfies the projection characterization on `closure A.dom`.
  exact
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
      (Maximal.closure_dom_isChebyshev hA) (convex_closure_dom_of_maximal A hA)).2
      ⟨hz_mem_closure, fun y hy ↦ by simpa [real_inner_comm] using hinner_closure y hy⟩

/-- Helper for Theorem 23.48: every zero-right resolvent sequence converges strongly to the
projection of `x` onto `closure A.dom`. -/
private theorem tendsto_resolventMap_of_zeroRightSeq_to_projection_closureDom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    {γs : ℕ → PosReal}
    (hγs : Tendsto γs atTop atZeroRightWithinUnitInterval) :
    Tendsto (fun n ↦ resolventMap A hA (γs n) x) atTop
      (nhds (P[closure A.dom, Maximal.closure_dom_isChebyshev hA] x)) := by
  let u : ℕ → H := fun n ↦ resolventMap A hA (γs n) x
  let p := P[closure A.dom, Maximal.closure_dom_isChebyshev hA] x
  have hbounded : Bornology.IsBounded (Set.range u) :=
    bounded_range_resolventMap_of_zeroRightSeq A hA x hγs
  have hcluster_eq :
      ∀ {y : H},
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H y) →
          y = p := by
    intro y hy
    simpa [u, p] using
      weakSequentialClusterPt_eq_projection_closureDom_of_zeroRightSeq A hA x hγs hy
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
    simpa [u, p, hy_eq] using hy
  have hp_char :
      p ∈ closure A.dom ∧ ∀ z ∈ closure A.dom, ⟪z - p, x - p⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (Maximal.closure_dom_isChebyshev hA) (convex_closure_dom_of_maximal A hA)).1 rfl
  have hγs_real :
      Tendsto (fun n ↦ ((γs n : PosReal) : ℝ)) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) := by
    simpa [atZeroRightWithinUnitInterval] using hγs
  have hγ_zero :
      Tendsto (fun n ↦ ((γs n : PosReal) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    hγs_real.trans nhdsWithin_le_nhds
  have hlimsup_sq_le :
      ∀ z ∈ A.dom, Filter.limsup (fun n ↦ ‖u n - z‖ ^ 2) atTop ≤ ⟪p - z, x - z⟫_ℝ := by
    intro z hz
    rcases (mem_dom_iff A z).1 hz with ⟨v, hv⟩
    have hnorm_nonneg : 0 ≤ᶠ[atTop] fun n ↦ ‖u n - z‖ :=
      Eventually.of_forall fun n ↦ norm_nonneg _
    have hnorm_bdd :
        atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖u n - z‖) := by
      let R : ℝ := Classical.choose (hbounded.subset_closedBall z)
      have hR : Set.range u ⊆ Metric.closedBall z R :=
        Classical.choose_spec (hbounded.subset_closedBall z)
      refine Filter.isBoundedUnder_of ?_
      refine ⟨R, fun n ↦ ?_⟩
      have hmem : u n ∈ Metric.closedBall z R := hR (Set.mem_range_self n)
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hmem
    have hweak_sub :
        Tendsto (fun n ↦ toWeakSpace ℝ H (u n - z)) atTop (𝓝 (toWeakSpace ℝ H (p - z))) := by
      simpa [sub_eq_add_neg] using
        hweak.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H z) atTop
            (𝓝 (toWeakSpace ℝ H z)))
    have hinner_tendsto :
        Tendsto (fun n ↦ ⟪u n - z, x - z⟫_ℝ) atTop (𝓝 ⟪p - z, x - z⟫_ℝ) := by
      simpa using
        (weakSpace_continuous_inner_right (x - z)).tendsto (toWeakSpace ℝ H (p - z)) |>.comp
          hweak_sub
    have hsmall_zero :
        Tendsto (fun n ↦ ((γs n : PosReal) : ℝ) * ‖u n - z‖ * ‖v‖) atTop (𝓝 0) := by
      have hprod_bdd :
          atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖u n - z‖ * ‖v‖) := by
        exact isBoundedUnder_le_mul_of_nonneg (Frequently.of_forall fun _ ↦ norm_nonneg _) hnorm_bdd
          (Eventually.of_forall fun _ ↦ norm_nonneg v)
          (Filter.isBoundedUnder_const : atTop.IsBoundedUnder (· ≤ ·) fun _ : ℕ ↦ ‖v‖)
      have hprod_norm_bdd :
          atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖‖u n - z‖ * ‖v‖‖) := by
        simpa [Function.comp, Real.norm_eq_abs, abs_of_nonneg, norm_nonneg] using hprod_bdd
      have hmul_zero :
          Tendsto (fun n ↦ ((γs n : PosReal) : ℝ) * (‖u n - z‖ * ‖v‖)) atTop (𝓝 0) :=
        Filter.Tendsto.zero_mul_isBoundedUnder_le hγ_zero hprod_norm_bdd
      simpa [mul_assoc] using hmul_zero
    have hrhs_tendsto :
        Tendsto
          (fun n ↦
            ⟪u n - z, x - z⟫_ℝ + ((γs n : PosReal) : ℝ) * ‖u n - z‖ * ‖v‖)
          atTop
          (𝓝 ⟪p - z, x - z⟫_ℝ) := by
      simpa using hinner_tendsto.add hsmall_zero
    have hsq_cobdd :
        atTop.IsCoboundedUnder (· ≤ ·) (fun n ↦ ‖u n - z‖ ^ 2) := by
      exact Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
        (Frequently.of_forall fun n ↦ by positivity)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hrhs_eventually :
        ∀ᶠ n in atTop,
          ⟪u n - z, x - z⟫_ℝ + ((γs n : PosReal) : ℝ) * ‖u n - z‖ * ‖v‖ <
            ⟪p - z, x - z⟫_ℝ + ε := by
      exact hrhs_tendsto.eventually (Iio_mem_nhds <| by linarith)
    have hsq_eventually :
        ∀ᶠ n in atTop, ‖u n - z‖ ^ 2 ≤ ⟪p - z, x - z⟫_ℝ + ε := by
      refine (hrhs_eventually.and (Eventually.of_forall fun n ↦
        resolventMap_normSq_sub_le_inner_add_mul_of_mem_graph A hA x (γs n)
          (by simpa [mem_graph] using hv))).mono ?_
      intro n hn
      exact hn.2.trans (le_of_lt hn.1)
    exact Filter.limsup_le_of_le hsq_cobdd hsq_eventually
  let g : H → ℝ := fun z ↦ (limsupDistanceFunction u z) ^ 2
  have hg_cont : Continuous g := by
    -- The limsup-distance function is `1`-Lipschitz on bounded ranges, so squaring preserves
    -- continuity on the nonnegative codomain.
    exact
      ((limsupDistanceFunction_convexOn_univ_and_lipschitzWith_one u hbounded).2.continuous).pow 2
  have hg_dom_le :
      ∀ z ∈ A.dom, g z ≤ ⟪p - z, x - z⟫_ℝ := by
    intro z hz
    have hnorm_nonneg : 0 ≤ᶠ[atTop] fun n ↦ ‖u n - z‖ :=
      Eventually.of_forall fun n ↦ norm_nonneg _
    have hnorm_bdd :
        atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖u n - z‖) := by
      let R : ℝ := Classical.choose (hbounded.subset_closedBall z)
      have hR : Set.range u ⊆ Metric.closedBall z R :=
        Classical.choose_spec (hbounded.subset_closedBall z)
      refine Filter.isBoundedUnder_of ?_
      refine ⟨R, fun n ↦ ?_⟩
      have hmem : u n ∈ Metric.closedBall z R := hR (Set.mem_range_self n)
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hmem
    have hsq_limsup :
        (Filter.limsup (fun n ↦ ‖u n - z‖) atTop) ^ 2 =
          Filter.limsup (fun n ↦ ‖u n - z‖ ^ 2) atTop :=
      sq_limsup_eq_limsup_sq_of_nonneg hnorm_nonneg hnorm_bdd
    have hsq_limsup_rev :
        (Filter.limsup (fun n ↦ ‖z - u n‖) atTop) ^ 2 =
          Filter.limsup (fun n ↦ ‖z - u n‖ ^ 2) atTop := by
      simpa [norm_sub_rev] using hsq_limsup
    calc
      g z = Filter.limsup (fun n ↦ ‖u n - z‖ ^ 2) atTop := by
        simpa [g, limsupDistanceFunction, dist_eq_norm, norm_sub_rev] using hsq_limsup_rev
      _ ≤ ⟪p - z, x - z⟫_ℝ := hlimsup_sq_le z hz
  rcases mem_closure_iff_seq_limit.mp hp_char.1 with ⟨zs, hzs_mem, hzs_tendsto⟩
  have hupper_zero :
      Tendsto (fun n ↦ ⟪p - zs n, x - zs n⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have hp_sub_zero : Tendsto (fun n ↦ p - zs n) atTop (𝓝 (0 : H)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ p) atTop (𝓝 p)).sub hzs_tendsto
    have hx_sub : Tendsto (fun n ↦ x - zs n) atTop (𝓝 (x - p)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x)).sub hzs_tendsto
    have hinner :
        Tendsto (fun n ↦ ⟪p - zs n, x - zs n⟫_ℝ) atTop (𝓝 ⟪(0 : H), x - p⟫_ℝ) := by
      simpa using Filter.Tendsto.inner hp_sub_zero hx_sub
    simpa using hinner
  have hg_seq_zero : Tendsto (fun n ↦ g (zs n)) atTop (𝓝 (0 : ℝ)) := by
    have hnonneg : ∀ n, 0 ≤ g (zs n) := by
      intro n
      exact sq_nonneg (limsupDistanceFunction u (zs n))
    have hupper : ∀ n, g (zs n) ≤ ⟪p - zs n, x - zs n⟫_ℝ := by
      intro n
      exact hg_dom_le (zs n) (hzs_mem n)
    exact squeeze_zero (fun n ↦ hnonneg n) hupper hupper_zero
  have hg_tendsto_p : Tendsto (fun n ↦ g (zs n)) atTop (𝓝 (g p)) :=
    hg_cont.tendsto p |>.comp hzs_tendsto
  have hgp_zero : g p = 0 := tendsto_nhds_unique hg_tendsto_p hg_seq_zero
  have hweak_sub :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u n - p)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [sub_eq_add_neg] using
      hweak.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H p) atTop
          (𝓝 (toWeakSpace ℝ H p)))
  have hnorm_bdd_p :
      atTop.IsBoundedUnder (· ≤ ·) (fun n ↦ ‖u n - p‖) := by
    let R : ℝ := Classical.choose (hbounded.subset_closedBall p)
    have hR : Set.range u ⊆ Metric.closedBall p R :=
      Classical.choose_spec (hbounded.subset_closedBall p)
    refine Filter.isBoundedUnder_of ?_
    refine ⟨R, fun n ↦ ?_⟩
    have hmem : u n ∈ Metric.closedBall p R := hR (Set.mem_range_self n)
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hmem
  have hlimsup_nonneg : 0 ≤ Filter.limsup (fun n ↦ ‖u n - p‖) atTop := by
    refine le_limsup_of_le hnorm_bdd_p ?_
    intro b hb
    rcases (hb.and (Eventually.of_forall fun n ↦ norm_nonneg (u n - p))).exists with ⟨n, hn, hn'⟩
    exact hn'.trans hn
  have hlimsup_zero :
      Filter.limsup (fun n ↦ ‖u n - p‖) atTop = 0 := by
    have hsq_zero :
        (Filter.limsup (fun n ↦ ‖u n - p‖) atTop) ^ 2 = 0 := by
      simpa [g, limsupDistanceFunction, dist_eq_norm, norm_sub_rev] using hgp_zero
    nlinarith [hsq_zero, hlimsup_nonneg]
  have hstrong_sub :
      Tendsto (fun n ↦ u n - p) atTop (𝓝 (0 : H)) := by
    exact
      (tendsto_iff_tendsto_weakly_and_limsup_norm_le (fun n ↦ u n - p) (0 : H)).2
        ⟨hweak_sub, by simp [hlimsup_zero]⟩
  -- Weak convergence plus the limsup-distance upgrade yields the strong limit `p`.
  simpa [u, p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hstrong_sub.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ p) atTop (𝓝 p))

/-- Helper for Theorem 23.48: inversion on `PosReal` sends `γ ↑ +∞` to `γ⁻¹ ↓ 0` through
`atZeroRightWithinUnitInterval`. -/
private theorem tendsto_inv_posReal_atTop_atZeroRightWithinUnitInterval :
    Filter.Tendsto (fun γ : PosReal ↦ γ⁻¹) Filter.atTop atZeroRightWithinUnitInterval := by
  -- Rewrite to the real-valued inverse and force the `γ⁻¹ < 1` side condition eventually.
  have hcoe_atTop : Tendsto (fun γ : PosReal ↦ ((γ : PosReal) : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    by_cases hb : b < 0
    · exact Eventually.of_forall fun γ ↦ hb.le.trans γ.2.le
    · let B : PosReal := ⟨max b 0 + 1, by positivity⟩
      filter_upwards [eventually_ge_atTop B] with γ hγ
      have hb_nonneg : 0 ≤ b := by linarith
      have hB : b ≤ (B : ℝ) := by
        dsimp [B]
        rw [max_eq_left hb_nonneg]
        linarith
      exact hB.trans hγ
  have hinv_pos :
      Tendsto (fun γ : PosReal ↦ (((γ⁻¹ : PosReal) : ℝ))) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    simpa using
      (tendsto_inv_atTop_nhdsGT_zero.comp hcoe_atTop)
  have hwithin :
      ∀ᶠ γ : PosReal in atTop, (((γ⁻¹ : PosReal) : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
    let γ₀ : PosReal := ⟨2, by positivity⟩
    filter_upwards [eventually_ge_atTop γ₀] with γ hγ
    constructor
    · exact (γ⁻¹).2
    · have hγ_real : (1 : ℝ) < (γ : ℝ) := by
        -- Compare `γ` with the explicit threshold `γ₀ = 2`.
        have hγ₀ : (γ₀ : ℝ) ≤ (γ : ℝ) := hγ
        have hγ₀_gt : (1 : ℝ) < (γ₀ : ℝ) := by
          simp [γ₀]
        linarith
      exact inv_lt_one_of_one_lt₀ hγ_real
  have hreal :
      Tendsto (fun γ : PosReal ↦ (((γ⁻¹ : PosReal) : ℝ))) atTop
        (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhds_of_tendsto_nhdsWithin hinv_pos, hwithin⟩
  simpa [atZeroRightWithinUnitInterval, Function.comp] using hreal

/-- Theorem 23.48 (1): if `A : H → 2^H` is maximally monotone, then the canonical resolvent curve
`γ ↦ resolventMap A γ x = J_{γ A} x` converges as `γ ↓ 0` to the metric projection of `x` onto
the closed convex set `closure A.dom`, which formalizes the textbook projector `P_{dom A}`. -/
theorem tendsto_resolventMap_atZeroRight_to_projection_closure_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H) :
    Filter.Tendsto (fun γ : PosReal ↦ resolventMap A hA γ x)
      atZeroRightWithinUnitInterval
      (nhds (P[closure A.dom, Maximal.closure_dom_isChebyshev hA] x)) := by
  haveI : atZeroRightWithinUnitInterval.IsCountablyGenerated := by
    dsimp [atZeroRightWithinUnitInterval]
    infer_instance
  -- Reduce the filter statement to the zero-right sequence theorem.
  apply Filter.tendsto_of_seq_tendsto
  intro γs hγs
  simpa [Function.comp] using
    tendsto_resolventMap_of_zeroRightSeq_to_projection_closureDom A hA x hγs

/-- Theorem 23.48 (2): if `A : H → 2^H` is maximally monotone and `zer A ≠ ∅`, then the canonical
resolvent curve `γ ↦ resolventMap A γ x = J_{γ A} x` converges to the metric projection of `x`
onto `A.zeros` as `γ ↑ +∞`. -/
theorem tendsto_resolventMap_atTop_of_zeros_nonempty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (hzero : A.zeros.Nonempty) :
    Filter.Tendsto (fun γ : PosReal ↦ resolventMap A hA γ x)
      Filter.atTop
      (nhds (P[A.zeros, Maximal.zeros_isChebyshev hA hzero] x)) := by
  -- Compose Theorem 23.44 with the inverse-parameter bridge `γ ↦ γ⁻¹`.
  have hcomp :
      Tendsto (fun γ : PosReal ↦ inverseParameterResolventCurve A hA x (γ⁻¹))
        atTop
        (nhds (P[A.zeros, Maximal.zeros_isChebyshev hA hzero] x)) :=
    (tendsto_resolventMap_atZeroRight_of_zeros_nonempty A hA x hzero).comp
      tendsto_inv_posReal_atTop_atZeroRightWithinUnitInterval
  refine hcomp.congr' ?_
  exact Eventually.of_forall fun γ ↦ by simp [inverseParameterResolventCurve]

/-- Theorem 23.48 (3): if `A : H → 2^H` is maximally monotone and `zer A = ∅`, then the canonical
resolvent values `J_{γ A} x`, realized as `resolventMap A γ x`, satisfy
`‖resolventMap A γ x‖ → +∞` as `γ ↑ +∞`. -/
theorem norm_resolventMap_tendsto_atTop_atTop_of_zeros_eq_empty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x : H)
    (hzero : A.zeros = ∅) :
    Filter.Tendsto (fun γ : PosReal ↦ ‖resolventMap A hA γ x‖)
      Filter.atTop
      Filter.atTop := by
  -- Compose the inverse-parameter divergence theorem with the same filter adapter.
  have hcomp :
      Tendsto (fun γ : PosReal ↦ ‖inverseParameterResolventCurve A hA x (γ⁻¹)‖)
        atTop
        atTop :=
    (norm_resolventMap_tendsto_atTop_atZeroRight_of_zeros_eq_empty A hA x hzero).comp
      tendsto_inv_posReal_atTop_atZeroRightWithinUnitInterval
  refine hcomp.congr' ?_
  exact Eventually.of_forall fun γ ↦ by simp [inverseParameterResolventCurve]

end SetValuedOperator
