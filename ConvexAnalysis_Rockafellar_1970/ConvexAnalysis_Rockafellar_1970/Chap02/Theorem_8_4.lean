import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open Bornology Filter Topology

/-
Source/core/bridge triage:
- `source-facing`: Theorem 8.4 states that a nonempty closed convex set `C` is bounded if
  and only if its recession cone `0⁺[𝕜] C` is trivial.
- `core/canonical`: the canonical owner-side boundedness API is `Bornology.IsBounded C`, and
  mathlib's direct boundedness criterion is stated on `asymptoticCone ℝ C`.
- `bridge/view`: this file exposes that canonical real asymptotic-cone criterion directly and
  then promotes the nonempty closed-convex statement to the scalar-`𝕜` asymptotic-cone owner
  before deriving the source-facing recession-cone bridge surface.
- Domain-style sampling: `recessionCone`,
  `isBounded_iff_asymptoticCone_subset_singleton`, `asymptoticCone_nonempty`,
  `Set.mem_recessionCone_iff`, and
  `Set.Nonempty.subset_singleton_iff`.
- Primitive data vs derived API: the primitive inputs are the set `C` and the source hypotheses
  that `C` is nonempty, closed, and convex; boundedness and triviality of the recession cone are
  the two equivalent derived properties.
- Abstraction-check answers:
  - codomain/ambient: no `EReal`-style codomain owner appears in this item; the ambient owner
    for the canonical boundedness criterion is `asymptoticCone ℝ`.
  - owner choice: the canonical owner theorem is exposed directly at the asymptotic-cone layer,
    and the source owner `0⁺[𝕜] C` is kept as a chapter-facing bridge surface.
  - intrinsic/relative topology: the source statement is not an ambient-vs-relative closure
    theorem; ambient `IsClosed C` remains part of the source-facing bridge surface.
- Layer target: expose the canonical asymptotic-cone subset criterion and its nonempty equality
  corollary at the owner layer, keep the recession-cone subset theorem as its source-facing bridge,
  and expose the source-facing equality as a thin corollary.
-/

namespace Convex

section Canonical

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- Canonical owner form for Theorem 8.4 at mathlib's asymptotic-cone layer.

This boundedness criterion is currently available in mathlib on the real asymptotic-cone API. -/
theorem isBounded_iff_asymptoticCone_subset_singleton_zero (C : Set P) :
    IsBounded C ↔ asymptoticCone ℝ C ⊆ ({0} : Set V) := by
  simpa using (isBounded_iff_asymptoticCone_subset_singleton (s := C))

/-- Nonempty-set equality corollary of the canonical asymptotic-cone owner criterion. -/
theorem isBounded_iff_asymptoticCone_eq_singleton_zero (C : Set P) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ asymptoticCone ℝ C = ({0} : Set V) := by
  have hcone_nonempty : (asymptoticCone ℝ C).Nonempty :=
    (asymptoticCone_nonempty (k := ℝ) (s := C)).2 hC_nonempty
  exact (isBounded_iff_asymptoticCone_subset_singleton_zero (C := C)).trans
    hcone_nonempty.subset_singleton_iff

end Canonical

section SourceFacing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [ProperSpace E]
variable {C : Set E}

/-- Nonempty-case helper for the scalar-`𝕜` asymptotic-cone boundedness criterion. -/
private theorem isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex_nonempty
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
  have not_isBounded_range_add_natCast_smul (x y : E) (hy : y ≠ 0) :
      ¬ IsBounded (Set.range fun n : ℕ => x + (n : 𝕜) • y) := by
    intro hbounded
    obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
    have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
    have hnorm : ‖x + (n : 𝕜) • y‖ ≤ R := by
      have hxR : x + (n : 𝕜) • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
    have hny : ‖(n : 𝕜)‖ * ‖y‖ ≤ R + ‖x‖ := by
      calc
        ‖(n : 𝕜)‖ * ‖y‖ = ‖(n : 𝕜) • y‖ := by
          simpa using (norm_smul (n : 𝕜) y).symm
        _ = ‖(x + (n : 𝕜) • y) - x‖ := by simp
        _ ≤ ‖x + (n : 𝕜) • y‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
    have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
    have hgt : R + ‖x‖ < ‖(n : 𝕜)‖ * ‖y‖ := by
      calc
        R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
        _ = ‖(n : 𝕜)‖ * ‖y‖ := by simp [norm_natCast]
    exact not_lt_of_ge hny hgt
  constructor
  · intro hC_bounded
    intro v hv
    by_contra hv0
    have hv_recession : v ∈ (0⁺[𝕜] C : Set E) := by
      simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using hv
    rcases hC_nonempty with ⟨x0, hx0⟩
    have hrange_subset : Set.range (fun n : ℕ => x0 + (n : 𝕜) • v) ⊆ C := by
      rintro _ ⟨n, rfl⟩
      exact (Set.mem_recessionCone_iff.mp hv_recession) x0 hx0 (n : 𝕜) (Nat.cast_nonneg n)
    exact
      not_isBounded_range_add_natCast_smul x0 v hv0
        (hC_bounded.subset hrange_subset)
  · intro hC_asymptotic_trivial
    by_contra hC_unbounded
    rcases hC_nonempty with ⟨x0, hx0⟩
    have h_unbounded_from_x0 : ∀ R : ℝ, ∃ x ∈ C, R < ‖x - x0‖ := by
      intro R
      by_contra hR
      push Not at hR
      apply hC_unbounded
      refine (isBounded_iff_forall_norm_le).2 ?_
      refine ⟨R + ‖x0‖, ?_⟩
      intro x hx
      calc
        ‖x‖ = ‖(x - x0) + x0‖ := by abel_nf
        _ ≤ ‖x - x0‖ + ‖x0‖ := norm_add_le _ _
        _ ≤ R + ‖x0‖ := add_le_add (hR x hx) le_rfl
    have hw : ∀ n : ℕ, ∃ x ∈ C, (n : ℝ) + 1 < ‖x - x0‖ := by
      intro n
      simpa using h_unbounded_from_x0 ((n : ℝ) + 1)
    choose w hwC hwgt using hw
    let r : ℕ → ℝ := fun n => ‖w n - x0‖ / ((n : ℝ) + 1)
    let m : ℕ → ℕ := fun n => Nat.floor (r n)
    let t : ℕ → 𝕜 := fun n => ((m n + 1 : ℕ) : 𝕜)⁻¹
    let y : ℕ → E := fun n => x0 + t n • (w n - x0)
    let a : ℕ → 𝕜 := fun n => ((n + 1 : ℕ) : 𝕜)
    let u : ℕ → E := fun n => (a n)⁻¹ • (y n - x0)
    have ht_nonneg : ∀ n : ℕ, 0 ≤ t n := by
      intro n
      dsimp [t]
      have hm1_pos : (0 : 𝕜) < (((m n) + 1 : ℕ) : 𝕜) := by
        exact_mod_cast Nat.succ_pos (m n)
      exact (inv_nonneg).2 hm1_pos.le
    have ht_le_one : ∀ n : ℕ, t n ≤ 1 := by
      intro n
      dsimp [t]
      have hm1_pos : (0 : 𝕜) < (((m n) + 1 : ℕ) : 𝕜) := by
        exact_mod_cast Nat.succ_pos (m n)
      have hcast_ge_one : (1 : 𝕜) ≤ (((m n) + 1 : ℕ) : 𝕜) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le (m n))
      have h := (one_div_le_one_div hm1_pos zero_lt_one).2 hcast_ge_one
      simpa [one_div] using h
    have hy_mem : ∀ n : ℕ, y n ∈ C := by
      intro n
      have hy_combo : y n = (1 - t n) • x0 + t n • w n := by
        dsimp [y]
        calc
          x0 + t n • (w n - x0) = x0 + (t n • w n - t n • x0) := by
            simp [smul_sub]
          _ = (1 - t n) • x0 + t n • w n := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_smul, one_smul, smul_add]
      have hconv :
          (1 - t n) • x0 + t n • w n ∈ C :=
        hC_convex hx0 (hwC n) (sub_nonneg.mpr (ht_le_one n)) (ht_nonneg n) (by ring)
      simpa [hy_combo] using hconv
    have ha_nonzero : ∀ n : ℕ, a n ≠ 0 := by
      intro n
      dsimp [a]
      exact_mod_cast Nat.succ_ne_zero n
    have ha_norm : ∀ n : ℕ, ‖a n‖ = (n : ℝ) + 1 := by
      intro n
      dsimp [a]
      simpa [Nat.cast_add] using (norm_natCast (α := 𝕜) (n + 1))
    have hu_mem : ∀ n : ℕ, a n • u n +ᵥ x0 ∈ C := by
      intro n
      have ha_ne : a n ≠ 0 := ha_nonzero n
      have hu_eq_smul : a n • u n = y n - x0 := by
        dsimp [u]
        calc
          a n • ((a n)⁻¹ • (y n - x0)) = (a n * (a n)⁻¹) • (y n - x0) := by
            simp [smul_smul]
          _ = (1 : 𝕜) • (y n - x0) := by rw [mul_inv_cancel₀ ha_ne]
          _ = y n - x0 := by simp
      have hu_eq : a n • u n +ᵥ x0 = y n := by
        calc
          a n • u n +ᵥ x0 = (y n - x0) +ᵥ x0 := by simpa [hu_eq_smul]
          _ = y n := by simpa [vadd_eq_add, sub_eq_add_neg, add_assoc]
      exact hu_eq ▸ hy_mem n
    have hu_lower : ∀ n : ℕ, (1 / 2 : ℝ) ≤ ‖u n‖ := by
      intro n
      have hden_pos : 0 < (n : ℝ) + 1 := by positivity
      have hr_gt_one : 1 < r n := by
        dsimp [r]
        exact (lt_div_iff₀ hden_pos).2 (by simpa using hwgt n)
      have hr_nonneg : 0 ≤ r n := le_of_lt (lt_trans zero_lt_one hr_gt_one)
      have hm_le : (m n : ℝ) ≤ r n := Nat.floor_le hr_nonneg
      have hm1_pos : 0 < (m n : ℝ) + 1 := by positivity
      have hm1_lt_2r : (m n : ℝ) + 1 < 2 * r n := by
        have hm1_le_r1 : (m n : ℝ) + 1 ≤ r n + 1 := by linarith [hm_le]
        linarith [hm1_le_r1, hr_gt_one]
      have hhalf_lt_r : ((m n : ℝ) + 1) / 2 < r n := by
        linarith [hm1_lt_2r]
      have hhalf_mul_lt : (((m n : ℝ) + 1) / 2) * ((n : ℝ) + 1) < ‖w n - x0‖ := by
        have : (((m n : ℝ) + 1) / 2) < ‖w n - x0‖ / ((n : ℝ) + 1) := by
          simpa [r] using hhalf_lt_r
        exact (lt_div_iff₀ hden_pos).1 this
      have hdist_lower : ((n : ℝ) + 1) / 2 < ‖w n - x0‖ / ((m n : ℝ) + 1) := by
        have hhalf_mul_lt' : (((n : ℝ) + 1) / 2) * ((m n : ℝ) + 1) < ‖w n - x0‖ := by
          simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hhalf_mul_lt
        exact (lt_div_iff₀ hm1_pos).2 hhalf_mul_lt'
      have hy_sub : y n - x0 = t n • (w n - x0) := by
        dsimp [y]
        simp
      have hy_norm :
          ‖y n - x0‖ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by
        have ht_norm : ‖t n‖ = (((m n : ℝ) + 1)⁻¹) := by
          have hm1_norm : ‖((m n : 𝕜) + (1 : 𝕜))‖ = ((m n : ℝ) + 1) := by
            simpa [Nat.cast_add] using (norm_natCast (α := 𝕜) (m n + 1))
          calc
            ‖t n‖ = ‖((m n : 𝕜) + (1 : 𝕜))⁻¹‖ := by simp [t, Nat.cast_add]
            _ = ‖((m n : 𝕜) + (1 : 𝕜))‖⁻¹ := norm_inv _
            _ = (((m n : ℝ) + 1)⁻¹) := by rw [hm1_norm]
        calc
          ‖y n - x0‖ = ‖t n • (w n - x0)‖ := by simpa [hy_sub]
          _ = ‖t n‖ * ‖w n - x0‖ := norm_smul _ _
          _ = (((m n : ℝ) + 1)⁻¹) * ‖w n - x0‖ := by simpa [ht_norm]
          _ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by ring
      have hu_norm :
          ‖u n‖ = ‖y n - x0‖ / ((n : ℝ) + 1) := by
        calc
          ‖u n‖ = ‖(a n)⁻¹ • (y n - x0)‖ := by rfl
          _ = ‖(a n)⁻¹‖ * ‖y n - x0‖ := norm_smul _ _
          _ = ‖a n‖⁻¹ * ‖y n - x0‖ := by simp [norm_inv]
          _ = ‖y n - x0‖ / ‖a n‖ := by ring
          _ = ‖y n - x0‖ / ((n : ℝ) + 1) := by simp [ha_norm n]
      have hy_lower_le : ((n : ℝ) + 1) / 2 ≤ ‖y n - x0‖ := by
        exact le_of_lt (by simpa [hy_norm] using hdist_lower)
      have : (1 / 2 : ℝ) * ((n : ℝ) + 1) ≤ ‖y n - x0‖ := by
        nlinarith [hy_lower_le]
      have hfinal : (1 / 2 : ℝ) ≤ ‖y n - x0‖ / ((n : ℝ) + 1) := by
        exact (le_div_iff₀ hden_pos).2 this
      simpa [hu_norm] using hfinal
    have hu_upper : ∀ n : ℕ, ‖u n‖ < 1 := by
      intro n
      have hden_pos : 0 < (n : ℝ) + 1 := by positivity
      have hm1_pos : 0 < (m n : ℝ) + 1 := by positivity
      have hr_lt : r n < (m n : ℝ) + 1 := by
        simpa [m] using Nat.lt_floor_add_one (r n)
      have hmul : ‖w n - x0‖ < ((m n : ℝ) + 1) * ((n : ℝ) + 1) := by
        have : ‖w n - x0‖ / ((n : ℝ) + 1) < (m n : ℝ) + 1 := by
          simpa [r] using hr_lt
        exact (div_lt_iff₀ hden_pos).1 this
      have hdist_upper : ‖w n - x0‖ / ((m n : ℝ) + 1) < (n : ℝ) + 1 := by
        exact (div_lt_iff₀ hm1_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
      have hy_sub : y n - x0 = t n • (w n - x0) := by
        dsimp [y]
        simp
      have hy_norm :
          ‖y n - x0‖ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by
        have ht_norm : ‖t n‖ = (((m n : ℝ) + 1)⁻¹) := by
          have hm1_norm : ‖((m n : 𝕜) + (1 : 𝕜))‖ = ((m n : ℝ) + 1) := by
            simpa [Nat.cast_add] using (norm_natCast (α := 𝕜) (m n + 1))
          calc
            ‖t n‖ = ‖((m n : 𝕜) + (1 : 𝕜))⁻¹‖ := by simp [t, Nat.cast_add]
            _ = ‖((m n : 𝕜) + (1 : 𝕜))‖⁻¹ := norm_inv _
            _ = (((m n : ℝ) + 1)⁻¹) := by rw [hm1_norm]
        calc
          ‖y n - x0‖ = ‖t n • (w n - x0)‖ := by simpa [hy_sub]
          _ = ‖t n‖ * ‖w n - x0‖ := norm_smul _ _
          _ = (((m n : ℝ) + 1)⁻¹) * ‖w n - x0‖ := by simpa [ht_norm]
          _ = ‖w n - x0‖ / ((m n : ℝ) + 1) := by ring
      have hu_norm :
          ‖u n‖ = ‖y n - x0‖ / ((n : ℝ) + 1) := by
        calc
          ‖u n‖ = ‖(a n)⁻¹ • (y n - x0)‖ := by rfl
          _ = ‖(a n)⁻¹‖ * ‖y n - x0‖ := norm_smul _ _
          _ = ‖a n‖⁻¹ * ‖y n - x0‖ := by simp [norm_inv]
          _ = ‖y n - x0‖ / ‖a n‖ := by ring
          _ = ‖y n - x0‖ / ((n : ℝ) + 1) := by simp [ha_norm n]
      have hy_lt : ‖y n - x0‖ < (n : ℝ) + 1 := by
        simpa [hy_norm] using hdist_upper
      have hfinal : ‖y n - x0‖ / ((n : ℝ) + 1) < 1 := by
        exact (div_lt_iff₀ hden_pos).2 (by simpa using hy_lt)
      simpa [hu_norm] using hfinal
    have hu_eventually_ball1 : ∀ᶠ n : ℕ in Filter.atTop, u n ∈ Metric.closedBall (0 : E) 1 := by
      exact Filter.Eventually.of_forall fun n ↦ by
        have hu_le : ‖u n‖ ≤ 1 := le_of_lt (hu_upper n)
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_le
    have hu_frequently_ball1 :
        ∃ᶠ n : ℕ in Filter.atTop, u n ∈ Metric.closedBall (0 : E) 1 :=
      hu_eventually_ball1.frequently
    obtain ⟨v, hv_ball2, hv_cluster⟩ :=
      (ProperSpace.isCompact_closedBall (x := (0 : E)) (r := 1)).exists_mapClusterPt_of_frequently
        hu_frequently_ball1
    have hu_eventually_half : ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) ≤ ‖u n‖ := by
      exact Filter.Eventually.of_forall hu_lower
    let S : Set E := {z : E | (1 / 2 : ℝ) ≤ ‖z‖}
    have hS_closed : IsClosed S := isClosed_le continuous_const continuous_norm
    have hv_memS : v ∈ S := by
      exact hS_closed.mem_of_mapClusterPt hv_cluster hu_eventually_half
    have hv_nonzero : v ≠ 0 := by
      have hv_norm_pos : 0 < ‖v‖ := by
        have hv_half : (1 / 2 : ℝ) ≤ ‖v‖ := hv_memS
        linarith
      exact norm_pos_iff.mp hv_norm_pos
    let l : Filter ℕ := Filter.atTop ⊓ Filter.comap u (𝓝 v)
    have hl_nebot : l.NeBot := by
      refine (Filter.neBot_inf_comap_iff_map).2 ?_
      simpa [l, MapClusterPt, ClusterPt, inf_comm] using hv_cluster
    haveI : l.NeBot := hl_nebot
    have ha_tendsto_atTop : Tendsto a Filter.atTop Filter.atTop := by
      simpa [a, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        (tendsto_atTop_add_const_right Filter.atTop (1 : 𝕜)
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ => (n : 𝕜)) Filter.atTop Filter.atTop))
    have h_a_tendsto : Tendsto a l Filter.atTop := ha_tendsto_atTop.mono_left inf_le_left
    have hu_tendsto : Tendsto u l (𝓝 v) := by
      show Filter.map u l ≤ 𝓝 v
      exact (Filter.map_le_iff_le_comap).2 inf_le_right
    have h_tendsto_asymptotic :
        Tendsto (fun n : ℕ => a n • u n +ᵥ x0) l (AffineSpace.asymptoticNhds 𝕜 E v) := by
      exact
        (h_a_tendsto.atTop_smul_nhds_tendsto_asymptoticNhds hu_tendsto).asymptoticNhds_vadd_const x0
    have hu_eventually_memC : ∀ᶠ n : ℕ in l, a n • u n +ᵥ x0 ∈ C := by
      exact Filter.Eventually.of_forall hu_mem
    have hv_asymptotic_mem : v ∈ asymptoticCone 𝕜 C := by
      rw [mem_asymptoticCone_iff]
      exact h_tendsto_asymptotic.frequently hu_eventually_memC.frequently
    have hv_zero : v = 0 := by
      exact Set.mem_singleton_iff.mp (hC_asymptotic_trivial hv_asymptotic_mem)
    exact hv_nonzero hv_zero

/-- Canonical owner form for Theorem 8.4 at the scalar-`𝕜` asymptotic-cone layer for closed
convex sets. -/
theorem isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) :
    IsBounded C ↔ asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
  by_cases hC_nonempty : C.Nonempty
  · simpa using
      isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex_nonempty
        (C := C) hC_convex hC_closed hC_nonempty
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    simp [hCempty, asymptoticCone_empty]

/-- Nonempty-case canonical owner corollary: under the source hypotheses, boundedness is
equivalent to singleton equality for the asymptotic cone. -/
theorem isBounded_iff_asymptoticCone_eq_singleton_zero_of_closed_convex
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ asymptoticCone 𝕜 C = ({0} : Set E) := by
  have hcone_nonempty : (asymptoticCone 𝕜 C).Nonempty :=
    (asymptoticCone_nonempty (k := 𝕜) (s := C)).2 hC_nonempty
  exact (hC_convex.isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
    hC_closed).trans hcone_nonempty.subset_singleton_iff

/-- Canonical source-owner bridge for Theorem 8.4: boundedness of `C` is equivalent to the
singleton-subset form `0⁺[𝕜] C ⊆ {0}`. -/
theorem isBounded_iff_recessionCone_subset_singleton_zero
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C ⊆ ({0} : Set E) := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    (hC_convex.isBounded_iff_asymptoticCone_subset_singleton_zero_of_closed_convex
      hC_closed)

/-- Theorem 8.4: a nonempty closed convex set `C` in a finite-dimensional normed `𝕜`-space is
bounded if and only if its recession cone consists of the zero vector alone. -/
theorem isBounded_iff_recessionCone_eq_singleton_zero
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (hC_nonempty : C.Nonempty) :
    IsBounded C ↔ 0⁺[𝕜] C = {0} := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    (hC_convex.isBounded_iff_asymptoticCone_eq_singleton_zero_of_closed_convex
      hC_closed hC_nonempty)

end SourceFacing

end Convex

end
