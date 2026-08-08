import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_18

-- Theorem-local interior-geometry helper for Lemma 13.19.

noncomputable section

open Matrix
open scoped BigOperators

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {l : ℕ}

variable {a : Fin l → E}

local notation "Ω" => convexHull ℝ (Set.range a)

namespace Lemma_13_19_InteriorWeights

/-- Helper for Lemma 13.19: a strictly positive simplex-weighted combination of the vertices lies
in the interior of the finite convex hull whenever that convex hull has nonempty interior. -/
theorem strictly_positive_stdSimplex_weighted_sum_mem_interior_convexHull
    {w : Fin l → ℝ}
    (hΩ : (interior Ω).Nonempty)
    (hw : w ∈ stdSimplex ℝ (Fin l))
    (hwPos : ∀ j, 0 < w j) :
    (∑ j, w j • a j) ∈ interior Ω := by
  -- Route correction: reuse the Assumption 13.18 barycentric-splitting proof with generic strictly
  -- positive simplex weights instead of the special initial-point record.
  have hspan : affineSpan ℝ (Set.range a) = ⊤ := by
    exact (interior_convexHull_nonempty_iff_affineSpan_eq_top).mp hΩ
  obtain ⟨s, hs, b, hb⟩ := AffineBasis.exists_affine_subbasis hspan
  classical
  haveI : Finite s := b.finite
  letI : Fintype s := Fintype.ofFinite s
  letI : Nonempty s := b.nonempty
  let y : E := Finset.univ.centroid ℝ b
  have hrange : Set.range b ⊆ Set.range a := by
    intro z hz
    rcases hz with ⟨p, rfl⟩
    simpa [hb] using hs p.2
  have hyΩ : y ∈ interior Ω := by
    -- The centroid of the extracted full-dimensional simplex stays interior to the larger hull.
    have hyb : y ∈ interior (convexHull ℝ (Set.range b)) := by
      simpa [y] using b.centroid_mem_interior_convexHull
    exact interior_mono (convexHull_mono hrange) hyb
  let σ : s → Fin l := fun p => Classical.choose (hs p.2)
  have hσ : ∀ p : s, a (σ p) = p := by
    intro p
    exact Classical.choose_spec (hs p.2)
  have hσ_injective : Function.Injective σ := by
    intro p q hpq
    apply Subtype.ext
    calc
      (p : E) = a (σ p) := by symm; exact hσ p
      _ = a (σ q) := by rw [hpq]
      _ = (q : E) := hσ q
  let e : s ↪ Fin l := ⟨σ, hσ_injective⟩
  let t : Finset (Fin l) := Finset.univ.map e
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun p : s ↦ w (σ p))
  have hm_pos : 0 < m := by
    -- The extracted representative coordinates inherit strict positivity from `hwPos`.
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun p _ ↦ hwPos (σ p)
  have hm_le : ∀ p : s, m ≤ w (σ p) := by
    -- The finite minimum is bounded above by every representative coordinate.
    intro p
    exact Finset.inf'_le _ (Finset.mem_univ p)
  have hs_card_pos_nat : 0 < Fintype.card s := Fintype.card_pos_iff.mpr b.nonempty
  have hs_card_pos : 0 < (Fintype.card s : ℝ) := by
    exact_mod_cast hs_card_pos_nat
  have hs_card_ne : (Fintype.card s : ℝ) ≠ 0 := ne_of_gt hs_card_pos
  let β : ℝ := (Fintype.card s : ℝ) * m
  have hβ_pos : 0 < β := by
    -- The peeled mass is a positive multiple of the positive minimum `m`.
    dsimp [β]
    positivity
  have hβ_le : β ≤ 1 := by
    -- The peeled representative mass cannot exceed the total simplex mass.
    calc
      β = ∑ p : s, m := by
        simp [β, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ∑ p : s, w (σ p) := by
        exact Finset.sum_le_sum fun p _ ↦ hm_le p
      _ = Finset.sum t fun i ↦ w i := by
        simpa [t, e] using (Finset.univ.sum_map e fun i : Fin l ↦ w i).symm
      _ ≤ ∑ i, w i := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro i hi; exact Finset.mem_univ i)
          (fun i _ _ ↦ hw.1 i)
      _ = 1 := hw.2
  have hcentroid : β • y = ∑ p : s, m • a (σ p) := by
    -- The peeled uniform mass is exactly the centroid contribution of the affine subbasis.
    calc
      β • y = β • ∑ p : s, b.coord p y • b p := by
        rw [b.linear_combination_coord_eq_self y]
      _ = ∑ p : s, β • (b.coord p y • b p) := by
        simpa using
          (Finset.smul_sum (s := Finset.univ) (r := β) (f := fun p : s ↦ b.coord p y • b p))
      _ = ∑ p : s, (β * b.coord p y) • b p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = ∑ p : s, (β * (Fintype.card s : ℝ)⁻¹) • b p := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa [Finset.card_univ] using
          congrArg (fun t : ℝ ↦ (β * t) • b p)
            (by
              rw [show y = Finset.univ.centroid ℝ b by rfl]
              simpa [Finset.card_univ] using
                b.coord_apply_centroid (Finset.mem_univ p))
      _ = ∑ p : s, m • b p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hβm : β * (Fintype.card s : ℝ)⁻¹ = m := by
          dsimp [β]
          calc
            ((Fintype.card s : ℝ) * m) * (Fintype.card s : ℝ)⁻¹
                = m * ((Fintype.card s : ℝ) * (Fintype.card s : ℝ)⁻¹) := by
                    ring
            _ = m := by
                rw [mul_inv_cancel₀ hs_card_ne, mul_one]
        rw [hβm]
      _ = ∑ p : s, m • a (σ p) := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa [hb, hσ p]
  let ρ : Fin l → ℝ := fun i ↦ w i - if i ∈ t then m else 0
  have hρ_nonneg : ∀ i, 0 ≤ ρ i := by
    -- Subtracting `m` only along the representative image preserves nonnegativity.
    intro i
    by_cases hi : i ∈ t
    · have hi_range : i ∈ Set.range σ := by
        simpa [t, e] using hi
      rcases hi_range with ⟨p, rfl⟩
      simpa [ρ, hi] using (sub_nonneg.mpr (hm_le p))
    · simpa [ρ, hi] using hw.1 i
  have hindicator_sum : (∑ i, if i ∈ t then m else 0) = β := by
    -- The indicator sum counts one copy of `m` for each point of the affine subbasis.
    calc
      (∑ i, if i ∈ t then m else 0) = Finset.sum t fun _ : Fin l ↦ m := by
        simpa using (Fintype.sum_ite_mem t fun _ : Fin l ↦ m)
      _ = β := by
        simp [β, t, e, Finset.card_map, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hρ_sum : (∑ i, ρ i) = 1 - β := by
    -- The residual weights carry exactly the unpeeled simplex mass.
    calc
      (∑ i, ρ i) = ∑ i, w i - ∑ i, if i ∈ t then m else 0 := by
        simp [ρ, Finset.sum_sub_distrib]
      _ = 1 - β := by
        rw [hw.2, hindicator_sum]
  have hsplit :
      ∑ i, w i • a i = ∑ i, ρ i • a i + β • y := by
    -- Split the original barycentric combination into residual and centroid contributions.
    calc
      ∑ i, w i • a i = ∑ i, (ρ i • a i + (if i ∈ t then m else 0) • a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hti : i ∈ t
        · simp [ρ, hti, sub_smul]
        · simp [ρ, hti, add_smul]
      _ = ∑ i, ρ i • a i + ∑ i, (if i ∈ t then m else 0) • a i := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i, ρ i • a i + Finset.sum t (fun i ↦ m • a i) := by
        congr 1
        simpa using (Fintype.sum_ite_mem t fun i : Fin l ↦ m • a i)
      _ = ∑ i, ρ i • a i + ∑ p : s, m • a (σ p) := by
        congr 1
        simpa [t, e] using (Finset.univ.sum_map e fun i : Fin l ↦ m • a i)
      _ = ∑ i, ρ i • a i + β • y := by
        rw [hcentroid]
  by_cases hβ1 : β = 1
  · have hρ_zero_sum : ∑ i, ρ i = 0 := by
      -- If `β = 1`, the residual simplex mass vanishes.
      simpa [hβ1] using hρ_sum
    have hρ_zero : ∀ i, ρ i = 0 := by
      -- Nonnegative residual weights with total sum zero are all zero.
      have hρ_eq_zero : ρ = 0 := (Fintype.sum_eq_zero_iff_of_nonneg hρ_nonneg).1 hρ_zero_sum
      intro i
      exact congrFun hρ_eq_zero i
    have hsum_eq_y : (∑ i, w i • a i) = y := by
      -- The peeled-mass decomposition collapses to the interior centroid.
      calc
        ∑ i, w i • a i = ∑ i, ρ i • a i + β • y := hsplit
        _ = 0 + 1 • y := by
            simp [hβ1, hρ_zero]
        _ = y := by simp
    simpa [hsum_eq_y] using hyΩ
  · have hβ_lt_one : β < 1 := lt_of_le_of_ne hβ_le hβ1
    have hden_pos : 0 < 1 - β := sub_pos.mpr hβ_lt_one
    let w' : Fin l → ℝ := fun i ↦ ρ i / (1 - β)
    let z : E := ∑ i, w' i • a i
    have hw'_nonneg : ∀ i, 0 ≤ w' i := by
      -- Normalizing the residual weights preserves nonnegativity.
      intro i
      exact div_nonneg (hρ_nonneg i) hden_pos.le
    have hw'_sum : ∑ i, w' i = 1 := by
      -- The normalized residual weights form a simplex point.
      calc
        ∑ i, w' i = (∑ i, ρ i) / (1 - β) := by
          simp [w', div_eq_mul_inv, Finset.sum_mul]
        _ = (1 - β) / (1 - β) := by
          rw [hρ_sum]
        _ = 1 := by
          field_simp [hden_pos.ne']
    have hzΩ : z ∈ Ω := by
      -- The normalized residual point is still a convex combination of the same vertices.
      exact weighted_sum_mem_convexHull_range (a := a) (w := w') hw'_nonneg hw'_sum rfl
    have hresidual : ∑ i, ρ i • a i = (1 - β) • z := by
      -- Rescaling the normalized residual point recovers the original residual barycentric sum.
      calc
        ∑ i, ρ i • a i = ∑ i, ((1 - β) * w' i) • a i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hwi : (1 - β) * w' i = ρ i := by
            dsimp [w']
            field_simp [hden_pos.ne']
          rw [← hwi]
        _ = (1 - β) • z := by
          rw [show z = ∑ i, w' i • a i by rfl]
          simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            (Finset.smul_sum (s := Finset.univ) (r := 1 - β) (f := fun i : Fin l ↦ w' i • a i)).symm
    have hsum_combo : ∑ i, w i • a i = (1 - β) • z + β • y := by
      -- The target weighted sum is a convex combination of a feasible point and an interior point.
      calc
        ∑ i, w i • a i = ∑ i, ρ i • a i + β • y := hsplit
        _ = (1 - β) • z + β • y := by
            rw [hresidual]
    have hcombo : (1 - β) • z + β • y ∈ interior Ω := by
      -- Any positive amount of the interior centroid pushes the whole combination into the interior.
      exact (convex_convexHull ℝ (Set.range a)).combo_self_interior_mem_interior
        hzΩ hyΩ (sub_nonneg.mpr hβ_le) hβ_pos (by ring)
    exact hsum_combo ▸ hcombo

end Lemma_13_19_InteriorWeights

end
