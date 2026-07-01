/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part1

noncomputable section
open scoped Pointwise

section Chap02
section Section06

/-- Reverse inclusion for the relative interior of a direct sum. -/
lemma euclideanRelativeInterior_directSumSetEuclidean_superset (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p))) :
    directSumSetEuclidean m p (euclideanRelativeInterior m C1)
        (euclideanRelativeInterior p C2) ⊆
      euclideanRelativeInterior (m + p) (directSumSetEuclidean m p C1 C2) := by
  intro z hz
  have hz' := hz
  rw [directSumSetEuclidean_eq_image_appendAffineEquiv] at hz'
  rcases hz' with ⟨⟨x, y⟩, hxy, rfl⟩
  rcases hxy with ⟨hx, hy⟩
  rcases hx with ⟨hx_aff, ε1, hε1, hx_subset⟩
  rcases hy with ⟨hy_aff, ε2, hε2, hy_subset⟩
  have hx_subset' :
      Metric.closedBall x ε1 ∩ (affineSpan Real C1 : Set _) ⊆ C1 := by
    have hball_x :
        (fun v => x + v) '' (ε1 • euclideanUnitBall m) =
          Metric.closedBall x ε1 := by
      simpa using
        (translate_smul_unitBall_eq_closedBall (n := m) (a := x) (ε := ε1) hε1)
    simpa [hball_x] using hx_subset
  have hy_subset' :
      Metric.closedBall y ε2 ∩ (affineSpan Real C2 : Set _) ⊆ C2 := by
    have hball_y :
        (fun v => y + v) '' (ε2 • euclideanUnitBall p) =
          Metric.closedBall y ε2 := by
      simpa using
        (translate_smul_unitBall_eq_closedBall (n := p) (a := y) (ε := ε2) hε2)
    simpa [hball_y] using hy_subset
  have hz_aff :
      appendAffineEquiv m p (x, y) ∈
          (affineSpan Real (directSumSetEuclidean m p C1 C2) :
            Set (EuclideanSpace Real (Fin (m + p)))) := by
    have hpair :
        appendAffineEquiv m p (x, y) ∈
          directSumSetEuclidean m p (affineSpan Real C1 : Set _)
            (affineSpan Real C2 : Set _) := by
      have : appendAffineEquiv m p (x, y) ∈ (appendAffineEquiv m p) '' Set.prod
          (affineSpan Real C1 : Set _) (affineSpan Real C2 : Set _) := by
        exact ⟨(x, y), ⟨hx_aff, hy_aff⟩, rfl⟩
      simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using this
    have hpair' := hpair
    rw [← affineSpan_directSumSetEuclidean_eq (m := m) (p := p) (C1 := C1) (C2 := C2)] at hpair'
    exact hpair'
  have hcont_symm :
      Continuous ((appendAffineEquiv m p).symm :
        EuclideanSpace Real (Fin (m + p)) →
          EuclideanSpace Real (Fin m) × EuclideanSpace Real (Fin p)) :=
    (AffineEquiv.continuous_of_finiteDimensional (f := (appendAffineEquiv m p).symm))
  have hopen_prod : IsOpen (Metric.ball x ε1 ×ˢ Metric.ball y ε2) :=
    (Metric.isOpen_ball.prod Metric.isOpen_ball)
  have hopen :
      IsOpen ((appendAffineEquiv m p).symm ⁻¹' (Metric.ball x ε1 ×ˢ Metric.ball y ε2)) :=
    hopen_prod.preimage hcont_symm
  have hzball :
      appendAffineEquiv m p (x, y) ∈
        (appendAffineEquiv m p).symm ⁻¹' (Metric.ball x ε1 ×ˢ Metric.ball y ε2) := by
    change (appendAffineEquiv m p).symm (appendAffineEquiv m p (x, y)) ∈
      Metric.ball x ε1 ×ˢ Metric.ball y ε2
    have hxball : x ∈ Metric.ball x ε1 := Metric.mem_ball_self hε1
    have hyball : y ∈ Metric.ball y ε2 := Metric.mem_ball_self hε2
    have hzball' : (x, y) ∈ Metric.ball x ε1 ×ˢ Metric.ball y ε2 := ⟨hxball, hyball⟩
    convert hzball' using 1; simp
  rcases (Metric.isOpen_iff.mp hopen) (appendAffineEquiv m p (x, y)) hzball with
    ⟨δ, hδpos, hballδ⟩
  have hδpos2 : 0 < δ / 2 := by linarith [hδpos]
  refine ⟨hz_aff, δ / 2, hδpos2, ?_⟩
  intro w hw
  rcases hw with ⟨hw_ball, hw_aff⟩
  have hball_z :
      (fun v => appendAffineEquiv m p (x, y) + v) '' ((δ / 2) • euclideanUnitBall (m + p)) =
        Metric.closedBall (appendAffineEquiv m p (x, y)) (δ / 2) := by
    simpa using
      (translate_smul_unitBall_eq_closedBall (n := m + p)
        (a := appendAffineEquiv m p (x, y)) (ε := δ / 2) hδpos2)
  have hw_ball_closed :
      w ∈ Metric.closedBall (appendAffineEquiv m p (x, y)) (δ / 2) := by
    simpa [hball_z] using hw_ball
  have hw_ball' : w ∈ Metric.ball (appendAffineEquiv m p (x, y)) δ := by
    have hsub :
        Metric.closedBall (appendAffineEquiv m p (x, y)) (δ / 2) ⊆
          Metric.ball (appendAffineEquiv m p (x, y)) δ :=
      Metric.closedBall_subset_ball (by linarith [hδpos])
    exact hsub hw_ball_closed
  have hw_pre :
      (appendAffineEquiv m p).symm w ∈ Metric.ball x ε1 ×ˢ Metric.ball y ε2 :=
    hballδ hw_ball'
  rcases hw_pre with ⟨hwx_ball, hwy_ball⟩
  have hwx_closed :
      ((appendAffineEquiv m p).symm w).1 ∈ Metric.closedBall x ε1 :=
    Metric.ball_subset_closedBall hwx_ball
  have hwy_closed :
      ((appendAffineEquiv m p).symm w).2 ∈ Metric.closedBall y ε2 :=
    Metric.ball_subset_closedBall hwy_ball
  have hw_aff' :
      (appendAffineEquiv m p).symm w ∈ Set.prod (affineSpan Real C1 : Set _)
        (affineSpan Real C2 : Set _) := by
    have hw_aff'' :
        w ∈ (appendAffineEquiv m p) '' Set.prod (affineSpan Real C1 : Set _)
          (affineSpan Real C2 : Set _) := by
      have hw_aff''' :
          w ∈ directSumSetEuclidean m p (affineSpan Real C1) (affineSpan Real C2) := by
        have hw_aff''' := hw_aff
        have h_aff :=
          affineSpan_directSumSetEuclidean_eq (m := m) (p := p) (C1 := C1) (C2 := C2)
        rw [h_aff] at hw_aff'''
        exact hw_aff'''
      have hw_aff'' := hw_aff'''
      rw [directSumSetEuclidean_eq_image_appendAffineEquiv] at hw_aff''
      exact hw_aff''
    rcases hw_aff'' with ⟨xy, hxy, rfl⟩
    simpa using hxy
  rcases hw_aff' with ⟨hwx_aff, hwy_aff⟩
  have hwx_C1 : ((appendAffineEquiv m p).symm w).1 ∈ C1 :=
    hx_subset' ⟨hwx_closed, hwx_aff⟩
  have hwy_C2 : ((appendAffineEquiv m p).symm w).2 ∈ C2 :=
    hy_subset' ⟨hwy_closed, hwy_aff⟩
  have hw_in :
      w ∈ (appendAffineEquiv m p) '' Set.prod C1 C2 := by
    refine ⟨(appendAffineEquiv m p).symm w, ⟨hwx_C1, hwy_C2⟩, ?_⟩
    simp
  simpa [directSumSetEuclidean_eq_image_appendAffineEquiv] using hw_in

/-- Text 6.18: For the direct sum `C1 ⊕ C2` in `R^{m+p}` of convex sets
`C1 ⊆ R^m` and `C2 ⊆ R^p` (modeled as `directSumSetEuclidean m p C1 C2`),
one has `ri (C1 ⊕ C2) = ri C1 ⊕ ri C2` and `cl (C1 ⊕ C2) = cl C1 ⊕ cl C2`. -/
theorem euclideanRelativeInterior_directSumSetEuclidean_eq_and_closure_eq (m p : Nat)
    (C1 : Set (EuclideanSpace Real (Fin m))) (C2 : Set (EuclideanSpace Real (Fin p)))
    :
    euclideanRelativeInterior (m + p) (directSumSetEuclidean m p C1 C2) =
        directSumSetEuclidean m p (euclideanRelativeInterior m C1)
          (euclideanRelativeInterior p C2) ∧
      closure (directSumSetEuclidean m p C1 C2) =
        directSumSetEuclidean m p (closure C1) (closure C2) := by
  constructor
  · apply subset_antisymm
    · exact euclideanRelativeInterior_directSumSetEuclidean_subset m p C1 C2
    · exact euclideanRelativeInterior_directSumSetEuclidean_superset m p C1 C2
  · exact closure_directSumSetEuclidean_eq m p C1 C2

/-- Points in the closure lie in the affine span. -/
lemma mem_affineSpan_of_mem_closure {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)} (hy : y ∈ closure C) :
    y ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
  have hCsub : C ⊆ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
    intro z hz
    exact subset_affineSpan Real C hz
  have hclosed : IsClosed (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
    simpa using
      (AffineSubspace.closed_of_finiteDimensional (s := affineSpan Real C))
  have hclosure : closure C ⊆ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
    closure_minimal hCsub hclosed
  exact hclosure hy

/-- A point in a scaled unit ball has norm bounded by the scale. -/
lemma norm_le_of_mem_smul_unitBall {n : Nat} {ε : Real} (hε : 0 ≤ ε)
    {v : EuclideanSpace Real (Fin n)} (hv : v ∈ ε • euclideanUnitBall n) : ‖v‖ ≤ ε := by
  rcases hv with ⟨u, hu, rfl⟩
  have hu' : ‖u‖ ≤ (1 : Real) := by
    simpa [euclideanUnitBall] using hu
  have hmul : ε * ‖u‖ ≤ ε * (1 : Real) := mul_le_mul_of_nonneg_left hu' hε
  calc
    ‖ε • u‖ = ε * ‖u‖ := by
      simp [norm_smul, abs_of_nonneg hε]
    _ ≤ ε * (1 : Real) := hmul
    _ = ε := by simp

/-- If a point has norm at most `ε`, it lies in the scaled unit ball `ε • B`. -/
lemma mem_smul_unitBall_of_norm_le {n : Nat} {ε : Real} (hε : 0 < ε)
    {v : EuclideanSpace Real (Fin n)} (hv : ‖v‖ ≤ ε) :
    v ∈ ε • euclideanUnitBall n := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  refine ⟨(1 / ε) • v, ?_, ?_⟩
  · have hpos : 0 < (1 / ε) := by
      simpa [one_div] using (inv_pos.mpr hε)
    have hmul : (1 / ε) * ‖v‖ ≤ (1 / ε) * ε :=
      mul_le_mul_of_nonneg_left hv (le_of_lt hpos)
    have hnorm : ‖(1 / ε) • v‖ ≤ (1 : Real) := by
      have hnorm' : ‖(1 / ε) • v‖ = (1 / ε) * ‖v‖ := by
        have hpos' : 0 ≤ (1 / ε) := le_of_lt hpos
        calc
          ‖(1 / ε) • v‖ = ‖(1 / ε)‖ * ‖v‖ := norm_smul _ _
          _ = (1 / ε) * ‖v‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hpos']
      calc
        ‖(1 / ε) • v‖ = (1 / ε) * ‖v‖ := hnorm'
        _ ≤ (1 / ε) * ε := hmul
        _ = 1 := by field_simp [hε0]
    simpa [euclideanUnitBall] using hnorm
  · simp [smul_smul, hε0]

/-- Theorem 6.1: Let `C` be a convex set in `R^n`. Let `x ∈ ri C` and `y ∈ cl C`.
Then `(1 - λ) x + λ y` belongs to `ri C` (and hence in particular to `C`)
for `0 ≤ λ < 1`. -/
theorem euclideanRelativeInterior_convex_combination_mem (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (x y : EuclideanSpace Real (Fin n))
    (hx : x ∈ euclideanRelativeInterior n C)
    (hy : y ∈ closure C) (t : Real) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) • x + t • y ∈ euclideanRelativeInterior n C := by
  classical
  rcases hx with ⟨hx_aff, ε0, hε0, hxsub⟩
  set affC : Set (EuclideanSpace Real (Fin n)) :=
    (affineSpan Real C : Set (EuclideanSpace Real (Fin n)))
  have hy_aff : y ∈ affC := by
    simpa [affC] using (mem_affineSpan_of_mem_closure (n := n) (C := C) hy)
  have hxsub' :
      ((fun y => x + y) '' (ε0 • euclideanUnitBall n)) ∩ affC ⊆ C := by
    simpa [affC] using hxsub
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  have h1pt_pos : 0 < 1 + t := by
    linarith [ht0]
  have h1t_ne : 1 - t ≠ 0 := ne_of_gt ht1'
  have h1pt_ne : 1 + t ≠ 0 := ne_of_gt h1pt_pos
  set ε : Real := ε0 * (1 - t) / (1 + t)
  have hεpos : 0 < ε := by
    have hmul : 0 < ε0 * (1 - t) := mul_pos hε0 ht1'
    exact div_pos hmul h1pt_pos
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have hyCε : y ∈ C + ε • euclideanUnitBall n := by
    have hyi : y ∈ ⋂ ε : {ε : ℝ // 0 < ε}, C + ε.1 • euclideanUnitBall n := by
      simpa [euclidean_closure_eq_iInter_thickening] using hy
    have hyi' := (Set.mem_iInter).1 hyi ⟨ε, hεpos⟩
    simpa using hyi'
  have hp_aff : (1 - t) • x + t • y ∈ affC := by
    have h :=
      AffineMap.lineMap_mem (Q := affineSpan Real C) (p₀ := x) (p₁ := y) t hx_aff hy_aff
    simpa [affC, AffineMap.lineMap_apply_module] using h
  refine ⟨hp_aff, ε, hεpos, ?_⟩
  intro z hz
  rcases hz with ⟨hz1, hz2⟩
  rcases hz1 with ⟨w, hw, rfl⟩
  rcases hyCε with ⟨c, hc, b, hb, rfl⟩
  set u : EuclideanSpace Real (Fin n) :=
    x + (1 / (1 - t)) • (t • b + w)
  have hz_repr :
      (1 - t) • u + t • c = (1 - t) • x + t • c + (t • b + w) := by
    simp [u, smul_add, smul_smul, h1t_ne, one_div, add_assoc, add_left_comm, add_comm]
  have hz_aff : (1 - t) • x + t • (c + b) + w ∈ affC := by
    simpa [affC, add_assoc, add_left_comm, add_comm] using hz2
  have hxc_aff : (1 - t) • x + t • c ∈ affC := by
    have hc_aff : c ∈ affC := by
      simpa [affC] using (subset_affineSpan Real C hc)
    have h :=
      AffineMap.lineMap_mem (Q := affineSpan Real C) (p₀ := x) (p₁ := c) t hx_aff hc_aff
    simpa [affC, AffineMap.lineMap_apply_module] using h
  have hdir : (t • b + w) ∈ (affineSpan Real C).direction := by
    have hdir' :
        ((1 - t) • x + t • (c + b) + w) -ᵥ ((1 - t) • x + t • c) ∈
          (affineSpan Real C).direction :=
      AffineSubspace.vsub_mem_direction hz_aff hxc_aff
    simpa [vsub_eq_sub, smul_add, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using hdir'
  have hdir_scaled :
      (1 / (1 - t)) • (t • b + w) ∈ (affineSpan Real C).direction :=
    (affineSpan Real C).direction.smul_mem (1 / (1 - t)) hdir
  have hu_aff : u ∈ affC := by
    have hmem :
        (1 / (1 - t)) • (t • b + w) +ᵥ x ∈
          (affineSpan Real C : AffineSubspace Real (EuclideanSpace Real (Fin n))) :=
      AffineSubspace.vadd_mem_of_mem_direction hdir_scaled (by simpa [affC] using hx_aff)
    simpa [u, affC, vadd_eq_add, add_comm, add_left_comm, add_assoc] using hmem
  have hb_norm : ‖b‖ ≤ ε := norm_le_of_mem_smul_unitBall hεnonneg hb
  have hw_norm : ‖w‖ ≤ ε := norm_le_of_mem_smul_unitBall hεnonneg hw
  have htb_norm : ‖t • b‖ ≤ t * ε := by
    calc
      ‖t • b‖ = ‖t‖ * ‖b‖ := norm_smul _ _
      _ = t * ‖b‖ := by simp [Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ t * ε := by exact mul_le_mul_of_nonneg_left hb_norm ht0
  have hsum_norm : ‖t • b + w‖ ≤ ε * (1 + t) := by
    calc
      ‖t • b + w‖ ≤ ‖t • b‖ + ‖w‖ := norm_add_le _ _
      _ ≤ t * ε + ε := by exact add_le_add htb_norm hw_norm
      _ = ε * (1 + t) := by ring
  have hscale_norm : ‖(1 / (1 - t)) • (t • b + w)‖ ≤ ε0 := by
    have hpos : 0 ≤ (1 / (1 - t)) := by
      have hpos' : 0 < (1 / (1 - t)) := by
        simpa [one_div] using (inv_pos.mpr ht1')
      exact le_of_lt hpos'
    have hε_eq : ε * (1 + t) = ε0 * (1 - t) := by
      unfold ε
      field_simp [h1pt_ne]
    have hmul := mul_le_mul_of_nonneg_left hsum_norm hpos
    calc
      ‖(1 / (1 - t)) • (t • b + w)‖ =
          ‖(1 / (1 - t))‖ * ‖t • b + w‖ := by
        simpa using (norm_smul (1 / (1 - t)) (t • b + w))
      _ = (1 / (1 - t)) * ‖t • b + w‖ := by
        have hnorm : ‖(1 / (1 - t))‖ = (1 / (1 - t)) := Real.norm_of_nonneg hpos
        rw [hnorm]
      _ ≤ (1 / (1 - t)) * (ε * (1 + t)) := hmul
      _ = ε0 := by
        calc
          (1 / (1 - t)) * (ε * (1 + t)) = (1 / (1 - t)) * (ε0 * (1 - t)) := by
            simp [hε_eq]
          _ = ε0 := by
            field_simp [h1t_ne]
  have hu_ball :
      u ∈ (fun y => x + y) '' (ε0 • euclideanUnitBall n) := by
    refine ⟨(1 / (1 - t)) • (t • b + w), ?_, ?_⟩
    · exact mem_smul_unitBall_of_norm_le hε0 hscale_norm
    · simp [u]
  have hu : u ∈ C := by
    have hu_in :
        u ∈ ((fun y => x + y) '' (ε0 • euclideanUnitBall n)) ∩ affC := by
      refine ⟨hu_ball, ?_⟩
      simpa [affC] using hu_aff
    exact hxsub' hu_in
  have hzC : (1 - t) • u + t • c ∈ C := by
    have ht1le : t ≤ 1 := le_of_lt ht1
    have hzC' : AffineMap.lineMap u c t ∈ C :=
      hC.lineMap_mem hu hc ⟨ht0, ht1le⟩
    simpa [AffineMap.lineMap_apply_module] using hzC'
  have hz_eq :
      (1 - t) • x + (t • c + t • b) + w = (1 - t) • u + t • c := by
    calc
      (1 - t) • x + (t • c + t • b) + w
          = (1 - t) • x + t • c + (t • b + w) := by
            simp [add_assoc, add_left_comm, add_comm]
      _ = (1 - t) • u + t • c := hz_repr.symm
  simpa [hz_eq] using hzC

/-- The closure of a convex set is convex. -/
lemma convex_closure_of_convex (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) : Convex Real (closure C) := by
  have hball_convex : Convex Real (euclideanUnitBall n) :=
    (euclideanUnitBall_closed_convex n).2
  have hthick :
      ∀ ε : {ε : Real // 0 < ε}, Convex Real (C + ε.1 • euclideanUnitBall n) := by
    intro ε
    exact hC.add (hball_convex.smul ε.1)
  have hconv :
      Convex Real (⋂ ε : {ε : Real // 0 < ε}, C + ε.1 • euclideanUnitBall n) :=
    convex_iInter hthick
  simpa [euclidean_closure_eq_iInter_thickening] using hconv

end Section06
end Chap02
