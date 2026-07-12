import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»
import DifferentialForms_Cartan_1970.III.section11.«0013_Proposition_5_2».WeightedLogPeriodicity
import DifferentialForms_Cartan_1970.III.section11.«0013_Proposition_5_2».PeriodParallelogramBoundary

open Filter
open scoped BigOperators Topology unitInterval
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: boundary order zero forces the divisor on the translated period
parallelogram to vanish on its frontier. -/
lemma divisor_eq_zero_on_frontier_of_boundary_order_zero
    {g : ℂ → ℂ} (z₀ : ℂ)
    (hg : Meromorphic g)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt g z = (0 : WithTop ℤ))
    {z : ℂ} (hz : z ∈ frontier (L.periodParallelogram z₀)) :
    divisor g (L.periodParallelogram z₀) z = 0 := by
  have hzK : z ∈ L.periodParallelogram z₀ := by
    exact (isCompact_periodParallelogram (L := L) z₀).isClosed.frontier_subset hz
  -- Rewrite the divisor through the meromorphic order and apply the boundary regularity
  -- hypothesis.
  simpa [hboundary z hz] using (hg.meromorphicOn.divisor_apply hzK)

/-- Helper for Proposition 5.2: the inverse basis map sends the first `Fin 2` coordinate to the
first basis coefficient. -/
lemma basis_equivFunL_symm_apply_zero (a b : ℝ) :
    L.basis.equivFun (L.basis.equivFunL.symm ![a, b]) 0 = a := by
  have h := congrFun (L.basis.equivFunL.apply_symm_apply ![a, b]) 0
  simpa using h

/-- Helper for Proposition 5.2: the inverse basis map sends the second `Fin 2` coordinate to the
second basis coefficient. -/
lemma basis_equivFunL_symm_apply_one (a b : ℝ) :
    L.basis.equivFun (L.basis.equivFunL.symm ![a, b]) 1 = b := by
  have h := congrFun (L.basis.equivFunL.apply_symm_apply ![a, b]) 1
  simpa using h

/-- Helper for Proposition 5.2: a frontier point of a period parallelogram has affine coordinates
in `[0, 1]^2`, and at least one coordinate lies on the boundary `{0, 1}`. -/
lemma frontier_periodParallelogram_coord_eq_zero_or_one {z z₀ : ℂ}
    (hz : z ∈ frontier (L.periodParallelogram z₀)) :
    ∃ t₁ t₂ : ℝ,
      0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      z = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂ ∧
      (t₁ = 0 ∨ t₁ = 1 ∨ t₂ = 0 ∨ t₂ = 1) := by
  let e : ℝ × ℝ ≃ₜ ℂ :=
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀)
  let square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have himage : e '' square = L.periodParallelogram z₀ := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hp₁, hp₂⟩
      refine ⟨p.1, p.2, hp₁.1, hp₁.2, hp₂.1, hp₂.2, ?_⟩
      -- Read the image point in period-basis coordinates.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
          z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
      rw [basis_pair_homeomorph_apply]
      simp [add_assoc]
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      refine ⟨(t₁, t₂), ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, ?_⟩
      -- The converse direction is the same affine-coordinate expansion.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (t₁, t₂) : ℂ) =
          z₀ + t₁ • L.ω₁ + t₂ • L.ω₂
      rw [basis_pair_homeomorph_apply]
      simp [add_assoc]
  have hz' : z ∈ e '' frontier square := by
    rw [e.image_frontier, himage]
    exact hz
  rcases hz' with ⟨p, hpfrontier, rfl⟩
  have hpcoords :
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) := by
    -- Transport the frontier condition back to the unit square.
    change p ∈ frontier (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) at hpfrontier
    have hpfrontier' :
        ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (p.2 = 0 ∨ p.2 = 1)) ∨
          ((p.1 = 0 ∨ p.1 = 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)) := by
      simpa only [frontier_prod_eq, closure_Icc, frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num),
        Set.mem_union, Set.mem_prod, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
        using hpfrontier
    rcases hpfrontier' with h | h
    · rcases h with ⟨hp₁, hp₂⟩
      rcases hp₂ with hp₂ | hp₂
      · exact ⟨hp₁.1, hp₁.2, by simpa [hp₂], by simpa [hp₂],
          Or.inr (Or.inr (Or.inl hp₂))⟩
      · exact ⟨hp₁.1, hp₁.2, by simpa [hp₂], by simpa [hp₂],
          Or.inr (Or.inr (Or.inr hp₂))⟩
    · rcases h with ⟨hp₁, hp₂⟩
      rcases hp₁ with hp₁ | hp₁
      · exact ⟨by simpa [hp₁], by simpa [hp₁], hp₂.1, hp₂.2, Or.inl hp₁⟩
      · exact ⟨by simpa [hp₁], by simpa [hp₁], hp₂.1, hp₂.2, Or.inr (Or.inl hp₁)⟩
  refine ⟨p.1, p.2, hpcoords.1, hpcoords.2.1, hpcoords.2.2.1, hpcoords.2.2.2.1, ?_,
    hpcoords.2.2.2.2⟩
  -- Translate the recovered square coordinates back to the actual period parallelogram.
  change
    z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
  rw [basis_pair_homeomorph_apply]
  simp [add_assoc]

/-- Helper for Proposition 5.2: lattice points have integral coordinates in the period basis. -/
lemma exists_int_basis_coords_of_mem_lattice {z : ℂ} (hz : z ∈ L.lattice) :
    ∃ m n : ℤ, L.basis.equivFun z 0 = m ∧ L.basis.equivFun z 1 = n := by
  obtain ⟨m, n, hmn⟩ := L.mem_lattice.mp hz
  have hmn' : z = (L.basis.equivFunL.symm ![(m : ℝ), (n : ℝ)] : ℂ) := by
    -- Repackage the lattice expansion through the inverse basis map.
    calc
      z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := hmn.symm
      _ = (L.basis.equivFunL.symm ![(m : ℝ), (n : ℝ)] : ℂ) := by
            symm
            simpa [smul_eq_mul] using
              (basis_pair_homeomorph_apply (L := L) ((m : ℝ), (n : ℝ)))
  refine ⟨m, n, ?_, ?_⟩
  · -- Read the first basis coordinate of the explicit lattice expansion.
    rw [hmn']
    simpa using basis_equivFunL_symm_apply_zero (L := L) (m : ℝ) (n : ℝ)
  · -- Read the second basis coordinate of the explicit lattice expansion.
    rw [hmn']
    simpa using basis_equivFunL_symm_apply_one (L := L) (m : ℝ) (n : ℝ)

/-- Helper for Proposition 5.2: a point of a period parallelogram has basis coordinates in
`[0, 1]^2` after subtracting the basepoint. -/
lemma basis_coords_sub_of_mem_periodParallelogram {z z₀ : ℂ}
    (hz : z ∈ L.periodParallelogram z₀) :
    ∃ u v : ℝ,
      0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      L.basis.equivFun (z - z₀) 0 = u ∧
      L.basis.equivFun (z - z₀) 1 = v := by
  rcases hz with ⟨u, v, hu0, hu1, hv0, hv1, hz⟩
  have hsub :
      z - z₀ = u • L.ω₁ + v • L.ω₂ := by
    -- Subtract the basepoint from the affine-coordinate description of `z`.
    calc
      z - z₀ = (z₀ + u • L.ω₁ + v • L.ω₂) - z₀ := by rw [hz]
      _ = u • L.ω₁ + v • L.ω₂ := by ring
  have hsub_coords : z - z₀ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
    -- Repackage the affine combination through the inverse basis map.
    calc
      z - z₀ = u • L.ω₁ + v • L.ω₂ := hsub
      _ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
            symm
            simpa [smul_eq_mul] using (basis_pair_homeomorph_apply (L := L) (u, v))
  have hcoord0 : L.basis.equivFun (z - z₀) 0 = u := by
    -- Read the first basis coordinate from the inverse basis map.
    rw [hsub_coords]
    simpa using basis_equivFunL_symm_apply_zero (L := L) u v
  have hcoord1 : L.basis.equivFun (z - z₀) 1 = v := by
    -- Read the second basis coordinate from the inverse basis map.
    rw [hsub_coords]
    simpa using basis_equivFunL_symm_apply_one (L := L) u v
  exact ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩

/-- Helper for Proposition 5.2: if a translated-boundary point is represented by `w` in the base
period parallelogram, then one of the representative coordinates must equal the chosen shift. -/
lemma representative_coord_eq_shift_of_translated_frontier
    {u v : ℝ} {z₀ z z₁ w : ℂ}
    (hz₁ : z₁ = z₀ + u • L.ω₁ + v • L.ω₂)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (hz : z ∈ frontier (L.periodParallelogram z₁))
    (hw : w ∈ L.periodParallelogram z₀)
    (hsub : w - z ∈ L.lattice) :
    L.basis.equivFun (w - z₀) 0 = u ∨ L.basis.equivFun (w - z₀) 1 = v := by
  obtain ⟨m, n, hm, hn⟩ := exists_int_basis_coords_of_mem_lattice (L := L) hsub
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hcoord0, hcoord1⟩ :=
    basis_coords_sub_of_mem_periodParallelogram (L := L) hw
  obtain ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, hz_eq, hedge⟩ :=
    frontier_periodParallelogram_coord_eq_zero_or_one (L := L) hz
  have hz_sub_eq : z - z₁ = (L.basis.equivFunL.symm ![t₁, t₂] : ℂ) := by
    -- The frontier coordinates are the basis coordinates after subtracting the translated basepoint.
    calc
      z - z₁ = t₁ • L.ω₁ + t₂ • L.ω₂ := by
        calc
          z - z₁ = (z₁ + t₁ • L.ω₁ + t₂ • L.ω₂) - z₁ := by rw [hz_eq]
          _ = t₁ • L.ω₁ + t₂ • L.ω₂ := by ring
      _ = (L.basis.equivFunL.symm ![t₁, t₂] : ℂ) := by
        symm
        simpa [smul_eq_mul] using (basis_pair_homeomorph_apply (L := L) (t₁, t₂))
  have hz_coord0 : L.basis.equivFun (z - z₁) 0 = t₁ := by
    -- Read the first frontier coordinate from the inverse basis map.
    rw [hz_sub_eq]
    simpa using basis_equivFunL_symm_apply_zero (L := L) t₁ t₂
  have hz_coord1 : L.basis.equivFun (z - z₁) 1 = t₂ := by
    -- Read the second frontier coordinate from the inverse basis map.
    rw [hz_sub_eq]
    simpa using basis_equivFunL_symm_apply_one (L := L) t₁ t₂
  have hz₁_sub_eq : z₁ - z₀ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
    -- The chosen translation vector has basis coordinates `(u, v)`.
    calc
      z₁ - z₀ = u • L.ω₁ + v • L.ω₂ := by
        calc
          z₁ - z₀ = (z₀ + u • L.ω₁ + v • L.ω₂) - z₀ := by rw [hz₁]
          _ = u • L.ω₁ + v • L.ω₂ := by ring
      _ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
        symm
        simpa [smul_eq_mul] using (basis_pair_homeomorph_apply (L := L) (u, v))
  have hz₁_coord0 : L.basis.equivFun (z₁ - z₀) 0 = u := by
    -- Read the first coordinate of the translation vector.
    rw [hz₁_sub_eq]
    simpa using basis_equivFunL_symm_apply_zero (L := L) u v
  have hz₁_coord1 : L.basis.equivFun (z₁ - z₀) 1 = v := by
    -- Read the second coordinate of the translation vector.
    rw [hz₁_sub_eq]
    simpa using basis_equivFunL_symm_apply_one (L := L) u v
  have hsum0 : a = m + t₁ + u := by
    -- The first representative coordinate splits into lattice, frontier, and translation parts.
    calc
      a = L.basis.equivFun (w - z₀) 0 := hcoord0.symm
      _ = L.basis.equivFun ((w - z) + ((z - z₁) + (z₁ - z₀))) 0 := by
            congr 1
            ring
      _ = L.basis.equivFun (w - z) 0 + (L.basis.equivFun (z - z₁) 0 + L.basis.equivFun (z₁ - z₀) 0) := by
            simp
      _ = m + t₁ + u := by
            rw [hm, hz_coord0, hz₁_coord0]
            ring
  have hsum1 : b = n + t₂ + v := by
    -- The second representative coordinate splits in the same way.
    calc
      b = L.basis.equivFun (w - z₀) 1 := hcoord1.symm
      _ = L.basis.equivFun ((w - z) + ((z - z₁) + (z₁ - z₀))) 1 := by
            congr 1
            ring
      _ = L.basis.equivFun (w - z) 1 + (L.basis.equivFun (z - z₁) 1 + L.basis.equivFun (z₁ - z₀) 1) := by
            simp
      _ = n + t₂ + v := by
            rw [hn, hz_coord1, hz₁_coord1]
            ring
  rcases hedge with ht₁ | ht₁ | ht₂ | ht₂
  · -- On the `t₁ = 0` edge, the first representative coordinate must be the chosen shift `u`.
    left
    have hm_gt_neg_one : (-1 : ℝ) < m := by
      have hsum0' : a = m + u := by simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.2, ha0, hsum0']
    have hm_lt_one : (m : ℝ) < 1 := by
      have hsum0' : a = m + u := by simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.1, ha1, hsum0']
    have hm_gt_neg_one' : (-1 : ℤ) < m := by exact_mod_cast hm_gt_neg_one
    have hm_lt_one' : m < 1 := by exact_mod_cast hm_lt_one
    have hm_zero : m = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 0 = a := hcoord0
      _ = u + m := by
            have hsum0' : a = m + u := by
              simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
            linarith
      _ = u := by simp [hm_zero]
  · -- On the `t₁ = 1` edge, integrality forces the lattice correction to be `-1`.
    left
    have hk_gt_neg_one : (-1 : ℝ) < (m + 1 : ℤ) := by
      have hsum0' : a = (m + 1 : ℤ) + u := by
        simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.2, ha0, hsum0']
    have hk_lt_one : (((m + 1 : ℤ) : ℝ)) < 1 := by
      have hsum0' : a = (m + 1 : ℤ) + u := by
        simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.1, ha1, hsum0']
    have hk_gt_neg_one' : (-1 : ℤ) < m + 1 := by exact_mod_cast hk_gt_neg_one
    have hk_lt_one' : m + 1 < 1 := by exact_mod_cast hk_lt_one
    have hk_zero : m + 1 = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 0 = a := hcoord0
      _ = u + ((m + 1 : ℤ) : ℝ) := by
            have hsum0' : a = (m + 1 : ℤ) + u := by
              simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
            linarith
      _ = u := by simp [hk_zero]
  · -- On the `t₂ = 0` edge, the second representative coordinate must be the chosen shift `v`.
    right
    have hn_gt_neg_one : (-1 : ℝ) < n := by
      have hsum1' : b = n + v := by simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.2, hb0, hsum1']
    have hn_lt_one : (n : ℝ) < 1 := by
      have hsum1' : b = n + v := by simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.1, hb1, hsum1']
    have hn_gt_neg_one' : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    have hn_lt_one' : n < 1 := by exact_mod_cast hn_lt_one
    have hn_zero : n = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 1 = b := hcoord1
      _ = v + n := by
            have hsum1' : b = n + v := by
              simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
            linarith
      _ = v := by simp [hn_zero]
  · -- On the `t₂ = 1` edge, integrality forces the second lattice correction to be `-1`.
    right
    have hk_gt_neg_one : (-1 : ℝ) < (n + 1 : ℤ) := by
      have hsum1' : b = (n + 1 : ℤ) + v := by
        simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.2, hb0, hsum1']
    have hk_lt_one : (((n + 1 : ℤ) : ℝ)) < 1 := by
      have hsum1' : b = (n + 1 : ℤ) + v := by
        simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.1, hb1, hsum1']
    have hk_gt_neg_one' : (-1 : ℤ) < n + 1 := by exact_mod_cast hk_gt_neg_one
    have hk_lt_one' : n + 1 < 1 := by exact_mod_cast hk_lt_one
    have hk_zero : n + 1 = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 1 = b := hcoord1
      _ = v + ((n + 1 : ℤ) : ℝ) := by
            have hsum1' : b = (n + 1 : ℤ) + v := by
              simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
            linarith
      _ = v := by simp [hk_zero]

/-- Helper for Proposition 5.2: every finite subset of `ℝ` misses some point of the open unit
interval. -/
lemma exists_point_Ioo_not_mem_finset (s : Finset ℝ) :
    ∃ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∉ s := by
  have hs : Set.Countable (↑s : Set ℝ) := s.finite_toSet.countable
  have hdense : Dense ((↑s : Set ℝ)ᶜ) := by
    simpa using (Set.Countable.dense_compl (𝕜 := ℝ) hs)
  have hnonempty : (Set.Ioo (0 : ℝ) 1).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    norm_num
  -- Intersect the dense complement of the finite set with the open unit interval.
  rcases hdense.inter_open_nonempty (Set.Ioo (0 : ℝ) 1) isOpen_Ioo hnonempty with ⟨u, hu, hus⟩
  refine ⟨u, hu, ?_⟩
  simpa [Set.mem_compl_iff] using hus

/-- Helper for Proposition 5.2: one can choose a translate of the period parallelogram whose two
shift coordinates avoid the finitely many coordinates of a prescribed finite support. -/
lemma period_parallelogram_shift_avoids_finite_boundary_coordinates
    {z₀ : ℂ} {S : Finset ℂ}
    (hS : (↑S : Set ℂ) ⊆ L.periodParallelogram z₀) :
    ∃ u v : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧ v ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ s ∈ S, L.basis.equivFun (s - z₀) 0 ≠ u ∧ L.basis.equivFun (s - z₀) 1 ≠ v := by
  classical
  let firstCoords : Finset ℝ := S.image fun s ↦ L.basis.equivFun (s - z₀) 0
  let secondCoords : Finset ℝ := S.image fun s ↦ L.basis.equivFun (s - z₀) 1
  obtain ⟨u, hu, hu_not_mem⟩ := exists_point_Ioo_not_mem_finset firstCoords
  obtain ⟨v, hv, hv_not_mem⟩ := exists_point_Ioo_not_mem_finset secondCoords
  refine ⟨u, v, hu, hv, ?_⟩
  intro s hs
  constructor
  · -- The first shift coordinate was chosen outside the first-coordinate image of `S`.
    intro hs_eq
    exact hu_not_mem <| Finset.mem_image.mpr ⟨s, hs, hs_eq⟩
  · -- The second shift coordinate was chosen outside the second-coordinate image of `S`.
    intro hs_eq
    exact hv_not_mem <| Finset.mem_image.mpr ⟨s, hs, hs_eq⟩

/-- Helper for Proposition 5.2: the quotient-section bijection `hπ` supplies a representative in
`P` for every lattice class. -/
lemma exists_section_representative_sub_mem_lattice
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (z : ℂ) :
    ∃ w : ℂ, w ∈ P ∧ w - z ∈ L.lattice := by
  rcases hπ.surjOn (show ((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) ∈ Set.univ by simp) with
    ⟨w, hwP, hwz⟩
  refine ⟨w, hwP, ?_⟩
  -- Equality in the quotient is exactly congruence modulo the lattice subgroup.
  rw [QuotientAddGroup.eq_iff_sub_mem] at hwz
  simpa using hwz

/-- Helper for Proposition 5.2: if one point has infinite meromorphic order, connectedness of `ℂ`
forces the divisor-weighted sums to vanish trivially. -/
lemma periodic_meromorphic_order_top_trivializes_weighted_divisor_sum
    {g : ℂ → ℂ}
    (hg : Meromorphic g)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (htop : ∃ z, meromorphicOrderAt g z = ⊤) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hnone_finite : ¬ ∃ u : Set.univ, meromorphicOrderAt g u.1 ≠ ⊤ := by
    intro hfinite
    have hforall_finite :
        ∀ u : Set.univ, meromorphicOrderAt g u.1 ≠ ⊤ :=
      (hg.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1 hfinite
    rcases htop with ⟨z, hz⟩
    exact hforall_finite ⟨z, by simp⟩ hz
  have htop_all : ∀ z : ℂ, meromorphicOrderAt g z = ⊤ := by
    intro z
    by_contra hz
    exact hnone_finite ⟨⟨z, by simp⟩, hz⟩
  have hroots_empty : roots = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rcases (hroots.mem_iff z).1 hz with ⟨hzP, hzpos⟩
    have hdiv : divisor g P z = 0 := by
      rw [hg.meromorphicOn.divisor_apply hzP, htop_all z]
      simp
    exact (show ¬ 0 < divisor g P z by simpa [hdiv]) hzpos
  have hpoles_empty : poles = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rcases (hpoles.mem_iff z).1 hz with ⟨hzP, hzneg⟩
    have hdiv : divisor g P z = 0 := by
      rw [hg.meromorphicOn.divisor_apply hzP, htop_all z]
      simp
    exact (show ¬ divisor g P z < 0 by simpa [hdiv]) hzneg
  -- Once both representative finsets are empty, the quotient-valued sums are both zero.
  simp [hroots_empty, hpoles_empty]

/-- Helper for Proposition 5.2: in the finite-order branch, one can translate the period
parallelogram so that its boundary avoids every zero and pole represented by the fixed section
`P`. -/
lemma exists_boundary_regular_translate_for_finite_order_support
    {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hfinite : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles) :
    ∃ z₁ : ℂ, ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ) := by
  -- Route correction: the source proof first chooses a translated period parallelogram whose
  -- boundary misses the divisor support before any contour integral is computed.
  let S : Finset ℂ := roots ∪ poles
  have hS : (↑S : Set ℂ) ⊆ L.periodParallelogram z₀ := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hP ((hroots.mem_iff z).1 hz).1
    · exact hP ((hpoles.mem_iff z).1 hz).1
  obtain ⟨u, v, hu, hv, havoid⟩ :=
    period_parallelogram_shift_avoids_finite_boundary_coordinates
      (L := L) (z₀ := z₀) (S := S) hS
  let z₁ : ℂ := z₀ + u • L.ω₁ + v • L.ω₂
  refine ⟨z₁, ?_⟩
  intro z hz
  by_contra hz_ne_zero
  obtain ⟨w, hwP, hwsub⟩ :=
    exists_section_representative_sub_mem_lattice (L := L) (P := P) hπ z
  have hwPar : w ∈ L.periodParallelogram z₀ := hP hwP
  have hcoord :
      L.basis.equivFun (w - z₀) 0 = u ∨ L.basis.equivFun (w - z₀) 1 = v :=
    representative_coord_eq_shift_of_translated_frontier
      (L := L) (z₀ := z₀) (z₁ := z₁) (z := z) (w := w) rfl hu hv hz hwPar hwsub
  have horder_w :
      meromorphicOrderAt g w = meromorphicOrderAt g z := by
    -- Transport the boundary order back to the chosen section representative.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (meromorphicOrderAt_add_period_eq
        (L := L) (g := g) hperiods (z := z) (ω := w - z) hwsub)
  have hdiv_ne_zero : divisor g P w ≠ 0 := by
    intro hdiv_zero
    have horder_zero_or_top :
        meromorphicOrderAt g w = (0 : WithTop ℤ) ∨ meromorphicOrderAt g w = ⊤ := by
      have horder_untop_zero : (meromorphicOrderAt g w).untop₀ = 0 := by
        simpa [hg.meromorphicOn.divisor_apply hwP] using hdiv_zero
      exact WithTop.untop₀_eq_zero.mp horder_untop_zero
    rcases horder_zero_or_top with horder_zero | horder_top
    · exact hz_ne_zero (by simpa [horder_w] using horder_zero)
    · exact hfinite w horder_top
  have hw_mem_support : w ∈ S := by
    -- A nonzero finite divisor at the section representative forces membership in `roots ∪ poles`.
    rcases lt_or_gt_of_ne hdiv_ne_zero with hdiv_neg | hdiv_pos
    · exact Finset.mem_union.mpr <| Or.inr ((hpoles.mem_iff w).2 ⟨hwP, hdiv_neg⟩)
    · exact Finset.mem_union.mpr <| Or.inl ((hroots.mem_iff w).2 ⟨hwP, hdiv_pos⟩)
  have havoid_w := havoid w hw_mem_support
  rcases hcoord with hcoord0 | hcoord1
  · exact havoid_w.1 hcoord0
  · exact havoid_w.2 hcoord1

/-- Helper for Proposition 5.2: a point of the closed period parallelogram whose affine period
coordinates hit one of the four boundary values `0` or `1` lies on the frontier. -/
lemma mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
    {z₀ : ℂ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hedge : u = 0 ∨ u = 1 ∨ v = 0 ∨ v = 1) :
    z₀ + u • L.ω₁ + v • L.ω₂ ∈ frontier (L.periodParallelogram z₀) := by
  let e : ℝ × ℝ ≃ₜ ℂ :=
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀)
  let square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have himage : e '' square = L.periodParallelogram z₀ := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hp₁, hp₂⟩
      refine ⟨p.1, p.2, hp₁.1, hp₁.2, hp₂.1, hp₂.2, ?_⟩
      -- Read the image point through the basis-coordinate homeomorphism.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
          z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
      rw [basis_pair_homeomorph_apply]
      simp [e, add_assoc]
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      refine ⟨(t₁, t₂), ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, ?_⟩
      -- The converse direction is the same affine-coordinate expansion.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (t₁, t₂) : ℂ) =
          z₀ + t₁ • L.ω₁ + t₂ • L.ω₂
      rw [basis_pair_homeomorph_apply]
      simp [e, add_assoc]
  have hpfrontier : (u, v) ∈ frontier square := by
    rw [frontier_prod_eq]
    rcases hedge with rfl | rfl | rfl | rfl
    · right
      refine ⟨?_, subset_closure ?_⟩
      · rw [frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
        simp [hu1]
      · exact ⟨hv0, hv1⟩
    · right
      refine ⟨?_, subset_closure ?_⟩
      · rw [frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
        simp [hu0]
      · exact ⟨hv0, hv1⟩
    · left
      refine ⟨subset_closure ?_, ?_⟩
      · exact ⟨hu0, hu1⟩
      · rw [frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
        simp [hv1]
    · left
      refine ⟨subset_closure ?_, ?_⟩
      · exact ⟨hu0, hu1⟩
      · rw [frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
        simp [hv0]
  have himage_frontier :
      z₀ + u • L.ω₁ + v • L.ω₂ ∈ e '' frontier square := by
    refine ⟨(u, v), hpfrontier, ?_⟩
    -- Translate the square boundary point through the basis homeomorphism.
    change
      z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
        (u, v) : ℂ) =
        z₀ + u • L.ω₁ + v • L.ω₂
    rw [basis_pair_homeomorph_apply]
    simp [e, add_assoc]
  have hfrontier_image :
      z₀ + u • L.ω₁ + v • L.ω₂ ∈ frontier (e '' square) := by
    simpa [e.image_frontier] using himage_frontier
  simpa [himage] using hfrontier_image

/-- Helper for Proposition 5.2: two interior points of the same period parallelogram that differ
by a lattice vector must coincide. -/
lemma eq_of_mem_interior_periodParallelogram_and_sub_mem_lattice
    {z z' z₀ : ℂ}
    (hz : z ∈ interior (L.periodParallelogram z₀))
    (hz' : z' ∈ interior (L.periodParallelogram z₀))
    (hsub : z - z' ∈ L.lattice) :
    z = z' := by
  rcases interior_subset hz with ⟨u₁, v₁, hu₁0, hu₁1, hv₁0, hv₁1, rfl⟩
  rcases interior_subset hz' with ⟨u₂, v₂, hu₂0, hu₂1, hv₂0, hv₂1, rfl⟩
  have hu₁_ne0 : u₁ ≠ 0 := by
    intro hu₁_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz)).1 hz <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₁0 hu₁1 hv₁0 hv₁1 (Or.inl hu₁_eq)
  have hu₁_ne1 : u₁ ≠ 1 := by
    intro hu₁_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz)).1 hz <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₁0 hu₁1 hv₁0 hv₁1 (Or.inr <| Or.inl hu₁_eq)
  have hv₁_ne0 : v₁ ≠ 0 := by
    intro hv₁_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz)).1 hz <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₁0 hu₁1 hv₁0 hv₁1 (Or.inr <| Or.inr <| Or.inl hv₁_eq)
  have hv₁_ne1 : v₁ ≠ 1 := by
    intro hv₁_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz)).1 hz <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₁0 hu₁1 hv₁0 hv₁1 (Or.inr <| Or.inr <| Or.inr hv₁_eq)
  have hu₂_ne0 : u₂ ≠ 0 := by
    intro hu₂_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz')).1 hz' <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₂0 hu₂1 hv₂0 hv₂1 (Or.inl hu₂_eq)
  have hu₂_ne1 : u₂ ≠ 1 := by
    intro hu₂_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz')).1 hz' <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₂0 hu₂1 hv₂0 hv₂1 (Or.inr <| Or.inl hu₂_eq)
  have hv₂_ne0 : v₂ ≠ 0 := by
    intro hv₂_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz')).1 hz' <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₂0 hu₂1 hv₂0 hv₂1 (Or.inr <| Or.inr <| Or.inl hv₂_eq)
  have hv₂_ne1 : v₂ ≠ 1 := by
    intro hv₂_eq
    exact (mem_interior_iff_notMem_frontier (interior_subset hz')).1 hz' <|
      mem_frontier_periodParallelogram_of_coord_eq_zero_or_one
        (L := L) hu₂0 hu₂1 hv₂0 hv₂1 (Or.inr <| Or.inr <| Or.inr hv₂_eq)
  have hu₁_lt : u₁ < 1 := lt_of_le_of_ne hu₁1 hu₁_ne1
  have hv₁_lt : v₁ < 1 := lt_of_le_of_ne hv₁1 hv₁_ne1
  have hu₂_lt : u₂ < 1 := lt_of_le_of_ne hu₂1 hu₂_ne1
  have hv₂_lt : v₂ < 1 := lt_of_le_of_ne hv₂1 hv₂_ne1
  have hu₁_pos : 0 < u₁ := lt_of_le_of_ne hu₁0 (by simpa [eq_comm] using hu₁_ne0)
  have hv₁_pos : 0 < v₁ := lt_of_le_of_ne hv₁0 (by simpa [eq_comm] using hv₁_ne0)
  have hu₂_pos : 0 < u₂ := lt_of_le_of_ne hu₂0 (by simpa [eq_comm] using hu₂_ne0)
  have hv₂_pos : 0 < v₂ := lt_of_le_of_ne hv₂0 (by simpa [eq_comm] using hv₂_ne0)
  obtain ⟨m, n, hm, hn⟩ := exists_int_basis_coords_of_mem_lattice (L := L) hsub
  have hcoord0 :
      L.basis.equivFun
          ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂)) 0 =
        u₁ - u₂ := by
    have hpair :
        ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂) : ℂ) =
          ((((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
            (u₁ - u₂, v₁ - v₂)) : ℂ) := by
      rw [basis_pair_homeomorph_apply]
      calc
        (z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂) =
            u₁ • L.ω₁ + v₁ • L.ω₂ - u₂ • L.ω₁ - v₂ • L.ω₂ := by ring
        _ = (u₁ • L.ω₁ - u₂ • L.ω₁) + (v₁ • L.ω₂ - v₂ • L.ω₂) := by abel
        _ = (u₁ - u₂) • L.ω₁ + (v₁ - v₂) • L.ω₂ := by rw [sub_smul, sub_smul]
    rw [hpair]
    change L.basis.equivFun (L.basis.equivFunL.symm ![u₁ - u₂, v₁ - v₂]) 0 = u₁ - u₂
    simpa using basis_equivFunL_symm_apply_zero (L := L) (u₁ - u₂) (v₁ - v₂)
  have hcoord1 :
      L.basis.equivFun
          ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂)) 1 =
        v₁ - v₂ := by
    have hpair :
        ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂) : ℂ) =
          ((((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
            (u₁ - u₂, v₁ - v₂)) : ℂ) := by
      rw [basis_pair_homeomorph_apply]
      calc
        (z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂) =
            u₁ • L.ω₁ + v₁ • L.ω₂ - u₂ • L.ω₁ - v₂ • L.ω₂ := by ring
        _ = (u₁ • L.ω₁ - u₂ • L.ω₁) + (v₁ • L.ω₂ - v₂ • L.ω₂) := by abel
        _ = (u₁ - u₂) • L.ω₁ + (v₁ - v₂) • L.ω₂ := by rw [sub_smul, sub_smul]
    rw [hpair]
    change L.basis.equivFun (L.basis.equivFunL.symm ![u₁ - u₂, v₁ - v₂]) 1 = v₁ - v₂
    simpa using basis_equivFunL_symm_apply_one (L := L) (u₁ - u₂) (v₁ - v₂)
  have hm_eq : (m : ℝ) = u₁ - u₂ := by
    linarith [hm, hcoord0]
  have hn_eq : (n : ℝ) = v₁ - v₂ := by
    linarith [hn, hcoord1]
  have hm_bounds : (-1 : ℝ) < (m : ℝ) ∧ (m : ℝ) < 1 := by
    constructor <;> linarith [hu₁_pos, hu₁_lt, hu₂_pos, hu₂_lt, hm_eq]
  have hn_bounds : (-1 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := by
    constructor <;> linarith [hv₁_pos, hv₁_lt, hv₂_pos, hv₂_lt, hn_eq]
  have hm_lower : -1 < m := by exact_mod_cast hm_bounds.1
  have hm_upper : m < 1 := by exact_mod_cast hm_bounds.2
  have hn_lower : -1 < n := by exact_mod_cast hn_bounds.1
  have hn_upper : n < 1 := by exact_mod_cast hn_bounds.2
  have hm_zero : m = 0 := by omega
  have hn_zero : n = 0 := by omega
  have hu_eq : u₁ = u₂ := by
    have hm_zero' : (m : ℝ) = 0 := by exact_mod_cast hm_zero
    linarith [hm_eq, hm_zero']
  have hv_eq : v₁ = v₂ := by
    have hn_zero' : (n : ℝ) = 0 := by exact_mod_cast hn_zero
    linarith [hn_eq, hn_zero']
  simp [hu_eq, hv_eq]

