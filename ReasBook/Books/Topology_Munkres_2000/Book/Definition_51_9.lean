module

public import Topology_Munkres_2000.Book.Exercise_51_2
import Topology_Munkres_2000.Book.Definition_51_7.PositiveHomeomorph

public section

open Set

namespace Path

variable {X : Type u} [TopologicalSpace X]

private noncomputable def tripleReparam (a b : unitInterval) (ha : 0 < a) (hab : a < b)
    (hb : b < 1) : unitInterval → unitInterval :=
  fun t ↦
    if hta : t ≤ a then
      let s := Set.Icc.positiveHomeomorph
        (show (0 : ℝ) < a from by exact_mod_cast ha) (by norm_num : (0 : ℝ) < 1 / 4)
        ⟨t, t.property.1, hta⟩
      ⟨s, s.property.1, s.property.2.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)⟩
    else if htb : t ≤ b then
      let s := Set.Icc.positiveHomeomorph
        (show (a : ℝ) < b from by exact_mod_cast hab) (by norm_num : (1 / 4 : ℝ) < 1 / 2)
        ⟨t, (not_le.mp hta).le, htb⟩
      ⟨s, (by norm_num : (0 : ℝ) ≤ 1 / 4).trans s.property.1,
        s.property.2.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)⟩
    else
      let s := Set.Icc.positiveHomeomorph
        (show (b : ℝ) < 1 from by exact_mod_cast hb) (by norm_num : (1 / 2 : ℝ) < 1)
        ⟨t, (not_le.mp htb).le, t.property.2⟩
      ⟨s, (by norm_num : (0 : ℝ) ≤ 1 / 2).trans s.property.1, s.property.2⟩

private theorem continuous_tripleReparam (a b : unitInterval) (ha : 0 < a) (hab : a < b)
    (hb : b < 1) : Continuous (tripleReparam a b ha hab hb) := by
  -- Paste the three affine branches along their matching endpoint values.
  apply continuous_induced_rng.mpr
  let first : unitInterval → ℝ := fun t ↦ (1 / 4 : ℝ) * ((t : ℝ) / a)
  let middle : unitInterval → ℝ := fun t ↦
    (1 / 4 : ℝ) * (((t : ℝ) - a) / (b - a)) + 1 / 4
  let last : unitInterval → ℝ := fun t ↦
    (1 / 2 : ℝ) * (((t : ℝ) - b) / (1 - b)) + 1 / 2
  have hcontinuous : Continuous fun t : unitInterval ↦
      if (t : ℝ) ≤ a then first t else if (t : ℝ) ≤ b then middle t else last t := by
    apply continuous_if_le (β := unitInterval) (α := ℝ) (γ := ℝ)
      (f := fun t : unitInterval ↦ (t : ℝ)) (g := fun _ ↦ (a : ℝ))
    · fun_prop
    · fun_prop
    · fun_prop
    · refine (continuous_if_le (β := unitInterval) (α := ℝ) (γ := ℝ)
        (f := fun t : unitInterval ↦ (t : ℝ)) (g := fun _ ↦ (b : ℝ))
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) ?_).continuousOn
      intro t ht
      have ht' : t = b := Subtype.ext ht
      subst t
      dsimp only [middle, last]
      have hba : (b : ℝ) - a ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hab))
      have hb1 : (1 : ℝ) - b ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hb))
      field_simp [hba, hb1]
      ring
    · intro t ht
      have ht' : t = a := Subtype.ext ht
      subst t
      dsimp only [first, middle]
      have ha0 : (a : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
      have hba : (b : ℝ) - a ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hab))
      simp only [show (a : ℝ) ≤ b from by exact_mod_cast hab.le, if_pos]
      field_simp [ha0, hba]
      ring
  convert hcontinuous using 1
  funext t
  simp only [Function.comp_apply, tripleReparam, Set.Icc.positiveHomeomorph_apply]
  simp only [show (t ≤ a) = ((t : ℝ) ≤ a) from rfl,
    show (t ≤ b) = ((t : ℝ) ≤ b) from rfl]
  split_ifs <;> norm_num [first, middle, last]

private theorem tripleReparam_zero (a b : unitInterval) (ha : 0 < a) (hab : a < b)
    (hb : b < 1) : tripleReparam a b ha hab hb 0 = 0 := by
  -- The initial point lies in the first branch and maps to its left endpoint.
  apply Subtype.ext
  simp [tripleReparam, Set.Icc.positiveHomeomorph_apply]

private theorem tripleReparam_one (a b : unitInterval) (ha : 0 < a) (hab : a < b)
    (hb : b < 1) : tripleReparam a b ha hab hb 1 = 1 := by
  -- The terminal point lies in the final branch and maps to its right endpoint.
  have hOneA : ¬(1 : unitInterval) ≤ a := not_le.mpr (hab.trans hb)
  have hOneB : ¬(1 : unitInterval) ≤ b := not_le.mpr hb
  have hbReal : (b : ℝ) < 1 := by exact_mod_cast hb
  apply Subtype.ext
  simp only [tripleReparam, dif_neg hOneA, dif_neg hOneB]
  rw [Set.Icc.positiveHomeomorph_apply]
  have hdiff : 1 - (b : ℝ) ≠ 0 := sub_ne_zero.mpr hbReal.ne'
  norm_num at hdiff ⊢
  field_simp [hdiff]
  norm_num

/-- Definition 51.9: The triple product path with interior breakpoints `0 < a < b < 1`. -/
noncomputable def triple {x₀ x₁ x₂ x₃ : X} (f : Path x₀ x₁) (g : Path x₁ x₂) (h : Path x₂ x₃)
    (a b : unitInterval) (ha : 0 < a) (hab : a < b) (hb : b < 1) : Path x₀ x₃ :=
  ((f.trans g).trans h).reparam (tripleReparam a b ha hab hb)
    (continuous_tripleReparam a b ha hab hb) (tripleReparam_zero a b ha hab hb)
    (tripleReparam_one a b ha hab hb)

/--
The triple product traverses its three factors by the positive affine maps on its subintervals.
-/
theorem triple_apply {x₀ x₁ x₂ x₃ : X} (f : Path x₀ x₁) (g : Path x₁ x₂)
    (h : Path x₂ x₃) (a b : unitInterval) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (t : unitInterval) :
    triple f g h a b ha hab hb t =
      if t ≤ a then
        f.extend ((t : ℝ) / a)
      else if t ≤ b then
        g.extend (((t : ℝ) - a) / (b - a))
      else
        h.extend (((t : ℝ) - b) / (1 - b)) := by
  -- Evaluate the reparameterized left-associated path and select its nested branches.
  simp only [triple, Path.coe_reparam, Function.comp_apply, tripleReparam,
    Set.Icc.positiveHomeomorph_apply]
  split_ifs with hta htb
  · rw [← Path.extend_extends' ((f.trans g).trans h)]
    have hsUpper := (Set.Icc.positiveHomeomorph
      (show (0 : ℝ) < a from by exact_mod_cast ha)
      (by norm_num : (0 : ℝ) < 1 / 4)
      ⟨t, t.property.1, hta⟩).property.2
    rw [Set.Icc.positiveHomeomorph_apply] at hsUpper
    norm_num at hsUpper
    norm_num
    rw [Path.extend_trans_of_le_half _ _ (by linarith)]
    rw [Path.extend_trans_of_le_half _ _ (by norm_num at hsUpper ⊢; linarith)]
    congr 1
    ring
  · rw [← Path.extend_extends' ((f.trans g).trans h)]
    have hsLower := (Set.Icc.positiveHomeomorph
      (show (a : ℝ) < b from by exact_mod_cast hab)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2)
      ⟨t, (not_le.mp hta).le, htb⟩).property.1
    have hsUpper := (Set.Icc.positiveHomeomorph
      (show (a : ℝ) < b from by exact_mod_cast hab)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2)
      ⟨t, (not_le.mp hta).le, htb⟩).property.2
    rw [Set.Icc.positiveHomeomorph_apply] at hsLower hsUpper
    norm_num at hsLower hsUpper
    norm_num
    rw [Path.extend_trans_of_le_half _ _ hsUpper]
    rw [Path.extend_trans_of_half_le _ _ (by norm_num at hsLower ⊢; linarith)]
    congr 1
    ring
  · rw [← Path.extend_extends' ((f.trans g).trans h)]
    rw [Path.extend_trans_of_half_le _ _ (by
      have hsLower := (Set.Icc.positiveHomeomorph
        (show (b : ℝ) < 1 from by exact_mod_cast hb)
        (by norm_num : (1 / 2 : ℝ) < 1)
        ⟨t, (not_le.mp htb).le, t.property.2⟩).property.1
      rw [Set.Icc.positiveHomeomorph_apply] at hsLower
      exact_mod_cast hsLower)]
    congr 1
    norm_num
    ring

/-- Breakpoints `1 / 2` and `3 / 4` give the right-associated triple product. -/
theorem triple_half_threeQuarters {x₀ x₁ x₂ x₃ : X} (f : Path x₀ x₁) (g : Path x₁ x₂)
    (h : Path x₂ x₃) :
    triple f g h ⟨(1 / 2 : ℝ), by norm_num⟩ ⟨(3 / 4 : ℝ), by norm_num⟩
        (by change (0 : ℝ) < 1 / 2; norm_num) (by norm_num)
        (by change (3 / 4 : ℝ) < 1; norm_num) = f.trans (g.trans h) := by
  -- Compare the source-facing three-piece formula with right-associated concatenation.
  ext t
  rw [triple_apply, ← Path.extend_extends' (f.trans (g.trans h)) t]
  split_ifs with ht₁ ht₂
  · rw [Path.extend_trans_of_le_half _ _ ht₁]
    congr 1
    norm_num
    ring
  · rw [Path.extend_trans_of_half_le _ _ (not_le.mp ht₁).le]
    rw [Path.extend_trans_of_le_half _ _]
    · congr 1
      norm_num
      ring
    · have htReal : (t : ℝ) ≤ 3 / 4 := by exact_mod_cast ht₂
      linarith
  · rw [Path.extend_trans_of_half_le _ _ (not_le.mp ht₁).le]
    rw [Path.extend_trans_of_half_le _ _]
    · congr 1
      norm_num
      ring
    · have htReal : (3 / 4 : ℝ) < t := by exact_mod_cast not_le.mp ht₂
      linarith

/-- Breakpoints `1 / 4` and `1 / 2` give the left-associated triple product. -/
theorem triple_quarter_half {x₀ x₁ x₂ x₃ : X} (f : Path x₀ x₁) (g : Path x₁ x₂)
    (h : Path x₂ x₃) :
    triple f g h ⟨(1 / 4 : ℝ), by norm_num⟩ ⟨(1 / 2 : ℝ), by norm_num⟩
        (by change (0 : ℝ) < 1 / 4; norm_num) (by norm_num)
        (by change (1 / 2 : ℝ) < 1; norm_num) = (f.trans g).trans h := by
  -- Compare the source-facing three-piece formula with left-associated concatenation.
  ext t
  rw [triple_apply, ← Path.extend_extends' ((f.trans g).trans h) t]
  split_ifs with ht₁ ht₂
  · rw [Path.extend_trans_of_le_half _ _]
    · rw [Path.extend_trans_of_le_half _ _]
      · congr 1
        norm_num
        ring
      · have htReal : (t : ℝ) ≤ 1 / 4 := by exact_mod_cast ht₁
        linarith
    · have htReal : (t : ℝ) ≤ 1 / 4 := by exact_mod_cast ht₁
      linarith
  · rw [Path.extend_trans_of_le_half _ _]
    · rw [Path.extend_trans_of_half_le _ _ (by
        have htReal : (1 / 4 : ℝ) < t := by exact_mod_cast not_le.mp ht₁
        linarith)]
      congr 1
      norm_num
      ring
    · exact ht₂
  · rw [Path.extend_trans_of_half_le _ _ (by
      have htReal : (1 / 2 : ℝ) < t := by exact_mod_cast not_le.mp ht₂
      exact htReal.le)]
    congr 1
    norm_num
    ring

/-- Triple product paths from two valid choices of breakpoints are path homotopic. -/
theorem triple_homotopic {x₀ x₁ x₂ x₃ : X} (f : Path x₀ x₁) (g : Path x₁ x₂)
    (h : Path x₂ x₃) (a b c d : unitInterval) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hc : 0 < c) (hcd : c < d) (hd : d < 1) :
    (triple f g h a b ha hab hb).Homotopic (triple f g h c d hc hcd hd) := by
  -- Both choices are endpoint-preserving reparameterizations of one fixed path.
  have habHomotopy : ((f.trans g).trans h).Homotopic (triple f g h a b ha hab hb) :=
    ⟨Path.Homotopy.reparam ((f.trans g).trans h) (tripleReparam a b ha hab hb)
      (continuous_tripleReparam a b ha hab hb) (tripleReparam_zero a b ha hab hb)
      (tripleReparam_one a b ha hab hb)⟩
  have hcdHomotopy : ((f.trans g).trans h).Homotopic (triple f g h c d hc hcd hd) :=
    ⟨Path.Homotopy.reparam ((f.trans g).trans h) (tripleReparam c d hc hcd hd)
      (continuous_tripleReparam c d hc hcd hd) (tripleReparam_zero c d hc hcd hd)
      (tripleReparam_one c d hc hcd hd)⟩
  exact habHomotopy.symm.trans hcdHomotopy


end Path
