import Mathlib
import Mathlib.Tactic.Recall
import BauschkeLean.Chap01.Text_1_0_28
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap19.Definition_19_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section ParametricDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Helper for Proposition 19 12: each first-variable slice is bounded above by subtracting the
fiber infimum from the fixed pairing value. -/
lemma iSup_first_slice_le_pairing_sub_fiberInf
    (G : H × K → EReal) (v y : K) :
    (⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - G (x, y))) ≤
      (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, G (x, y)) := by
  -- The map `t ↦ a - t` is antitone, so it sends the fiber infimum to an upper bound
  -- for every affine defect on that fiber.
  let a : EReal := ((⟪y, v⟫_ℝ : ℝ) : EReal)
  have h_antitone : Antitone (fun t : EReal ↦ a - t) := by
    intro s t hst
    exact EReal.sub_le_sub le_rfl hst
  simpa [a] using (Antitone.le_map_iInf h_antitone (s := fun x : H ↦ G (x, y)))

/-- Helper for Proposition 19 12: subtracting the first-variable fiber infimum is bounded above by
the supremum of the corresponding first-variable slices. -/
lemma pairing_sub_fiberInf_le_iSup_first_slice
    (G : H × K → EReal) (v y : K) :
    (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, G (x, y)) ≤
      (⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - G (x, y))) := by
  -- Rewrite the fiber infimum as an `sInf`, then choose a near-minimizer in the fiber and
  -- transport it back to a near-maximizer after subtracting from the fixed pairing value.
  let a : EReal := ((⟪y, v⟫_ℝ : ℝ) : EReal)
  let s : Set EReal := Set.range (fun x : H ↦ G (x, y))
  have hs : (⨅ x : H, G (x, y)) = sInf s := by
    simpa [s] using (sInf_range (f := fun x : H ↦ G (x, y))).symm
  rw [hs]
  refine le_of_forall_lt fun c hc ↦ ?_
  have hsInf_ne_top : sInf s ≠ ⊤ := by
    intro hsInf_top
    have : ¬ c < (⊥ : EReal) := by simp
    simp [hsInf_top] at hc
  have hc_ne_top : c ≠ ⊤ := hc.ne_top
  have hc_add : c + sInf s < a := by
    exact
      (EReal.lt_sub_iff_add_lt (b := sInf s) (c := c) (Or.inr hc_ne_top) (Or.inl hsInf_ne_top)).1
        hc
  have hs_lt : sInf s < a - c := by
    exact
      (EReal.lt_sub_iff_add_lt (b := c) (c := sInf s) (Or.inr hsInf_ne_top) (Or.inl hc_ne_top)).2
        (by simpa [add_comm] using hc_add)
  obtain ⟨z, hzmem, hzlt⟩ := (sInf_lt_iff).1 hs_lt
  rcases hzmem with ⟨x, rfl⟩
  have hlt : c < a - G (x, y) := by
    have hz_add : G (x, y) + c < a := by
      exact EReal.add_lt_of_lt_sub hzlt
    exact
      (EReal.lt_sub_iff_add_lt (b := G (x, y)) (c := c) (Or.inr hc_ne_top) (Or.inl hzlt.ne_top)).2
        (by simpa [add_comm] using hz_add)
  exact lt_of_lt_of_le hlt (le_iSup (fun x : H ↦ a - G (x, y)) x)

/-- Helper for Proposition 19 12: fiberwise, subtracting the first-variable infimum is the same as
taking the supremum of the corresponding first-variable slices. -/
lemma pairing_sub_fiberInf_eq_iSup_first_slice
    (G : H × K → EReal) (v y : K) :
    (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, G (x, y)) =
      (⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - G (x, y))) := by
  -- Combine the antitone upper bound with the near-minimizer argument for the reverse bound.
  refine le_antisymm
    (pairing_sub_fiberInf_le_iSup_first_slice G v y)
    (iSup_first_slice_le_pairing_sub_fiberInf G v y)

/-- Helper for Proposition 19 12: evaluating the conjugate at the origin turns the supremum of
affine defects into the negative of the infimum. -/
lemma conjugate_zero_eq_neg_iInf_local
    (φ : K → EReal) :
    φ∗ 0 = -(⨅ x : K, φ x) := by
  -- Rewrite the conjugate at the origin as a supremum of negatives, then convert the supremum
  -- of negated values into the negation of the corresponding infimum.
  calc
    φ∗ 0 = ⨆ x : K, -φ x := by
      simp [conjugate_apply]
    _ = sSup (Set.range fun x : K ↦ -φ x) := by
      rw [sSup_range]
    _ = -sInf ((-·) '' Set.range (fun x : K ↦ -φ x)) := by
      rw [EReal.sSup_eq_neg_sInf_image_neg]
    _ = -sInf (Set.range φ) := by
      congr 2
      ext z
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, by simp⟩
      · rintro ⟨x, rfl⟩
        refine ⟨-φ x, ?_, by simp⟩
        exact ⟨x, rfl⟩
    _ = -(⨅ x : K, φ x) := by
      rw [sInf_range]

/-- Helper for Proposition 19 12: the Fenchel biconjugate is pointwise bounded above by the
original function. -/
lemma biconjugate_le_local
    (φ : K → EReal) :
    φ∗∗ ≤ φ := by
  -- Reuse the canonical Chapter 13 biconjugate bound.
  simpa using biconjugate_le φ

-- Proof sketch: expand the conjugate of the value function `Prod.snd ▷ F` directly on `K`, use
-- `infimalPostcomposition_snd_apply` to rewrite the value function as the fiberwise infimum of the
-- slices `x ↦ F (x, y)`, and then commute the outer supremum in `y` with the inner infimum in `x`
-- to obtain the explicit dual-objective formula `v ↦ F^*(0, v)`.
/-- Proposition 19 12 (1): if `ϑ = Prod.snd ▷ F`, then `ϑ*` is the dual objective
`v ↦ F^*(0, v)` of `F`. -/
theorem conjugate_valueFunction_eq_dualObjective
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.snd ▷ F)∗ = perturbationDualObjective F := by
  ext v
  -- Expand the conjugate of the value function and the explicit dual objective at the same
  -- dual variable `v`.
  rw [conjugate_apply, perturbationDualObjective_apply]
  -- Rewrite the value function as the infimum over the first-variable fiber at each fixed `y`.
  simp_rw [infimalPostcomposition_snd_apply]
  -- Replace each fixed-`y` summand by the supremum over `x`, then reindex the double supremum
  -- by pairs `(x, y)` to match the dual objective formula.
  calc
    (⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - ⨅ x : H, (F (x, y) : EReal))) =
        (⨆ y : K, ⨆ x : H, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          refine iSup_congr fun y => ?_
          exact
            pairing_sub_fiberInf_eq_iSup_first_slice
              (G := fun p : H × K ↦ (F p : EReal)) v y
    _ = (⨆ x : H, ⨆ y : K, (((⟪y, v⟫_ℝ : ℝ) : EReal) - (F (x, y) : EReal))) := by
          rw [iSup_comm]
    _ = ⨆ p : H × K, (((⟪p.2, v⟫_ℝ : ℝ) : EReal) - (F p : EReal)) := by
          rw [iSup_prod']

-- Proof sketch: specialize `conjugate_zero_eq_neg_iInf` to `ϑ* = (Prod.snd ▷ F)∗`, then rewrite
-- the resulting infimum with clause (1).
/-- Proposition 19 12 (2): the negative infimum of the slice `v ↦ F^*(0, v)` equals the value of
`ϑ**` at the origin. -/
theorem neg_sInf_perturbationDualObjective_eq_biconjugate_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    -sInf (Set.range (perturbationDualObjective F)) =
      (Prod.snd ▷ F)∗∗ 0 := by
  rw [← conjugate_valueFunction_eq_dualObjective]
  simpa [sInf_range] using
    (conjugate_zero_eq_neg_iInf_local ((Prod.snd ▷ F)∗)).symm

-- Proof sketch: this is `biconjugate_le` for the canonical owner `Prod.snd ▷ F`, evaluated at
-- `0`.
/-- Proposition 19 12 (3): the biconjugate of the value function at the origin is bounded above by
its value at the origin. -/
theorem biconjugate_valueFunction_zero_le_valueFunction_zero
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    (Prod.snd ▷ F)∗∗ 0 ≤ (Prod.snd ▷ F) 0 := by
  simpa using (biconjugate_le_local (Prod.snd ▷ F)) 0

/- Proposition 19.12 (4) is the specialization at `0` of the defining evaluation formula for the
canonical owner `Prod.snd ▷ F`. -/
recall infimalPostcomposition_snd_apply

end ParametricDuality

end

end ERealFunction
