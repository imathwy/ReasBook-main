import Mathlib
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap08.Proposition_8_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Set

universe u

namespace ERealFunction

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18 4 is the textbook small-support-slice statement for a bounded
  set `C`.
- `core/canonical`: the owner abstractions already live upstream as the support function `σ[C]`
  from Chapter 7 and the positive-parameter type `PosReal` from Chapter 8.
- `bridge/view`: no extra bridge owner is needed here; the slice itself is just the source-facing
  subset of `C` cut out by the support inequality with margin `α`.
-/

omit [CompleteSpace H] in
/-- Helper for Proposition 18 4: if the support value at `x` is finite above, then each point of
`C` yields the usual real lower bound for the support function at `x`. -/
private lemma inner_le_supportFunction_toReal_of_mem
    (C : Set H) (hC_nonempty : C.Nonempty) {x u : H} (hu : u ∈ C)
    (hσ_top : σ[C] x ≠ ⊤) :
    ⟪x, u⟫_ℝ ≤ (σ[C] x).toReal := by
  -- Realizing the support function as a supremum gives the canonical `EReal` lower bound; the
  -- nonemptiness hypothesis removes the `⊥` case so `toReal` is available.
  have hσ_bot : σ[C] x ≠ ⊥ :=
    ne_of_gt (bot_lt_supportFunction_of_nonempty C hC_nonempty x)
  have hinner_le : (⟪x, u⟫_ℝ : EReal) ≤ σ[C] x := by
    rw [supportFunction_eq_sSup_image]
    exact (isLUB_sSup _).1 ⟨u, hu, by simp [real_inner_comm]⟩
  have hinner_le_toReal :
      (⟪x, u⟫_ℝ : EReal) ≤ (((σ[C] x).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hσ_top hσ_bot] using hinner_le
  exact_mod_cast hinner_le_toReal

omit [CompleteSpace H] in
/-- Helper for Proposition 18 4: the squared distance expands into the two norm squares minus
twice the inner product. -/
private lemma dist_sq_eq_norm_sq_add_norm_sq_sub_two_real_inner
    (x y : H) :
    dist x y ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ⟪x, y⟫_ℝ := by
  rw [dist_eq_norm, norm_sub_sq_real]
  ring

omit [CompleteSpace H] in
/-- Proposition 18 4: if `C` is a nonempty bounded subset of a real Hilbert space and `ε > 0`,
then there exist `x` and `α > 0` such that the subset of points of `C` where the support function
at `x` is attained up to the margin `α` has diameter at most `ε`. -/
theorem exists_support_slice_diam_le_of_nonempty_of_bounded
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C)
    (ε : PosReal) :
    ∃ x : H, ∃ α : PosReal,
      Metric.diam {u ∈ C | (σ[C] x).toReal - (α : ℝ) < ⟪x, u⟫_ℝ} ≤ (ε : ℝ) := by
  let S : Set ℝ := (fun u : H ↦ ‖u‖ ^ 2) '' C
  have hS_nonempty : S.Nonempty := by
    rcases hC_nonempty with ⟨u, hu⟩
    exact ⟨‖u‖ ^ 2, ⟨u, hu, rfl⟩⟩
  have hS_bdd : BddAbove S := by
    obtain ⟨R, hR_pos, hR⟩ := hC_bounded.exists_pos_norm_le
    refine ⟨R ^ 2, ?_⟩
    intro s hs
    rcases hs with ⟨u, hu, rfl⟩
    have hu_norm : ‖u‖ ≤ R := hR u hu
    have hu_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
    exact (sq_le_sq₀ hu_nonneg hR_pos.le).2 hu_norm
  let gap : ℝ := (ε : ℝ) ^ 2 / 8
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    nlinarith [ε.2]
  have hgap_lt : sSup S - gap < sSup S := by
    linarith
  rcases exists_lt_of_lt_csSup hS_nonempty hgap_lt with ⟨s, hsS, hs_lt⟩
  rcases hsS with ⟨x, hxC, rfl⟩
  let αval : ℝ := (ε : ℝ) ^ 2 / 16
  have hα_pos : 0 < αval := by
    dsimp [αval]
    nlinarith [ε.2]
  let α : PosReal := ⟨αval, hα_pos⟩
  have hσ_top : σ[C] x ≠ ⊤ := by
    exact ne_of_lt
      (example_11_2_5_supportFunction_realValued_of_bounded C hC_nonempty hC_bounded x).2
  have hx_support :
      ‖x‖ ^ 2 ≤ (σ[C] x).toReal := by
    simpa [real_inner_self_eq_norm_sq] using
      inner_le_supportFunction_toReal_of_mem C hC_nonempty hxC hσ_top
  refine ⟨x, α, ?_⟩
  have hslice_ball :
      ∀ {u : H},
        u ∈ {u ∈ C | (σ[C] x).toReal - (α : ℝ) < ⟪x, u⟫_ℝ} →
          dist u x < (ε : ℝ) / 2 := by
    intro u hu
    have hu_norm : ‖u‖ ^ 2 ≤ sSup S := by
      exact le_csSup hS_bdd ⟨u, hu.1, rfl⟩
    have hgap_sq : sSup S - ‖x‖ ^ 2 < gap := by
      linarith [hs_lt]
    have hsum :
        gap + 2 * (α : ℝ) = (ε : ℝ) ^ 2 / 4 := by
      dsimp [gap, α, αval]
      ring
    have hdist_sq :
        dist u x ^ 2 < (ε : ℝ) ^ 2 / 4 := by
      calc
        dist u x ^ 2 = ‖u‖ ^ 2 + ‖x‖ ^ 2 - 2 * ⟪u, x⟫_ℝ := by
          simpa [real_inner_comm] using
            dist_sq_eq_norm_sq_add_norm_sq_sub_two_real_inner u x
        _ ≤ sSup S + ‖x‖ ^ 2 - 2 * ⟪u, x⟫_ℝ := by
          linarith [hu_norm]
        _ < sSup S + ‖x‖ ^ 2 - 2 * ((σ[C] x).toReal - (α : ℝ)) := by
          have hu_slice : (σ[C] x).toReal - (α : ℝ) < ⟪u, x⟫_ℝ := by
            simpa [real_inner_comm] using hu.2
          linarith [hu_slice]
        _ ≤ sSup S - ‖x‖ ^ 2 + 2 * (α : ℝ) := by
          linarith [hx_support]
        _ < (ε : ℝ) ^ 2 / 4 := by
          rw [← hsum]
          linarith [hgap_sq]
    have hhalf_sq : ((ε : ℝ) / 2) ^ 2 = (ε : ℝ) ^ 2 / 4 := by
      ring
    have hdist_sq' : dist u x ^ 2 < ((ε : ℝ) / 2) ^ 2 := by
      rw [hhalf_sq]
      exact hdist_sq
    have hhalf_nonneg : 0 ≤ (ε : ℝ) / 2 := by
      linarith [ε.2]
    exact (sq_lt_sq₀ dist_nonneg hhalf_nonneg).1 hdist_sq'
  refine Metric.diam_le_of_forall_dist_le ε.2.le ?_
  intro u hu v hv
  have hu_close : dist u x < (ε : ℝ) / 2 := hslice_ball hu
  have hv_close : dist v x < (ε : ℝ) / 2 := hslice_ball hv
  have htriangle : dist u v ≤ dist u x + dist v x := by
    simpa [dist_comm] using dist_triangle u x v
  have hsum_lt : dist u x + dist v x < (ε : ℝ) := by
    linarith
  exact le_of_lt (lt_of_le_of_lt htriangle hsum_lt)

end EkelandLebourgTheorem

end ERealFunction
