import Mathlib
import BauschkeLean.Chap27.Proposition_27_5

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Corollary 27.6 combines three textbook alternatives for the pointwise sum
  problem `min_x f x + g x`.
- `core/canonical`: the Chapter 27 owner is `CompositePrimalObjectiveRegularity`, together with
  the three Proposition 27.5 optimality theorems.
- `bridge/view`: this file specializes the composite owner to `ContinuousLinearMap.id ℝ H` and
  rewrites the resulting objective and adjoint-image subdifferential back to `(f + g).asEReal`
  and `(∂ f) + (∂ g)`.
-/

-- Semantic recall note: `lean_leansearch` only surfaced generic convexity and indicator lemmas
-- here, not the Chapter 27 pointwise-sum optimality owner. The verified local surfaces used for
-- this corollary are the three Chapter 27 specializations
-- `argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular`,
-- `argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_separate_minimizers`, and
-- `argmin_compositeIndicatorObjective_eq_zeros_subdifferential_sum_of_feasibility`.

section PointwiseAddOptimality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem adjointImageSubdifferential_id
    (g : H → Set.Ioi (⊥ : EReal)) :
    ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g = ∂ g := by
  ext x u
  simp [ContinuousLinearMap.adjointImageSubdifferential]

omit [CompleteSpace H] in
private theorem zero_mem_sri_sub_range_id
    {D : Set H} (hD : D.Nonempty) :
    (0 : H) ∈ sri (D - Set.range (ContinuousLinearMap.id ℝ H)) := by
  have hsub : D - Set.range (ContinuousLinearMap.id ℝ H) = (univ : Set H) := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rcases hD with ⟨x, hx⟩
      exact Set.mem_sub.mpr ⟨x, hx, x - y, ⟨x - y, by simp⟩, by abel⟩
  rw [hsub, Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem argmin_add_subset_argmin_inter_of_nonempty
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty)
    (hcommon : (Argmin f.asEReal ∩ Argmin g.asEReal).Nonempty) :
    Argmin (f + g).asEReal ⊆ Argmin f.asEReal ∩ Argmin g.asEReal := by
  intro x hx
  rcases hcommon with ⟨z, hz⟩
  rcases hz with ⟨hzF, hzG⟩
  have hxsum_min : IsMinOn (f + g).asEReal univ x := (mem_argmin_iff.mp hx)
  have hzF_min : IsMinOn f.asEReal univ z := (mem_argmin_iff.mp hzF)
  have hzG_min : IsMinOn g.asEReal univ z := (mem_argmin_iff.mp hzG)
  rw [isMinOn_univ_iff] at hxsum_min hzF_min hzG_min
  rcases hf with ⟨yF, hyF⟩
  rcases hg with ⟨yG, hyG⟩
  have hsum_le : (f x : EReal) + (g x : EReal) ≤ (f z : EReal) + (g z : EReal) := hxsum_min z
  have hfz_le : (f z : EReal) ≤ f x := hzF_min x
  have hgz_le : (g z : EReal) ≤ g x := hzG_min x
  have hfz_ne_top : (f z : EReal) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ne_of_lt ((mem_effectiveDomain_iff).mp hyF)) (hzF_min yF)
  have hgz_ne_top : (g z : EReal) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (ne_of_lt ((mem_effectiveDomain_iff).mp hyG)) (hzG_min yG)
  have hfz_ne_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hgz_ne_bot : (g z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g z : EReal) from (g z).2)
  have hsum_right_ne_top : (f z : EReal) + (g z : EReal) ≠ ⊤ :=
    EReal.add_ne_top hfz_ne_top hgz_ne_top
  have hfx_eq : (f x : EReal) = f z := by
    refine le_antisymm ?_ hfz_le
    by_contra hfx
    have hlt : (f z : EReal) < f x := lt_of_not_ge hfx
    have hgx_ne_top : (g x : EReal) ≠ ⊤ := by
      intro hgx_top
      have hfx_ne_bot : (f x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
      rw [hgx_top, EReal.add_top_of_ne_bot hfx_ne_bot] at hsum_le
      exact hsum_right_ne_top (top_le_iff.mp hsum_le)
    have hsum_lt : (f z : EReal) + (g z : EReal) < (f x : EReal) + (g x : EReal) :=
      EReal.add_lt_add_of_lt_of_le hlt hgz_le hgz_ne_bot hgx_ne_top
    exact (not_lt_of_ge hsum_le) hsum_lt
  have hgx_eq : (g x : EReal) = g z := by
    refine le_antisymm ?_ hgz_le
    by_contra hgx
    have hlt : (g z : EReal) < g x := lt_of_not_ge hgx
    have hfx_ne_top : (f x : EReal) ≠ ⊤ := by
      intro hfx_top
      have hgx_ne_bot : (g x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
      rw [hfx_top, EReal.top_add_of_ne_bot hgx_ne_bot] at hsum_le
      exact hsum_right_ne_top (top_le_iff.mp hsum_le)
    have hsum_lt : (f z : EReal) + (g z : EReal) < (f x : EReal) + (g x : EReal) := by
      simpa [add_comm] using
        (EReal.add_lt_add_of_lt_of_le hlt hfz_le hfz_ne_bot hfx_ne_top)
    exact (not_lt_of_ge hsum_le) hsum_lt
  refine ⟨?_, ?_⟩
  · rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    simpa [hfx_eq] using hzF_min y
  · rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    simpa [hgx_eq] using hzG_min y

private theorem argmin_add_eq_zeros_subdifferential_sum_and_nonempty_of_common_argmin
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcommon : (Argmin f.asEReal ∩ Argmin g.asEReal).Nonempty) :
    Argmin (f + g).asEReal = ((∂ f) + (∂ g)).zeros ∧
      (Argmin (f + g).asEReal).Nonempty := by
  have hid :
      ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g = ∂ g :=
    adjointImageSubdifferential_id g
  have hsubset :
      Argmin (compositePrimalObjective f g (ContinuousLinearMap.id ℝ H)) ⊆
        Argmin f.asEReal ∩ (ContinuousLinearMap.id ℝ H) ⁻¹' Argmin g.asEReal := by
    simpa [compositePrimalObjective, primalObjective] using
      argmin_add_subset_argmin_inter_of_nonempty hf.2.nonempty hg.2.nonempty hcommon
  have hnonempty :
      (Argmin f.asEReal ∩ (ContinuousLinearMap.id ℝ H) ⁻¹' Argmin g.asEReal).Nonempty := by
    simpa using hcommon
  have hsri :
      (0 : H) ∈ sri (effectiveDomain g - Set.range (ContinuousLinearMap.id ℝ H)) :=
    zero_mem_sri_sub_range_id hg.2.nonempty
  rcases
      argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_separate_minimizers
        hf hg (ContinuousLinearMap.id ℝ H) hsubset hnonempty hsri with
    ⟨heq, hargmin⟩
  refine ⟨?_, ?_⟩
  · simpa [compositePrimalObjective, primalObjective, hid] using heq
  · simpa [compositePrimalObjective, primalObjective] using hargmin

private theorem argmin_add_eq_zeros_subdifferential_sum_and_nonempty_of_indicator_feasibility
    (C D : Set H)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hfeasible : (C ∩ D).Nonempty) :
    Argmin ((ι[C] + ι[D]).asEReal) = ((∂ (ι[C])) + (∂ (ι[D]))).zeros ∧
      (Argmin ((ι[C] + ι[D]).asEReal)).Nonempty := by
  have hid :
      ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) (ι[D]) =
        ∂ (ι[D]) :=
    adjointImageSubdifferential_id (ι[D])
  have hsri :
      (0 : H) ∈ sri (D - Set.range (ContinuousLinearMap.id ℝ H)) :=
    zero_mem_sri_sub_range_id (hfeasible.mono fun x hx ↦ hx.2)
  rcases
      argmin_compositeIndicatorObjective_eq_zeros_subdifferential_sum_of_feasibility
        C D hC_closed hC_convex hD_closed hD_convex
        (ContinuousLinearMap.id ℝ H) (by simpa using hfeasible) hsri with
    ⟨heq, hargmin⟩
  refine ⟨?_, ?_⟩
  · simpa [compositePrimalObjective, primalObjective, hid]
      using (heq :
        Argmin (compositePrimalObjective (ι[C]) (ι[D]) (ContinuousLinearMap.id ℝ H)) =
          ((∂ (ι[C])) +
            ContinuousLinearMap.adjointImageSubdifferential
              (ContinuousLinearMap.id ℝ H) (ι[D])).zeros)
  · simpa [compositePrimalObjective, primalObjective] using hargmin

/-- Corollary 27.6 (1): if `f, g ∈ Γ₀(H)` and one of the three source alternatives holds, then
the minimizers of `f + g` are exactly the zeros of `∂ f + ∂ g`. -/
theorem argmin_add_eq_zeros_subdifferential_sum_of_regularity_or_common_argmin_or_indicator
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcond :
      CompositePrimalObjectiveRegularity f g (ContinuousLinearMap.id ℝ H) ∨
        (Argmin f.asEReal ∩ Argmin g.asEReal).Nonempty ∨
          ∃ C D : Set H,
            IsClosed C ∧ Convex ℝ C ∧ IsClosed D ∧ Convex ℝ D ∧
              (C ∩ D).Nonempty ∧ f = ι[C] ∧ g = ι[D]) :
    Argmin (f + g).asEReal = ((∂ f) + (∂ g)).zeros := by
  have hid :
      ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g = ∂ g :=
    adjointImageSubdifferential_id g
  rcases hcond with hregular | hcommon | hindicator
  · simpa [compositePrimalObjective, primalObjective, hid] using
      (argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular
        hf hg (ContinuousLinearMap.id ℝ H) hregular)
  · exact (argmin_add_eq_zeros_subdifferential_sum_and_nonempty_of_common_argmin
      hf hg hcommon).1
  · rcases hindicator with
      ⟨C, D, hC_closed, hC_convex, hD_closed, hD_convex, hfeasible, rfl, rfl⟩
    exact (argmin_add_eq_zeros_subdifferential_sum_and_nonempty_of_indicator_feasibility
      C D hC_closed hC_convex hD_closed hD_convex hfeasible).1

/-- Corollary 27.6 (2): if the regularity branch also has a minimizer, or if one of the other two
source alternatives holds, then the zero set of `∂ f + ∂ g` is nonempty. -/
theorem
    zeros_subdifferential_sum_nonempty_of_nonempty_argmin_regularity_or_common_argmin_or_indicator
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hcond :
      ((Argmin (f + g).asEReal).Nonempty ∧
          CompositePrimalObjectiveRegularity f g (ContinuousLinearMap.id ℝ H)) ∨
        (Argmin f.asEReal ∩ Argmin g.asEReal).Nonempty ∨
          ∃ C D : Set H,
            IsClosed C ∧ Convex ℝ C ∧ IsClosed D ∧ Convex ℝ D ∧
              (C ∩ D).Nonempty ∧ f = ι[C] ∧ g = ι[D]) :
    (((∂ f) + (∂ g)).zeros).Nonempty := by
  have hid :
      ContinuousLinearMap.adjointImageSubdifferential (ContinuousLinearMap.id ℝ H) g = ∂ g :=
    adjointImageSubdifferential_id g
  rcases hcond with hregular | hcommon | hindicator
  · rcases hregular with ⟨hargmin, hregular⟩
    simpa [compositePrimalObjective, primalObjective, hid] using
      (zeros_subdifferential_sum_nonempty_of_nonempty_argmin_and_regular
        hf hg (ContinuousLinearMap.id ℝ H)
        (by simpa [compositePrimalObjective, primalObjective] using hargmin)
        hregular)
  · have hpair :=
      argmin_add_eq_zeros_subdifferential_sum_and_nonempty_of_common_argmin hf hg hcommon
    rw [← hpair.1]
    exact hpair.2
  · rcases hindicator with
      ⟨C, D, hC_closed, hC_convex, hD_closed, hD_convex, hfeasible, rfl, rfl⟩
    have hpair :=
      argmin_add_eq_zeros_subdifferential_sum_and_nonempty_of_indicator_feasibility
        C D hC_closed hC_convex hD_closed hD_convex hfeasible
    rw [← hpair.1]
    exact hpair.2

end PointwiseAddOptimality

end ERealFunction
