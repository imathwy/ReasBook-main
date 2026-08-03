import Mathlib
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap15.Definition_15_24_1
import BauschkeLean.Chap15.Theorem_15_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 15.28 contributes the Chapter 15 attainment/exactness consequence
  for the adjoint infimal postcomposition attached to `g ∘ L`.
- `core/canonical`: the conjugation identity itself is the Chapter 13 composition-conjugation
  formula for `g ∘ L`.
- `bridge/view`: the fiberwise `sInf` formula is the pointwise view of that owner identity,
  while `infimalPostcomposition.Exact L.adjoint (g∗[hg])` is the genuinely new
  Chapter 15 regularity conclusion.
-/

variable
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)

-- Proof sketch: evaluate the Chapter 13 owner identity
-- at `u` and unfold `infimalPostcomposition`.
/-- Helper for Corollary 15 28: evaluating the canonical composition-conjugation identity gives
the fiberwise infimum formula from `(15.45)`. -/
theorem conjugate_comp_apply_eq_sInf_fiber_conjugate_of_range_inter_effectiveDomain_nonempty
    (hdom : (range L ∩ effectiveDomain g).Nonempty)
    (u : H) :
    (g ∘ L).asEReal∗ u =
      sInf (g.asEReal∗ '' {v : K | L.adjoint v = u}) := by
  simpa [infimalPostcomposition_apply] using
    congrFun (conjugate_comp_eq_adjointInfimalPostcomposition g L hdom) u

-- Proof sketch: the same specialization of Theorem 15.27 that gives the function identity also
-- gives exactness of the dual infimal postcomposition on its domain, i.e. whenever the fiberwise
-- infimum is finite it is attained by some `v` with `L.adjoint v = u`.
/-- Corollary 15 28: under the regularity hypotheses, the infimal postcomposition `L^* ▷ g^*` is
exact on its domain, so the fiberwise infimum in `(15.45)` is attained whenever finite. -/
theorem infimalPostcomposition_adjoint_conjugate_exact_of_regular
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - Set.range L) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ Set.range L).Nonempty))
    :
    infimalPostcomposition.Exact L.adjoint (g∗[hg]) := by
  let f0 : H → Set.Ioi (⊥ : EReal) := (fun _ : H ↦ (0 : ℝ)).toEReal
  have hf0 : f0 ∈ Γ₀(H) := by
    rw [mem_gammaZero_iff]
    refine ⟨?_, ?_⟩
    · simpa [f0] using
        (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (0 : EReal)))
    · refine ⟨?_, subset_rfl, ?_⟩
      · refine ⟨0, ?_⟩
        simp [f0]
      · intro x hx y hy a ha0 ha1
        simp [f0]
  have hf0_dom : effectiveDomain f0 = Set.univ := by
    ext x
    simp [f0]
  have hsingle : (ι[({(0 : H)} : Set H)] : H → Set.Ioi (⊥ : EReal)) ∈ Γ₀(H) := by
    rw [mem_gammaZero_iff]
    constructor
    · simpa using
        (lowerSemicontinuous_indicator_compl_top_iff_isClosed ({(0 : H)} : Set H)).2
          isClosed_singleton
    · refine ⟨by simp, subset_rfl, ?_⟩
      intro x hx y hy a ha0 ha1
      have hx0 : x = 0 := by simpa using hx
      have hy0 : y = 0 := by simpa using hy
      subst x
      subst y
      simp [ERealFunction.indicator_apply]
  have hsingle_conj :
      ((ι[({(0 : H)} : Set H)] : H → Set.Ioi (⊥ : EReal)).asEReal)∗ =
        (fun _ : H ↦ (0 : EReal)) := by
    ext z
    rw [conjugate_indicator_eq_supportFunction]
    simp
  have hf0_asEReal : f0.asEReal = (fun _ : H ↦ (0 : EReal)) := by
    ext x
    simp [f0]
  have hf0_conj :
      f0.asEReal∗ =
        (ι[({(0 : H)} : Set H)] : H → Set.Ioi (⊥ : EReal)).asEReal := by
    calc
      f0.asEReal∗ = (fun _ : H ↦ (0 : EReal))∗ := by
        rw [hf0_asEReal]
      _ = (((ι[({(0 : H)} : Set H)] : H → Set.Ioi (⊥ : EReal)).asEReal)∗)∗ := by
        rw [hsingle_conj.symm]
      _ = (ι[({(0 : H)} : Set H)] : H → Set.Ioi (⊥ : EReal)).asEReal := by
        simpa using biconjugate_eq_of_mem_gammaZero hsingle
  have hdom : (Set.range L ∩ effectiveDomain g).Nonempty := by
    rcases hregular with hsri | hpoly
    · rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
      rcases Set.mem_sub.mp hzero with ⟨y, hy, z, hz, hyz⟩
      refine ⟨y, ?_, hy⟩
      simpa [sub_eq_zero.mp hyz] using hz
    · simpa [Set.inter_comm] using hpoly.2.2
  have hregular' :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f0) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f0)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f0.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f0).Nonempty) := by
    rcases hregular with hsri | hpoly
    · left
      simpa [hf0_dom] using hsri
    · right
      left
      rcases hpoly with ⟨hfdK, hgpoly, hnonempty⟩
      rcases hnonempty with ⟨y, hyg, hyL⟩
      have hyri : y ∈ ri (L.range : Set K) := by
        simpa [relativeInterior_submodule_eq_self] using hyL
      refine ⟨hfdK, hgpoly, ⟨y, hyg, ?_⟩⟩
      simpa [hf0_dom] using hyri
  have hprimal : compositePrimalObjective f0 g L = (g ∘ L).asEReal := by
    funext x
    simp [f0, compositePrimalObjective_apply, Function.toEReal_apply]
  intro u hu
  obtain ⟨v, _, hvEq⟩ :=
    exists_mem_argmin_shiftedCompositeDualObjective_eq_conjugate_addComp_of_regular
      (f := f0) (hf := hf0) (g := g) (hg := hg) (L := L) (hregular := hregular') (u := u)
  have hu_lt : (L.adjoint ▷ g.asEReal∗) u < ⊤ := by
    rw [mem_dom_iff] at hu
    simpa [infimalPostcomposition_apply] using hu
  have hcomp_lt : (compositePrimalObjective f0 g L)∗ u < ⊤ := by
    rw [hprimal]
    rw [conjugate_comp_apply_eq_sInf_fiber_conjugate_of_range_inter_effectiveDomain_nonempty
      (g := g) (L := L) hdom u]
    exact hu_lt
  have hv_lt : shiftedCompositeDualObjective f0 g L u v < ⊤ := by
    rw [← hvEq]
    exact hcomp_lt
  have hLv : L.adjoint v = u := by
    by_contra hne
    have hsub_ne : u - L.adjoint v ≠ 0 := by
      intro hsub
      exact hne (sub_eq_zero.mp hsub).symm
    have hg_ne_bot : g.asEReal∗ v ≠ ⊥ :=
      conjugate_ne_bot_of_effectiveDomain_nonempty hg.2.nonempty v
    have hv_top : shiftedCompositeDualObjective f0 g L u v = ⊤ := by
      rw [shiftedCompositeDualObjective_apply, hf0_conj]
      have hind :
          (ι[({(0 : H)} : Set H)] : H → Set.Ioi (⊥ : EReal)).asEReal (u - L.adjoint v) = ⊤ := by
        simp [ERealFunction.indicator_apply, hsub_ne]
      rw [hind, EReal.top_add_of_ne_bot hg_ne_bot]
    rw [hv_top] at hv_lt
    exact (lt_irrefl (⊤ : EReal)) hv_lt
  have hvalue : (L.adjoint ▷ g.asEReal∗) u = g.asEReal∗ v := by
    calc
      (L.adjoint ▷ g.asEReal∗) u = (g ∘ L).asEReal∗ u := by
        symm
        exact
          conjugate_comp_apply_eq_sInf_fiber_conjugate_of_range_inter_effectiveDomain_nonempty
            (g := g) (L := L) hdom u
      _ = (compositePrimalObjective f0 g L)∗ u := by rw [hprimal]
      _ = shiftedCompositeDualObjective f0 g L u v := hvEq
      _ = g.asEReal∗ v := by
        rw [shiftedCompositeDualObjective_apply, hf0_conj, hLv]
        simp [ERealFunction.indicator_apply]
  refine (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) u).2 ?_
  refine ⟨hu, v, hLv, ?_⟩
  simpa [infimalPostcomposition_apply] using hvalue

end FenchelRockafellarDuality

end ERealFunction
