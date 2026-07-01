import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_3

noncomputable section

universe u

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.4 says that a polyhedral convex function attains its infimum on
  any nonempty polyhedral convex set on which it is bounded below.
- `core/canonical`: the minimization mechanism itself only needs a closedness hypothesis on the
  scalar height projection of the intrinsic constrained epigraph `epi[C] h`, together with
  nonemptiness and bounded-below data on that scalar height projection.
- `bridge/view`: the proof should pass through the constrained epigraph
  `epi h ∩ (LinearMap.fst 𝕜 E 𝕜) ⁻¹' C` and its height projection under `LinearMap.snd`,
  while polyhedrality is used only to certify that this projected height set is closed.

Primary mathematical domain: polyhedral convex analysis via epigraph geometry.

Domain-style sampling used here:
- core owner:
  `Function.exists_mem_isMinOn_of_isClosed_heightProjection_of_bddBelow`;
- bridge owners:
  `Function.HasPolyhedralEpigraph`, `Set.IsPolyhedral.linear_preimage`,
  `Set.IsPolyhedral.linear_image`, and `Set.IsPolyhedral.isClosed_of_finiteDimensional`.

Primitive data vs derived API:
- primitive inputs for the core owner theorem: a function `h : E → WithBotTop 𝕜`, a nonempty set
  `C`, bounded-below data for `Prod.snd '' (epi[C] h : Set (E × 𝕜))`, and closedness of
  `Prod.snd '' (epi[C] h : Set (E × 𝕜))`;
- derived bridge object for the source-facing corollary:
  the constrained epigraph
  `epi h ∩ (LinearMap.fst 𝕜 E 𝕜) ⁻¹' C`;
- derived API: existence of a minimizer in the canonical owner form
  `∃ x ∈ C, IsMinOn h C x`, and the companion source-facing `sInf (h '' C)` equality.

Ambient-assumption audit:
- `ConditionallyCompleteLinearOrder 𝕜` and `OrderTopology 𝕜` are exactly the scalar hypotheses
  needed for the `sInf` attainment step (`IsClosed.csInf_mem`);
- finite-dimensional Hausdorff topological-module assumptions are not part of the core
  minimization owner and appear only in the polyhedral bridge proving closedness of the projected
  height set.
-/

section CoreMinimization

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u}

namespace Function

variable {h : E → WithBotTop 𝕜} {C : Set E}

/-- Core owner theorem: if `C` is nonempty, the scalar height projection
`Prod.snd '' (epi[C] h : Set (E × 𝕜))` is bounded below and closed, then `h` attains its infimum
on `C`. -/
theorem exists_mem_isMinOn_of_isClosed_heightProjection_of_bddBelow
    (hC_nonempty : C.Nonempty)
    (hheight_bddBelow :
      BddBelow (Prod.snd '' (epi[C] h : Set (E × 𝕜))))
    (hheight_closed :
      IsClosed (Prod.snd '' (epi[C] h : Set (E × 𝕜)))) :
    ∃ x ∈ C, IsMinOn h C x := by
  by_cases hbot : ∃ x ∈ C, h x = ⊥
  · rcases hbot with ⟨x, hxC, hxbot⟩
    refine ⟨x, hxC, isMinOn_iff.mpr ?_⟩
    intro y hyC
    simp [hxbot]
  · have h_not_bot : ∀ x ∈ C, h x ≠ ⊥ := by
      intro x hxC hxbot
      exact hbot ⟨x, hxC, hxbot⟩
    by_cases hfinite : ∃ x ∈ C, h x < ⊤
    · rcases hfinite with ⟨x₀, hx₀C, hx₀top⟩
      have hx₀bot : ⊥ < h x₀ := bot_lt_iff_ne_bot.mpr (h_not_bot x₀ hx₀C)
      lift h x₀ to 𝕜 using ⟨ne_of_lt hx₀top, ne_of_gt hx₀bot⟩ with r₀ hr₀
      let P : Set (E × 𝕜) := epi[C] h
      have hheight_closed' : IsClosed (Prod.snd '' P) := by
        simpa [P] using hheight_closed
      have hheight_bddBelow' : BddBelow (Prod.snd '' P) := by
        simpa [P] using hheight_bddBelow
      have hP_nonempty : P.Nonempty := by
        refine ⟨(x₀, r₀), ?_⟩
        exact (mem_epi_restrict_iff).2 ⟨hx₀C, by simp [hr₀]⟩
      have hheight_nonempty : (Prod.snd '' P).Nonempty := hP_nonempty.image Prod.snd
      have hsInf_mem : sInf (Prod.snd '' P) ∈ Prod.snd '' P :=
        hheight_closed'.csInf_mem hheight_nonempty hheight_bddBelow'
      rcases hsInf_mem with ⟨p, hpP, hp₂⟩
      have hpC : p.1 ∈ C := (mem_epi_restrict_iff.mp hpP).1
      have hp_epi : h p.1 ≤ (p.2 : WithBotTop 𝕜) := (mem_epi_restrict_iff.mp hpP).2
      have hpbot : ⊥ < h p.1 := bot_lt_iff_ne_bot.mpr (h_not_bot p.1 hpC)
      have hptop : h p.1 < ⊤ := by
        exact lt_of_le_of_lt hp_epi (WithBotTop.coe_lt_top p.2)
      lift h p.1 to 𝕜 using ⟨ne_of_lt hptop, ne_of_gt hpbot⟩ with rp hrp
      have hrp_mem : rp ∈ Prod.snd '' P := by
        refine ⟨(p.1, rp), ?_, by simp⟩
        exact (mem_epi_restrict_iff).2 ⟨hpC, by simp [hrp]⟩
      have hsInf_le_rp : sInf (Prod.snd '' P) ≤ rp :=
        csInf_le hheight_bddBelow' hrp_mem
      have hrp_le_p₂ : rp ≤ p.2 := by
        exact WithBotTop.coe_le_coe.mp hp_epi
      have hrp_eq_p₂ : rp = p.2 := by
        refine le_antisymm hrp_le_p₂ ?_
        calc
          p.2 = sInf (Prod.snd '' P) := by simpa using hp₂
          _ ≤ rp := hsInf_le_rp
      have hp_eq : h p.1 = (p.2 : WithBotTop 𝕜) := by
        simpa [hrp_eq_p₂] using hrp.symm
      refine ⟨p.1, hpC, isMinOn_iff.mpr ?_⟩
      intro y hyC
      by_cases hytop : h y = ⊤
      · simp [hytop]
      · have hybot : ⊥ < h y := bot_lt_iff_ne_bot.mpr (h_not_bot y hyC)
        have hyfinite : h y < ⊤ := lt_of_le_of_ne le_top hytop
        lift h y to 𝕜 using ⟨ne_of_lt hyfinite, ne_of_gt hybot⟩ with ry hry
        have hry_mem : ry ∈ Prod.snd '' P := by
          refine ⟨(y, ry), ?_, by simp⟩
          exact (mem_epi_restrict_iff).2 ⟨hyC, by simp [hry]⟩
        have hsInf_le_ry : sInf (Prod.snd '' P) ≤ ry :=
          csInf_le hheight_bddBelow' hry_mem
        have hp₂_le_ry : p.2 ≤ ry := by
          calc
            p.2 = sInf (Prod.snd '' P) := by simpa using hp₂
            _ ≤ ry := hsInf_le_ry
        have hpy : h p.1 ≤ (ry : WithBotTop 𝕜) := by
          simpa [hp_eq] using
            (WithBotTop.coe_le_coe.mpr hp₂_le_ry : (p.2 : WithBotTop 𝕜) ≤ (ry : WithBotTop 𝕜))
        simpa [hry.symm] using hpy
    · obtain ⟨x, hxC⟩ := hC_nonempty
      have hxTop : h x = ⊤ := by
        by_contra hxTop
        exact hfinite ⟨x, hxC, lt_of_le_of_ne le_top hxTop⟩
      refine ⟨x, hxC, isMinOn_iff.mpr ?_⟩
      intro y hyC
      have hyTop : h y = ⊤ := by
        by_contra hyTop
        exact hfinite ⟨y, hyC, lt_of_le_of_ne le_top hyTop⟩
      simp [hxTop, hyTop]

/-- Source-facing lower-bound bridge: a scalar lower bound on `h` over `C` induces the
`BddBelow` hypothesis on `Prod.snd '' (epi[C] h : Set (E × 𝕜))` needed by the core owner theorem.
-/
theorem exists_mem_isMinOn_of_isClosed_heightProjection_of_lower_bound
    (hC_nonempty : C.Nonempty)
    (hlower : ∃ α : 𝕜, ∀ x ∈ C, (α : WithBotTop 𝕜) ≤ h x)
    (hheight_closed :
      IsClosed (Prod.snd '' (epi[C] h : Set (E × 𝕜)))) :
    ∃ x ∈ C, IsMinOn h C x := by
  rcases hlower with ⟨α, hα⟩
  have hheight_bddBelow :
      BddBelow (Prod.snd '' (epi[C] h : Set (E × 𝕜))) := by
    refine ⟨α, ?_⟩
    rintro _ ⟨p, hpP, rfl⟩
    rcases (mem_epi_restrict_iff.mp hpP) with ⟨hpC, hp_epi⟩
    exact WithBotTop.coe_le_coe.mp <| le_trans (hα p.1 hpC) hp_epi
  exact exists_mem_isMinOn_of_isClosed_heightProjection_of_bddBelow
    hC_nonempty hheight_bddBelow hheight_closed

end Function

end CoreMinimization

section PolyhedralBridge

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

namespace Function.HasPolyhedralEpigraph

variable {h : E → WithBotTop 𝕜} {C : Set E}

/-- Core bridge companion for Corollary 6.27.4: polyhedrality assumptions provide closedness of
the constrained-epigraph height projection, so the intrinsic bounded-below hypothesis on that
height projection suffices to get an attained minimum on `C`. -/
theorem exists_mem_isMinOn_of_isPolyhedral_of_bddBelow_heightProjection
    (hh : h.HasPolyhedralEpigraph) (hC_poly : C.IsPolyhedral 𝕜) (hC_nonempty : C.Nonempty)
    (hheight_bddBelow :
      BddBelow (Prod.snd '' (epi[C] h : Set (E × 𝕜)))) :
    ∃ x ∈ C, IsMinOn h C x := by
  let fstMap : E × 𝕜 →ₗ[𝕜] E := LinearMap.fst 𝕜 E 𝕜
  let sndMap : E × 𝕜 →ₗ[𝕜] 𝕜 := LinearMap.snd 𝕜 E 𝕜
  let P : Set (E × 𝕜) := epi[C] h
  have hP_eq : P = epi h ∩ fstMap ⁻¹' C := by
    ext p
    constructor
    · intro hp
      rcases (mem_epi_restrict_iff.mp hp) with ⟨hpC, hp_epi⟩
      exact ⟨(mem_epi_iff).2 hp_epi, by simpa [fstMap] using hpC⟩
    · intro hp
      rcases hp with ⟨hp_epi, hpC⟩
      exact (mem_epi_restrict_iff).2 ⟨by simpa [fstMap] using hpC, (mem_epi_iff).1 hp_epi⟩
  have hP_poly : P.IsPolyhedral 𝕜 := by
    rw [hP_eq]
    exact Set.IsPolyhedral.inter 𝕜 hh (hC_poly.linear_preimage fstMap)
  have hheight_poly : (sndMap '' P).IsPolyhedral 𝕜 :=
    hP_poly.linear_image sndMap
  have hheight_closed_linear : IsClosed (sndMap '' P) :=
    hheight_poly.isClosed_of_finiteDimensional
  have hheight_closed : IsClosed (Prod.snd '' P) := by
    simpa [sndMap] using hheight_closed_linear
  exact
    Function.exists_mem_isMinOn_of_isClosed_heightProjection_of_bddBelow
      hC_nonempty (by simpa [P] using hheight_bddBelow) (by simpa [P] using hheight_closed)

/-- Source-facing form of Corollary 6.27.4: an explicit scalar lower bound on `h` over `C`
induces the intrinsic bounded-below hypothesis on the constrained-epigraph height projection. -/
theorem exists_mem_isMinOn_of_isPolyhedral_of_lower_bound
    (hh : h.HasPolyhedralEpigraph) (hC_poly : C.IsPolyhedral 𝕜) (hC_nonempty : C.Nonempty)
    (hlower : ∃ α : 𝕜, ∀ x ∈ C, (α : WithBotTop 𝕜) ≤ h x) :
    ∃ x ∈ C, IsMinOn h C x := by
  rcases hlower with ⟨α, hα⟩
  have hheight_bddBelow :
      BddBelow (Prod.snd '' (epi[C] h : Set (E × 𝕜))) := by
    refine ⟨α, ?_⟩
    rintro _ ⟨p, hpP, rfl⟩
    rcases (mem_epi_restrict_iff.mp hpP) with ⟨hpC, hp_epi⟩
    exact WithBotTop.coe_le_coe.mp <| le_trans (hα p.1 hpC) hp_epi
  exact exists_mem_isMinOn_of_isPolyhedral_of_bddBelow_heightProjection
    hh hC_poly hC_nonempty hheight_bddBelow

/-- Core companion at the intrinsic owner layer: under polyhedral assumptions and boundedness
of the constrained-epigraph height projection, some point of `C` realizes `sInf (h '' C)`. -/
theorem exists_mem_eq_sInf_image_of_isPolyhedral_of_bddBelow_heightProjection
    (hh : h.HasPolyhedralEpigraph) (hC_poly : C.IsPolyhedral 𝕜) (hC_nonempty : C.Nonempty)
    (hheight_bddBelow :
      BddBelow (Prod.snd '' (epi[C] h : Set (E × 𝕜)))) :
    ∃ x ∈ C, h x = sInf (h '' C) := by
  obtain ⟨x, hxC, hxmin⟩ :=
    exists_mem_isMinOn_of_isPolyhedral_of_bddBelow_heightProjection
      hh hC_poly hC_nonempty hheight_bddBelow
  have hleast : IsLeast (h '' C) (h x) := by
    refine ⟨⟨x, hxC, rfl⟩, ?_⟩
    rintro _ ⟨y, hyC, rfl⟩
    exact (isMinOn_iff.mp hxmin) y hyC
  exact ⟨x, hxC, (IsLeast.csInf_eq hleast).symm⟩

/-- Source-facing companion: under the same hypotheses, some point of `C` realizes the infimum
`inf_{x ∈ C} h x`, written canonically as `sInf (h '' C)`. -/
theorem exists_mem_eq_sInf_image_of_isPolyhedral_of_lower_bound
    (hh : h.HasPolyhedralEpigraph) (hC_poly : C.IsPolyhedral 𝕜) (hC_nonempty : C.Nonempty)
    (hlower : ∃ α : 𝕜, ∀ x ∈ C, (α : WithBotTop 𝕜) ≤ h x) :
    ∃ x ∈ C, h x = sInf (h '' C) := by
  rcases hlower with ⟨α, hα⟩
  have hheight_bddBelow :
      BddBelow (Prod.snd '' (epi[C] h : Set (E × 𝕜))) := by
    refine ⟨α, ?_⟩
    rintro _ ⟨p, hpP, rfl⟩
    rcases (mem_epi_restrict_iff.mp hpP) with ⟨hpC, hp_epi⟩
    exact WithBotTop.coe_le_coe.mp <| le_trans (hα p.1 hpC) hp_epi
  exact exists_mem_eq_sInf_image_of_isPolyhedral_of_bddBelow_heightProjection
    hh hC_poly hC_nonempty hheight_bddBelow

end Function.HasPolyhedralEpigraph

end PolyhedralBridge
