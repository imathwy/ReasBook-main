import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_6_27_3 (from Chap06) -/
open scoped Pointwise
open scoped Rockafellar
open Set

noncomputable section

universe u

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 27.3 says that a closed proper convex function on a finite-dimensional
  topological vector space over `𝕜` attains its infimum on a nonempty closed convex set `C` when
  `C` and the function have no common nonzero recession direction.
- `core/canonical`: the owner abstractions already present in the project are `IsMinOn` for
  minimizers, `Set.RecedesInDirection` and `Function.RecedesInDirection` for the source-facing
  recession-direction predicates, the Chapter 2 recession-cone owner
  `((h)₀⁺).recessionCone` for the function-side core criterion.
- `bridge/view`: the source-facing exclusion of a common recession direction is converted in the
  proof to the Chapter 9 recession-kernel hypothesis using
  `Function.recedesInDirection_iff_mem_recessionCone` under primitive convex/proper assumptions,
  then fed into the
  translate-attainment theorem
  `exists_mem_translate_eq_infimal_convolution_of_no_common_recession_direction`, specialized at
  the translate parameter `x = 0`, together with the companion identity
  `infimal_convolution_indicator_neg_eq_sInf_image_translate`.

Domain-style sampling used here:
- `IsMinOn` from mathlib's order-extrema API;
- `Set.RecedesInDirection` from `Chap02/Definition_8_0_1`;
- `Function.RecedesInDirection` from `Definition_6_27_4`;
- object-prefix recession-cone owner `(·).recessionCone` from `Chap02/Definiton_8_5_0`;
- `exists_mem_translate_eq_infimal_convolution_of_no_common_recession_direction` from
  `Chap02/Example_9_2_2_2`.

Primitive data vs derived API:
- primitive inputs: the closed convex constraint set `C`, the closed proper convex function `h`,
  nonemptiness of `C`, and the source-facing exclusion
  `¬ ∃ y, C.RecedesInDirection 𝕜 y ∧ h.RecedesInDirection 𝕜 y`;
- derived API: existence of a minimizer in the canonical owner form `∃ x ∈ C, IsMinOn h C x`,
  and the companion source wording `h x = sInf (h '' C)`.

Layer target: `source-facing`, but with the main public theorem stated on the canonical minimizer
owner `IsMinOn` rather than through a new local wrapper around attained infima.
- scalar-layer note: this item follows the scalar-generic ambient layer already used by the
  Chapter 2 translate-attainment theorem. Closed/proper/convex assumptions are kept in primitive
  canonical owner form (`IsConvex`, `IsProper`, `LowerSemicontinuous`) rather than bundled in a
  stronger real-only owner.
- bridge-layer note: the source-to-core recession-direction equivalence is stated on the weaker
  ordered-module layer needed by the recession-cone bridge, while attainment itself stays on the
  finite-dimensional topological layer required by the Chapter 2/9 translate theorem.
-/

section RecessionBridge

variable {𝕜 : Type*} {E : Type u}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [AddRightMono 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

-- Proof sketch: the source-facing no-common-direction hypothesis is equivalent (under
-- convex/proper assumptions on `h`) to the canonical recession-cone kernel condition used by the
-- Chapter 2/9 attainment bridge.
theorem no_common_recession_direction_iff_recessionCone_inter_subset_zero
    {C : Set E} {h : E → WithTopBot 𝕜}
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) :
    (¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧ h.RecedesInDirection 𝕜 y) ↔
      0⁺[𝕜]C ∩ ((h)₀⁺).recessionCone ⊆ {0} := by
  constructor
  · intro hno_common y hy
    rcases hy with ⟨hyC, hyh⟩
    have hy0 : y = 0 := by
      by_contra hy_ne
      have hyC' : C.RecedesInDirection 𝕜 y := ⟨hy_ne, hyC⟩
      have hyh' : h.RecedesInDirection 𝕜 y :=
        Function.RecedesInDirection.of_mem_recessionCone hh_convex hh_proper hy_ne hyh
      exact hno_common ⟨y, hyC', hyh'⟩
    simp [hy0]
  · intro hno_common
    rintro ⟨y, hyC, hyh⟩
    have hy_mem : y ∈ 0⁺[𝕜]C ∩ ((h)₀⁺).recessionCone := by
      refine ⟨hyC.2, ?_⟩
      exact Function.RecedesInDirection.mem_recessionCone hyh hh_convex hh_proper
    have hy0 : y = 0 := by simpa using hno_common hy_mem
    exact hyC.1 hy0

end RecessionBridge

section Attainment

variable {𝕜 : Type*} {E : Type u}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

-- Proof sketch: specialize the Chapter 9 translate-attainment theorem to `x = 0`; the attained
-- infimal-convolution value at `0` is identified with `sInf (h '' C)`, yielding `IsMinOn`.
/-- Canonical owner form of Theorem 27.3: if `C` is nonempty, closed, and convex and if `h` is
convex, proper, and lower semicontinuous, then the recession-kernel condition
`0⁺[𝕜]C ∩ ((h)₀⁺).recessionCone ⊆ {0}` implies that `h` attains its infimum on `C`. -/
theorem exists_mem_isMinOn_of_recessionCone_inter_subset_zero
    {C : Set E} {h : E → WithTopBot 𝕜}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper)
    (hh_closed : LowerSemicontinuous h)
    (hno_common :
      0⁺[𝕜]C ∩ ((h)₀⁺).recessionCone ⊆ {0}) :
    ∃ x ∈ C, IsMinOn h C x := by
  obtain ⟨x, hxC, hxeq⟩ :=
    exists_mem_translate_eq_infimal_convolution_of_no_common_recession_direction
      hC_closed hC_convex hno_common hC_nonempty hh_convex hh_proper.bot_lt hh_closed (0 : E)
  have hxC' : x ∈ C := by
    simpa using hxC
  have hsInf : h x = sInf (h '' C) := by
    rw [← hxeq]
    simpa using
      (infimal_convolution_indicator_neg_eq_sInf_image_translate C h hh_proper.bot_lt (0 : E))
  refine ⟨x, hxC', isMinOn_iff.mpr ?_⟩
  intro z hzC
  rw [hsInf]
  exact sInf_le ⟨z, hzC, rfl⟩

-- Proof sketch: convert the source-facing no-common-direction hypothesis to the canonical
-- recession-kernel condition and apply the canonical attainment theorem above.
/-- Source-facing form of Theorem 27.3: if `C` and `h` have no common nonzero recession
direction, then `h` attains its infimum on `C` (in canonical owner form `IsMinOn`). -/
theorem exists_mem_isMinOn_of_no_common_recession_direction
    {C : Set E} {h : E → WithTopBot 𝕜}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hno_common : ¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧ h.RecedesInDirection 𝕜 y) :
    ∃ x ∈ C, IsMinOn h C x := by
  have hno_common' :
      0⁺[𝕜]C ∩ ((h)₀⁺).recessionCone ⊆ {0} :=
    (no_common_recession_direction_iff_recessionCone_inter_subset_zero
      hh_convex hh_proper).1 hno_common
  exact exists_mem_isMinOn_of_recessionCone_inter_subset_zero
    hC_nonempty hC_closed hC_convex hh_convex hh_proper hh_closed hno_common'

/-- Source-facing companion to Theorem 27.3: under the same hypotheses, some point of `C`
realizes the infimum `inf_{x ∈ C} h x`, written canonically as `sInf (h '' C)`. -/
theorem exists_mem_eq_sInf_image_of_no_common_recession_direction
    {C : Set E} {h : E → WithTopBot 𝕜}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hno_common : ¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧ h.RecedesInDirection 𝕜 y) :
    ∃ x ∈ C, h x = sInf (h '' C) := by
  obtain ⟨x, hxC, hxmin⟩ :=
    exists_mem_isMinOn_of_no_common_recession_direction
      hC_nonempty hC_closed hC_convex hh_convex hh_proper hh_closed hno_common
  have hxmin' : ∀ y ∈ C, h x ≤ h y := isMinOn_iff.mp hxmin
  refine ⟨x, hxC, le_antisymm ?_ ?_⟩
  · exact le_sInf fun y hyC ↦ by
      rcases hyC with ⟨z, hzC, rfl⟩
      exact hxmin' z hzC
  · exact sInf_le ⟨x, hxC, rfl⟩

end Attainment

/-! ### Corollary_6_27_4 (from Chap06) -/
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

/-! ### Definition_6_27_4 (from Chap06) -/
universe u v w

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
  [Preorder β] [Top β] [Preorder 𝕜] [Zero 𝕜] [Zero E] [Add E] [SMul 𝕜 E]

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.4 introduces a direction of recession of an extended-real-valued
  function `f` as a nonzero vector `y` such that every ray profile
  `λ ↦ f (x + λ • y)` is non-increasing for `λ ≥ 0`, starting from every base point
  `x ∈ dom(f)`.
- `core/canonical`: the primitive owner only needs order and top on the codomain so that
  `dom(f)` and the ray inequality are meaningful; this is kept codomain-generic as
  `f : E → β` with `[Preorder β] [Top β]`.
- `bridge/canonical`: the closest existing owner abstraction already present upstream is the
  Chapter 2 recession-cone owner `Function.recessionCone`, applied to the recession function
  `((f)₀⁺)`. However, that owner matches the present source notion canonically only
  under additional convex/proper hypotheses from Theorem 8.6.
- `bridge/view`: the file therefore keeps the textbook predicate as the primitive public owner and
  adds only a thin bridge to `((f)₀⁺).recessionCone` under the stronger
  owner hypotheses `f.IsConvex 𝕜` and `f.IsProper`.

Domain-style sampling used here:
- `Set.RecedesInDirection` from `Chap02/Definition_8_0_1`, which keeps the source-facing nonzero
  direction predicate while delegating the core geometry to `recessionCone`, and makes the scalar
  a core owner parameter because it is not recoverable from the set and the direction;
- `Function.recessionCone` and `Function.mem_recessionCone_iff` from `Chap02/Definiton_8_5_0`;
- `Function.forall_antitone_translate_iff_mem_recessionCone` from
  `Chap02/Theorem_8_6`, giving the convex/proper bridge from linewise monotonicity to
  recession-function nonpositivity.

Primitive data vs derived API:
- primitive source-facing data: the function `f`, the direction `y`, nonzeroness of `y`, and for
  each `x ∈ dom(f)` the canonical order-theoretic owner `AntitoneOn` of the forward ray profile
  `t ↦ f (x + t • y)` on `Set.Ici 0`;
- derived public API: the textbook basepoint inequality `f (x + λ • y) ≤ f x` for `λ ≥ 0`, and
  under convexity/proper hypotheses the canonical bridge to membership in
  `((f)₀⁺).recessionCone`;
- companion bridge: on additive commutative monoids, the same source-facing predicate is
  equivalent to
  antitonicity of every translate profile on the whole scalar line, which feeds directly into
  Theorem 8.6.

Layer target: `source-facing`. The source notion is more general than the Chapter 2 recession
function owner, so the refinement preserves that general source predicate and connects it to the
more specific owner abstraction only when the needed hypotheses are made explicit. As on the set
side, the scalar is a core owner parameter and stays explicit in the public API.
-/

namespace Function

variable (𝕜)

/-- Definition 6.27.4: a nonzero vector `y` is a direction of recession of `f` when every forward
ray profile `λ ↦ f (x + λ • y)` is non-increasing from every base point `x ∈ dom(f)`.

The scalar is a core owner parameter for this notion and cannot be recovered from `f` and `y`, so
the primary owner is scalar-parameterized. The textbook real statement is a specialization. -/
def RecedesInDirection (f : E → β) (y : E) : Prop :=
  y ≠ 0 ∧ ∀ x ∈ dom(f), AntitoneOn (fun t : 𝕜 ↦ f (x + t • y)) (Set.Ici 0)

variable {𝕜}

namespace RecedesInDirection

theorem ne_zero {f : E → β} {y : E} (hy : f.RecedesInDirection 𝕜 y) : y ≠ 0 :=
  hy.1

theorem antitoneOn_translate {f : E → β} {y : E} (hy : f.RecedesInDirection 𝕜 y)
    {x : E} (hx : x ∈ dom(f)) :
    AntitoneOn (fun t : 𝕜 ↦ f (x + t • y)) (Set.Ici 0) :=
  hy.2 x hx

end RecedesInDirection

end Function

end

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
  [Preorder β] [Top β] [Preorder 𝕜] [Zero 𝕜]
  [AddZeroClass E] [SMulWithZero 𝕜 E]

open scoped Rockafellar

namespace Function

namespace RecedesInDirection

theorem ray_le {f : E → β} {y : E} (hy : f.RecedesInDirection 𝕜 y)
    {x : E} (hx : x ∈ dom(f)) {t : 𝕜} (ht : 0 ≤ t) :
    f (x + t • y) ≤ f x :=
  by
    have hle : f (x + t • y) ≤ f (x + (0 : 𝕜) • y) :=
      (hy.antitoneOn_translate hx) (by simp) ht ht
    simpa [zero_smul, add_zero] using hle

end RecedesInDirection

end Function

end

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
  [Preorder β] [Top β] [Ring 𝕜] [Preorder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

/-- The source-facing recession-direction predicate is exactly nonzeroness together with the
textbook ray inequality. -/
theorem recedesInDirection_iff {f : E → β} {y : E} :
    f.RecedesInDirection 𝕜 y ↔
      y ≠ 0 ∧ ∀ x ∈ dom(f), ∀ t : 𝕜, 0 ≤ t → f (x + t • y) ≤ f x :=
  by
    constructor
    · rintro ⟨hy, hanti⟩
      refine ⟨hy, ?_⟩
      intro x hx t ht
      have hle : f (x + t • y) ≤ f (x + (0 : 𝕜) • y) := hanti x hx (by simp) ht ht
      simpa [zero_smul, add_zero] using hle
    · rintro ⟨hy, hray⟩
      refine ⟨hy, ?_⟩
      intro x hx s hs t ht hst
      have hxs : x + s • y ∈ dom(f) := by
        rw [mem_effectiveDomain]
        exact lt_of_le_of_lt (hray x hx s hs) hx
      have hle := hray (x + s • y) hxs (t - s) (sub_nonneg.mpr hst)
      have hsmul : s • y + (t - s) • y = (s + (t - s)) • y := by
        exact (add_smul s (t - s) y).symm
      have htranslate : x + (s • y + (t - s) • y) = x + t • y := by
        calc
          x + (s • y + (t - s) • y) = x + (s + (t - s)) • y := by rw [hsmul]
          _ = x + t • y := by rw [add_sub_cancel]
      simpa [add_assoc, htranslate] using hle

end Function

end

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}
  [Preorder α] [Ring 𝕜] [Preorder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

-- Proof sketch: if `f` recedes in the source-facing sense, then for `s ≤ t` one applies the
-- defining ray inequality at the shifted base point `x + s • y` with step `t - s`. Conversely,
-- antitonicity of every translate profile immediately gives the source ray inequality by setting
-- `s = 0`.
/-- On additive commutative monoids, the source-facing recession-direction predicate is equivalent
to antitonicity of every translate profile on the whole scalar line. -/
theorem recedesInDirection_iff_forall_antitone_translate
    {f : E → WithTopBot α} {y : E} :
    f.RecedesInDirection 𝕜 y ↔
      y ≠ 0 ∧ ∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y)) := by
  constructor
  · rintro ⟨hy, hanti⟩
    refine ⟨hy, ?_⟩
    intro x s t hst
    by_cases hxs : x + s • y ∈ dom(f)
    · have hle := hanti (x + s • y) hxs (by simp) (sub_nonneg.mpr hst) (sub_nonneg.mpr hst)
      have hsmul : s • y + (t - s) • y = (s + (t - s)) • y := by
        exact (add_smul s (t - s) y).symm
      have hleft : x + (s • y + (t - s) • y) = x + t • y := by
        calc
          x + (s • y + (t - s) • y) = x + (s + (t - s)) • y := by rw [hsmul]
          _ = x + t • y := by rw [add_sub_cancel]
      have hright : x + (s • y + (0 : 𝕜) • y) = x + s • y := by simp
      simpa [add_assoc, hleft, hright] using hle
    · rw [mem_effectiveDomain] at hxs
      have hs_top : f (x + s • y) = (⊤ : WithTopBot α) := by
        by_contra hs_top
        have hlt : f (x + s • y) < (⊤ : WithTopBot α) := by
          cases hfx : f (x + s • y) using WithBotTop.rec with
          | bot =>
              simpa [hfx] using (WithBot.bot_lt_coe (⊤ : WithTop α))
          | coe a =>
              simpa [hfx] using (WithBotTop.coe_lt_top a)
          | top =>
              exact False.elim (hs_top hfx)
        exact hxs hlt
      simp [hs_top]
  · rintro ⟨hy, hanti⟩
    refine ⟨hy, ?_⟩
    intro x hx
    exact fun s hs t ht hst ↦ hanti x hst

end Function

end

section

variable {𝕜 : Type v} {E : Type u}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddRightMono 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

-- Proof sketch: Theorem 8.6 identifies the antitonicity of all translate profiles directly with
-- membership in `((f)₀⁺).recessionCone`.
/-- Under the canonical convex/proper hypotheses, the source-facing recession-direction predicate
is exactly nonzeroness together with membership in the owner recession cone
`((f)₀⁺).recessionCone`. -/
@[simp] theorem recedesInDirection_iff_mem_recessionCone
    {f : E → WithTopBot 𝕜} {y : E}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    f.RecedesInDirection 𝕜 y ↔
      y ∈ ((f)₀⁺).recessionCone ∧ y ≠ 0 := by
  rw [recedesInDirection_iff_forall_antitone_translate]
  constructor
  · rintro ⟨hy, hanti⟩
    exact
      ⟨(forall_antitone_translate_iff_mem_recessionCone
        (f := f) hf_convex hf_proper y).mp hanti, hy⟩
  · rintro ⟨hy_mem, hy⟩
    exact
      ⟨hy, (forall_antitone_translate_iff_mem_recessionCone
        (f := f) hf_convex hf_proper y).mpr hy_mem⟩

namespace RecedesInDirection

/-- Under convex/proper hypotheses, a recession direction belongs to the recession cone of the
recession function. -/
theorem mem_recessionCone
    {f : E → WithTopBot 𝕜} {y : E}
    (hy : f.RecedesInDirection 𝕜 y)
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    y ∈ ((f)₀⁺).recessionCone := by
  exact ((recedesInDirection_iff_mem_recessionCone
    (f := f) (y := y) hf_convex hf_proper).mp hy).1

/-- Under convex/proper hypotheses, nonzero membership in `((f)₀⁺).recessionCone` gives a
source-facing recession direction. -/
theorem of_mem_recessionCone
    {f : E → WithTopBot 𝕜} {y : E}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hy_ne : y ≠ 0) (hy_mem : y ∈ ((f)₀⁺).recessionCone) :
    f.RecedesInDirection 𝕜 y := by
  exact (recedesInDirection_iff_mem_recessionCone
    (f := f) (y := y) hf_convex hf_proper).mpr ⟨hy_mem, hy_ne⟩

end RecedesInDirection

end Function

end

/-! ### Proposition_6_27_4 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.4 states that the minimum set `M` of a convex function is a
  convex subset.
- `core/canonical`: the source-facing set owner is `minimumSet`, and the primitive convexity owner
  for this item is `QuasiconvexOn 𝕜 Set.univ f`; convexity of a minimum set only needs convexity
  of all closed sublevel sets.
- `bridge/view`: intrinsically, `minimumSet f` is the intersection of the sublevel sets
  `{x | f x ≤ f y}` over all `y`, so the canonical theorem applies `QuasiconvexOn` pointwise and
  intersects the resulting convex sets; Proposition 6.27.4 is then the specialization
  `Function.IsConvex → QuasiconvexOn`.

Domain-style sampling used here:
- the Chapter 6 minimum-set owner `minimumSet` from Definition 6.27.3;
- the extrema owner theorem `isMinOn_univ_iff` from mathlib;
- `QuasiconvexOn 𝕜 (Set.univ : Set E)` from mathlib's ordered convex-analysis owner layer;
- `Function.IsConvex 𝕜` from the chapter convex-function owner layer;
- `ConvexOn.convex_le` from mathlib for convex closed-sublevel sets.

Primitive data vs derived API:
- primitive input: a function `f` and a quasiconvexity owner on `Set.univ`;
- derived API: convexity of the canonical minimum set `minimumSet f`;
- source-facing specialization: the convex-function owner `f.IsConvex 𝕜`.

Layer target: `source-facing`, stated directly on the canonical owner `minimumSet f` rather than
on the equivalent raw sublevel-set expression.
-/

universe u v w

open scoped Rockafellar

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [Preorder β]

namespace QuasiconvexOn

-- Proof sketch: `minimumSet f` is exactly the intersection of the sublevel sets
-- `{x | f x ≤ f y}` as `y` varies. Quasiconvexity on `Set.univ` says each of these sublevel
-- sets is convex, and arbitrary intersections of convex sets are convex.
/-- A quasiconvex function on the whole ambient space has a convex minimum set. -/
theorem convex_minimumSet {f : E → β} (hf : QuasiconvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (argmin(f)) := by
  have hminimumSet :
      argmin(f) = ⋂ y : E, {x : E | f x ≤ f y} := by
    ext x
    simp [mem_minimumSet_iff]
  rw [hminimumSet]
  refine convex_iInter ?_
  intro y
  simpa [Set.sep_univ] using hf (f y)

end QuasiconvexOn

/-- The minimum set of a quasiconvex function on the ambient space is convex. -/
theorem minimumSet_isConvex_of_quasiconvexOn {f : E → β}
    (hf_quasiconvex : QuasiconvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (argmin(f)) :=
  hf_quasiconvex.convex_minimumSet

end

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

namespace ConvexOn

-- Proof sketch: rewrite `minimumSet f` as an intersection of closed sublevel sets
-- `{x | f x ≤ f y}` and apply the intrinsic owner theorem `ConvexOn.convex_le` to each
-- level `f y`.
/-- A convex function on the whole ambient space has a convex minimum set. -/
theorem convex_minimumSet {f : E → β} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    Convex 𝕜 (argmin(f)) := by
  have hminimumSet :
      argmin(f) = ⋂ y : E, {x : E | f x ≤ f y} := by
    ext x
    simp [mem_minimumSet_iff]
  rw [hminimumSet]
  refine convex_iInter ?_
  intro y
  simpa [Set.sep_univ] using hf.convex_le (r := f y)

end ConvexOn

end

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

namespace Function.IsConvex

-- Proof sketch: pass from the chapter owner `Function.IsConvex` to whole-space quasiconvexity
-- via `Function.IsConvex.quasiconvexOn`, then apply `QuasiconvexOn.convex_minimumSet`.
/-- A convex function has a convex minimum set. -/
theorem convex_minimumSet {f : E → WithTopBot α} (hf : f.IsConvex 𝕜) :
    Convex 𝕜 (argmin(f)) := by
  exact (hf.quasiconvexOn).convex_minimumSet

end Function.IsConvex

/-- Proposition 6.27.4: the minimum set of a convex function is a convex subset of the ambient
module. -/
theorem minimumSet_isConvex {f : E → WithTopBot α} (hf_convex : f.IsConvex 𝕜) :
    Convex 𝕜 (argmin(f)) :=
  hf_convex.convex_minimumSet

end

/-! ### Theorem_6_27_4 (from Chap06) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v

section

variable {𝕜 : Type v} [AddGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommGroup E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 27.4 is the constrained first-order optimality criterion: a feasible
  minimizer of a convex function on a convex set is characterized by a subgradient whose negative
  lies in the normal cone of the constraint set.
- `core/canonical`: the owner abstractions already present upstream are `IsMinOn`,
  `subdifferentialAt`, `N[𝕜](· | ·)`, `riDom[𝕜](·)`, and `ri[𝕜](·)`.
- `bridge/view`: the textbook optimality condition is best expressed directly on those owners,
  rather than by introducing a packaged constrained-minimum structure or a duplicate local
  “KKT-point” wrapper.

Domain-style sampling used here:
- `IsMinOn` from mathlib's order-extrema API;
- `N[𝕜](· | ·)` from `Chap01.Definition_2_7_10`;
- `subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive inputs: the convex constraint set `C`, the convex function `h`, the base point `x`,
  the pairing codomain `N`, and the owner-side optimality witness
  `xStar ∈ ∂[N]h(x)` with `-xStar ∈ N[𝕜](x | C)`;
- derived API: feasibility of `x`, the canonical minimizer owner `IsMinOn h C x`, and under the
  relative-interior qualification the full equivalence between minimizers and normal-cone
  subgradient witnesses.

Ambient-layer lock-in:
- the current canonical owner `subdifferentialAt` is defined for
  `h : E → WithTopBot 𝕜` and supports pairing-based witness codomains `N`;
- the companion normal-cone owner used here is `N[𝕜](· | ·)`;
- the owner-level sufficiency theorem below is pairing-intrinsic at codomain `N`, and uses only
  the pairing-compatibility data needed for sign/subtraction rewrites in the normal-cone and
  subgradient inequalities, over scalar/order assumptions
  `[AddGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]`.
- the later equivalence theorem keeps the stronger finite-dimensional normed-space layer required by
  the relative-interior qualification machinery.

Layer target: `source-facing`. The numbered item states a theorem about the existing owners
`IsMinOn`, `subdifferentialAt`, and `N[𝕜](· | ·)`; it does not own a new abstraction.
-/

-- Proof sketch: combine the subgradient inequality for `h` at `x` with the defining inequality of
-- `N[𝕜](x | C)` for `-xStar`. On every `z ∈ C`, the normal-cone inequality gives
-- `(⟪z - x, xStar⟫ₚ : 𝕜) ≥ 0`, so the subgradient inequality reduces to `h x ≤ h z`. The same
-- normal-cone membership, via `mem_normalCone_iff`, already forces the feasibility condition
-- `x ∈ C`.
/-- A subgradient at `x` whose negative lies in the normal cone to `C` at `x` certifies that `x`
is feasible and minimizes `h` over `C`. -/
theorem isMinOn_of_mem_subdifferentialAt_and_neg_mem_normalCone
    {N : Type (max u v)} [AddCommGroup N]
    [HasPairing E N 𝕜] [HasPairingSubLeft E N 𝕜] [HasPairingNegRight E N 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E} {xStar : N}
    (hxStar_sub : xStar ∈ ∂[N]h(x))
    (hxStar_normal : -xStar ∈ N[𝕜](x | C)) :
    x ∈ C ∧ IsMinOn h C x := by
  rcases (mem_normalCone_iff_sub_nonpos.mp hxStar_normal) with ⟨hxC, hxStar_normal'⟩
  refine ⟨hxC, (isMinOn_iff.mpr ?_)⟩
  intro z hzC
  have hsub : h x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ h z := by
    simpa [ge_iff_le] using (mem_subdifferentialAt_pairing.mp hxStar_sub) z
  have hnonneg_scalar : 0 ≤ (⟪z - x, xStar⟫ₚ : 𝕜) := by
    have hnonneg_neg : 0 ≤ -(⟪z - x, -xStar⟫ₚ : 𝕜) :=
      neg_nonneg.mpr (hxStar_normal' z hzC)
    simpa [HasPairingNegRight.pairing_neg_right] using hnonneg_neg
  have hnonneg : (0 : WithTopBot 𝕜) ≤ ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
    simpa using (WithTopBot.coe_le_coe.mpr hnonneg_scalar)
  have hx_le_add : h x ≤ h x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hnonneg (h x))
  exact le_trans hx_le_add hsub

/-- Existential-witness wrapper of
`isMinOn_of_mem_subdifferentialAt_and_neg_mem_normalCone`. -/
theorem isMinOn_of_exists_subgradient_neg_mem_normalCone
    {N : Type (max u v)} [AddCommGroup N]
    [HasPairing E N 𝕜] [HasPairingSubLeft E N 𝕜] [HasPairingNegRight E N 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hopt :
      ∃ xStar : N,
        xStar ∈ ∂[N]h(x) ∧ -xStar ∈ N[𝕜](x | C)) :
    x ∈ C ∧ IsMinOn h C x := by
  rcases hopt with ⟨xStar, hxStar_sub, hxStar_normal⟩
  exact isMinOn_of_mem_subdifferentialAt_and_neg_mem_normalCone hxStar_sub hxStar_normal

end

section

variable {𝕜 : Type v} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddLeftMono 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

-- Proof sketch: view minimization of `h` on `C` as unconstrained minimization of
-- `h + indicatorFunction C`, use the Chapter 23/25 owner layer for subdifferentials of the
-- indicator-augmented objective under the relative-interior qualification, and rewrite the
-- resulting vanishing-subgradient condition as the existence of
-- `xStar ∈ (∂ h at x)` with `-xStar ∈ N[𝕜](x | C)`.
/-- Theorem 27.4: in a finite-dimensional seminormed space over `𝕜`, under the relative-interior
qualification `riDom[𝕜](h) ∩ ri[𝕜](C) ≠ ∅`, a point `x` is a feasible minimizer of a convex
function `h` on a convex set `C` exactly when some dual subgradient at `x` has negative
lying in the normal cone of `C` at `x`. The theorem is stated directly on the canonical owners
`IsMinOn`, `subdifferentialAt`, and `N[𝕜](· | ·)`. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hneBot : ∀ y, h y ≠ ⊥) (hh_convex : h.IsConvex 𝕜) (hC_convex : Convex 𝕜 C)
    (hqual : (riDom[𝕜](h) ∩ ri[𝕜](C)).Nonempty) :
    (x ∈ C ∧ IsMinOn h C x) ↔
      ∃ xStar : StrongDual 𝕜 E,
        xStar ∈ (∂ h at x) ∧ -xStar ∈ N[𝕜](x | C) := by
  constructor
  · intro hxmin
    let f : Fin 2 → E → WithTopBot 𝕜 := Fin.cases (δ[𝕜](· | C)) (fun _ : Fin 1 => h)
    have hh_proper : h.IsProper := by
      rcases hqual with ⟨xq, hxq_ri, _⟩
      refine (Function.isProper_iff (f := h)).2 ?_
      refine ⟨⟨xq, intrinsicInterior_subset hxq_ri⟩, hneBot⟩
    have h_ind_proper : (δ[𝕜](· | C) : E → WithTopBot 𝕜).IsProper := by
      rcases hqual with ⟨xq, _, hxq_ri⟩
      refine (Function.isProper_iff (f := (δ[𝕜](· | C) : E → WithTopBot 𝕜))).2 ?_
      refine ⟨?_, ?_⟩
      · refine ⟨xq, ?_⟩
        rw [mem_effectiveDomain]
        exact
          (indicator_lt_top_iff_mem (α := 𝕜) (C := C) (x := xq)).2
            (intrinsicInterior_subset hxq_ri)
      · intro y
        by_cases hy : y ∈ C
        · simp [hy]
        · simp [hy]
    have hf_convex : ∀ i : Fin 2, (f i).IsConvex 𝕜 := by
      intro i
      fin_cases i
      · simpa [f] using
          ((indicator_isConvex_iff (𝕜 := 𝕜) (C := C)).2 hC_convex :
            (δ[𝕜](· | C) : E → WithTopBot 𝕜).IsConvex 𝕜)
      · simpa [f] using hh_convex
    have hf_proper : ∀ i : Fin 2, (f i).IsProper := by
      intro i
      fin_cases i
      · simpa [f] using h_ind_proper
      · simpa [f] using hh_proper
    have hri_f : (⋂ i : Fin 2, riDom[𝕜](f i)).Nonempty := by
      rcases hqual with ⟨xq, hxq_riDom, hxq_riC⟩
      refine ⟨xq, Set.mem_iInter.mpr ?_⟩
      intro i
      fin_cases i
      · classical
        have hdom_if :
            dom(fun y : E ↦ if y ∈ C then (0 : WithTopBot 𝕜) else ⊤) = C := by
          ext y
          rw [mem_effectiveDomain]
          by_cases hy : y ∈ C
          · simpa [hy] using (WithTopBot.coe_lt_top (0 : 𝕜))
          · simp [hy]
        simpa [f, hdom_if] using hxq_riC
      · simpa [f] using hxq_riDom
    have hsum_sub :
        subdifferentialAt (∑ i, f i) x (StrongDual 𝕜 E) =
          ∑ i, subdifferentialAt (f i) x (StrongDual 𝕜 E) :=
      subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
        f hf_convex hf_proper hri_f x
    have hsum_sub' :
        subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x (StrongDual 𝕜 E) =
          subdifferentialAt (δ[𝕜](· | C)) x (StrongDual 𝕜 E) +
            subdifferentialAt h x (StrongDual 𝕜 E) := by
      simpa [Fin.sum_univ_two, f] using hsum_sub
    have hsum_min :
        ∀ z, (δ[𝕜](x | C) : WithTopBot 𝕜) + h x ≤ (δ[𝕜](z | C) : WithTopBot 𝕜) + h z := by
      intro z
      by_cases hzC : z ∈ C
      · have hxy : h x ≤ h z := (isMinOn_iff.mp hxmin.2) z hzC
        simpa [hxmin.1, hzC, add_comm, add_left_comm, add_assoc] using hxy
      · have hz_top : (δ[𝕜](z | C) : WithTopBot 𝕜) + h z = ⊤ := by
          calc
            (δ[𝕜](z | C) : WithTopBot 𝕜) + h z = ⊤ + h z := by simp [hzC]
            _ = ⊤ := WithTopBot.top_add_of_ne_bot (hneBot z)
        calc
          (δ[𝕜](x | C) : WithTopBot 𝕜) + h x = h x := by simp [hxmin.1]
          _ ≤ ⊤ := le_top
          _ = (δ[𝕜](z | C) : WithTopBot 𝕜) + h z := hz_top.symm
    have hzero_sub :
        (0 : StrongDual 𝕜 E) ∈
          subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x (StrongDual 𝕜 E) := by
      rw [mem_subdifferentialAt]
      intro z
      simpa [ge_iff_le] using hsum_min z
    rw [hsum_sub'] at hzero_sub
    rcases (Set.mem_add.mp hzero_sub) with ⟨u, hu, v, hv, huv0⟩
    refine ⟨v, hv, ?_⟩
    have hu_normal : u ∈ N[𝕜](x | C) := by
      exact
        (subdifferentialAt_indicatorFunction_eq_normalCone
          (𝕜 := 𝕜) (N := StrongDual 𝕜 E) C x) ▸ hu
    have hu_eq : u = -v := eq_neg_of_add_eq_zero_left huv0
    exact hu_eq ▸ hu_normal
  · intro hopt
    exact
      isMinOn_of_exists_subgradient_neg_mem_normalCone
        (N := StrongDual 𝕜 E) hopt

end

/-! ### Corollary_6_27_5 (from Chap06) -/
open scoped Rockafellar

noncomputable section

universe u v

variable {𝕜 : Type*} {E : Type u}

variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.5 concerns minimization of a closed proper convex objective
  `f₀` under an arbitrary family of weak convex inequalities `fᵢ(x) ≤ 0`, first under a
  no-common-recession hypothesis and then under the finite-polyhedral refinement where the
  remaining common recession directions are constant for the objective and the nonpolyhedral
  constraints.
- `core/canonical`: the owner abstractions already present in the project are the Chapter 21 weak
  feasible-set owner `weakConvexInequalitySolutionSet`, the source-facing function recession
  predicate `Function.RecedesInDirection`, the primitive convex/proper/lower-semicontinuous
  owners (`Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`), the
  polyhedral-function owner
  `Function.HasPolyhedralEpigraph`, the canonical constant-translation-direction owner
  `Function.lineal`, and the minimizer owner `IsMinOn`.
- `bridge/view`: textbook consistency is recorded canonically as nonemptiness of the weak feasible
  set, while the conclusion is stated in owner form as existence of a minimizer of `f₀` on that
  feasible set. The second clause keeps the source's finite polyhedral subsystem explicitly as an
  intrinsic finite subset `I₀ : Set I` together with `I₀.Finite`, but phrases constant common
  recession directions through the intrinsic nonpolyhedral owner test
  `¬ (f i).HasPolyhedralEpigraph` and the existing lineality notation `lin(·)`, instead of a
  parallel local predicate.

Domain-style sampling used here:
- `weakConvexInequalitySolutionSet` from `Chap04/Text_21_0_1`;
- `Function.RecedesInDirection` from `Chap06/Definition_6_27_4`;
- `exists_mem_isMinOn_of_no_common_recession_direction` from `Chap06/Theorem_6_27_3`;
- `Function.HasPolyhedralEpigraph` from `Chap04/Text_19_0_8`;
- `Function.lineal` and
  `Function.mem_lineal_iff_forall_translate_profile_constant` from
  `Chap02/Definition_8_9_1`.

Primitive data vs derived API:
- primitive inputs: the objective `f₀`, the constraint family `f`, consistency of the weak
  feasible set, the source-facing common-recession hypotheses, and in the refined clause a finite
  polyhedral subfamily `I₀ : Set I` together with its finiteness witness `I₀.Finite` and the
  canonical lineality owner for constant-translation directions;
- derived API: existence of a minimizer in the canonical owner form
  `∃ x ∈ weakConvexInequalitySolutionSet f, IsMinOn f₀ ... x`.

Layer target: `source-facing`, but stated directly on the canonical feasible-set and minimizer
owners, with constant common recession directions expressed by the existing owner `lineal`
instead of a separate constrained-program wrapper or local constancy predicate.

Ambient-layer note:
- clause (1) is placed on the same finite-dimensional topological-vector-space layer over `𝕜` as the
  owner theorem `exists_mem_isMinOn_of_no_common_recession_direction`;
- clause (2) stays on that same faithful TVS layer, keeping the topological-vector-space
  compatibility and separation assumptions needed for Chapter 6 closed/proper/convex attainment
  statements, without reintroducing any stronger concrete model.
-/

variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

section NoCommonRecessionDirection

variable {I : Sort v}
variable (f : I → E → WithBotTop 𝕜)

local notation "C" => weakConvexInequalitySolutionSet f

-- Proof sketch: let `C := weakConvexInequalitySolutionSet f`. Closedness and
-- convexity of `C` come from the Chapter 21 owner theorems applied to the closed proper convex
-- constraint family. Any common recession direction of all `f i` preserves all weak constraints,
-- hence is a recession direction of `C`; Theorem 6.27.3 then yields a minimizer of `f₀` on `C`.
/-- Corollary 6.27.5 (1): if the weak system `f i x ≤ 0` is consistent and no recession direction
is common to the objective `f₀` and to every constraint function `f i`, then `f₀` attains its
infimum on the weak feasible set cut out by those constraints. -/
theorem exists_mem_isMinOn_of_no_common_recession_direction_for_convex_inequalities
    (f₀ : E → WithBotTop 𝕜)
    (hf₀_convex : f₀.IsConvex 𝕜) (hf₀_proper : f₀.IsProper)
    (hf₀_closed : LowerSemicontinuous f₀)
    (hf_convex : ∀ i : I, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : I, (f i).IsProper)
    (hf_closed : ∀ i : I, LowerSemicontinuous (f i))
    (hconsistent : Set.Nonempty C)
    (hno_common :
      ¬ ∃ y : E, f₀.RecedesInDirection 𝕜 y ∧ ∀ i : I, (f i).RecedesInDirection 𝕜 y) :
    ∃ x ∈ C, IsMinOn f₀ C x := sorry

end NoCommonRecessionDirection

section FinitePolyhedralRefinement

variable {I : Type v}
variable (f : I → E → WithBotTop 𝕜)

local notation "C" => weakConvexInequalitySolutionSet f

-- Proof sketch: keep the finite polyhedral subsystem indexed by a finite subset `I₀ : Set I` as
-- the explicit feasible set, and absorb the remaining constraints into a modified objective by
-- adding the indicator of their common feasible region. The polyhedral hypotheses make the
-- retained subsystem fit the finite polyhedral attainment route, while the lineality assumption
-- turns every common recession direction of the reduced problem into a direction harmless for the
-- modified objective. The resulting minimizer is then feasible for the full family.
/-- Corollary 6.27.5 (2): more generally, if a finite subset `I₀` is polyhedral and every
recession direction common to `f₀` and all constraints lies in `lin(f₀)` and in `lin(f i)` for
every nonpolyhedral constraint `i` (i.e. `¬ (f i).HasPolyhedralEpigraph`), then `f₀` still
attains its infimum on the weak feasible set. -/
theorem exists_mem_isMinOn_of_finite_polyhedral_subfamily_and_constant_common_recession_directions
    (f₀ : E → WithBotTop 𝕜) (I₀ : Set I) (hI₀_finite : I₀.Finite)
    (hf₀_convex : f₀.IsConvex 𝕜) (hf₀_proper : f₀.IsProper)
    (hf₀_closed : LowerSemicontinuous f₀)
    (hf_convex : ∀ i : I, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i : I, (f i).IsProper)
    (hf_closed : ∀ i : I, LowerSemicontinuous (f i))
    (hpoly : ∀ i : I, i ∈ I₀ → (f i).HasPolyhedralEpigraph)
    (hconsistent : Set.Nonempty C)
    (hlineal :
      ∀ ⦃y : E⦄, f₀.RecedesInDirection 𝕜 y → (∀ i : I, (f i).RecedesInDirection 𝕜 y) →
        y ∈ lin(f₀) ∧ ∀ i : I, ¬ (f i).HasPolyhedralEpigraph → y ∈ lin(f i)) :
    ∃ x ∈ C, IsMinOn f₀ C x := sorry

end FinitePolyhedralRefinement

/-! ### Definition_6_27_5 (from Chap06) -/
noncomputable section

section Ordered

variable {𝕜 : Type*} [LE 𝕜] [Pow 𝕜 ℕ]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.5 names the concrete set
  `P = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` from the Section 27 example.
- `core/canonical`: this set is already owned upstream as
  `paraboloidEpigraph : Set (𝕜 × 𝕜)` in `Chap02/ParaboloidEpigraph`.
- `bridge/view`: the coordinate inequality `ξ₁² ≤ ξ₂` is the canonical set-of/membership view
  already provided by upstream owner API (`paraboloidEpigraph_eq_setOf_sq_le`,
  `mem_paraboloidEpigraph_iff`).

Primitive data vs derived API:
- primitive public data: the canonical owner `paraboloidEpigraph : Set (𝕜 × 𝕜)`;
- derived API: this file keeps only source-level recall/use of the upstream owner and bridge
  theorems, without introducing a parallel local alias.

Domain-style sampling used here:
- the shared source owner `paraboloidEpigraph`.

Layer target: `source-facing` recall at the canonical owner layer.
-/

/- Definition 6.27.5: the source set `P = {(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` is already the shared owner
`paraboloidEpigraph`. -/
recall paraboloidEpigraph

/- Source-facing coordinate/set presentation of the same owner. -/
recall paraboloidEpigraph_eq_setOf_sq_le

/- Pointwise membership view of Definition 6.27.5. -/
recall mem_paraboloidEpigraph_iff

end Ordered

/-! ### Proposition_6_27_5 (from Chap06) -/
universe u v

section

variable {E : Type u} {γ : Type v} [TopologicalSpace E] [Preorder γ]
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.5 says that the minimum set of a closed proper convex
  function is a closed subset of the ambient space.
- `core/canonical`: the owner abstractions sampled for this repair are
  the source-facing minimum-set owner `minimumSet` from `Definition_6_27_3`,
  mathlib's owner theorem `LowerSemicontinuous.isClosed_preimage` for lower-ray preimages,
  and the Chapter 3 bundle `Function.IsClosedProperConvex` only as a downstream bridge to that
  lower-semicontinuous owner.
- `bridge/view`: the canonical theorem is stated on `LowerSemicontinuous`, while the textbook
  closed-proper-convex proposition is kept as a one-line specialization on the same
  source-facing set owner `minimumSet f`.

Domain-style sampling used here:
- `minimumSet` and `isMinOn_univ_iff` from `Definition_6_27_3` and mathlib's extrema API;
- `LowerSemicontinuous.isClosed_preimage` from mathlib's semicontinuity API;
- `Function.IsClosedProperConvex.lowerSemicontinuous` from `Text_12_3_6`;
- `lowerSemicontinuous_iff_isClosed_sublevel` from `Chap02.Theorem_7_1`, whose forward direction
  is the chapter owner for ordinary sublevel-set closedness.

Primitive data vs derived API:
- primitive data: a function `f : E → γ` and closedness of each scalar lower-ray preimage
  `f ⁻¹' Set.Iic r`;
- derived API: the closedness of the source-facing minimum set `minimumSet f`;
- bridge API: lower semicontinuity and closed-proper-convexity as sufficient hypotheses that
  imply the primitive closed-sublevel input.

Layer target: `source-facing`, with the owner abstraction refined downward to the minimal
closedness input.
-/

-- Proof sketch: `minimumSet f` is exactly the intersection of scalar lower-ray preimages
-- `f ⁻¹' Set.Iic (f y)` over all `y`. If every scalar lower-ray preimage is closed, then the minimum set is
-- closed by arbitrary intersection.
/-- The minimum set is closed whenever all scalar lower-ray preimages are closed. -/
theorem minimumSet_isClosed_of_isClosed_sublevel {f : E → γ}
    (hsublevel : ∀ r : γ, IsClosed (f ⁻¹' Set.Iic r)) :
    IsClosed (minimumSet f) := by
  rw [show minimumSet f = ⋂ y, f ⁻¹' Set.Iic (f y) by
    ext x
    simp [minimumSet, isMinOn_univ_iff]]
  refine isClosed_iInter ?_
  intro y
  exact hsublevel (f y)

end

section

variable {E : Type u} {γ : Type v} [TopologicalSpace E] [LinearOrder γ]

namespace LowerSemicontinuous

-- Proof sketch: lower semicontinuity gives closedness of scalar lower-ray preimages
-- `f ⁻¹' Set.Iic r`, then the primitive closed-sublevel minimum-set theorem applies.
/-- The minimum set of a lower semicontinuous function is closed. -/
theorem minimumSet_isClosed {f : E → γ} (hf : LowerSemicontinuous f) :
    IsClosed (minimumSet f) :=
  minimumSet_isClosed_of_isClosed_sublevel (f := f) hf.isClosed_preimage

end LowerSemicontinuous

end

section

variable {𝕜 : Type*} {E : Type u} {α : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [LinearOrder α] [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul 𝕜 α]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace Function.IsClosedProperConvex

-- Proof sketch: closed-proper-convexity provides lower semicontinuity via the owner projection,
-- then the canonical lower-semicontinuous minimum-set theorem applies.
/-- The minimum set of a closed proper convex function is closed. -/
theorem minimumSet_isClosed {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsClosed (minimumSet f) :=
  hf.lowerSemicontinuous.minimumSet_isClosed

end Function.IsClosedProperConvex

-- Proof sketch: Proposition 6.27.5 is the source-facing specialization of the canonical owner
-- theorem `Function.IsClosedProperConvex.minimumSet_isClosed`.
/-- Proposition 6.27.5: the minimum set of a closed proper convex function is closed. -/
theorem minimumSet_isClosed {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsClosed (minimumSet f) :=
  hf.minimumSet_isClosed

end
