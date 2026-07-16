import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_11

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [AddCommGroup 𝕜] [PartialOrder 𝕜]
variable {E : Type u} {Y : Type*} [HasPairing E Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.6 says that once a weakly separating nonvertical hyperplane for
  `epi h` and `C₂ C α` is chosen through the feasible contact point `(xBar, α)`, its dual normal
  vector is both a subgradient of `h` at `xBar` and a normal vector to `C` at `xBar`.
- `core/canonical`: the owner abstractions already present upstream are the epigraph owner
  `epi h`, the Chapter 6 auxiliary-set owner `C₂ C α`, the Chapter 23 subdifferential owner
  `_root_.subdifferentialAt`, the Chapter 1 normal-cone owner `N[𝕜](· | ·)`, and the Chapter 6
  separator theorem
  `weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone`,
  which already fixes the separator height canonically as `α - ⟪xBar, xStar⟫ₚ`.
- `bridge/view`: the canonical-height formulation is the specialization obtained by rewriting an
  arbitrary source separator height `β` at the contact point `(xBar, α)`.

Domain-style sampling used here:
- `mem_epi_iff` / `epi h`;
- `mem_C₂_iff` for `C₂ C α`;
- `_root_.mem_subdifferentialAt_pairing` and `mem_normalCone_iff_sub_nonpos`;
- `weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone`.

Primitive data vs derived API:
- primitive inputs: a feasible contact point `xBar ∈ C` with `h xBar = α`, together with the two
  weak-separation inequalities for a separator dual normal `xStar`;
- derived API: the canonical separator height `α - ⟪xBar, xStar⟫ₚ`, its agreement with an
  arbitrary source height `β`, subgradient membership of `xStar`, and normal-cone membership of
  `-xStar`.

Layer target:
- `source-facing`: the main corollary keeps the textbook arbitrary separator height `β`;
- `bridge/view`: a thin companion specializes that source-facing theorem to the canonical height
  `α - ⟪xBar, xStar⟫ₚ`.

The closedness, convexity, attainment, and qualification hypotheses from the preceding theorem are
intentionally not repeated here, since the corollary's conclusions depend only on the contact-point
equalities and the separator inequalities themselves.
-/

-- Proof sketch: the point `(xBar, α)` belongs both to `epi h` and to `C₂ C α`, so the two weak
-- separation inequalities sandwich `α` between `⟪xBar, xStar⟫ₚ + β` and itself. Rearranging gives
-- the canonical separator height `α - ⟪xBar, xStar⟫ₚ`.
/-- A weakly separating source height agrees with the canonical height
`α - ⟪xBar, xStar⟫ₚ` at the feasible contact point `(xBar, α)`. -/
theorem separatorHeight_eq_canonical_of_weaklySeparating_epi_and_C₂
    {h : E → WithBotTop 𝕜} {C : Set E} {α β : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi : ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + β ≤ μ)
    (hsep_aux : ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + β) :
    β = α - ⟪xBar, xStar⟫ₚ := by
  have hle_epi : ⟪xBar, xStar⟫ₚ + β ≤ α :=
    hsep_epi xBar α <| by simp [hxBar_value]
  have hle_aux : α ≤ ⟪xBar, xStar⟫ₚ + β :=
    hsep_aux xBar α <| by simp [hxBar_mem]
  have hEq : (⟪xBar, xStar⟫ₚ : 𝕜) + β = α := le_antisymm hle_epi hle_aux
  exact (eq_sub_iff_add_eq').2 hEq

end

section

variable {𝕜 : Type v}
variable [CommRing 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜] [AddLeftMono 𝕜] [NoBotOrder 𝕜]
variable {E : Type u}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [AddCommGroup Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-!
Ambient-layer note for the subgradient/normal-cone conclusions:

- the separator-height theorem above is purely pairing-level and needs no normed-space structure;
- the theorems below conclude membership in `_root_.subdifferentialAt` and `N[𝕜](· | ·)`;
- in this chapter, `_root_.subdifferentialAt` is the ordered-scalar owner
  `(E → WithBotTop 𝕜) → E → Set Y` parameterized by
  `[AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]`.

Hence these ambient assumptions are owner-surface requirements of the stated conclusions, not
proof-local artifacts.
-/

-- Proof sketch: use the epigraph half of the canonical weak-separation inequality to rewrite the
-- support bound into the defining inequality of `_root_.subdifferentialAt h xBar`. For `x ∈ C`,
-- use the auxiliary-set half with height `α` and conclude `-xStar ∈ N[𝕜](xBar | C)` via
-- `mem_normalCone_iff_sub_nonpos`.
private theorem mem_subdifferentialAt_and_neg_mem_normalCone_of_canonicalSeparatorHeight
    {h : E → WithBotTop 𝕜} {C : Set E} {α : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi :
      ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ)
    (hsep_aux :
      ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ)) :
    xStar ∈ (∂[Y]h(xBar)) ∧ -xStar ∈ N[𝕜](xBar | C) := by
  refine ⟨?_, ?_⟩
  · rw [mem_subdifferentialAt_pairing]
    intro z
    change h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ h z
    have hz_sep :
        ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithBotTop 𝕜) ≤ h z := by
      by_cases hz_bot : h z = (⊥ : WithBotTop 𝕜)
      · exfalso
        have hz_sep_all :
            ∀ μ : 𝕜, (⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) ≤ μ := by
          intro μ
          exact hsep_epi z μ <| by simp [hz_bot]
        rcases NoBotOrder.exists_not_ge
            (a := (⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜)) with ⟨μ, hμ⟩
        exact hμ (hz_sep_all μ)
      · by_cases hz_top : h z = (⊤ : WithBotTop 𝕜)
        · simp [hz_top]
        · rcases (WithBotTop.canLift_iff_ne_top_ne_bot).2 ⟨hz_top, hz_bot⟩ with ⟨r, hr⟩
          have hreal : ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ r :=
            hsep_epi z r <| by simp [hr]
          exact hr ▸ WithBotTop.coe_le_coe.mpr hreal
    have hz_real :
        α + (⟪z - xBar, xStar⟫ₚ : 𝕜) =
          ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
      calc
        α + (⟪z - xBar, xStar⟫ₚ : 𝕜)
            = α + ((⟪z, xStar⟫ₚ : 𝕜) - (⟪xBar, xStar⟫ₚ : 𝕜)) := by
                simp [sub_eq_add_neg, map_add, map_neg]
        _ = ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by ring
    have hz_eq :
        h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) =
          ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithBotTop 𝕜) := by
      rw [hxBar_value, ← WithBotTop.coe_add]
      exact congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : WithBotTop 𝕜)) hz_real
    rw [hz_eq]
    exact hz_sep
  · rw [mem_normalCone_iff_sub_nonpos]
    refine ⟨hxBar_mem, ?_⟩
    intro z hzC
    have hz_sep : α ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) :=
      hsep_aux z α <| by simp [hzC]
    have hbase : (⟪xBar, xStar⟫ₚ : 𝕜) - (⟪z, xStar⟫ₚ : 𝕜) ≤ 0 := by
      have hshift :=
        add_le_add_right hz_sep ((⟪xBar, xStar⟫ₚ : 𝕜) - α)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
    simpa [sub_eq_add_neg, map_add, map_neg, add_assoc, add_left_comm, add_comm] using hbase

/-- Corollary 6.27.6: an arbitrary weakly separating hyperplane for `epi h` and `C₂ C α`
through the feasible contact point `(xBar, α)` yields a dual vector `xStar` that is simultaneously a
subgradient of `h` at `xBar` and a normal vector to `C` at `xBar`. -/
theorem mem_subdifferentialAt_and_neg_mem_normalCone_of_weaklySeparating_epi_and_C₂
    {h : E → WithBotTop 𝕜} {C : Set E} {α β : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi : ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + β ≤ μ)
    (hsep_aux : ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + β) :
    xStar ∈ (∂[Y]h(xBar)) ∧ -xStar ∈ N[𝕜](xBar | C) := by
  have hβ :
      β = α - ⟪xBar, xStar⟫ₚ :=
    separatorHeight_eq_canonical_of_weaklySeparating_epi_and_C₂
      hxBar_mem hxBar_value hsep_epi hsep_aux
  refine mem_subdifferentialAt_and_neg_mem_normalCone_of_canonicalSeparatorHeight
    hxBar_mem hxBar_value ?_ ?_
  · intro z μ hz
    simpa [hβ] using hsep_epi z μ hz
  · intro z μ hz
    simpa [hβ] using hsep_aux z μ hz

/-- Corollary 6.27.6, canonical-height companion: specializing the source separator height to
`α - ⟪xBar, xStar⟫ₚ` recovers the same converse surface as
`weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone`. -/
theorem mem_subdifferentialAt_and_neg_mem_normalCone_of_weaklySeparates_epi_and_C₂
    {h : E → WithBotTop 𝕜} {C : Set E} {α : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi :
      ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ)
    (hsep_aux :
      ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ)) :
    xStar ∈ (∂[Y]h(xBar)) ∧ -xStar ∈ N[𝕜](xBar | C) :=
  mem_subdifferentialAt_and_neg_mem_normalCone_of_weaklySeparating_epi_and_C₂
    hxBar_mem hxBar_value hsep_epi hsep_aux

end
