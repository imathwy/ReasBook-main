import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_27_4

open scoped Rockafellar

noncomputable section

universe u v

section

variable {𝕜 : Type v} [AddCommGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u}
variable [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.27.6 is the weak-separation statement for the constrained minimum
  problem, expressed by a non-vertical hyperplane `μ = ⟪z, x⋆⟫ₚ + β` separating the epigraph
  `epi h` from the auxiliary set `C₂ C α`.
- `core/canonical`: the owner abstractions already present in the project are `epi h`, `C₂ C α`,
  `Function.IsConvex`, `_root_.subdifferentialAt`, `N[𝕜](· | ·)`, `IsMinOn`, and the chapter
  relative-interior notations `riDom(h)` and `ri(C)`.
- `bridge/view`: the source hyperplane is recorded directly through inequalities on those owner
  sets rather than through a second local separator wrapper.

Primitive data vs derived API:
- primitive bridge data for the separator construction: a dual subgradient
  `xStar ∈ subdifferentialAt h xBar`, a normal-cone certificate
  `-xStar ∈ N[𝕜](xBar | C)`, and the attained-value identity `h xBar = α`;
- derived API: weak-separation inequalities on `epi h` and `C₂ C α`, with canonical height
  `α - ⟪xBar, xStar⟫ₚ`.

Layer target: `source-facing`, with the owner kept at the intrinsic dual/pairing layer rather than
at a Euclidean Fréchet-Riesz bridge layer.
-/

-- Proof sketch: use the subgradient inequality to control points in `epi h` and the normal-cone
-- inequality to control points in `C₂ C α`, with canonical separator height
-- `β = α - ⟪xBar, xStar⟫ₚ`.
/-- A dual subgradient at `xBar` whose negative is normal to `C` yields weak-separation
inequalities for `epi h` and `C₂ C α`, with canonical source height
`α - ⟪xBar, xStar⟫ₚ`. -/
theorem weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone
    {Y : Type (max u v)} [Neg Y] [HasPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]
    [HasPairingNegRight E Y 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {α : 𝕜} {xBar : E} {xStar : Y}
    (hxStar_sub : xStar ∈ ∂[Y]h(xBar))
    (hxStar_normal : -xStar ∈ N[𝕜](xBar | C))
    (hxBar_value : h xBar = α) :
    (∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ) ∧
      ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
  refine ⟨?_, ?_⟩
  · intro z μ hz_epi
    have hz_sub :
        h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ h z :=
      (mem_subdifferentialAt_pairing.mp hxStar_sub) z
    have hz_eq :
        h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) =
          ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithTopBot 𝕜) := by
      rw [hxBar_value]
      have hz_real :
          α + (⟪z - xBar, xStar⟫ₚ : 𝕜) =
            ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
        calc
          α + (⟪z - xBar, xStar⟫ₚ : 𝕜)
              = α + ((⟪z, xStar⟫ₚ : 𝕜) - (⟪xBar, xStar⟫ₚ : 𝕜)) := by
                  simpa using (congrArg (fun t : 𝕜 ↦ α + t)
                    (HasPairingSubLeft.pairing_sub_left z xBar xStar))
          _ = ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      change (((α + (⟪z - xBar, xStar⟫ₚ : 𝕜) : 𝕜) : WithTopBot 𝕜)) =
        ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithTopBot 𝕜)
      simpa using congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : WithTopBot 𝕜)) hz_real
    have hz_le :
        ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithTopBot 𝕜) ≤ μ := by
      rw [← hz_eq]
      exact le_trans hz_sub (mem_epi_iff.mp hz_epi)
    exact WithTopBot.coe_le_coe.mp hz_le
  · intro z μ hz_aux
    rcases (mem_C₂_iff.mp hz_aux) with ⟨hzC, hμ⟩
    rcases (mem_normalCone_iff_sub_nonpos.mp hxStar_normal) with ⟨_, hxStar_normal'⟩
    have hsub_nonneg : (0 : 𝕜) ≤ (⟪z - xBar, xStar⟫ₚ : 𝕜) := by
      have hsub_nonneg_neg : (0 : 𝕜) ≤ -(⟪z - xBar, -xStar⟫ₚ : 𝕜) :=
        neg_nonneg.mpr (hxStar_normal' z hzC)
      simpa [HasPairingNegRight.pairing_neg_right] using hsub_nonneg_neg
    have hbase : (⟪xBar, xStar⟫ₚ : 𝕜) ≤ (⟪z, xStar⟫ₚ : 𝕜) := by
      have hbase' : (0 : 𝕜) ≤ (⟪z, xStar⟫ₚ : 𝕜) - (⟪xBar, xStar⟫ₚ : 𝕜) := by
        simpa [HasPairingSubLeft.pairing_sub_left] using hsub_nonneg
      exact sub_nonneg.mp hbase'
    have hα : α ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
      have hα' := add_le_add_right hbase (α - ⟪xBar, xStar⟫ₚ)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hα'
    exact le_trans hμ hα

end

section

variable {𝕜 : Type v} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddLeftMono 𝕜]
variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Theorem 6.27.6: if `xBar ∈ C` attains the finite minimum value `α` of a convex
function `h` on the convex set `C`, if `h` never takes the value `⊥`, and if `ri(dom h)` meets
`ri[𝕜](C)`, then some continuous-dual vector `xStar` determines a non-vertical hyperplane with
canonical height `β = α - ⟪xBar, xStar⟫ₚ` that weakly separates `epi h` from `C₂ C α`. -/
theorem exists_weaklySeparating_nonverticalHyperplane_of_isMinOn_of_intrinsicInterior
    {h : E → WithTopBot 𝕜} {C : Set E} {α : 𝕜} {xBar : E}
    (hneBot : ∀ y, h y ≠ ⊥) (hh_convex : h.IsConvex 𝕜) (hC_convex : Convex 𝕜 C)
    (hxBar_mem : xBar ∈ C)
    (hxBar_min : IsMinOn h C xBar) (hxBar_value : h xBar = α)
    (hqual : (riDom[𝕜](h) ∩ ri[𝕜](C)).Nonempty) :
    ∃ xStar : StrongDual 𝕜 E,
      (∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ) ∧
        ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
  rcases
      (isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior
        hneBot hh_convex hC_convex hqual).mp ⟨hxBar_mem, hxBar_min⟩ with
    ⟨xStar, hxStar_sub, hxStar_normal⟩
  exact ⟨xStar,
    weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone
      hxStar_sub
      hxStar_normal
      hxBar_value⟩

end
