import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_13
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasPairing Y E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 16.2 characterizes when a subspace `L` meets `ri (dom f)` for a proper
  convex function `f` by excluding annihilator directions with an asymmetric support-function
  behavior for `dom f`, i.e. for Rockafellar's `f⋆0⁺`.
- `core/canonical`: the owner abstractions already present in the project are
  `supportFunction`, `Function.IsConvex`, `Function.IsProper`, the chapter notation `riDom(·)`
  for relative interiors of effective domains, the effective-domain set `dom(f)`, and
  `Submodule.pairingOrthogonal`.
- `bridge/view`: Rockafellar's `ri (dom f)` is rendered directly by the established chapter
  notation `riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f)`.

Domain-style sampling used here:
- `supportFunction` from `Defintion_4_8_2`;
- `riDom(·)` from `Definition_4_4`, reexported through the Chapter 1 effective-domain API;
- `exists_hyperplane_separating_properly_iff_supportFunction_conditions` from
  `Chap03/Theorem_11_1`;
- `exists_separatesProperly_iff_disjoint_ri` from
  `Chap03/Theorem_11_3`;
- `Submodule.pairingOrthogonal` for `Lᗮₚ`.

Primitive data vs derived API:
- primitive inputs (core theorem): the subspace `L` and a nonempty convex set `C`;
- source-facing wrapper inputs: `f` with owner hypotheses `Function.IsConvex f` and
  `Function.IsProper f`, used only to derive `Convex 𝕜 dom(f)` and `dom(f).Nonempty`;
- derived API: the `riDom[𝕜](f)` statement is now a thin bridge over the primitive set-owner
  theorem, and recession-function rewrites belong downstream via Theorem 13.3.

Layer target: core owner-first at the intrinsic set layer, with the textbook `riDom[𝕜](f)` form
as a source-facing wrapper.

Ambient refinement:
- The separation and support-function owners used here already live on arbitrary finite-dimensional
  normed pairing spaces over conditionally complete linearly ordered fields, so the public
  statement is refined away from the concrete model `EuclideanSpace ℝ (Fin n)` and from the
  inner-product-only owner layer.
-/

-- Proof sketch: apply Theorem 11.3 to the convex sets `L` and `dom(f)`. Since a subspace is
-- relatively open in its affine hull, disjointness of `L` from `ri (dom f)` is equivalent to the
-- existence of a proper separating hyperplane. Then use Theorem 11.1 to rewrite proper
-- separation by one vector `xStar`, note that the extremal values on `L` force `xStar ∈ Lᗮₚ`.
/-- Primitive set-owner form of Lemma 16.2: for a subspace `L` and a nonempty convex set `C`,
`L` meets `ri[𝕜](C)` iff there is no pairing-orthogonal vector `x⋆ ∈ Lᗮₚ` with
`δᵛ(x⋆ | C) ≤ 0 < δᵛ(-x⋆ | C)`. -/
theorem
    submodule_meets_intrinsicInterior_iff_no_pairingOrthogonal_asymmetric_supportFunction
    (L : Submodule 𝕜 E) (C : Set E) (hC_conv : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    ((L : Set E) ∩ ri[𝕜](C)).Nonempty ↔
      ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | C) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | C) := by
  classical
  have hL_nonempty : ((L : Set E)).Nonempty := ⟨0, L.zero_mem⟩
  have hL_ri : ri[𝕜]((L : Set E)) = (L : Set E) := by
    simpa only [Submodule.mem_toAffineSubspace] using
      (L.toAffineSubspace.intrinsicInterior_coe :
        intrinsicInterior 𝕜 ((L.toAffineSubspace : AffineSubspace 𝕜 E) : Set E) =
          ((L.toAffineSubspace : AffineSubspace 𝕜 E) : Set E))
  have hL_cone : Set.IsCone 𝕜 (L : Set E) := by
    intro c x _ hx
    exact L.smul_mem c hx
  have hL_support_eq_zero {xStar : Y} (hxStar : xStar ∈ Lᗮₚ) :
      δᵛ(xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
    have hsupport := congrFun
      (supportFunction_eq_indicatorFunction_polarCone (𝕜 := 𝕜)
        (K := (L : Set E)) hL_nonempty hL_cone) xStar
    have hxStar_polar : xStar ∈ (((L : Set E)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
      simpa [Submodule.polarCone_eq_pairingOrthogonal] using hxStar
    have hpolar_zero : δ[𝕜](xStar | ((L : Set E)ᵒ[𝕜] : Set Y)) = 0 := by
      simpa using indicator_of_mem (C := ((L : Set E)ᵒ[𝕜] : Set Y)) hxStar_polar
    exact hsupport.trans hpolar_zero
  have hL_support_eq_top {xStar : Y} (hxStar : xStar ∉ Lᗮₚ) :
      δᵛ(xStar | (L : Set E)) = (⊤ : WithBotTop 𝕜) := by
    have hsupport := congrFun
      (supportFunction_eq_indicatorFunction_polarCone (𝕜 := 𝕜)
        (K := (L : Set E)) hL_nonempty hL_cone) xStar
    have hxStar_polar : xStar ∉ (((L : Set E)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
      simpa [Submodule.polarCone_eq_pairingOrthogonal] using hxStar
    have hpolar_top : δ[𝕜](xStar | ((L : Set E)ᵒ[𝕜] : Set Y)) = ⊤ := by
      simpa using indicator_of_notMem (C := ((L : Set E)ᵒ[𝕜] : Set Y)) hxStar_polar
    exact hsupport.trans hpolar_top
  have hsep_disjoint :
      (∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H (L : Set E) C) ↔
        Disjoint (L : Set E) (ri[𝕜](C)) := by
    simpa [hL_ri] using
      (exists_separatesProperly_iff_disjoint_ri
        L.convex hL_nonempty hC_conv hC_nonempty : (∃ H : AffineSubspace 𝕜 E,
          AffineSubspace.SeparatesProperly Y H (L : Set E) C) ↔
            Disjoint
              (ri[𝕜](
                ((L.toAffineSubspace : AffineSubspace 𝕜 E) : Set E))
              )
              (ri[𝕜](C)))
  have hsep_pairingOrthogonal :
      (∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H (L : Set E) C) ↔
        ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
          δᵛ(xStar | C) ≤ (0 : WithTopBot 𝕜) ∧
            (0 : WithTopBot 𝕜) < δᵛ(-xStar | C) := by
    constructor
    · intro hsep
      rcases
        (exists_hyperplane_separating_properly_iff_supportFunction_conditions
          hL_nonempty hC_nonempty).1 hsep with
        ⟨xStar, hxStar_left, hxStar_right⟩
      have hC_bot : ⊥ < δᵛ(xStar | C) := by
        rcases hC_nonempty with ⟨x, hx⟩
        have hx_le :
            (⟪xStar, x⟫ₚ : WithBotTop 𝕜) ≤ δᵛ(xStar | C) := by
          rw [supportFunction_def]
          exact le_iSup (fun z : C => (⟪xStar, (z : E)⟫ₚ : WithBotTop 𝕜)) ⟨x, hx⟩
        exact lt_of_lt_of_le (WithBotTop.bot_lt_coe _) hx_le
      have hxStar_mem : xStar ∈ Lᗮₚ := by
        by_contra hxStar_mem
        have hneg_top : δᵛ(-xStar | (L : Set E)) = (⊤ : WithBotTop 𝕜) := by
          have hxStar_not_mem : xStar ∉ Lᗮₚ := hxStar_mem
          have hneg_not_mem : -xStar ∉ Lᗮₚ := by
            intro hneg_mem
            exact hxStar_not_mem (by simpa using (Lᗮₚ).neg_mem hneg_mem)
          simpa using hL_support_eq_top hneg_not_mem
        have hbot_ge : (⊥ : WithBotTop 𝕜) ≥ δᵛ(xStar | C) := by
          simpa [hneg_top] using hxStar_left
        exact (not_le_of_gt hC_bot) hbot_ge
      refine ⟨xStar, hxStar_mem, ?_, ?_⟩
      · have hneg_zero : δᵛ(-xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          have hneg_mem : -xStar ∈ Lᗮₚ := by
            simpa using (Lᗮₚ).neg_mem hxStar_mem
          simpa using hL_support_eq_zero hneg_mem
        simpa [hneg_zero] using hxStar_left
      · have hzero : δᵛ(xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          simpa using hL_support_eq_zero hxStar_mem
        simpa [hzero] using hxStar_right
    · rintro ⟨xStar, hxStar_mem, hxStar_left, hxStar_right⟩
      refine
        (exists_hyperplane_separating_properly_iff_supportFunction_conditions
          hL_nonempty hC_nonempty).2 ?_
      refine ⟨xStar, ?_, ?_⟩
      · have hneg_zero : δᵛ(-xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          have hneg_mem : -xStar ∈ Lᗮₚ := by
            simpa using (Lᗮₚ).neg_mem hxStar_mem
          simpa using hL_support_eq_zero hneg_mem
        simpa [hneg_zero] using hxStar_left
      · have hzero : δᵛ(xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          simpa using hL_support_eq_zero hxStar_mem
        simpa [hzero] using hxStar_right
  calc
    ((L : Set E) ∩ ri[𝕜](C)).Nonempty ↔
        ¬ Disjoint (L : Set E) (ri[𝕜](C)) := by
      rw [Set.not_disjoint_iff_nonempty_inter]
    _ ↔ ¬ ∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H (L : Set E) C :=
      not_congr hsep_disjoint.symm
    _ ↔ ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | C) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | C) :=
      not_congr hsep_pairingOrthogonal

/-- Lemma 16.2 on the `riDom` notation surface, at primitive domain data:
a subspace `L` meets `riDom[𝕜](f)` iff there is no pairing-orthogonal vector `x⋆ ∈ Lᗮₚ`
with `δᵛ(x⋆ | dom(f)) ≤ 0 < δᵛ(-x⋆ | dom(f))`, assuming only convexity and nonemptiness of
`dom(f)`. -/
theorem
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction
    {β : Type*} [LT β] [Top β]
    (L : Submodule 𝕜 E) (f : E → β)
    (hdom_conv : Convex 𝕜 dom(f)) (hdom_nonempty : dom(f).Nonempty) :
    ((L : Set E) ∩ riDom[𝕜](f)).Nonempty ↔
      ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | dom(f)) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | dom(f)) := by
  simpa using
    (submodule_meets_intrinsicInterior_iff_no_pairingOrthogonal_asymmetric_supportFunction
      (L := L) (C := dom(f)) hdom_conv hdom_nonempty)

/-- Source-facing convex/proper bridge for Lemma 16.2. -/
theorem
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction_of_isConvex_isProper
    {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [Preorder α]
    (L : Submodule 𝕜 E) (f : E → WithTopBot α) (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    ((L : Set E) ∩ riDom[𝕜](f)).Nonempty ↔
      ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | dom(f)) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | dom(f)) := by
  exact
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction
      (L := L) (f := f) hf_convex.convex_dom hf_proper.nonempty_dom
