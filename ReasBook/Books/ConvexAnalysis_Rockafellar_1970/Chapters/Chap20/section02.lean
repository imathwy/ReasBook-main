import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_20_2_1 (from Chap04) -/
noncomputable section

open scoped Rockafellar

universe u v

variable {𝕜 : Type u} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [TopologicalSpace 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type v} {Y : Type (max u v)} [TopologicalSpace E] [AddCommGroup E]
  [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [AddCommGroup Y] [Module 𝕜 Y]
  [HasLinearPairing E Y 𝕜] [HasPairing Y E 𝕜] [HasPairingSwap E Y 𝕜]
  [HasLinearPairing.Nondegenerate E Y 𝕜]
  [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 20.2.1 characterizes nonemptiness of `C1 ∩ ri[𝕜](C2)` for a nonempty
  polyhedral convex set `C1` and a nonempty convex set `C2` by a support-function criterion on
  every separating normal vector `xStar`.
- `core/canonical`: the owner abstractions are the Chapter 11 separation relation
  `AffineSubspace.SeparatesProperly`, the support-function owner notation `δᵛ(· | ·)` with
  codomain fixed to `WithTopBot 𝕜`, the
  polyhedral-set predicate `Set.IsPolyhedral`, the convexity predicate `Convex 𝕜`, and the
  relative interior owner `ri[𝕜](·)`.
- `bridge/view`: Rockafellar's `δ*(x* | C)` is represented by `δᵛ(xStar | C)`, and
  `ri C2` is represented by `ri[𝕜](C2)`. The support-function implication is the
  vector-side reformulation of the hyperplane-separation owner criterion from Theorem 11.1, while
  Theorem 20.2 supplies the relative-interior owner criterion.
- Layer target: this item is a `bridge/view` corollary built on the Section 20 separation owner
  theorem, and because the left-hand asymmetric hypothesis is exactly `C1.IsPolyhedral 𝕜 Y`,
  the best owner abstraction is the existing namespace owner `Set.IsPolyhedral`.
- Domain-style sampling used here: the project declarations `supportFunction`,
  `Set.IsPolyhedral`, `AffineSubspace.SeparatesProperly`,
  `exists_hyperplane_separating_properly_iff_supportFunction_conditions`, and
  `Set.IsPolyhedral.exists_separator_not_subset_right_iff_disjoint_ri`.
- Primitive data vs derived API: the primitive inputs are the sets `C1`, `C2` and the owner
  hypotheses `C1.IsPolyhedral 𝕜 Y`, `C1.Nonempty`, and `Convex 𝕜 C2`; the support-function
  criterion is derived theorem-level content, not primitive data.
- Ambient refinement: both imported owner theorems already live on arbitrary finite-dimensional
  topological pairing modules over ordered fields, so this corollary should live at that
  pairing-owner level with explicit symmetry/nondegeneracy assumptions, rather than on a concrete
  inner-product coordinate model.
-/

namespace Set.IsPolyhedral

-- Fixed-codomain support-function notation used throughout this corollary.
local notation3:max "δᵛ(" x " | " C ")" => supportFunction (L := WithTopBot 𝕜) C x

omit [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]
  [AddCommGroup Y] [Module 𝕜 Y]
  [HasLinearPairing E Y 𝕜] [HasPairingSwap E Y 𝕜]
  [HasLinearPairing.Nondegenerate E Y 𝕜] in
private theorem supportFunction_zero_of_nonempty_of_pairing_zero
    {C : Set E} (hC : C.Nonempty) {xStar : Y}
    (hxStar_zero : ∀ y : E, (⟪xStar, y⟫ₚ : 𝕜) = 0) :
    δᵛ(xStar | C) = 0 := by
  rcases hC with ⟨y, hy⟩
  have h_upper : δᵛ(xStar | C) ≤ 0 := by
    rw [supportFunction_def]
    refine iSup_le ?_
    intro z
    change (((⟪xStar, (z : E)⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ 0)
    simp [hxStar_zero (z : E)]
  have h_lower : (0 : WithTopBot 𝕜) ≤ δᵛ(xStar | C) := by
    rw [supportFunction_def]
    have hy0eq : (⟪xStar, y⟫ₚ : WithTopBot 𝕜) = 0 := by
      change (((⟪xStar, y⟫ₚ : 𝕜) : WithTopBot 𝕜) = 0)
      simp [hxStar_zero y]
    calc
      (0 : WithTopBot 𝕜) = (⟪xStar, y⟫ₚ : WithTopBot 𝕜) := by simpa using hy0eq.symm
      _ ≤ ⨆ z : C, (⟪xStar, (z : E)⟫ₚ : WithTopBot 𝕜) := by
        simpa using
          (le_iSup (fun z : C ↦ (⟪xStar, (z : E)⟫ₚ : WithTopBot 𝕜)) ⟨y, hy⟩)
  exact le_antisymm h_upper h_lower

omit [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasLinearPairing.Nondegenerate E Y 𝕜] in
private theorem supportFunction_zero_of_nonempty {C : Set E} (hC : C.Nonempty) :
    δᵛ((0 : Y) | C) = 0 := by
  have hzero_pair : ∀ y : E, (⟪(0 : Y), y⟫ₚ : 𝕜) = 0 := by
    intro y
    calc
      (⟪(0 : Y), y⟫ₚ : 𝕜) = ⟪y, (0 : Y)⟫ₚ :=
        (HasPairingSwap.pairing_swap (𝕜 := 𝕜) y (0 : Y)).symm
      _ = 0 := by
        rw [HasLinearPairing.pairing_eq_pairingLinear]
        simp
  exact supportFunction_zero_of_nonempty_of_pairing_zero hC hzero_pair

omit [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasLinearPairing.Nondegenerate E Y 𝕜] in
private theorem neg_supportFunction_neg_le_pairing
    {C : Set E} {xStar : Y} {y : E} (hy : y ∈ C) :
    -(δᵛ(-xStar | C)) ≤ (⟪xStar, y⟫ₚ : WithTopBot 𝕜) := by
  rw [neg_supportFunction_neg_eq_sInf_image_pairing (C := C) (xStar := xStar)]
  exact sInf_le ⟨y, hy, rfl⟩

omit [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasLinearPairing.Nondegenerate E Y 𝕜] in
private theorem neg_supportFunction_neg_le_supportFunction
    {C : Set E} (hC : C.Nonempty) (xStar : Y) :
    -(δᵛ(-xStar | C)) ≤ δᵛ(xStar | C) := by
  rcases hC with ⟨y, hy⟩
  have hsInf : -(δᵛ(-xStar | C)) ≤ (⟪xStar, y⟫ₚ : WithTopBot 𝕜) :=
    neg_supportFunction_neg_le_pairing (C := C) (xStar := xStar) hy
  have hiSup : (⟪xStar, y⟫ₚ : WithTopBot 𝕜) ≤ δᵛ(xStar | C) := by
    simpa [supportFunction_def] using
      (le_iSup (fun z : C ↦ (⟪xStar, (z : E)⟫ₚ : WithTopBot 𝕜)) ⟨y, hy⟩)
  exact hsInf.trans hiSup

omit [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasLinearPairing.Nondegenerate E Y 𝕜] in
private theorem exists_separator_not_subset_right_of_supportFunction_condition
  {C1 C2 : Set E} (hC1_ne : C1.Nonempty) (hC2_ne : C2.Nonempty) {xStar : Y}
    (hle : δᵛ(xStar | C1) ≤ -(δᵛ(-xStar | C2)))
    (hneq : δᵛ(xStar | C1) ≠ δᵛ(xStar | C2)) :
    ∃ H : AffineSubspace 𝕜 E,
      AffineSubspace.Separates Y H C1 C2 ∧ ¬ C2 ⊆ H := by
  have hle' : δᵛ(xStar | C1) ≤ δᵛ(xStar | C2) :=
    le_trans hle (neg_supportFunction_neg_le_supportFunction hC2_ne xStar)
  have hlt : δᵛ(xStar | C1) < δᵛ(xStar | C2) :=
    lt_of_le_of_ne hle' hneq
  have hxStar_flip_ne : HasLinearPairing.pairingLinear.flip xStar ≠ (0 : E →ₗ[𝕜] 𝕜) := by
    intro hflip_zero
    have hxStar_zero : ∀ y : E, (⟪xStar, y⟫ₚ : 𝕜) = 0 := by
      intro y
      have hy_pair : (⟪y, xStar⟫ₚ : 𝕜) = 0 := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using
          congrArg (fun f : E →ₗ[𝕜] 𝕜 ↦ f y) hflip_zero
      exact (HasPairingSwap.pairing_swap (𝕜 := 𝕜) y xStar).symm.trans hy_pair
    have hC1_zero : δᵛ(xStar | C1) = 0 :=
      supportFunction_zero_of_nonempty_of_pairing_zero hC1_ne hxStar_zero
    have hC2_zero : δᵛ(xStar | C2) = 0 :=
      supportFunction_zero_of_nonempty_of_pairing_zero hC2_ne hxStar_zero
    exact hneq (hC1_zero.trans hC2_zero.symm)
  have hδ1_bot : (⊥ : WithTopBot 𝕜) < δᵛ(xStar | C1) := by
    rcases hC1_ne with ⟨y, hy⟩
    rw [supportFunction_def]
    exact lt_of_lt_of_le ((WithTop.coe_lt_coe).2 (WithBot.bot_lt_coe _))
      (by simpa using
        (le_iSup (fun z : C1 ↦ (⟪xStar, (z : E)⟫ₚ : WithTopBot 𝕜)) ⟨y, hy⟩))
  have hδ1_top : δᵛ(xStar | C1) ≠ ⊤ :=
    ne_of_lt (lt_of_lt_of_le hlt le_top)
  obtain ⟨β, hβ⟩ :
      ∃ β : 𝕜, ((β : 𝕜) : WithTopBot 𝕜) = δᵛ(xStar | C1) := by
    rcases hδ : δᵛ(xStar | C1) with _ | a
    · exact (hδ1_top hδ).elim
    · rcases a with _ | β
      · exact (ne_of_gt hδ1_bot hδ).elim
      · exact ⟨β, rfl⟩
  have hC1_le : C1 ⊆ closedHalfSpaceLE xStar β := by
    intro y hy
    rw [mem_closedHalfSpaceLE_iff]
    have hy_support : (⟪xStar, y⟫ₚ : WithTopBot 𝕜) ≤ δᵛ(xStar | C1) := by
      rw [supportFunction_def]
      exact le_iSup (fun z : C1 ↦ (⟪xStar, (z : E)⟫ₚ : WithTopBot 𝕜)) ⟨y, hy⟩
    have hy_support' : (⟪xStar, y⟫ₚ : WithTopBot 𝕜) ≤ ((β : 𝕜) : WithTopBot 𝕜) := by
      simpa [hβ] using hy_support
    have hy_support'' : ((⟪xStar, y⟫ₚ : 𝕜) : WithBot 𝕜) ≤ (β : WithBot 𝕜) :=
      (WithTop.coe_le_coe).1 hy_support'
    have hy_support''' : (⟪xStar, y⟫ₚ : 𝕜) ≤ β := (WithBot.coe_le_coe).1 hy_support''
    exact (HasPairingSwap.pairing_swap (𝕜 := 𝕜) y xStar).symm ▸ hy_support'''
  have hC2_ge : C2 ⊆ closedHalfSpaceGE xStar β := by
    intro y hy
    rw [mem_closedHalfSpaceGE_iff]
    have hy_sInf :
        -(δᵛ(-xStar | C2)) ≤ (⟪xStar, y⟫ₚ : WithTopBot 𝕜) := by
      exact neg_supportFunction_neg_le_pairing (C := C2) (xStar := xStar) hy
    have hβle : ((β : 𝕜) : WithTopBot 𝕜) ≤
        -(δᵛ(-xStar | C2)) := by
      simpa [hβ] using hle
    have hy_ge :
        ((β : 𝕜) : WithTopBot 𝕜) ≤ (⟪xStar, y⟫ₚ : WithTopBot 𝕜) := by
      calc
        ((β : 𝕜) : WithTopBot 𝕜) ≤ -(δᵛ(-xStar | C2)) := hβle
        _ ≤ (⟪xStar, y⟫ₚ : WithTopBot 𝕜) := hy_sInf
    have hy_ge' : (β : WithBot 𝕜) ≤ ((⟪xStar, y⟫ₚ : 𝕜) : WithBot 𝕜) :=
      (WithTop.coe_le_coe).1 hy_ge
    have hy_ge'' : β ≤ (⟪xStar, y⟫ₚ : 𝕜) := (WithBot.coe_le_coe).1 hy_ge'
    exact (HasPairingSwap.pairing_swap (𝕜 := 𝕜) y xStar).symm ▸ hy_ge''
  have hy_ex : ∃ y ∈ C2, β < ⟪y, xStar⟫ₚ := by
    have hβ_lt : ((β : 𝕜) : WithTopBot 𝕜) < δᵛ(xStar | C2) := by
      simpa [hβ] using hlt
    rw [supportFunction_def] at hβ_lt
    rcases lt_iSup_iff.mp hβ_lt with ⟨a, ha⟩
    refine ⟨a, a.2, ?_⟩
    have ha' : ((β : 𝕜) : WithTopBot 𝕜) < (⟪xStar, (a : E)⟫ₚ : WithTopBot 𝕜) := ha
    have ha'' : (β : WithBot 𝕜) < ((⟪xStar, (a : E)⟫ₚ : 𝕜) : WithBot 𝕜) :=
      (WithTop.coe_lt_coe).1 ha'
    have ha''' : β < (⟪xStar, (a : E)⟫ₚ : 𝕜) := (WithBot.coe_lt_coe).1 ha''
    exact (HasPairingSwap.pairing_swap (𝕜 := 𝕜) (a : E) xStar).symm ▸ ha'''
  refine ⟨affineHyperplane xStar β, ?_⟩
  constructor
  · exact ⟨xStar, β,
      hxStar_flip_ne,
      rfl, hC1_le, hC2_ge⟩
  · intro hC2_subset
    rcases hy_ex with ⟨y, hyC2, hy_gt⟩
    have hyH : y ∈ affineHyperplane xStar β := hC2_subset hyC2
    have hy_eq : ⟪y, xStar⟫ₚ = β := mem_affineHyperplane_iff.mp hyH
    rw [hy_eq] at hy_gt
    exact (lt_irrefl β) hy_gt

omit [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [HasLinearPairing.Nondegenerate E Y 𝕜] in
private theorem exists_supportFunction_counterexample_of_separator_not_subset_right
    {C1 C2 : Set E}
    (hsep : ∃ H : AffineSubspace 𝕜 E,
      AffineSubspace.Separates Y H C1 C2 ∧ ¬ C2 ⊆ H) :
    ∃ xStar : Y,
      δᵛ(xStar | C1) ≤ -(δᵛ(-xStar | C2)) ∧
        δᵛ(xStar | C1) ≠ δᵛ(xStar | C2) := by
  rcases hsep with ⟨H, hH_sep, hH_not_subset⟩
  rcases hH_sep with ⟨xStar, β, hxStar_ne, hH, hC1_le, hC2_ge⟩
  refine ⟨xStar, ?_, ?_⟩
  · have hC1_support : δᵛ(xStar | C1) ≤ β :=
      by
        rw [supportFunction_def]
        refine iSup_le ?_
        intro z
        have hz_le : (⟪(z : E), xStar⟫ₚ : 𝕜) ≤ β :=
          mem_closedHalfSpaceLE_iff.mp (hC1_le z.2)
        have hz_le' : (⟪xStar, (z : E)⟫ₚ : 𝕜) ≤ β :=
          (HasPairingSwap.pairing_swap (𝕜 := 𝕜) (z : E) xStar) ▸ hz_le
        exact (WithTop.coe_le_coe).2 ((WithBot.coe_le_coe).2 hz_le')
    have hC2_inf : ((β : 𝕜) : WithTopBot 𝕜) ≤
        -(δᵛ(-xStar | C2)) := by
      rw [neg_supportFunction_neg_eq_sInf_image_pairing (C := C2) (xStar := xStar)]
      refine le_sInf ?_
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      have hz_ge : β ≤ (⟪(z : E), xStar⟫ₚ : 𝕜) := mem_closedHalfSpaceGE_iff.mp (hC2_ge hz)
      have hz_ge' : β ≤ (⟪xStar, (z : E)⟫ₚ : 𝕜) :=
        (HasPairingSwap.pairing_swap (𝕜 := 𝕜) (z : E) xStar) ▸ hz_ge
      exact (WithTop.coe_le_coe).2 ((WithBot.coe_le_coe).2 hz_ge')
    exact le_trans hC1_support hC2_inf
  · intro hEq
    have hC2_subset : C2 ⊆ H := by
      intro y hyC2
      have hy_aff : y ∈ affineHyperplane xStar β := by
        rw [mem_affineHyperplane_iff]
        have hy_ge : β ≤ (⟪y, xStar⟫ₚ : 𝕜) :=
          mem_closedHalfSpaceGE_iff.mp (hC2_ge hyC2)
        have hy_ge' : ((β : 𝕜) : WithTopBot 𝕜) ≤ (⟪y, xStar⟫ₚ : WithTopBot 𝕜) := by
          exact (WithTop.coe_le_coe).2 ((WithBot.coe_le_coe).2 hy_ge)
        have hy_le : (⟪y, xStar⟫ₚ : WithTopBot 𝕜) ≤ δᵛ(xStar | C2) := by
          have hy_le' : (⟪xStar, y⟫ₚ : WithTopBot 𝕜) ≤ δᵛ(xStar | C2) := by
            rw [supportFunction_def]
            exact le_iSup (fun z : C2 ↦ (⟪xStar, (z : E)⟫ₚ : WithTopBot 𝕜)) ⟨y, hyC2⟩
          calc
            (⟪y, xStar⟫ₚ : WithTopBot 𝕜) = (⟪xStar, y⟫ₚ : WithTopBot 𝕜) := by
              exact congrArg ((↑) : 𝕜 → WithTopBot 𝕜)
                (HasPairingSwap.pairing_swap (𝕜 := 𝕜) y xStar)
            _ ≤ δᵛ(xStar | C2) := hy_le'
        have hδ2_le_β : δᵛ(xStar | C2) ≤ β := by
          have hδ1_le_β : δᵛ(xStar | C1) ≤ β :=
            by
              rw [supportFunction_def]
              refine iSup_le ?_
              intro z
              have hz_le : (⟪(z : E), xStar⟫ₚ : 𝕜) ≤ β :=
                mem_closedHalfSpaceLE_iff.mp (hC1_le z.2)
              have hz_le' : (⟪xStar, (z : E)⟫ₚ : 𝕜) ≤ β :=
                (HasPairingSwap.pairing_swap (𝕜 := 𝕜) (z : E) xStar) ▸ hz_le
              exact (WithTop.coe_le_coe).2 ((WithBot.coe_le_coe).2 hz_le')
          exact hEq.symm ▸ hδ1_le_β
        have hy_eq : (⟪y, xStar⟫ₚ : WithTopBot 𝕜) = β := by
          refine le_antisymm ?_ hy_ge'
          exact le_trans hy_le hδ2_le_β
        exact WithTop.coe_eq_coe.mp (WithBot.coe_eq_coe.mp hy_eq)
      simpa [hH] using hy_aff
    exact hH_not_subset hC2_subset

/-- Corollary 20.2.1: a nonempty polyhedral convex set `C1` meets the relative interior
`ri[𝕜](C2)` of a convex set `C2` if and only if every dual vector
`xStar` whose support-function inequality
`δᵛ(xStar | C1) ≤ -δᵛ(-xStar | C2)`
holds also satisfies the equality
`δᵛ(xStar | C1) = δᵛ(xStar | C2)`. The source also assumes `C2` nonempty, but that hypothesis is
redundant here: if `C2 = ∅`, the left-hand side is false and the right-hand side already fails at
`xStar = 0`. -/
-- Proof sketch: when `C2` is nonempty, Theorem 20.2 identifies failure of
-- `(C1 ∩ ri[𝕜](C2)).Nonempty` with the existence of a separating hyperplane that does not contain
-- `C2`. One direction reads the support-function inequality directly from the separating
-- half-space containments and shows that equality of support values would force `C2` into the
-- hyperplane. Conversely, from a vector `xStar` satisfying the inequality but not the equality,
-- lift the finite support value `δᵛ(xStar | C1)` to a scalar level `β`; the owner half-space
-- theorem for `supportFunction` gives `C1 ⊆ closedHalfSpaceLE xStar β`, the dual infimum formula
-- gives `C2 ⊆ closedHalfSpaceGE xStar β`, and the strict support gap yields a point of `C2` off
-- the hyperplane `affineHyperplane xStar β`. If `C2 = ∅`, both sides are false by the previous
-- observation.
theorem inter_ri_nonempty_iff_supportFunction_condition
    {C1 C2 : Set E} (hC1 : C1.IsPolyhedral 𝕜 Y) (hC1_ne : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) :
    (C1 ∩ ri[𝕜](C2)).Nonempty ↔
      ∀ xStar : Y,
        δᵛ(xStar | C1) ≤ -δᵛ(-xStar | C2) →
          δᵛ(xStar | C1) = δᵛ(xStar | C2) := by
  by_cases hC2_ne : C2.Nonempty
  · have h20 :
        (∃ H : AffineSubspace 𝕜 E,
          AffineSubspace.SeparatesProperly Y H C1 C2 ∧ ¬ C2 ⊆ H) ↔
          Disjoint C1 (ri[𝕜](C2)) :=
      exists_separator_not_subset_right_iff_disjoint_ri
        hC1 hC1_ne hC2_conv hC2_ne
    constructor
    · intro hinter xStar hle
      by_contra hneq
      rcases
          exists_separator_not_subset_right_of_supportFunction_condition
            hC1_ne hC2_ne hle hneq
        with ⟨H, hH_sep, hH_not_subset⟩
      have hH_sepProper : AffineSubspace.SeparatesProperly Y H C1 C2 := by
        refine ⟨hH_sep, ?_⟩
        intro hboth
        exact hH_not_subset hboth.2
      have hdisj : Disjoint C1 (ri[𝕜](C2)) :=
        h20.mp ⟨H, hH_sepProper, hH_not_subset⟩
      exact (Set.not_disjoint_iff_nonempty_inter.mpr hinter) hdisj
    · intro hcond
      by_contra hnonempty
      have hdisj : Disjoint C1 (ri[𝕜](C2)) := by
        by_contra hnotdisj
        exact hnonempty (Set.not_disjoint_iff_nonempty_inter.mp hnotdisj)
      have hsep : ∃ H : AffineSubspace 𝕜 E,
          AffineSubspace.SeparatesProperly Y H C1 C2 ∧ ¬ C2 ⊆ H :=
        h20.mpr hdisj
      have hsep' : ∃ H : AffineSubspace 𝕜 E,
          AffineSubspace.Separates Y H C1 C2 ∧ ¬ C2 ⊆ H := by
        rcases hsep with ⟨H, hH_sepProper, hH_not_subset⟩
        exact ⟨H, hH_sepProper.separates, hH_not_subset⟩
      rcases exists_supportFunction_counterexample_of_separator_not_subset_right
          hsep' with
        ⟨xStar, hle, hneq⟩
      exact hneq (hcond xStar hle)
  · constructor
    · intro hinter
      exfalso
      simp [Set.not_nonempty_iff_eq_empty.mp hC2_ne] at hinter
    · intro hcond
      exfalso
      have hfalse := hcond 0
      have hC2_empty : C2 = ∅ := Set.not_nonempty_iff_eq_empty.mp hC2_ne
      have hC2_support_zero :
          δᵛ((0 : Y) | C2) = (⊥ : WithTopBot 𝕜) := by
        rw [hC2_empty, supportFunction_def]
        simp
      have hC2_support_negzero :
          δᵛ((-(0 : Y)) | C2) = (⊥ : WithTopBot 𝕜) := by
        rw [hC2_empty, supportFunction_def]
        simp
      have hle :
          δᵛ((0 : Y) | C1) ≤ -δᵛ((-(0 : Y)) | C2) := by
        have hneg_support :
            -δᵛ((-(0 : Y)) | C2) = (⊤ : WithTopBot 𝕜) := by
          rw [hC2_support_negzero]
          rfl
        calc
          δᵛ((0 : Y) | C1) ≤ (⊤ : WithTopBot 𝕜) := le_top
          _ = -δᵛ((-(0 : Y)) | C2) := hneg_support.symm
      have hEq := hfalse hle
      have hC1_zero : δᵛ((0 : Y) | C1) = 0 :=
        supportFunction_zero_of_nonempty hC1_ne
      have hzero_eq_bot : (0 : WithTopBot 𝕜) = (⊥ : WithTopBot 𝕜) := by
        simpa [hC1_zero, hC2_support_zero] using hEq
      have hzero_ne_bot : (0 : WithTopBot 𝕜) ≠ (⊥ : WithTopBot 𝕜) := by
        intro h
        cases h
      exact hzero_ne_bot hzero_eq_bot

end Set.IsPolyhedral

end

/-! ### Theorem_20_2 (from Chap04) -/
universe u v w

section

open scoped Rockafellar

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜]
variable {E : Type v} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {Y : Type w} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
  [HasLinearPairing.Nondegenerate E Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 20.2 characterizes when a nonempty convex set can be properly separated
  from a nonempty polyhedral convex set by a hyperplane that does not contain the right-hand set.
- `core/canonical`: the owner abstractions are `AffineSubspace.SeparatesProperly`, the subset
  predicates `Convex 𝕜` and `Set.IsPolyhedral` in the same pairing codomain `Y`, and the
  relative interior owner notation `ri[𝕜](·)`.
- `bridge/view`: Rockafellar's `ri C₂` is represented by `ri[𝕜](C2)`, and the source's
  separator is recorded by the Chapter 11 owner `H.SeparatesProperly Y C1 C2` together with the
  source-asymmetric clause `¬ C2 ⊆ H`.
- Primitive data vs derived API: the primitive inputs are the sets `C1`, `C2` and the hypotheses
  that `C1` is polyhedral and nonempty while `C2` is convex and nonempty; the separation criterion
  and the relative-interior disjointness condition are the derived theorem-level content.
- Domain-style sampling used here: the project declarations `AffineSubspace.SeparatesProperly`,
  `Set.IsPolyhedral`, and `Set.IsPolyhedral.convex`, together with the chapter owner notation
  `ri[𝕜](·)` and `Disjoint`.
- Layer target: `source-facing`, but attached to the left owner `Set.IsPolyhedral` rather
  than kept as a parallel free-standing theorem, with proper separation carried by the existing
  owner `AffineSubspace.SeparatesProperly` and the right-side noncontainment clause kept explicit.
- Ambient refinement: no coordinate-level data are used, and the separator owner is pairing-based
  with an explicit pairing codomain `Y`, so the theorem lives canonically on finite-dimensional
  topological pairing modules over an ordered-compatible topological scalar layer, rather than on
  any concrete inner-product coordinate model.
- Nondegeneracy boundary: `HasLinearPairing E Y 𝕜` by itself allows degenerate pairings, which can
  invalidate the source equivalence. The theorem therefore uses the canonical pairing owner
  class `HasLinearPairing.Nondegenerate E Y 𝕜`.
-/

namespace Set.IsPolyhedral

/-- Theorem 20.2: for a nonempty polyhedral convex set `C1` and a nonempty convex set `C2` in a
finite-dimensional topological nondegenerate pairing module over `𝕜`, there exists a hyperplane
that separates `C1` from `C2` properly and does not contain `C2` if and only if
`C1 ∩ ri[𝕜](C2) = ∅`, represented canonically as `Disjoint C1 (ri[𝕜](C2))`.
This keeps proper separation on the canonical owner surface while retaining the source's
asymmetric right-side noncontainment clause explicitly. -/
-- Proof sketch: for necessity, if `H.SeparatesProperly C1 C2` and `C2` is not contained in `H`,
-- then `ri[𝕜](C2)` lies in the open half-space on the `C2` side of `H`,
-- hence it is disjoint
-- from `C1`. For sufficiency, intersect `C1` with `affineSpan 𝕜 C2`; if this intersection is
-- empty, use the strong separation theorem for a polyhedral set and an affine subspace. Otherwise
-- first separate inside `affineSpan 𝕜 C2`, enlarge `C2` to a polyhedral half-space of that affine
-- span, and reduce to the polyhedral-polyhedral separation argument from Corollary 19.3.3.
theorem exists_separator_not_subset_right_iff_disjoint_ri
    {C1 C2 : Set E} (hC1 : C1.IsPolyhedral 𝕜 Y) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_ne : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H C1 C2 ∧ ¬ C2 ⊆ H) ↔
      Disjoint C1 (ri[𝕜](C2)) := sorry

end Set.IsPolyhedral

end
