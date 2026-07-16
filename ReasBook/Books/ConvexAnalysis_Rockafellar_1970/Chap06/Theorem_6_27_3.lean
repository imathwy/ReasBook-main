import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Example_9_2_2_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4

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
