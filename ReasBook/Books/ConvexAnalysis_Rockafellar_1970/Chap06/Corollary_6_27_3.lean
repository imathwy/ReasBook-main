import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_4

noncomputable section

universe u

open scoped Rockafellar

section RecessionDirectionBridge

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [AddRightMono 𝕜]
variable {E : Type u}
variable [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: `Set.RecedesInDirection` is by definition nonzero membership in `0⁺[𝕜]C`, while
-- `Function.RecedesInDirection` is equivalent (under convex/proper hypotheses) to nonzero
-- membership in `((h)₀⁺).recessionCone`.
/-- Bridge equivalence between the cone-owner common-direction hypothesis and the
source-facing common-recession-direction hypothesis. This bridge lives on the weaker
ordered-module layer and does not require any finite-dimensional topological assumptions. -/
theorem common_recessionCone_lineal_iff_common_recessionDirections_lineal
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) :
    (∀ ⦃y : E⦄, y ∈ 0⁺[𝕜]C → y ∈ ((h)₀⁺).recessionCone → y ≠ 0 →
      y ∈ Function.lineal h) ↔
      (∀ ⦃y : E⦄, C.RecedesInDirection 𝕜 y → h.RecedesInDirection 𝕜 y →
        y ∈ Function.lineal h) := by
  constructor
  · intro hlineal y hyC hyh
    have hy_mem : y ∈ ((h)₀⁺).recessionCone :=
      Function.RecedesInDirection.mem_recessionCone hyh hh_convex hh_proper
    exact hlineal hyC.2 hy_mem hyC.1
  · intro hlineal y hyC hyh hy_ne
    have hyC' : C.RecedesInDirection 𝕜 y := ⟨hy_ne, hyC⟩
    have hyh' : h.RecedesInDirection 𝕜 y :=
      Function.RecedesInDirection.of_mem_recessionCone hh_convex hh_proper hy_ne hyh
    exact hlineal hyC' hyh'

end RecessionDirectionBridge

section

variable {𝕜 : Type*}
variable [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
variable [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the corollary says that a closed proper convex function attains its infimum on
  any polyhedral convex set where it is bounded below, provided every recession direction of the
  function is a direction along which the function is affine.
- `core/canonical`: the relevant project owners already present are
  `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`,
  `0⁺[𝕜]C`, `((h)₀⁺).recessionCone`,
  `Function.HasTranslationSlope`, `Function.lineal`, `Set.IsPolyhedral`, `BddBelow`,
  and the minimizer owner `IsMinOn`.
  the upstream owner `∃ v, h.HasTranslationSlope 𝕜 y v`, while the chapter's canonical owner for
  harmless common recession directions is `y ∈ Function.lineal h`.

Domain-style sampling used here:
- `Function.IsConvex`, `Function.IsProper`, `LowerSemicontinuous`;
- `Set.recessionCone` / `0⁺[𝕜]C`;
- `((h)₀⁺).recessionCone`;
- `Function.RecedesInDirection` from Definition 6.27.4;
- `Function.HasTranslationSlope` from Theorem 8.8;
- `Function.lineal` from Definition 8.9.0 and
  `ConvexERealFunction.mem_lineal_iff_forall_translate_profile_constant` from Definition 8.9.1;
- `Set.IsPolyhedral`, together with its derived convexity/closedness API;
- `IsMinOn` from mathlib's order-extrema layer.

Primitive data vs derived API:
- primitive inputs for the core owner theorem: the function `h`, the polyhedral set `C`,
  bounded-below data on `h '' C`, and the common-direction hypothesis in cone-owner form
  `y ∈ 0⁺[𝕜]C → y ∈ ((h)₀⁺).recessionCone → y ≠ 0 → y ∈ Function.lineal h`;
- source-facing bridge companion: the common-direction hypothesis phrased through
  `Set.RecedesInDirection` and `Function.RecedesInDirection`;
- derived output: existence of a minimizer in the canonical owner form `∃ x ∈ C, IsMinOn h C x`.

Layer target:
- `core/canonical` companion: common directions are stated on cone owners
  `0⁺[𝕜]C` and `((h)₀⁺).recessionCone`, with harmlessness in `Function.lineal h`;
- `source-facing` main theorem: the textbook affine-direction hypothesis is preserved and exposed
  through `Function.HasTranslationSlope`, rather than through a new wrapper for attained
  constrained infima.

Nonemptiness note: the textbook phrase "attains its infimum on `C`" is rendered by an existential
minimizer statement, so the set `C` is kept explicitly nonempty on the Lean theorem surface.
-/

-- Proof sketch: this source-facing theorem is the attainment step at recession-direction owner
-- level. The cone-owner variant below is a bridge corollary of this statement.
/-- Source-facing bridge companion: if every common recession direction of `C` and `h` lies in
`Function.lineal h`, then `h` attains its infimum on `C`. -/
theorem exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_common_recessionDirections_lineal
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hC_nonempty : C.Nonempty) (hC_poly : C.IsPolyhedral 𝕜)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hlineal :
      ∀ ⦃y : E⦄, C.RecedesInDirection 𝕜 y → h.RecedesInDirection 𝕜 y →
        y ∈ Function.lineal h)
    (hbounded : BddBelow (h '' C)) :
    ∃ x ∈ C, IsMinOn h C x := sorry

-- Proof sketch: rewrite the cone-owner hypothesis to the source-facing recession-direction
-- hypothesis using the bridge theorem above, then apply the source-facing attainment theorem.
/-- Core owner companion: if `h` is a closed proper convex function, `C` is a nonempty
polyhedral convex set, `h` is bounded below on `C`, and every nonzero vector common to the set
recession cone `0⁺[𝕜]C` and to the function recession cone `((h)₀⁺).recessionCone` lies
in `Function.lineal h`, then `h` attains its infimum on `C`. The conclusion is stated in the
canonical minimizer owner form `∃ x ∈ C, IsMinOn h C x`. -/
theorem exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_common_recessionCone_lineal
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hC_nonempty : C.Nonempty) (hC_poly : C.IsPolyhedral 𝕜)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hlineal :
      ∀ ⦃y : E⦄, y ∈ 0⁺[𝕜]C → y ∈ ((h)₀⁺).recessionCone → y ≠ 0 →
        y ∈ Function.lineal h)
    (hbounded : BddBelow (h '' C)) :
    ∃ x ∈ C, IsMinOn h C x := by
  have hlineal' :
      ∀ ⦃y : E⦄, C.RecedesInDirection 𝕜 y → h.RecedesInDirection 𝕜 y →
        y ∈ Function.lineal h :=
    (common_recessionCone_lineal_iff_common_recessionDirections_lineal
      (C := C) (h := h) hh_convex hh_proper).1 hlineal
  exact
    exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_common_recessionDirections_lineal
      hC_nonempty hC_poly hh_convex hh_proper hh_closed hlineal' hbounded

-- Proof sketch: first pass from the source affine-direction hypothesis to the source-facing
-- harmless-common-direction condition on `Function.lineal h`; then apply the bridge theorem above.
-- This keeps the textbook affine wording on the public theorem surface while delegating the
-- canonical cone-owner abstraction to the core theorem.
/-- Corollary 6.27.3: if `h` is a closed proper convex function and every recession direction of
`h` is a direction along which `h` is affine, then `h` attains its infimum on any nonempty
polyhedral convex set `C` on which it is bounded below. The conclusion is stated in the canonical
minimizer owner form `∃ x ∈ C, IsMinOn h C x`. -/
theorem exists_mem_isMinOn_of_polyhedral_of_bddBelow_of_recessionDirections_affine
    {C : Set E} {h : E → WithBotTop 𝕜}
    (hC_nonempty : C.Nonempty) (hC_poly : C.IsPolyhedral 𝕜)
    (hh_convex : h.IsConvex 𝕜) (hh_proper : h.IsProper) (hh_closed : LowerSemicontinuous h)
    (hrecession_affine :
      ∀ ⦃y : E⦄, h.RecedesInDirection 𝕜 y → ∃ v, h.HasTranslationSlope 𝕜 y v)
    (hbounded : BddBelow (h '' C)) :
    ∃ x ∈ C, IsMinOn h C x := by
  sorry

end
