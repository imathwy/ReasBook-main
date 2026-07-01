import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_4_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_2

noncomputable section

universe u v w z

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type w} {U : Type u}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.11 says that a convex generalized program is strictly consistent if
  and only if every direction in the perturbation space meets the bifunction effective domain after
  some positive dilation.
- `core/canonical`: the existing owner for strict consistency is
  `Bifunction.IsStrictlyConsistent F`, while the source domain owner from Definition 6.29.8 is
  `Bifunction.dom F`.
- `bridge/view`: the source clause “`F (λu)` is not the constant function `+∞`” is exactly the
  membership condition `λ • u ∈ dom F`.

Domain-style sampling used here:
- `Bifunction.IsStrictlyConsistent`;
- `dom(·)` from Chapter 1 effective-domain notation;
- `convᵇ[𝕜](F)`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- primitive owner hypotheses: strict consistency of `F` and convexity of the source-facing domain
  owner `dom F`;
- derived source-facing bridge: the convex-bifunction specialization where
  `convᵇ[𝕜](F)` implies `Convex 𝕜 (dom F)`.

Layer target: `source-facing`, stated directly on the existing canonical owners rather than through
any new program wrapper; the primary theorem stays at the primitive domain-convexity layer.
-/

-- Proof sketch: `Bifunction.isStrictlyConsistent_iff` identifies strict consistency with
-- `0 ∈ interior (dom F)`, and Corollary 6.4.1 rewrites interior membership at `0` for a convex
-- set into the positive-ray intersection criterion.
/-- Primitive-domain form of Lemma 6.29.11: if `dom F` is convex, then strict consistency is
equivalent to the condition that every perturbation direction `u` has a positive dilation `a`
with `a • u ∈ dom F`. -/
theorem isStrictlyConsistent_iff_forall_exists_pos_smul_mem_dom
    {X : Type v} {β : Type z}
    [Top β] [LT β]
    {F : U → X → β}
    (hdom_convex : Convex 𝕜 (dom F)) :
    IsStrictlyConsistent F ↔
      ∀ u : U, ∃ a > (0 : 𝕜), a • u ∈ dom F := by
  have hzero :
      (0 : U) ∈ interior (dom F) ↔
        ∀ u : U, ∃ a > (0 : 𝕜), (0 : U) + a • u ∈ dom F :=
    hdom_convex.mem_interior_iff_forall_exists_pos_add_smul_mem
  have hzero' :
      (0 : U) ∈ interior (dom F) ↔
        ∀ u : U, ∃ a > (0 : 𝕜), a • u ∈ dom F := by
    simpa [zero_add] using hzero
  exact (isStrictlyConsistent_iff (F := F)).trans hzero'

-- `convᵇ[𝕜](F)` is a derived sufficient owner hypothesis via
-- `Bifunction.convex_dom`.
/-- Convex-bifunction specialization of Lemma 6.29.11. -/
theorem isStrictlyConsistent_iff_forall_exists_pos_smul_mem_dom_of_convex_bifunction
    {X : Type v} {α : Type z}
    [AddCommMonoid X] [SMul 𝕜 X]
    [AddCommMonoid α] [Preorder α] [SMul 𝕜 α]
    {F : U → X → WithBotTop α}
    (hF_convex : convᵇ[𝕜](F)) :
    IsStrictlyConsistent F ↔
      ∀ u : U, ∃ a > (0 : 𝕜), a • u ∈ dom F := by
  exact isStrictlyConsistent_iff_forall_exists_pos_smul_mem_dom
    (convex_dom hF_convex.convex_dom)

end

end Bifunction
