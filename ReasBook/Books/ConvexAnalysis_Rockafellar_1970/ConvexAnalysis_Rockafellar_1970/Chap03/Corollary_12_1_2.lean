import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_1_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Rockafellar

section

variable {𝕜 : Type*} {X : Type u} {Y : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.1.2 states that every proper convex function on `R^n` admits at
  least one affine function `x ↦ ⟪x, b⟫ₚ - β` lying pointwise below it.
- `core/canonical`: the owner abstractions already present upstream are `convexConjugate`,
  `Function.IsProper`, and the properness transfer theorem
  `Function.IsConvex.convexConjugate_isProper_iff`.
- `bridge/view`: the source coordinate form `⟪x, b⟫ₚ - β ≤ f x` is obtained from the canonical
  one-minorant constructor `pairingSubConstAffineMinorant`.

Domain-style sampling used here:
- `Function.IsProper` from `Definition_4_6`;
- `convexConjugate` and `Function.IsConvex.convexConjugate_isProper_iff` from `Theorem_12_2`;
- `pairingSubConstAffineMinorant` and `affineMinorant_le` from `Text_12_1_2`.

Primitive data vs derived API:
- primitive owner input: one dual-side properness witness
  `hf_conj_proper : (f⋆ : Y → WithBotTop 𝕜).IsProper`;
- owner-derived data: one dual point `y` where `f⋆ y` is finite;
- derived API here: the textbook affine lower bound `⟪x, y⟫ₚ - β ≤ f x`.

Layer target:
- the canonical owner theorem below is the primitive statement "proper conjugate gives an affine
  minorant", and it lives on the weaker module/pairing layer;
- the Rockafellar corollary is then a thin source-facing bridge from
  `f.IsConvex 𝕜 ∧ f.IsProper` using Theorem 12.2(3).

Codomain/scalar canonicalization note:
- this local closure uses the canonical codomain layer `WithBotTop 𝕜` directly, matching the
  upstream owners `pairingSubConstAffineMinorant` and
  `Function.IsConvex.convexConjugate_isProper_iff`;
- the finite dual value `f⋆ y` is lifted to a scalar `β : 𝕜` via the canonical
  `WithBotTop` finite-value lift, avoiding `EReal`-specific bridges.

Finite-dimensional / continuity irreducibility note:
- `FiniteDimensional 𝕜 X` and `HasContinuousPairing X Y 𝕜` are not needed for the primitive
  affine-minorant constructor theorem in this file;
- they are only needed in the source-facing bridge through
  `Function.IsConvex.convexConjugate_isProper_iff`, whose current upstream owner statement is at
  that ambient layer.
-/

-- Proof sketch: properness of `f⋆` gives `y` with finite value `f⋆ y`. Taking
-- the scalar lift `β` of `f⋆ y`, Text 12.1.2 yields the corresponding affine-map minorant.
/-- Canonical owner form for Corollary 12.1.2: if the conjugate `f⋆` is proper, then `f` admits
one pairing affine map `pairingSubConstAffineMap y β` below it. -/
theorem exists_pairingSubConstAffineMap_le_of_convexConjugate_isProper
    (f : X → WithBotTop 𝕜) (hf_conj_proper : (f⋆ : Y → WithBotTop 𝕜).IsProper) :
    ∃ y : Y, ∃ β : 𝕜, (pairingSubConstAffineMap y β).toWithBotTop ≤ f := by
  set g : Y → WithBotTop 𝕜 := (f⋆ : Y → WithBotTop 𝕜)
  have hg_proper : g.IsProper := by
    simpa [g] using hf_conj_proper
  obtain ⟨y, hy_dom⟩ := hg_proper.nonempty_dom
  have hy_top : g y < ⊤ := mem_effectiveDomain.mp hy_dom
  have hy_ne_top : g y ≠ ⊤ := ne_of_lt hy_top
  have hy_ne_bot : g y ≠ ⊥ := hg_proper.ne_bot y
  lift g y to 𝕜 using ⟨hy_ne_top, hy_ne_bot⟩ with β hβ
  have hy_le : g y ≤ (β : WithBotTop 𝕜) := by simp [hβ]
  refine ⟨y, β, ?_⟩
  exact
    (pairingSubConstAffineMap_le_iff_convexConjugate_le (f := f) y β).2
      (by simpa [g] using hy_le)

/-- Source-facing bridge: if the conjugate `f⋆` is proper, then `f` admits an affine lower bound
`x ↦ ⟪x, y⟫ₚ - β`. -/
theorem exists_pairing_sub_const_le_of_convexConjugate_isProper
    (f : X → WithBotTop 𝕜) (hf_conj_proper : (f⋆ : Y → WithBotTop 𝕜).IsProper) :
    ∃ y : Y, ∃ β : 𝕜, ∀ x : X, ((⟪x, y⟫ₚ - β : 𝕜) : WithBotTop 𝕜) ≤ f x := by
  obtain ⟨y, β, hminor⟩ :=
    exists_pairingSubConstAffineMap_le_of_convexConjugate_isProper (f := f) hf_conj_proper
  refine ⟨y, β, ?_⟩
  intro x
  simpa [pairingSubConstAffineMap_apply, coe_sub] using hminor x

end

section

variable {𝕜 : Type*} {E : Type u}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

-- Proof sketch: Theorem 12.2(3) turns `f.IsConvex 𝕜 ∧ f.IsProper` into properness of `f⋆`;
-- then apply the primitive owner theorem above.
namespace Function.IsConvex

/-- Corollary 12.1.2 (source-facing bridge): given a proper convex function `f` on a
finite-dimensional scalar space with a continuous linear self-pairing, there exist `b` and
`β` such that
`f x ≥ ⟪x, b⟫ₚ - β` for every `x`. -/
theorem exists_pairing_sub_const_le_of_isProper
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    ∃ b : E, ∃ β : 𝕜, ∀ x : E, ((⟪x, b⟫ₚ - β : 𝕜) : WithBotTop 𝕜) ≤ f x := by
  have hf_conj_proper : (f⋆ : E → WithBotTop 𝕜).IsProper := by
    exact (hf_convex.convexConjugate_isProper_iff).2 hf_proper
  exact exists_pairing_sub_const_le_of_convexConjugate_isProper (f := f) hf_conj_proper

end Function.IsConvex

end
