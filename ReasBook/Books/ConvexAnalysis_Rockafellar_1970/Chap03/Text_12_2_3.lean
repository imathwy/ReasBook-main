import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.3 computes the Fenchel conjugate of the indicator of a linear
  subspace `L`, specialized in the source to a subspace of `R^n`, and identifies it with the
  indicator of the orthogonal complement `Lᗮ`.
- `core/canonical`: the owner declarations are the chapter indicator bridge `indicatorFunction`,
  the Fenchel conjugate owner `convexConjugate`, and the pairing-annihilator owner
  `Submodule.pairingOrthogonal`.
- `bridge/view`: the inner-product orthogonal-complement owner `Submodule.orthogonal` is retained
  as the textbook-facing specialization through
  `Submodule.pairingOrthogonal_eq_orthogonal_real`.

Primitive data vs derived API:
- primitive datum: a subspace `L : Submodule 𝕜 X` in paired modules `X` and `Y`;
- derived API: the indicator-conjugacy identity first at `Lᗮₚ : Submodule 𝕜 Y`, then the
  source-facing self-pairing specialization `Lᗮ`.

Layer target: owner-first at `Submodule.pairingOrthogonal`, with a thin bridge theorem for the
textbook orthogonal notation.

Ambient minimization note:
- the owner-side statement is kept at the pairing/scalar-generic Chapter 14 layer;
- the remaining `ℝ` / inner-product specialization is only the textbook bridge `Lᗮ`.
-/

namespace Submodule

section PairingOwner

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

-- Proof sketch: apply the owner polar-cone conjugacy theorem to `K = L`, then rewrite
-- the polar cone of a submodule as its pairing annihilator.
/-- Text 12.2.3 at the canonical pairing-owner layer: the Fenchel conjugate of `δ(· | L)` is the
indicator of the pairing annihilator `Lᗮₚ`. -/
theorem convexConjugate_indicatorFunction_eq_indicatorFunction_pairingOrthogonal
    (L : Submodule 𝕜 X) :
    (δ[𝕜](· | L) : X → WithBotTop 𝕜)⋆ =
      (δ[𝕜](· | (Lᗮₚ : Set Y)) : Y → WithBotTop 𝕜) := by
  have hL_nonempty : (L : Set X).Nonempty := ⟨0, L.zero_mem⟩
  have hL_cone : Set.IsCone 𝕜 (L : Set X) := by
    intro c x _ hx
    exact L.smul_mem c hx
  have hpolar :
      (δ[𝕜](· | L) : X → WithBotTop 𝕜)⋆ =
        (δ[𝕜](· | (((L : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y)) : Y → WithBotTop 𝕜) := by
    simpa using
      (convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone
        (K := (L : Set X)) hL_nonempty hL_cone)
  have hset :
      (((L : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) = ((Lᗮₚ : Submodule 𝕜 Y) : Set Y) := by
    simpa using (Submodule.polarCone_set_eq_pairingOrthogonal (K := L))
  calc
    (δ[𝕜](· | L) : X → WithBotTop 𝕜)⋆
        = (δ[𝕜](· | (((L : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y)) : Y → WithBotTop 𝕜) := hpolar
    _ = (δ[𝕜](· | ((Lᗮₚ : Submodule 𝕜 Y) : Set Y)) : Y → WithBotTop 𝕜) := by
      simp [hset]

end PairingOwner

section RealInnerProductBridge

open scoped RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Text 12.2.3 (source-facing inner-product specialization): the Fenchel conjugate of `δ(· | L)`
is the indicator of the orthogonal complement `Lᗮ`. -/
theorem convexConjugate_indicatorFunction_eq_indicatorFunction_orthogonal
    (L : Submodule ℝ E) :
    (δ[ℝ](· | L) : E → WithBotTop ℝ)⋆ =
      (δ[ℝ](· | (Lᗮ : Set E)) : E → WithBotTop ℝ) := by
  have hpair :
      (δ[ℝ](· | L) : E → WithBotTop ℝ)⋆ =
        (δ[ℝ](· | (Lᗮₚ : Set E)) : E → WithBotTop ℝ) :=
    convexConjugate_indicatorFunction_eq_indicatorFunction_pairingOrthogonal (L := L)
  have hset :
      (Lᗮₚ : Set E) = (Lᗮ : Set E) := by
    simpa using
      congrArg (fun K : Submodule ℝ E => (K : Set E))
        (Submodule.pairingOrthogonal_eq_orthogonal_real L)
  calc
    (δ[ℝ](· | L) : E → WithBotTop ℝ)⋆
        = (δ[ℝ](· | (Lᗮₚ : Set E)) : E → WithBotTop ℝ) := hpair
    _ = (δ[ℝ](· | (Lᗮ : Set E)) : E → WithBotTop ℝ) := by
      simp [hset]

end RealInnerProductBridge

end Submodule

end
