import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped RealInnerProductSpace PolarCone Rockafellar

universe u v w

section

variable {𝕜 : Type w} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.2 identifies the polar of a linear subspace of `R^n` with its
  orthogonal complement.
- `core/canonical`: the owner abstractions are the source-facing polar formula `polarCone` from
  `Text_14_0_1` and the chapter pairing-annihilator owner `Submodule.pairingOrthogonal` from
  `Text_1_6`, both at the primitive pairing layer.
- `bridge/view`: the textbook orthogonal complement `Submodule.orthogonal` is retained as the real
  inner-product specialization through `Submodule.pairingOrthogonal_eq_orthogonal_real`.

Domain-style sampling used here:
- `polarCone` and `mem_polarCone_iff_pairing` from `Text_14_0_1`;
- `Submodule.pairingOrthogonal` and `Submodule.mem_pairingOrthogonal_iff` from `Text_1_6`;
- `Submodule.pairingOrthogonal_eq_orthogonal_real` from `Text_1_6`.

Primitive data vs derived API:
- primitive datum: a subspace `K : Submodule 𝕜 X` in a paired module;
- derived API: first the canonical pairing-annihilator identity for the polar cone of `K`, then the
  source-facing real inner-product orthogonal-complement specialization.

Layer target: owner-first. The primary declaration is now at the primitive pairing layer; the
source-facing `R^n` orthogonal statement is a thin specialization bridge.
-/

namespace Submodule

@[simp] theorem mem_polarCone_submodule_iff {K : Submodule 𝕜 X} {y : Y} :
    y ∈ (K : Set X)ᵒ[𝕜] ↔ y ∈ Kᗮₚ := by
  rw [mem_polarCone_iff_pairing]
  rw [mem_pairingOrthogonal_iff]
  constructor
  · intro hy x hxK
    have hle : (⟪x, y⟫ₚ : 𝕜) ≤ 0 := hy x hxK
    have hge : (0 : 𝕜) ≤ ⟪x, y⟫ₚ := by
      have hxneg : (⟪(-1 : 𝕜) • x, y⟫ₚ : 𝕜) ≤ 0 :=
        hy (((-1 : 𝕜) • x)) (K.smul_mem (-1) hxK)
      have hxneg' : -(⟪x, y⟫ₚ : 𝕜) ≤ 0 := by
        simpa [HasLinearPairing.pairing_eq_pairingLinear] using hxneg
      exact neg_nonpos.mp hxneg'
    exact le_antisymm hle hge
  · intro hy x hxK
    simpa [HasLinearPairing.pairing_eq_pairingLinear] using (hy x hxK).le

/-- The polar of a subspace is exactly its pairing annihilator in the chapter owner sense. -/
theorem polarCone_eq_pairingOrthogonal (K : Submodule 𝕜 X) :
    ((K : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) = PointedCone.ofSubmodule Kᗮₚ := by
  ext y
  simpa using (mem_polarCone_submodule_iff (K := K) (y := y))

/-- Set-level view of `polarCone_eq_pairingOrthogonal`. -/
theorem polarCone_set_eq_pairingOrthogonal (K : Submodule 𝕜 X) :
    (((K : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) = ((Kᗮₚ : Submodule 𝕜 Y) : Set Y) := by
  simpa using congrArg
    (fun C : PointedCone 𝕜 Y => (C : Set Y))
    (polarCone_eq_pairingOrthogonal (K := K))

end Submodule

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Submodule

@[simp] theorem mem_polarCone_submodule_iff_orthogonal {K : Submodule ℝ E} {y : E} :
    y ∈ (K : Set E)ᵒ[ℝ] ↔ y ∈ Kᗮ := by
  simpa [pairingOrthogonal_eq_orthogonal_real] using
    (mem_polarCone_submodule_iff (K := K) (y := y))

/-- Text 14.0.2: if `K` is a linear subspace of a real inner-product space, specialized in the
source to `R^n`, then the polar `Kᵒ[ℝ]` of `K` coincides with its orthogonal complement. -/
@[simp] theorem polarCone_eq_orthogonal (K : Submodule ℝ E) :
    (K : Set E)ᵒ[ℝ] = PointedCone.ofSubmodule Kᗮ := by
  ext y
  simpa using (mem_polarCone_submodule_iff_orthogonal (K := K) (y := y))

/-- Set-level view of `polarCone_eq_orthogonal`. -/
theorem polarCone_set_eq_orthogonal (K : Submodule ℝ E) :
    (((K : Set E)ᵒ[ℝ] : PointedCone ℝ E) : Set E) = (Kᗮ : Set E) := by
  exact congrArg
    (fun C : PointedCone ℝ E => (C : Set E))
    (polarCone_eq_orthogonal (K := K))

end Submodule

end
