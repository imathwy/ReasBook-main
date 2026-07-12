import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {𝕜 : Type v} [Semiring 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type w} [AddCommMonoid F] [Module 𝕜 F]

namespace LinearMap

/-- For any linear map, preimages preserve recession directions in the primitive direction:
if `A y` is a recession direction of `C`, then `y` is a recession direction of `A ⁻¹' C`. -/
theorem preimage_recessionCone_subset
    (A : E →ₗ[𝕜] F) (C : Set F) :
    A ⁻¹' (0⁺[𝕜] C) ⊆ 0⁺[𝕜] (A ⁻¹' C) := by
  intro y hy
  change A y ∈ 0⁺[𝕜] C at hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  change A (x + a • y) ∈ C
  simpa [map_add, map_smul] using (Set.mem_recessionCone_iff.mp hy) (A x) hx a ha

end LinearMap

namespace Set

variable {C : Set F}

/-- Primitive bridge-layer inclusion for linear preimages: if a nonempty preimage `A ⁻¹' C` is
given and one nonnegative ray in `C` implies recession-cone membership in `C`, then every
recession direction of `A ⁻¹' C` maps to a recession direction of `C`. -/
theorem recessionCone_linear_preimage_subset_of_nonneg_ray
    (A : E →ₗ[𝕜] F) (hpre_nonempty : (A ⁻¹' C).Nonempty)
    (hRayToRecession :
      ∀ {x y : F}, x ∈ C →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C) → y ∈ 0⁺[𝕜] C) :
    0⁺[𝕜] (A ⁻¹' C) ⊆ A ⁻¹' (0⁺[𝕜] C) := by
  rcases hpre_nonempty with ⟨x, hx⟩
  intro y hy
  change A y ∈ 0⁺[𝕜] C
  have hAx : A x ∈ C := hx
  exact hRayToRecession hAx fun a ha ↦ by
    simpa [Set.mem_preimage, map_add, map_smul] using
      (Set.mem_recessionCone_iff.mp hy) x hx a ha

/-- Primitive bridge-layer equality for linear preimages: if `A ⁻¹' C` is nonempty and one
nonnegative ray in `C` implies recession-cone membership in `C`, then the recession cone of the
preimage is exactly the preimage of the recession cone. -/
theorem recessionCone_linear_preimage_eq_preimage_recessionCone_of_nonneg_ray
    (A : E →ₗ[𝕜] F) (hpre_nonempty : (A ⁻¹' C).Nonempty)
    (hRayToRecession :
      ∀ {x y : F}, x ∈ C →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C) → y ∈ 0⁺[𝕜] C) :
    0⁺[𝕜] (A ⁻¹' C) = A ⁻¹' (0⁺[𝕜] C) := by
  exact Set.Subset.antisymm
    (recessionCone_linear_preimage_subset_of_nonneg_ray
      (A := A) (C := C) hpre_nonempty hRayToRecession)
    (A.preimage_recessionCone_subset C)

end Set

end

section

universe u v w

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type w} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

namespace Convex

variable {C : Set F}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.3.4 identifies the recession cone of a linear preimage with the
  preimage of the recession cone.
- `core/canonical`: the chapter owner object for this notion is `recessionCone`; the primitive
  linear-preimage bridge theorem is owner-level data in `Set`, while the closed-convex upgrade
  remains on the source-facing `Convex` owner namespace.
- `bridge/view`: the closed-convex comparison with mathlib's `asymptoticCone ℝ` already lives
  upstream in `recessionCone_eq_asymptoticCone`, so this file should not keep a second public
  wrapper around that bridge.
- Domain-style sampling: `recessionCone`, `Set.mem_recessionCone_iff`,
  `LinearMap.preimage_recessionCone_subset`,
  `Set.recessionCone_linear_preimage_subset_of_nonneg_ray`,
  `Set.recessionCone_linear_preimage_eq_preimage_recessionCone_of_nonneg_ray`,
  `Convex.mem_recessionCone_of_nonneg_ray`, and `Convex.linear_preimage`.
- Primitive data vs derived API: the primitive preimage inclusion
  `A ⁻¹' (0⁺[𝕜] C) ⊆ 0⁺[𝕜] (A ⁻¹' C)` depends only on linearity and the owner definition. The
  reverse inclusion from `0⁺[𝕜] (A ⁻¹' C)` to `A ⁻¹' (0⁺[𝕜] C)` is split into a primitive
  capability-style bridge in `Set` and the genuinely closed-convex upgrade from Theorem 8.3.
- Ambient minimization: the proof uses only the scalar-generic Chapter 8 ray criterion from
  `Theorem_8_3`, so the theorem should live over the same ordered topological field `𝕜` rather
  than being frozen to `ℝ`.
- Layer target: split owner layers (`Set` primitive bridge, `Convex` source-facing corollary).
-/

/-- Corollary 8.3.4, nontrivial inclusion: when `A ⁻¹' C` is nonempty, every recession direction
of `A ⁻¹' C` maps to a recession direction of `C`. -/
theorem recessionCone_linear_preimage_subset
    (hC_convex : Convex 𝕜 C) (A : E →ₗ[𝕜] F) (hC_closed : IsClosed C)
    (hpre_nonempty : (A ⁻¹' C).Nonempty) :
    0⁺[𝕜] (A ⁻¹' C) ⊆ A ⁻¹' (0⁺[𝕜] C) := by
  exact Set.recessionCone_linear_preimage_subset_of_nonneg_ray
    (A := A) (C := C) hpre_nonempty
    (fun {x y} hx hRay ↦
      hC_convex.mem_recessionCone_of_nonneg_ray (x := x) (y := y) hC_closed hRay)

/-- Corollary 8.3.4: if `A : E →ₗ[𝕜] F` is linear, `C ⊆ F` is closed and convex, and the preimage
`A ⁻¹' C` is nonempty, then the recession cone `0⁺[𝕜] (A⁻¹ C)` is exactly the preimage of
`0⁺[𝕜] C`. The textbook real statement is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: combine the nontrivial closed-convex inclusion
-- `0⁺[𝕜] (A ⁻¹' C) ⊆ A ⁻¹' (0⁺[𝕜] C)` with the primitive linearity inclusion
-- `A ⁻¹' (0⁺[𝕜] C) ⊆ 0⁺[𝕜] (A ⁻¹' C)`.
theorem recessionCone_linear_preimage
    (hC_convex : Convex 𝕜 C) (A : E →ₗ[𝕜] F) (hC_closed : IsClosed C)
    (hpre_nonempty : (A ⁻¹' C).Nonempty) :
    0⁺[𝕜] (A ⁻¹' C) = A ⁻¹' (0⁺[𝕜] C) := by
  exact Set.recessionCone_linear_preimage_eq_preimage_recessionCone_of_nonneg_ray
    (A := A) (C := C) hpre_nonempty
    (fun {x y} hx hRay ↦
      hC_convex.mem_recessionCone_of_nonneg_ray (x := x) (y := y) hC_closed hRay)

end Convex

end
