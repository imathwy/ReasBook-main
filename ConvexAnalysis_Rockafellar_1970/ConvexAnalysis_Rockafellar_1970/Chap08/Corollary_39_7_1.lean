import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_0_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_9_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_5

section

open Set
open scoped Pointwise Rockafellar SetRel

universe u v

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable {U : Type u} {X : Type v}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [T2Space U]
variable [_root_.FiniteDimensional 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
variable [_root_.FiniteDimensional 𝕜 X]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 39.7.1 says that the image `AC` of a closed convex set `C`
  under a closed convex process `A` is closed when no nonzero vector in `A⁻¹ {0}` belongs to the
  recession cone of `C`.
- `core/canonical`: the owner abstractions are Chapter 8's process predicate
  `SetRel.IsConvexProcess 𝕜` on `A : SetRel U X` and Chapter 2's closed-image owner theorem
  `LinearMap.isClosed_image_of_recessionKernelTrivial`.
- `bridge/view`: the source image `AC` is `A.image C`, and the reduction to the Chapter 2 owner
  goes through the graph slice `S = A ∩ (C ×ˢ univ)` together with the second projection
  `LinearMap.snd 𝕜 U X`.

Primary mathematical domain:
- closed images of convex graph relations via recession-direction criteria.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `LinearMap.isClosed_image_of_recessionKernelTrivial` from `Chap02.Theorem_9_1`;
- `Convex.mem_recessionCone_of_nonneg_ray` from `Chap02.Theorem_8_3`.

Primitive data vs derived API:
- primitive owner data: a relation `A : SetRel U X`, graph closedness, and the process owner
  predicate `A.IsConvexProcess 𝕜`;
- primitive source set data: a closed convex set `C : Set U`;
- derived API: closedness of `A.image C`, obtained by applying the Chapter 2 closed-image owner to
  the graph slice.

Ambient refinement:
- the main theorem lives at the same finite-dimensional Hausdorff topological vector-space
  layer over the ordered topological scalar field `𝕜` as the Chapter 2 owner theorem applied to the
  graph slice in `U × X`.

Layer target: `source-facing`, but organized as the canonical graph/projection bridge to the
Chapter 2 owner theorem.
-/

namespace SetRel.IsConvexProcess

variable {A : SetRel U X}

/-- Corollary 39.7.1: let `A : SetRel U X` be a closed convex process, expressed canonically by
the graph-closed owner `A.IsClosed` together with `A.IsConvexProcess 𝕜`. Let `C` be a closed
convex set in `U`.
If every recession direction of `C` lying in the zero fiber `(A⁻¹)[[0]]` is zero,
then the image `A.image C` is closed. The source Euclidean statement is the finite-dimensional
real specialization of this intrinsic graph/projection form. -/
theorem isClosed_image_of_isClosed_of_inv_image_zero_recessionCone_trivial
    (hA : A.IsConvexProcess 𝕜)
    (hA_closed : A.IsClosed)
    {C : Set U} (hC_closed : _root_.IsClosed C) (hC_convex : Convex 𝕜 C)
    (hkernel :
      0⁺[𝕜]C ∩ (A⁻¹)[[0]] ⊆ ({0} : Set U)) :
    _root_.IsClosed (A.image C) := by
  set S : Set (U × X) := (A : Set (U × X)) ∩ (C ×ˢ (Set.univ : Set X))
  have hS_closed : _root_.IsClosed S := by
    simpa [S] using hA_closed.inter (hC_closed.prod isClosed_univ)
  have hS_convex : Convex 𝕜 S := by
    simpa [S] using hA.convex.inter (hC_convex.prod convex_univ)
  have hsnd_image : LinearMap.snd 𝕜 U X '' S = A.image C := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.2.1, hp.1⟩
    · rintro ⟨u, huC, huA⟩
      exact ⟨(u, x), ⟨huA, huC, by simp⟩, rfl⟩
  by_cases hS_nonempty : S.Nonempty
  · have hkernel' :
        0⁺[𝕜] S ∩ (LinearMap.snd 𝕜 U X).ker ⊆ ({0} : Set (U × X)) := by
      rcases hS_nonempty with ⟨p, hp⟩
      intro z hz
      have hzker : z ∈ (LinearMap.snd 𝕜 U X).ker := hz.2
      have hz2 : z.2 = 0 := by
        simpa using hzker
      have hzC : z.1 ∈ 0⁺[𝕜] C := by
        refine hC_convex.mem_recessionCone_of_nonneg_ray (x := p.1) hC_closed ?_
        intro a ha
        have hpa : p + a • z ∈ S := (Set.mem_recessionCone_iff.mp hz.1) p hp a ha
        simpa using hpa.2.1
      have hzA_recession : z ∈ 0⁺[𝕜] (A : Set (U × X)) := by
        refine hA.convex.mem_recessionCone_of_nonneg_ray (x := p) hA_closed ?_
        intro a ha
        exact ((Set.mem_recessionCone_iff.mp hz.1) p hp a ha).1
      have hzA : z ∈ (A : Set (U × X)) := by
        simpa using
          (Set.mem_recessionCone_iff.mp hzA_recession) (0 : U × X) hA.zero_mem 1 zero_le_one
      have hz_inv_image_zero : z.1 ∈ (A⁻¹)[[0]] := by
        have hz_eq : z = ((z.1, 0) : U × X) := by
          ext <;> simp [hz2]
        have hzA0 : ((z.1, 0) : U × X) ∈ A := by
          rw [← hz_eq]
          exact hzA
        have hzA0' : z.1 ~[A] (0 : X) := by
          simpa using hzA0
        simpa using hzA0'
      have hz1 : z.1 = 0 := by
        have hz1_mem_zero : z.1 ∈ ({0} : Set U) := hkernel ⟨hzC, hz_inv_image_zero⟩
        simpa using hz1_mem_zero
      have hz_eq_zero : z = 0 := by
        ext <;> simp [hz1, hz2]
      simp [hz_eq_zero]
    have hsnd_closed_of_kernel_trivial :
        ∀ {T : Set (U × X)}, Convex 𝕜 T → _root_.IsClosed T →
          (0⁺[𝕜] T ∩ (LinearMap.snd 𝕜 U X).ker ⊆ ({0} : Set (U × X))) →
          _root_.IsClosed (LinearMap.snd 𝕜 U X '' T) :=
      LinearMap.isClosed_image_of_recessionKernelTrivial (A := LinearMap.snd 𝕜 U X)
    have hsnd_closed : _root_.IsClosed (LinearMap.snd 𝕜 U X '' S) :=
      hsnd_closed_of_kernel_trivial hS_convex hS_closed hkernel'
    rw [hsnd_image] at hsnd_closed
    exact hsnd_closed
  · rw [← hsnd_image, Set.not_nonempty_iff_eq_empty.mp hS_nonempty]
    simp

/-- Corollary 39.7.1, stronger-hypothesis owner form:
if `C` is closed and convex and its recession cone is trivial, then for every closed convex process
`A`, the image `A.image C` is closed. This is the scalar-generic replacement for the textbook's
bounded-set specialization. -/
theorem isClosed_image_of_isClosed_of_recessionCone_trivial
    (hA : A.IsConvexProcess 𝕜)
    (hA_closed : A.IsClosed)
    {C : Set U} (hC_closed : _root_.IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_recession_trivial : 0⁺[𝕜]C ⊆ ({0} : Set U)) :
    _root_.IsClosed (A.image C) := by
  refine
    hA.isClosed_image_of_isClosed_of_inv_image_zero_recessionCone_trivial
      hA_closed hC_closed hC_convex ?_
  intro u hu
  exact hC_recession_trivial hu.1

end SetRel.IsConvexProcess

end
