import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar
variable {𝕜 E : Type*}

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.1 states that if `x` lies in the relative interior of a convex set
  `C` in a finite-dimensional normed space and `y` lies in `closure C`, then the segment from `x`
  toward `y` stays in the relative interior up to but excluding the endpoint at `y`.
- `core/canonical`: mathlib's owner notions are `Convex 𝕜`, `closure`, and
  `intrinsicInterior 𝕜`, written on the chapter theorem surface as `ri[𝕜](C)`, together with the
  finite-dimensional bridge
  `intrinsicClosure_eq_closure 𝕜`.
- `bridge/view`: Rockafellar's relative interior is represented canonically by `ri[𝕜](C)`, while
  the stronger intrinsic-closure statement is only internal proof infrastructure for transporting
  the ordinary interior theorem on the affine-span model back to `C`; it should not remain on the
  public theorem surface.
- Domain-style sampling used here: the chapter notation owner `ri[𝕜](C)` from `Text_6_8`,
  `mem_intrinsicInterior`, `mem_intrinsicClosure`,
  `Convex.openSegment_interior_closure_subset_interior`, and `intrinsicClosure_eq_closure`.
- Primitive data vs derived API: the primitive owner data is the convex set `C` together with
  `hC : Convex 𝕜 C`; the public open-segment inclusion for `closure C` is derived API on that
  owner, and the intrinsic-closure variant is a private bridge rather than part of the public
  surface.
- Layer target: this item stays `source-facing`, expressed in the canonical `intrinsicInterior`
  language under the `Convex` owner namespace, with the chapter notation `ri[𝕜](C)` used on the
  source-facing theorem surface and only the closure statement exposed publicly.
-/

namespace Convex

open AffineMap

section IntrinsicClosure

variable [Field 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-- Owner-level intrinsic-closure form behind Theorem 6.1: if `x ∈ ri[𝕜](C)` and
`y ∈ intrinsicClosure 𝕜 C`, then the open segment from `x` to `y` stays in `ri[𝕜](C)`. The
ambient-closure statement is the finite-dimensional bridge corollary below. -/
theorem openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior {C : Set E}
    (hC : Convex 𝕜 C)
    {x y : E} (hx : x ∈ ri[𝕜](C))
    (hy : y ∈ intrinsicClosure 𝕜 C) :
    openSegment 𝕜 x y ⊆ ri[𝕜](C) := by
  rcases (mem_intrinsicInterior).1 hx with ⟨xA, hxA, rfl⟩
  rcases (mem_intrinsicClosure).1 hy with ⟨yA, hyA, rfl⟩
  letI : Nonempty ↥(affineSpan 𝕜 C) := ⟨xA⟩
  let e : (affineSpan 𝕜 C).direction ≃ᵃ[𝕜] affineSpan 𝕜 C := AffineEquiv.vaddConst 𝕜 xA
  let h : (affineSpan 𝕜 C).direction ≃ₜ affineSpan 𝕜 C := Homeomorph.vaddConst xA
  let A : (affineSpan 𝕜 C).direction →ᵃ[𝕜] E := (affineSpan 𝕜 C).subtype.comp e.toAffineMap
  let s : Set (affineSpan 𝕜 C) := ((↑) : affineSpan 𝕜 C → E) ⁻¹' C
  let t : Set (affineSpan 𝕜 C).direction := e ⁻¹' s
  let y0 : (affineSpan 𝕜 C).direction := e.symm yA
  letI : ContinuousConstSMul 𝕜 (affineSpan 𝕜 C).direction :=
    { continuous_const_smul := fun c ↦ by
        rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
        simpa using (continuous_subtype_val.const_smul c) }
  have ht : Convex 𝕜 t := by
    simpa [A, s, t, e] using hC.affine_preimage A
  have hts : e '' t = s := by
    change e '' (e ⁻¹' s) = s
    exact Set.image_preimage_eq_of_subset fun u hu ↦ ⟨e.symm u, by simp⟩
  have hinter : e '' interior t = interior s := by
    calc
      e '' interior t = h '' interior t := by rfl
      _ = interior (h '' t) := by simpa using h.image_interior t
      _ = interior s := by simpa [e, h] using congrArg interior hts
  have hx0 : (0 : (affineSpan 𝕜 C).direction) ∈ interior t := by
    have hx0' : (0 : (affineSpan 𝕜 C).direction) ∈ h ⁻¹' interior s := by
      simpa [h, s] using hxA
    rw [h.preimage_interior] at hx0'
    simpa [t, e, h] using hx0'
  have hy0 : y0 ∈ closure t := by
    have hy0' : y0 ∈ h ⁻¹' closure s := by
      simpa [y0, h, e, s] using hyA
    rw [h.preimage_closure] at hy0'
    simpa [t, e, h] using hy0'
  have hseg : openSegment 𝕜 (0 : (affineSpan 𝕜 C).direction) y0 ⊆ interior t :=
    ht.openSegment_interior_closure_subset_interior hx0 hy0
  have hA : A '' interior t = ri[𝕜](C) := by
    calc
      A '' interior t = ((↑) '' (e '' interior t)) := by
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact ⟨e u, ⟨u, hu, rfl⟩, rfl⟩
        · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
          exact ⟨u, hu, rfl⟩
      _ = ri[𝕜](C) := by
        rw [hinter, _root_.intrinsicInterior]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  have hz0 : lineMap (0 : (affineSpan 𝕜 C).direction) y0 b ∈ interior t := by
    apply hseg
    exact ⟨a, b, ha, hb, hab, by simp [lineMap_apply_module]⟩
  rw [← hA]
  refine ⟨lineMap (0 : (affineSpan 𝕜 C).direction) y0 b, hz0, ?_⟩
  have hab' : 1 - b = a := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm] using hab.symm
  calc
    A (lineMap (0 : (affineSpan 𝕜 C).direction) y0 b) = lineMap (xA : E) (yA : E) b := by
          simp [A, y0, e]
    _ = a • (xA : E) + b • (yA : E) := by
          simp [lineMap_apply_module, hab']

end IntrinsicClosure

section Closure

variable [NontriviallyNormedField 𝕜] [PartialOrder 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Theorem 6.1: if `x` lies in the relative interior `ri[𝕜](C)` of a convex set `C`, and `y`
lies in `closure C`, then the open segment from `x` to `y` is contained in `ri[𝕜](C)`. The
source states this in `ℝ^n`; this is the finite-dimensional
corollary obtained from the intrinsic-closure version via `intrinsicClosure_eq_closure 𝕜 C`. -/
theorem openSegment_intrinsicInterior_closure_subset_intrinsicInterior {C : Set E}
    (hC : Convex 𝕜 C) {x y : E} (hx : x ∈ ri[𝕜](C)) (hy : y ∈ closure C) :
    openSegment 𝕜 x y ⊆ ri[𝕜](C) := by
  have hy' : y ∈ intrinsicClosure 𝕜 C := by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using hy
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hC hx hy'

end Closure

end Convex

end
