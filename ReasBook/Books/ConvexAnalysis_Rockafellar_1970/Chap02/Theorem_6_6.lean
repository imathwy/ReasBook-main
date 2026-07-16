import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

open AffineSubspace Submodule
open scoped Rockafellar

section RelativeInterior

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 6.6 (1) states how relative interiors behave under a linear
  transformation of a convex subset of a finite-dimensional normed space over `𝕜` into a normed
  space over the same scalar field.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, `intrinsicInterior 𝕜` (surface notation
  `ri[𝕜](·)`), `closure`,
  the set image `A '' C` of a `LinearMap`, and the general continuity theorem
  `image_closure_subset_closure_image`.
- `bridge/view`: Rockafellar's `ri C` is represented by the canonical chapter notation
  `ri[𝕜](C)`, and the
  textbook notation `AC` is represented by the set image `A '' C`.
- Domain-style sampling used here: `Convex.linear_image`,
  `LinearMap.finiteDimensional_range`, `LinearMap.surjective_rangeRestrict`,
  `AffineIsometry.image_intrinsicInterior`, and
  `image_closure_subset_closure_image`.
- Primitive data vs derived API: the primitive owner data is `hC : Convex 𝕜 C`; the
  relative-interior identity is derived API on that owner. By contrast, the closure inclusion is
  already owned upstream by `image_closure_subset_closure_image`, so keeping a second local theorem
  would be duplicate wheel.
- Redundant-assumption cleanup: the codomain `F` need not be finite-dimensional; only the source
  space `E` needs the finite-dimensional hypothesis to support the chapter's relative-interior
  machinery and continuity of linear maps out of `E`.
- Layer target: clause (1) remains `source-facing` but is expressed as owner-style `Convex` API;
  clause (2) is a direct `core/canonical` recall.
-/

namespace Convex

/-- Theorem 6.6 (1): for a convex set `C` in a finite-dimensional normed space over `𝕜` and a
linear map `A` into a normed space over the same scalar field, the relative interior of the image
`A '' C` is exactly the image of the relative interior of `C`. -/
-- Proof sketch: factor `A` through its finite-dimensional range `LinearMap.range A`. The induced
-- map `E → LinearMap.range A` has the same set image as `A`, while the subtype
-- `LinearMap.range A → F` is an affine isometry, so `AffineIsometry.image_intrinsicInterior`
-- transfers relative interiors between the range and the ambient codomain. This reduces the
-- statement to the finite-dimensional codomain case, where `A '' intrinsicInterior 𝕜 C` and
-- `A '' C` have the same closure by `Convex.closure_intrinsicInterior_eq_closure` together with
-- `image_closure_subset_closure_image`, and the relative-interior identity follows inside the
-- finite-dimensional range model.
@[simp] theorem intrinsicInterior_linear_image {C : Set E} (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F) :
    ri[𝕜](A '' C) = A '' ri[𝕜](C) := by
  let A' := A.rangeRestrict
  have himage_subset :
      A' '' ri[𝕜](C) ⊆ ri[𝕜](A' '' C) := by
    let S : AffineSubspace 𝕜 E := affineSpan 𝕜 C
    let T : AffineSubspace 𝕜 A.range := affineSpan 𝕜 (A' '' C)
    have hmap : S.map A'.toAffineMap = T := by
      simpa [S, T] using AffineSubspace.map_span A'.toAffineMap C
    rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨xS, hxS, rfl⟩
    haveI : Nonempty S := ⟨xS⟩
    haveI : Nonempty T := by
      rw [← hmap]
      infer_instance
    let φ : S →ᵃ[𝕜] T := A'.toAffineMap.restrict (by
      simp [hmap])
    have hφ_surj : Function.Surjective φ := by
      simpa [φ] using AffineMap.restrict.surjective A'.toAffineMap hmap
    have hφlin_surj : Function.Surjective φ.linear :=
      (AffineMap.linear_surjective_iff φ).2 hφ_surj
    have hφ_open : IsOpenMap φ :=
      (AffineMap.isOpenMap_linear_iff).1
        (LinearMap.isOpenMap_of_finiteDimensional φ.linear hφlin_surj)
    have hφ_image :
        φ '' (((↑) : S → E) ⁻¹' C) = ((↑) : T → A.range) ⁻¹' (A' '' C) := by
      ext z
      constructor
      · rintro ⟨w, hwC, rfl⟩
        exact ⟨(w : E), hwC, by simp [φ, AffineMap.restrict.coe_apply]⟩
      · rintro ⟨w, hwC, hwz⟩
        refine ⟨⟨w, subset_affineSpan 𝕜 C hwC⟩, hwC, ?_⟩
        apply Subtype.ext
        simpa [φ, AffineMap.restrict.coe_apply] using hwz
    refine ⟨φ xS, ?_, by simp [φ, AffineMap.restrict.coe_apply]⟩
    have hφ_mem :
        φ xS ∈ interior (φ '' (((↑) : S → E) ⁻¹' C : Set S)) :=
      hφ_open.image_interior_subset (((↑) : S → E) ⁻¹' C) ⟨xS, hxS, rfl⟩
    simpa [intrinsicInterior, T, hφ_image] using hφ_mem
  have hclosure :
      closure (A' '' C) = closure (A' '' ri[𝕜](C)) := by
    apply subset_antisymm
    · refine closure_minimal ?_ isClosed_closure
      rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ closure (ri[𝕜](C)) := by
        simpa [hC.closure_intrinsicInterior_eq_closure] using (subset_closure hx : x ∈ closure C)
      exact image_closure_subset_closure_image (LinearMap.continuous_of_finiteDimensional A')
        ⟨x, hx', rfl⟩
    · exact closure_mono (Set.image_mono intrinsicInterior_subset)
  have h_image_convex : Convex 𝕜 (A' '' ri[𝕜](C)) :=
    (hC.intrinsicInterior).linear_image A'
  have hri :
      ri[𝕜](A' '' C) = ri[𝕜](A' '' ri[𝕜](C)) := by
    calc
      ri[𝕜](A' '' C) = ri[𝕜](closure (A' '' C)) := by
        simpa using (hC.linear_image A').intrinsicInterior_closure_eq_intrinsicInterior.symm
      _ = ri[𝕜](closure (A' '' ri[𝕜](C))) := by
        simp [hclosure]
      _ = ri[𝕜](A' '' ri[𝕜](C)) := by
        simpa using h_image_convex.intrinsicInterior_closure_eq_intrinsicInterior
  have hself :
      ri[𝕜](A' '' ri[𝕜](C)) = A' '' ri[𝕜](C) := by
    apply subset_antisymm intrinsicInterior_subset
    intro y hy
    have : y ∈ ri[𝕜](A' '' C) := himage_subset hy
    rw [hri] at this
    exact this
  letI : NormedAddTorsor A.range A.range := SeminormedAddCommGroup.toNormedAddTorsor
  let ι : A.range →ᵃⁱ[𝕜] F := (subtypeₗᵢ A.range).toAffineIsometry
  have himage_eq (s : Set E) : ι '' (A' '' s) = A '' s := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A' x, ⟨x, hx, rfl⟩, rfl⟩
  calc
    ri[𝕜](A '' C) = ri[𝕜](ι '' (A' '' C)) := by
      rw [himage_eq C]
    _ = ι '' ri[𝕜](A' '' C) := by
      exact ι.image_intrinsicInterior (A' '' C)
    _ = ι '' (A' '' ri[𝕜](C)) := by
      simp [hri, hself]
    _ = A '' ri[𝕜](C) := himage_eq (ri[𝕜](C))

end Convex

end RelativeInterior

section ClosureImage

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- Theorem 6.6 (2): for any set `C` in a finite-dimensional normed space over `𝕜` and linear map
`A : E →ₗ[𝕜] F`, the image of the closure of `C` is contained in the closure of `A '' C`.
Equivalently, `cl (A C) ⊇ A (cl C)`. This is the canonical owner theorem
`image_closure_subset_closure_image`, with continuity of `A` supplied automatically by
finite-dimensionality of the source through `LinearMap.continuous_of_finiteDimensional`. -/
recall image_closure_subset_closure_image

end ClosureImage

end
