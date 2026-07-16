import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_18
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 (E × F)]

open AffineSubspace Submodule

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.8 studies the relative interior of a convex subset of
  a product space `E × F` in terms of its vertical fibers over `E`.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicInterior 𝕜`, the product-space
  projection `Prod.fst`, and affine sections of `C` by the canonical preimages `Prod.mk y ⁻¹' C`.
- `bridge/view`: Rockafellar's `C_y` is represented by `Prod.mk y ⁻¹' C`, and the set
  `D = {y | C_y ≠ ∅}` is represented canonically by the projection image `Prod.fst '' C`.
- Domain-style sampling used here: `intrinsicInterior_linear_image` from Theorem 6.6,
  `AffineSubspace.intrinsicInterior_inter_eq` from Corollary 6.5.1,
  `ri_prod_eq` from Text 6.18, and mathlib's core definition
  `intrinsicInterior`.
- Primitive data vs derived API: the primitive owner data is only `hC : Convex 𝕜 C`; the
  projected domain and the fibers are derived canonical set expressions and should not remain as
  separate public wrapper definitions.
- Best owner abstraction: there is no earlier chapter or mathlib owner theorem for this exact
  base-fiber decomposition, so this file keeps the source-facing theorem itself on the existing
  `Convex` owner surface rather than introducing a section/projection package.
- Layer target: the main theorem is source-facing, stated directly as owner-style `Convex` API in
  terms of the canonical projection image and fiber preimages.
  the public theorem is stated at the canonical level of a finite-dimensional product ambient
  space over the underlying ordered complete normed field `𝕜`.
-/

namespace Convex

/-- Theorem 6.8: a point `(y, z)` lies in the relative interior of a convex set `C ⊆ E × F`
if and only if `y` lies in the relative interior of the projection domain `D = {y | C_y ≠ ∅}`
and `z` lies in the relative interior of the fiber `C_y`. Specializing to Euclidean spaces
recovers the textbook `R^m × R^p` statement. -/
-- Proof sketch: apply Theorem 6.6 to the projection `Prod.fst` to identify the base coordinates
-- of `ri C` with `ri (Prod.fst '' C)`. For a fixed `y ∈ ri (Prod.fst '' C)`, intersect `C`
-- with the affine fiber
-- `{(y, z) | z ∈ F}` and use Corollary 6.5.1 to identify the relative interior of that section
-- with the fiberwise relative interior `ri (Prod.mk y ⁻¹' C)`.
theorem mem_ri_iff_mem_ri_base_and_fiber
    {C : Set (E × F)} (hC : Convex 𝕜 C) {y : E} {z : F} :
    (y, z) ∈ ri[𝕜](C) ↔ y ∈ ri[𝕜](Prod.fst '' C) ∧ z ∈ ri[𝕜](Prod.mk y ⁻¹' C) := by
  let M : AffineSubspace 𝕜 (E × F) :=
    AffineSubspace.mk' (y, (0 : F)) (Submodule.prod (⊥ : Submodule 𝕜 E) ⊤)
  have hM : (M : Set (E × F)) = ({y} : Set E) ×ˢ (Set.univ : Set F) := by
    ext p
    simp [M, mem_mk', mem_prod, sub_eq_zero]
  have hMC : (M : Set (E × F)) ∩ C = ({y} : Set E) ×ˢ (Prod.mk y ⁻¹' C) := by
    ext p
    rcases p with ⟨a, b⟩
    constructor
    · rintro ⟨hpM, hpC⟩
      rw [hM] at hpM
      have ha : a = y := by simpa using hpM.1
      subst ha
      simpa using hpC
    · rintro ⟨ha, hpC⟩
      subst ha
      rw [hM]
      exact ⟨⟨by simp, by simp⟩, hpC⟩
  have himage : ri[𝕜](Prod.fst '' C) = Prod.fst '' ri[𝕜](C) := by
    simpa [LinearMap.fst] using hC.intrinsicInterior_linear_image (LinearMap.fst 𝕜 E F)
  have hsection (hy : y ∈ ri[𝕜](Prod.fst '' C)) :
      ri[𝕜]((M : Set (E × F)) ∩ C) = (M : Set (E × F)) ∩ ri[𝕜](C) := by
    have hMri : ((M : Set (E × F)) ∩ ri[𝕜](C)).Nonempty := by
      rw [himage] at hy
      rcases hy with ⟨p, hp, hp1⟩
      refine ⟨p, ?_, hp⟩
      rw [hM]
      exact ⟨hp1, by simp⟩
    exact M.intrinsicInterior_inter_eq hC hMri
  constructor
  · intro hyz
    have hy : y ∈ ri[𝕜](Prod.fst '' C) := by
      rw [himage]
      exact ⟨(y, z), hyz, rfl⟩
    have hyz_section : (y, z) ∈ ri[𝕜]((M : Set (E × F)) ∩ C) := by
      rw [hsection hy]
      exact ⟨by simp [hM], hyz⟩
    have hz : z ∈ ri[𝕜](Prod.mk y ⁻¹' C) := by
      rw [hMC, ri_prod_eq, intrinsicInterior_singleton] at hyz_section
      simpa using hyz_section.2
    exact ⟨hy, hz⟩
  · rintro ⟨hy, hz⟩
    have hyz_section : (y, z) ∈ ri[𝕜]((M : Set (E × F)) ∩ C) := by
      rw [hMC, ri_prod_eq, intrinsicInterior_singleton]
      exact ⟨by simp, hz⟩
    have hyz_mem : (y, z) ∈ (M : Set (E × F)) ∩ ri[𝕜](C) := by
      rw [← hsection hy]
      exact hyz_section
    exact hyz_mem.2

end Convex

end
