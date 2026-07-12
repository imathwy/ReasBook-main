import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap29.Lemma_29_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/- Semantic recall / source-core-bridge check:
- mathlib's canonical owner is `AlgebraicGeometry.Smooth`, with direct recall item `smooth_iff`
  and the restriction instance on `f.resLE V U e`;
- the chapter-local bridge owner for affine-local ring-map properties is
  `LocallyOfType RingHom.Smooth`, linked to `Smooth` by `RingHom.Smooth.propertyIsLocal` and
  `locallyOfType_iff_affineLocally`;
- `Lemma_29_14_4.lean` already provides the reusable open-cover and affine-open-cover
  formulations for `LocallyOfType`, so the source-facing cover clauses here should specialize that
  existing API rather than restating it independently.
-/

/-- Lemma 29.34.2 (1): a morphism of schemes is smooth if and only if for every affine open
`U ⊆ X` and affine open `V ⊆ S` with `f(U) ⊆ V`, the induced ring map on sections
`\Gamma(V, \mathcal O_S) → \Gamma(U, \mathcal O_X)` is smooth. -/
@[stacks 01V6]
theorem smooth_iff_affineOpen_appLE_smooth
    (f : X ⟶ S) :
    Smooth f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Smooth ((f.appLE V U e).hom) := by
  constructor
  · intro hf U hU V hV e
    exact (smooth_iff f).1 hf hV hU e
  · intro hf
    exact (smooth_iff f).2 <| fun {_} hV {_} hU e ↦ hf hU hV e

private theorem smooth_iff_locallyOfType (f : X ⟶ S) :
    Smooth f ↔ LocallyOfType RingHom.Smooth f := by
  rw [locallyOfType_iff_affineLocally RingHom.Smooth f RingHom.Smooth.propertyIsLocal]
  rw [smooth_iff, affineLocally_iff_forall_isAffineOpen]

/-- Lemma 29.34.2 (2): a morphism of schemes is smooth if and only if there is an open cover of
the base and open covers of the corresponding preimages such that each restricted morphism is
smooth. -/
@[stacks 01V6]
theorem smooth_iff_exists_openCover
    (f : X ⟶ S) :
    Smooth f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Smooth (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  simpa [smooth_iff_locallyOfType] using
    (locallyOfType_iff_exists_openCover RingHom.Smooth RingHom.Smooth.propertyIsLocal)

/-- Lemma 29.34.2 (3): a morphism of schemes is smooth if and only if there are affine open covers
`V_j` of `S` and `U_i` of each `f^{-1}(V_j)` such that the induced ring maps on sections are
smooth. -/
@[stacks 01V6]
theorem smooth_iff_exists_affineOpenCover
    (f : X ⟶ S) :
    Smooth f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Smooth (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  simpa [smooth_iff_locallyOfType] using
    (locallyOfType_iff_exists_affineOpenCover
      RingHom.Smooth RingHom.Smooth.propertyIsLocal)

/- Lemma 29.34.2 (4): restriction to open subschemes is already the canonical instance on
`f.resLE V U e`. -/
recall AlgebraicGeometry.instSmoothResLE
    {f : X ⟶ S} {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V) [Smooth f] :
    Smooth (f.resLE V U e)

end Scheme.Hom

end

end AlgebraicGeometry
