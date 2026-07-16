import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/- Semantic recall / source-core-bridge check:
- mathlib's canonical owner is `AlgebraicGeometry.Etale`, with direct recall items `etale_iff`
  and the restriction instance on `f.resLE V U e`;
- the chapter-local bridge owner for affine-local ring-map properties is
  `LocallyOfType RingHom.Etale`, linked to `Etale` by `RingHom.Etale.propertyIsLocal` and
  `locallyOfType_iff_affineLocally`;
- `Lemma_29_14_4.lean` already provides the reusable open-cover and affine-open-cover
  formulations for `LocallyOfType`, so the source-facing cover clauses here should specialize that
  existing API rather than restating it independently.
-/

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Bridge `Etale` to the Chapter 29 affine-local owner specialized to `RingHom.Etale`. -/
theorem etale_iff_locallyOfType :
    Etale f ↔ LocallyOfType RingHom.Etale f := by
  rw [locallyOfType_iff_affineLocally RingHom.Etale f RingHom.Etale.propertyIsLocal]
  rw [etale_iff, affineLocally_iff_forall_isAffineOpen]

/- Lemma 29.36.2 (1): this affine-open criterion is exactly the canonical owner theorem
`AlgebraicGeometry.etale_iff`. -/
recall AlgebraicGeometry.etale_iff
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Etale ((f.appLE V U e).hom)

/-- Lemma 29.36.2 (2): a morphism of schemes is étale if and only if the target admits an open
cover such that each pullback piece over a member of that cover admits an open cover by schemes
étale over that member. -/
@[stacks 02GJ]
theorem etale_iff_exists_openCover :
    Etale f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Etale (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  simpa [etale_iff_locallyOfType] using
    (locallyOfType_iff_exists_openCover RingHom.Etale RingHom.Etale.propertyIsLocal)

/-- Lemma 29.36.2 (3): a morphism of schemes is étale if and only if the target admits an affine
open cover such that each pullback piece over a member of that cover admits an affine open cover on
which the induced map on global sections is étale. -/
@[stacks 02GJ]
theorem etale_iff_exists_affineOpenCover :
    Etale f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Etale (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  simpa [etale_iff_locallyOfType] using
    (locallyOfType_iff_exists_affineOpenCover RingHom.Etale RingHom.Etale.propertyIsLocal)

/- Lemma 29.36.2 (4): restriction to open subschemes is already the canonical instance on
`f.resLE V U e`. -/
variable [Etale f]
variable {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V)

#check
  (inferInstance :
    Etale (f.resLE V U e))

end

end Scheme.Hom

end AlgebraicGeometry
