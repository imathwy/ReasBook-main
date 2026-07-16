import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}
variable
  (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)

/- Semantic recall / owner check:
- `lean_leansearch` recalled the affine-open criterion
  `AlgebraicGeometry.affineLocally_iff_forall_isAffineOpen` and the target-local cover API
  around `Scheme.OpenCover.pullback₁` / `pullbackHom`;
- `Chap29/Definition_29_14_2.lean` and `Chap29/Lemma_29_14_3.lean` already fix the source-facing
  owner as `LocallyOfType P f`, so this file records the remaining equivalent cover formulations
  and the restriction stability statement over that owner.
-/

/-- Lemma 29.14.4 (1): for a local property `P` of ring maps, a morphism `f : X ⟶ S` is locally
of type `P` if and only if for every affine opens `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, the
induced ring map `Γ(S, V) → Γ(X, U)` has property `P`. -/
@[stacks 01SU]
theorem locallyOfType_iff_forall_affineOpen_appLE
    (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔
      ∀ {V : S.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          P (f.appLE V U e).hom := by
  rw [locallyOfType_iff_affineLocally P f hP, affineLocally_iff_forall_isAffineOpen]

/-- Lemma 29.14.4 (2): for a local property `P` of ring maps, `f : X ⟶ S` is locally of type `P`
if and only if there is an open cover `𝒱` of `S` such that each pullback piece of `f` over a
member of `𝒱` admits an open cover by morphisms that are locally of type `P`. -/
@[stacks 01SU]
theorem locallyOfType_iff_exists_openCover
    (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔
      ∃ 𝒱 : S.OpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀, LocallyOfType P (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- Lemma 29.14.4 (3): for a local property `P` of ring maps, `f : X ⟶ S` is locally of type `P`
if and only if there is an affine open cover `𝒱` of `S` such that each pullback piece of `f` over
`𝒱` admits an affine open cover whose induced maps on global sections satisfy `P`. -/
@[stacks 01SU]
theorem locallyOfType_iff_exists_affineOpenCover
    (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔
      ∃ 𝒱 : S.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              P ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom := sorry

/-- Lemma 29.14.4 (4): if `f : X ⟶ S` is locally of type `P`, then for any open subschemes
`U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is still locally of type
`P`. -/
@[stacks 01SU]
theorem locallyOfType_resLE
    (hP : RingHom.PropertyIsLocal P)
    (hf : LocallyOfType P f) {V : S.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfType P (f.resLE V U e) := sorry

end AlgebraicGeometry
