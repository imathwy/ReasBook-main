import StacksProject_2024.Chap07.Lemma_7_41_1.Basic

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Helper for Lemma 7.41.1: the pullback of `(f _*).map φ` along the adjunction unit. -/
private noncomputable abbrev unit_pullback_cover
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) : Sheaf J (Type w) :=
  pullback ((f _*).map φ) ((f.adjunction.unit).app 𝒢)

/-- Helper for Lemma 7.41.1: the canonical projection from the unit pullback cover. -/
private noncomputable abbrev unit_pullback_cover_projection
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) :
    unit_pullback_cover (f := f) φ ⟶ 𝒢 :=
  pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)

/-- Helper for Lemma 7.41.1: the inverse-image morphism from the unit pullback cover to `ℱ`. -/
private noncomputable abbrev inverseImage_unit_pullback_cover_lift
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢)
    [PreservesFiniteLimits (f⁻¹)] :
    (f⁻¹).obj (unit_pullback_cover (f := f) φ) ⟶ ℱ :=
  (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
    pullback.fst ((f⁻¹).map ((f _*).map φ)) ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
      (f.adjunction.counit).app ℱ

/-- Helper for Lemma 7.41.1: the canonical map from the inverse image of the pullback cover
factors through the pulled-back surjection. -/
private theorem inverseImage_pullback_cover_factorization
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢)
    [PreservesFiniteLimits (f⁻¹)] :
    inverseImage_unit_pullback_cover_lift (f := f) φ ≫ φ =
      (f⁻¹).map (unit_pullback_cover_projection (f := f) φ) := by
  -- Flatten the transport-heavy composite into directed rewrites.
  dsimp [inverseImage_unit_pullback_cover_lift, unit_pullback_cover_projection]
  have hCounit :
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f.adjunction.counit).app ℱ ≫ φ
        =
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f _*).map φ) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
    -- Rewrite the final leg using counit naturality at `φ`.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
            k)
        (f.adjunction.counit_naturality φ).symm
  have hPullback :
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.fst ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f _*).map φ) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢)
        =
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.snd ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f.adjunction.unit).app 𝒢) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
    -- The pullback relation swaps the first leg for the second.
    rw [pullback.condition_assoc]
    rfl
  have hTriangle :
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
            pullback.snd ((f⁻¹).map ((f _*).map φ))
              ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
          (f⁻¹).map ((f.adjunction.unit).app 𝒢) ≫
            (f.adjunction.counit).app ((f⁻¹).obj 𝒢)
        =
      (f⁻¹).map (pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)) := by
    -- Identify the preserved-pullback projection with the mapped projection downstairs, then
    -- contract the unit-counit zig-zag by the triangle identity.
    rw [PreservesPullback.iso_hom_snd_assoc]
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (f⁻¹).map (pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)) ≫
            k)
        (f.adjunction.right_triangle_components 𝒢)
  exact hCounit.trans (hPullback.trans hTriangle)

/-- Helper for Lemma 7.41.1: if `f_*` maps locally surjective morphisms to locally surjective
morphisms, then covers of inverse images lift after a locally surjective cover upstairs. -/
private theorem pullback_cover_lift_data
    (h₄ : ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ))
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢)
    (hφ : Sheaf.IsLocallySurjective φ) :
    ∃ (𝒢' : Sheaf J (Type w)) (π : 𝒢' ⟶ 𝒢),
      Sheaf.IsLocallySurjective π ∧
        ∃ ι : (f⁻¹).obj 𝒢' ⟶ ℱ,
          ι ≫ φ = (f⁻¹).map π := by
  let ψ : (f _*).obj ℱ ⟶ (f _*).obj ((f⁻¹).obj 𝒢) := (f _*).map φ
  let 𝒢' : Sheaf J (Type w) := unit_pullback_cover (f := f) φ
  let π : 𝒢' ⟶ 𝒢 := unit_pullback_cover_projection (f := f) φ
  have hψ : Sheaf.IsLocallySurjective ψ := h₄ φ hφ
  letI : PreservesFiniteLimits (f⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits f
  have hπ : Sheaf.IsLocallySurjective π := by
    -- Pull back the mapped cover along the unit to build the lifted cover of `𝒢`.
    change Sheaf.IsLocallySurjective (pullback.snd ψ ((f.adjunction.unit).app 𝒢))
    simpa [ψ, unit_pullback_cover, unit_pullback_cover_projection] using
      sheaf_pullback_snd_isLocallySurjective
        (J := J) ψ ((f.adjunction.unit).app 𝒢) hψ
  let ι : (f⁻¹).obj 𝒢' ⟶ ℱ := inverseImage_unit_pullback_cover_lift (f := f) φ
  refine ⟨𝒢', π, hπ, ι, ?_⟩
  -- Route correction: reuse the cached preserved-pullback rewrite lemma instead of replaying the
  -- transport-heavy calculation inline.
  simpa [𝒢', π, ι] using
    inverseImage_pullback_cover_factorization (f := f) (φ := φ)

/-- Helper for Lemma 7.41.1: if `f_*` maps locally surjective morphisms to locally surjective
morphisms, then covers of inverse images lift after a locally surjective cover upstairs. -/
theorem pushforwardMapsLocallySurjective_implies_surjectionLiftingAlongInverseImage
    (h₄ : ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ)) :
    f.surjectionLiftingAlongInverseImage := by
  intro ℱ 𝒢 φ hφ
  -- Use the unit pullback construction to build the lifted cover in the target topos.
  exact pullback_cover_lift_data (f := f) h₄ φ hφ

end

end MorphismOfTopoiIn

end CategoryTheory
