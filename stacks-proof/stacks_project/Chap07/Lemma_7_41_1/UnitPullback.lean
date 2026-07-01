import stacks_project.Chap07.Lemma_7_41_1.Basic

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
private abbrev unit_pullback_cover
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) : Sheaf J (Type w) :=
  pullback ((f _*).map φ) ((f.adjunction.unit).app 𝒢)

/-- Helper for Lemma 7.41.1: the canonical projection from the unit pullback cover. -/
private abbrev unit_pullback_cover_projection
    {ℱ : Sheaf K (Type w)} {𝒢 : Sheaf J (Type w)}
    (φ : ℱ ⟶ (f⁻¹).obj 𝒢) :
    unit_pullback_cover (f := f) φ ⟶ 𝒢 :=
  pullback.snd ((f _*).map φ) ((f.adjunction.unit).app 𝒢)

/-- Helper for Lemma 7.41.1: the inverse-image morphism from the unit pullback cover to `ℱ`. -/
private abbrev inverseImage_unit_pullback_cover_lift
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
  -- Compare the two routes through the preserved pullback and then contract the triangle.
  calc
    inverseImage_unit_pullback_cover_lift (f := f) φ ≫ φ
        =
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
          pullback.fst ((f⁻¹).map ((f _*).map φ))
            ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
        (f⁻¹).map ((f _*).map φ) ≫
          (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
          -- Rewrite the counit leg using naturality at `φ`.
          rw [← Category.assoc]
          rw [f.adjunction.counit_naturality_assoc]
    _ =
      (PreservesPullback.iso (f⁻¹) ((f _*).map φ) ((f.adjunction.unit).app 𝒢)).hom ≫
          pullback.snd ((f⁻¹).map ((f _*).map φ))
            ((f⁻¹).map ((f.adjunction.unit).app 𝒢)) ≫
        (f⁻¹).map ((f.adjunction.unit).app 𝒢) ≫
          (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
          -- Replace the first pullback projection by the second using the pullback relation.
          rw [pullback.condition_assoc]
    _ =
      (f⁻¹).map (unit_pullback_cover_projection (f := f) φ) ≫
        (f⁻¹).map ((f.adjunction.unit).app 𝒢) ≫
          (f.adjunction.counit).app ((f⁻¹).obj 𝒢) := by
          -- Identify the preserved pullback projection with the mapped projection downstairs.
          rw [PreservesPullback.iso_hom_snd_assoc]
    _ = (f⁻¹).map (unit_pullback_cover_projection (f := f) φ) := by
          -- Contract the remaining unit-counit zig-zag with the left triangle identity.
          simpa using
            f.adjunction.left_triangle_components_assoc 𝒢
              ((f⁻¹).map (unit_pullback_cover_projection (f := f) φ))

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
