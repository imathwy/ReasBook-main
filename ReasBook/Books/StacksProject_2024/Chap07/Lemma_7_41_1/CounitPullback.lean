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

/-- Helper for Lemma 7.41.1: the pushforward morphism induced by a lifted pullback cover. -/
private abbrev pushforward_lifted_cover_map
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢)) :
    𝒢' ⟶ (f _*).obj ℱ :=
  (f.adjunction.unit).app 𝒢' ≫
    (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢))

/-- Helper for Lemma 7.41.1: the map produced from a lifted pullback cover pushes forward to the
original target cover. -/
private theorem pushforward_lifted_cover_factorization
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (γ : 𝒢' ⟶ (f _*).obj 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢))
    (hι : ι ≫ pullback.snd φ ((f.adjunction.counit).app 𝒢) = (f⁻¹).map γ) :
    pushforward_lifted_cover_map (f := f) φ ι ≫ (f _*).map φ = γ := by
  have hpb :
      ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ =
        (f⁻¹).map γ ≫ (f.adjunction.counit).app 𝒢 := by
    -- First move across the pullback relation, then insert the lifted cover factorization.
    rw [pullback.condition_assoc]
    rw [hι]
  -- Push forward the pullback factorization and contract the remaining unit-counit zig-zag.
  calc
    pushforward_lifted_cover_map (f := f) φ ι ≫ (f _*).map φ
        =
      (f.adjunction.unit).app 𝒢' ≫
        (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢)) ≫
          (f _*).map φ := by
          rfl
    _ =
      (f.adjunction.unit).app 𝒢' ≫
        (f _*).map (ι ≫ pullback.fst φ ((f.adjunction.counit).app 𝒢) ≫ φ) := by
          rw [← Category.assoc, ← Functor.map_comp, Category.assoc]
    _ =
      (f.adjunction.unit).app 𝒢' ≫
        (f _*).map ((f⁻¹).map γ ≫ (f.adjunction.counit).app 𝒢) := by
          rw [hpb]
    _ =
      (f.adjunction.unit).app 𝒢' ≫
        (f _*).map ((f⁻¹).map γ) ≫
          (f _*).map ((f.adjunction.counit).app 𝒢) := by
          rw [Functor.map_comp, Category.assoc]
    _ =
      γ ≫ (f.adjunction.unit).app ((f _*).obj 𝒢) ≫
        (f _*).map ((f.adjunction.counit).app 𝒢) := by
          -- Move the unit past the mapped lifted cover using naturality.
          rw [f.adjunction.unit_naturality_assoc]
    _ = γ := by
          -- Contract the right triangle on the pushforward of `𝒢`.
          simpa using
            f.adjunction.right_triangle_components_assoc 𝒢 γ

/-- Helper for Lemma 7.41.1: if covers onto inverse images lift after a locally surjective
cover upstairs, then `f_*` maps locally surjective morphisms to locally surjective morphisms. -/
private theorem pushforward_factorization_of_lifted_cover
    {ℱ 𝒢 : Sheaf K (Type w)} {𝒢' : Sheaf J (Type w)}
    (φ : ℱ ⟶ 𝒢)
    (γ : 𝒢' ⟶ (f _*).obj 𝒢)
    (ι : (f⁻¹).obj 𝒢' ⟶ pullback φ ((f.adjunction.counit).app 𝒢))
    (hι : ι ≫ pullback.snd φ ((f.adjunction.counit).app 𝒢) = (f⁻¹).map γ) :
    ∃ δ : 𝒢' ⟶ (f _*).obj ℱ, δ ≫ (f _*).map φ = γ := by
  let δ : 𝒢' ⟶ (f _*).obj ℱ := pushforward_lifted_cover_map (f := f) φ ι
  refine ⟨δ, ?_⟩
  -- Route correction: reuse the cached unit-counit rewrite lemma instead of replaying the full
  -- transport calculation inside this wrapper.
  simpa [δ] using
    pushforward_lifted_cover_factorization
      (f := f) (φ := φ) (γ := γ) (ι := ι) hι

/-- Helper for Lemma 7.41.1: if covers onto inverse images lift after a locally surjective
cover upstairs, then `f_*` maps locally surjective morphisms to locally surjective morphisms. -/
theorem surjectionLiftingAlongInverseImage_implies_pushforwardMapsLocallySurjective
    (hLift : f.surjectionLiftingAlongInverseImage) :
    ∀ {ℱ 𝒢 : Sheaf K (Type w)} (φ : ℱ ⟶ 𝒢),
      Sheaf.IsLocallySurjective φ →
        Sheaf.IsLocallySurjective ((f _*).map φ) := by
  intro ℱ 𝒢 φ hφ
  let b : pullback φ ((f.adjunction.counit).app 𝒢) ⟶ (f⁻¹).obj ((f _*).obj 𝒢) :=
    pullback.snd φ ((f.adjunction.counit).app 𝒢)
  have hb : Sheaf.IsLocallySurjective b := by
    -- Pull back the original cover along the counit before applying the lifting hypothesis.
    simpa [b] using
      sheaf_pullback_snd_isLocallySurjective (J := K) φ ((f.adjunction.counit).app 𝒢) hφ
  rcases hLift b hb with ⟨𝒢', γ, hγ, ι, hι⟩
  rcases pushforward_factorization_of_lifted_cover
      (f := f) (φ := φ) (γ := γ) (ι := ι) hι with ⟨δ, hδ⟩
  -- Descend local surjectivity of `γ` across the exhibited factorization.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  change Presheaf.IsLocallySurjective J (((f _*).map φ).hom)
  letI : Presheaf.IsLocallySurjective J γ.hom := hγ
  simpa using Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (J := J)
    (f₁ := δ.hom)
    (f₂ := ((f _*).map φ).hom)
    (f₃ := γ.hom)
    (by
      simpa using congrArg (fun t ↦ t.hom) hδ)

end

end MorphismOfTopoiIn

end CategoryTheory
