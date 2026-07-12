import StacksProject_2024.Chap08.Lemma_8_12_2.CoverDescent
import StacksProject_2024.Chap08.Lemma_8_12_2.HomPresheafPrestack

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: for a fixed cover, prestack full faithfulness plus
essential surjectivity upgrades the pullback descent functor to an equivalence. -/
theorem pullbackProjection_cover_isEquivalence_of_prestack_essSurj
    (p : S ⥤ D) [p.IsFibered]
    [Pseudofunctor.IsPrestack (canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)) J]
    {U : C} (S : J.Cover U)
    (hEss :
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
        (fun I : S.Arrow ↦ I.f)).EssSurj) :
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  -- The cover arrows in the descent functor generate exactly the original covering sieve.
  have hCover :
      Sieve.ofArrows (fun I : S.Arrow ↦ I.Y) (fun I ↦ I.f) ∈ J U := by
    rw [S.ofArrows_eq]
    exact S.condition
  -- Prestackness supplies full faithfulness; the explicit essential-surjectivity hypothesis
  -- supplies the remaining field of `Functor.IsEquivalence`.
  exact
    { faithful :=
        ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).fullyFaithfulToDescentData
          (fun I : S.Arrow ↦ I.f) hCover).faithful
      full :=
        ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).fullyFaithfulToDescentData
          (fun I : S.Arrow ↦ I.f) hCover).full
      essSurj := hEss }

/-- Helper for Chap08 Lemma 8 12 2: after strictifying the central pullback fiber, the target
image-cover descent functor is an equivalence. -/
theorem pullbackProjection_targetStrictifiedImageDescentFunctor_isEquivalence
    [Functor.IsContinuous u J K]
    (p : S ⥤ D) [IsStackOnSite K p] {U : C} (S : J.Cover U) :
    ((pullbackProjection_targetFiberFunctor u p U) ⋙
      ((canonicalFiberPseudofunctor p).toDescentData
        (fun I : S.Arrow ↦ u.map I.f))).IsEquivalence := by
  -- The source-to-target strictification is an equivalence on the central fiber.
  letI : (pullbackProjection_targetFiberFunctor u p U).IsEquivalence :=
    pullbackProjection_targetFiberFunctor_isEquivalence u p U
  -- The stack condition on `p` gives effective descent for the image of the source cover.
  have hTarget :
      ((canonicalFiberPseudofunctor p).toDescentData
        (fun I : S.Arrow ↦ u.map I.f)).IsEquivalence :=
    targetStack_imageDescentFunctor_isEquivalence (J := J) (K := K) u p S
  -- Compose the strictification equivalence with the target image-cover descent equivalence.
  exact
    @Functor.isEquivalence_trans _ _ _ _ _ _
      (pullbackProjection_targetFiberFunctor u p U)
      ((canonicalFiberPseudofunctor p).toDescentData
        (fun I : S.Arrow ↦ u.map I.f))
      inferInstance hTarget

end

end CategoryTheory
