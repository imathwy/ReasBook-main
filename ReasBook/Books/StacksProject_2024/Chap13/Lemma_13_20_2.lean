import Mathlib
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap13.Lemma_13_6_6
import StacksProject_2024.Chap13.Lemma_13_18_3
import StacksProject_2024.Chap13.Lemma_13_23_5
import StacksProject_2024.Chap13.Lemma_13_31_2
import StacksProject_2024.Chap13.Lemma_13_31_4
import StacksProject_2024.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Category.{v₂} 𝒟]

variable (F : K⁺(𝒜) ⥤ 𝒟)

local notation "Qhplus" => HomotopyCategory.Plus.quotient 𝒜

-- Proof sketch: use Lemma 13.18.3 to replace every bounded-below complex by a quasi-isomorphic
-- bounded-below complex of injectives, so every object reaches the bounded-below injective
-- homotopy subcategory. Lemma 13.31.2, together with the canonical K-injective instance on the
-- chapter owner `CochainComplex.InjectivePlus 𝒜`, implies that a quasi-isomorphism between
-- bounded-below injective complexes
-- is already an isomorphism in `K^+(\mathcal A)`, hence any exact functor out of
-- `K^+(\mathcal A)` sends it to an isomorphism. Lemma 13.14.15 then yields pointwise existence of
-- the right derived functor.
/-- Lemma 13.20.2: if `𝒜` is an abelian category with enough injectives, then for every exact
functor `F : K^+(\mathcal A) ⥤ \mathcal D` into a triangulated category, the right derived
functor `RF : D^+(\mathcal A) ⥤ \mathcal D` is everywhere defined. -/
theorem boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives :
    F.HasPointwiseRightDerivedFunctor (Qis⁺(𝒜)) := by
  let _ : ObjectProperty.IsStableUnderRetracts (Ac⁺(𝒜)) := by
    dsimp [HomotopyCategory.subcategoryAcyclic]
    infer_instance
  let _ : IsSaturatedMultiplicativeSystem (Qis⁺(𝒜)) := by
    rw [← boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso 𝒜]
    infer_instance
  refine F.hasPointwiseRightDerivedFunctor_of_subset (Qis⁺(𝒜))
    (boundedBelowInjectiveHomotopyProperty 𝒜) ?_ ?_
  · intro X
    let K : Comp⁺(𝒜) := ⟨X.obj.as, X.property⟩
    obtain ⟨a, hX⟩ := (CochainComplex.plus_iff 𝒜 X.obj.as).1 X.property
    obtain ⟨I, -, -⟩ :=
      exists_injectiveResolution_strictlyGE_with_termwise_mono a hX
    let ι : K ⟶ I.complex.obj := ⟨I.ι⟩
    refine ⟨(Qhplus).obj I.complex.obj, (Qhplus).map ι, ?_, ?_⟩
    · intro n
      simpa using I.injective n
    ·
      simpa [K] using
        (show (Qis⁺(𝒜)) ((Qhplus).map ι) by
          change HomotopyCategory.quasiIso 𝒜 (up ℤ)
            ((HomotopyCategory.quotient 𝒜 (up ℤ)).map I.ι)
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact I.quasiIso)
  · intro X X' s hX hX' hs
    change IsIso (F.map s)
    let _ : IsIso s := by
      let Xc : CochainComplex 𝒜 ℤ := X.obj.as
      let Xc' : CochainComplex 𝒜 ℤ := X'.obj.as
      let XI : CochainComplex.InjectivePlus 𝒜 := ⟨⟨Xc, X.property⟩, fun n ↦ by
        simpa [Xc] using hX n⟩
      let X'I : CochainComplex.InjectivePlus 𝒜 := ⟨⟨Xc', X'.property⟩, fun n ↦ by
        simpa [Xc'] using hX' n⟩
      have hs' : HomotopyCategory.quasiIso 𝒜 (up ℤ) s.hom := by
        simpa [boundedBelowHomotopyQuasiIso] using hs
      letI : Xc.IsKInjective :=
        by
          simpa [XI, Xc] using CochainComplex.PlusWithTermsIn.instIsKInjective XI
      letI : Xc'.IsKInjective :=
        by
          simpa [X'I, Xc'] using CochainComplex.PlusWithTermsIn.instIsKInjective X'I
      have hbij :
          ∀ ⦃M N : K(𝒜)⦄ (f : M ⟶ N), HomotopyCategory.quasiIso 𝒜 (up ℤ) f →
            Function.Bijective
              (fun g : N ⟶ (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Xc ↦ f ≫ g) :=
        (CochainComplex.isKInjective_iff_precomp_bijective_of_quasiIso Xc).1
          (show Xc.IsKInjective from inferInstance)
      have hbij' :=
        (CochainComplex.isKInjective_iff_precomp_bijective_of_quasiIso Xc').1
          (show Xc'.IsKInjective from inferInstance)
      obtain ⟨t, ht⟩ := (hbij s.hom hs').surjective (𝟙 X.obj)
      have ht' : s.hom ≫ t = 𝟙 X.obj := by
        simpa using ht
      refine ⟨⟨⟨t⟩, ?_, ?_⟩⟩
      · ext
        exact ht'
      · ext
        apply (hbij' s.hom hs').injective
        calc
          s.hom ≫ t ≫ s.hom = (s.hom ≫ t) ≫ s.hom := by simp [Category.assoc]
          _ = 𝟙 X.obj ≫ s.hom := by rw [ht']; rfl
          _ = s.hom ≫ 𝟙 X'.obj := by simp
    infer_instance

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

-- Proof sketch: specialize the previous theorem to the canonical bounded-below source functor
-- `K^+(\mathcal A) ⥤ D^+(\mathcal B)` attached to `F`.
/-- An additive functor from an abelian category with enough injectives has its bounded-below
right derived functor to `D^+(\mathcal B)` everywhere defined. -/
theorem additiveFunctor_boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives :
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).HasPointwiseRightDerivedFunctor
      (Qis⁺(𝒜)) := by
  simpa using
    (boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F))

attribute [instance]
  additiveFunctor_boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives

end

end CategoryTheory
