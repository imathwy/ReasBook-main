import Mathlib
import StacksProject_2024.Chap10.Lemma_10_154_2
import StacksProject_2024.Chap10.Lemma_10_154_5

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

noncomputable section

section EtaleIndEtale

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Helper for Chap10 Lemma 10 155 12: an étale algebra map is a one-object filtered colimit of
étale algebras. -/
private theorem isFilteredColimitOfEtale_of_etaleAlgebraMap
    (hAB : (algebraMap A B).Etale) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- Translate the chapter owner to the raw categorical ind-owner, then use the canonical
  -- inclusion of étale morphisms into ind-étale morphisms.
  rw [← RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale]
  exact
    (CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale))
      (CommRingCat.ofHom (algebraMap A B))
      (by simpa [CommRingCat.etale] using hAB)

omit [Algebra A B] in
/-- Helper for Chap10 Lemma 10 155 12: a ring isomorphism is a one-object filtered colimit of
étale algebras. -/
private theorem isFilteredColimitOfEtale_of_bijective (f : A →+* B)
    (hf : Function.Bijective f) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} f := by
  -- A bijective ring map is étale; after installing its algebra structure, the previous
  -- one-object adapter gives the ind-étale presentation of the same map.
  letI : Algebra A B := f.toAlgebra
  have hfEtale : f.Etale := RingHom.Etale.of_bijective hf
  have halgEtale : (algebraMap A B).Etale := by
    simpa [RingHom.algebraMap_toAlgebra] using hfEtale
  simpa [RingHom.algebraMap_toAlgebra] using
    isFilteredColimitOfEtale_of_etaleAlgebraMap (A := A) (B := B) halgEtale

variable {C : Type u} [CommRing C] [Algebra A C]

/-- Helper for Chap10 Lemma 10 155 12: ind-étaleness transports across an algebra
equivalence of targets. -/
theorem isFilteredColimitOfEtale_of_algEquiv (e : B ≃ₐ[A] C)
    (hAB : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A C) := by
  -- Compose the given ind-étale map with the bijective map underlying the equivalence, then
  -- rewrite the composite back to the target algebra map.
  have he : RingHom.IsFilteredColimitOfEtale.{u, u, u} e.toRingHom :=
    isFilteredColimitOfEtale_of_bijective e.toRingHom e.bijective
  have hcomp :
      RingHom.IsFilteredColimitOfEtale.{u, u, u}
        (e.toRingHom.comp (algebraMap A B)) :=
    RingHom.isFilteredColimitOfEtale_comp (algebraMap A B) e.toRingHom hAB he
  have hmap : e.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    ext x
    exact e.commutes x
  rw [hmap] at hcomp
  exact hcomp

/-- Helper for Chap10 Lemma 10 155 12: an away localization is ind-étale over its source. -/
theorem isFilteredColimitOfEtale_of_isLocalizationAway (r : A)
    [IsLocalization.Away r B] :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B) := by
  -- Mathlib gives away localizations as étale; the one-object adapter converts this finite
  -- stage into the chapter's ind-étale owner.
  have hEtale : (algebraMap A B).Etale := by
    exact (RingHom.etale_algebraMap (R := A) (S := B)).2
      (Algebra.Etale.of_isLocalizationAway r)
  exact isFilteredColimitOfEtale_of_etaleAlgebraMap hEtale

/-- Helper for Chap10 Lemma 10 155 12: étale morphisms in commutative rings are stable under
cobase change, in the categorical spelling used by `ind`. -/
private instance etale_isStableUnderCobaseChange_forTensorBaseChange :
    (CommRingCat.etale : CategoryTheory.MorphismProperty CommRingCat.{u}).IsStableUnderCobaseChange := by
  -- Translate the ring-hom base-change theorem through the categorical morphism-property bridge.
  simpa [CommRingCat.etale, RingHom.toMorphismProperty] using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Etale.isStableUnderBaseChange

/-- Helper for Chap10 Lemma 10 155 12: same-universe tensor base change preserves
ind-étaleness. -/
theorem isFilteredColimitOfEtale_tensorBaseChangeSameUniverse
    {T : Type u} [CommRing T] [Algebra A T]
    (hAB : RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap A B)) :
    RingHom.IsFilteredColimitOfEtale.{u, u, u} (algebraMap T (T ⊗[A] B)) := by
  -- Move the source-facing owner to the raw categorical `ind` owner, apply pushout stability
  -- along the tensor-product pushout square, and then move back to the source-facing owner.
  letI : Algebra B (T ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower A B (T ⊗[A] B) := by infer_instance
  rw [← RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale] at hAB ⊢
  exact CategoryTheory.MorphismProperty.of_isPushout
    (P := CategoryTheory.MorphismProperty.ind CommRingCat.etale)
    (CommRingCat.isPushout_tensorProduct A T B) hAB

end EtaleIndEtale
