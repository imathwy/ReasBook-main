import Mathlib
import stacks_project.Chap10.Lemma_10_144_3
import stacks_project.Chap10.Lemma_10_154_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing
open scoped RatFunc

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Lemma 10.159.1: the residue field at the maximal ideal agrees with the ordinary
residue field of a local ring. -/
noncomputable def maximalIdealResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Lemma 10.159.1: the canonical equivalence from the maximal-ideal residue field
sends the image of `a` to the ordinary residue class of `a`. -/
theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  -- Rewrite the source element through the quotient presentation of `ResidueField A`.
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  -- The chosen equivalence is inverse to this algebra map.
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

/-- Helper for Lemma 10.159.1: the maximal-ideal residue-field model is compatible with the
ordinary residue-field map induced by a local ring homomorphism. -/
theorem maximalIdealResidueFieldEquiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealResidueFieldEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdealResidueFieldEquiv A).toRingHom := by
  -- Compare the two maps on residue classes coming from elements of the source local ring.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdealResidueFieldEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a))
  -- Each side is the residue class of `f a` in the ordinary residue field of `B`.
  rw [Ideal.ResidueField.map_algebraMap, maximalIdealResidueFieldEquiv_apply_algebraMap,
    maximalIdealResidueFieldEquiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 10.159.1: quotienting `AdjoinRoot f` by the extended maximal ideal reduces
to adjoining a root of the reduced polynomial over the residue field. This is the algebraic bridge
for the source proof's monic quotient step. -/
noncomputable def adjoinRoot_quotient_by_mapped_maximalIdeal_equiv
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Polynomial A)
    (P : Polynomial (ResidueField A))
    (hP : f.map (algebraMap A (ResidueField A)) = P) :
    (AdjoinRoot f ⧸ Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A)) ≃+* AdjoinRoot P := by
  -- Rewrite the quotient through `AdjoinRoot.quotEquivQuotMap`, then substitute the reduced
  -- polynomial identified in the source algebraic branch.
  subst hP
  change (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) (maximalIdeal A)) ≃+*
      AdjoinRoot (Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) f)
  simpa [AdjoinRoot, IsLocalRing.ResidueField] using
    (AdjoinRoot.quotEquivQuotMap f (maximalIdeal A)).toRingEquiv

/-- Helper for Lemma 10.159.1: if the reduction of `f` modulo the maximal ideal is irreducible,
then `AdjoinRoot f` is already a local ring. This is the source proof's algebraic monogenic
successor stage before identifying its residue field. -/
theorem adjoinRoot_isLocalRing_of_irreducible_reduction
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Polynomial A) (hf : f.Monic)
    (P : Polynomial (ResidueField A))
    (hP : f.map (algebraMap A (ResidueField A)) = P)
    [Fact (Irreducible P)] :
    IsLocalRing (AdjoinRoot f) := by
  let J : Ideal (AdjoinRoot f) :=
    Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A)
  let e :
      (AdjoinRoot f ⧸ J) ≃+* AdjoinRoot P :=
    adjoinRoot_quotient_by_mapped_maximalIdeal_equiv A f P hP
  letI : Module.Finite A (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.IsIntegral A (AdjoinRoot f) := inferInstance
  have hqf : IsField (AdjoinRoot f ⧸ J) := by
    exact e.isField (Field.toIsField (AdjoinRoot P))
  have hJmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hqf
  -- The lifted polynomial is monic, so the extension is integral. Every maximal ideal upstairs
  -- contracts to the maximal ideal of the base local ring and therefore contains `J`.
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨J, hJmax, ?_⟩
  intro M hM
  have hMcomap_max : Ideal.IsMaximal (Ideal.comap (algebraMap A (AdjoinRoot f)) M) := by
    letI : M.IsMaximal := hM
    simpa using
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := AdjoinRoot f) M)
  have hcomap_eq :
      Ideal.comap (algebraMap A (AdjoinRoot f)) M = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hMcomap_max
  have hcomap_eq_of :
      Ideal.comap (AdjoinRoot.of f) M = maximalIdeal A := by
    simpa [AdjoinRoot.algebraMap_eq] using hcomap_eq
  have hJleM : J ≤ M := by
    rw [show J = Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A) by rfl]
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hcomap_eq_of.symm
  exact (hJmax.eq_of_le hM.1.1 hJleM).symm

/-- Helper for Lemma 10.159.1: in the algebraic `AdjoinRoot` stage, the maximal ideal is exactly
the extension of the maximal ideal from the base local ring. -/
theorem adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Polynomial A)
    (P : Polynomial (ResidueField A))
    (hP : f.map (algebraMap A (ResidueField A)) = P)
    [IsLocalRing (AdjoinRoot f)]
    [Fact (Irreducible P)] :
    Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A) = maximalIdeal (AdjoinRoot f) := by
  let J : Ideal (AdjoinRoot f) :=
    Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A)
  let e :
      (AdjoinRoot f ⧸ J) ≃+* AdjoinRoot P :=
    adjoinRoot_quotient_by_mapped_maximalIdeal_equiv A f P hP
  have hqf : IsField (AdjoinRoot f ⧸ J) := by
    exact e.isField (Field.toIsField (AdjoinRoot P))
  have hJmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hqf
  -- In the local ring just constructed, the extended maximal ideal is the unique maximal ideal.
  change J = maximalIdeal (AdjoinRoot f)
  exact IsLocalRing.eq_maximalIdeal hJmax

/-- Helper for Lemma 10.159.1: once the algebraic `AdjoinRoot` stage is local and its maximal
ideal is the extension of the maximal ideal of the base, the structural map from the base local
ring is automatically a local ring homomorphism. -/
theorem adjoinRoot_isLocalHom_of_irreducible_reduction
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Polynomial A)
    (P : Polynomial (ResidueField A))
    (hP : f.map (algebraMap A (ResidueField A)) = P)
    [IsLocalRing (AdjoinRoot f)]
    [Fact (Irreducible P)] :
    IsLocalHom (algebraMap A (AdjoinRoot f)) := by
  -- The source and target maximal ideals line up, so the standard local-hom criterion applies.
  have hmap :
      Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A) = maximalIdeal (AdjoinRoot f) :=
    adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction A f P hP
  exact ((IsLocalRing.local_hom_TFAE (algebraMap A (AdjoinRoot f))).out 2 0).mp (le_of_eq hmap)

/-- Helper for Lemma 10.159.1: after proving the algebraic `AdjoinRoot` stage is local, its
residue field is obtained by rewriting the quotient bridge definitionally. -/
noncomputable def adjoinRoot_residueField_equiv_of_irreducible_reduction
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Polynomial A)
    (P : Polynomial (ResidueField A))
    (hP : f.map (algebraMap A (ResidueField A)) = P)
    [IsLocalRing (AdjoinRoot f)]
    [Fact (Irreducible P)] :
    ResidueField (AdjoinRoot f) ≃+* AdjoinRoot P := by
  have hJ :
      Ideal.map (algebraMap A (AdjoinRoot f)) (maximalIdeal A) = maximalIdeal (AdjoinRoot f) :=
    adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction A f P hP
  have hJ_of :
      Ideal.map (AdjoinRoot.of f) (maximalIdeal A) = maximalIdeal (AdjoinRoot f) := by
    simpa [AdjoinRoot.algebraMap_eq] using hJ
  -- Route correction: use the residue field definition directly instead of reintroducing a
  -- separate maximal-ideal residue-field transport.
  simpa [IsLocalRing.ResidueField] using
    (Ideal.quotEquivOfEq hJ_of).symm.trans
      (adjoinRoot_quotient_by_mapped_maximalIdeal_equiv A f P hP)

/-- Helper for Lemma 10.159.1: in the algebraic `AdjoinRoot` branch, the chosen residue-field
identification carries the residue-field map from the base local ring to the canonical coefficient
embedding into the reduced `AdjoinRoot`. -/
theorem adjoinRoot_residueField_equiv_of_irreducible_reduction_comp_residueFieldMap
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Polynomial A)
    (P : Polynomial (ResidueField A))
    (hP : f.map (algebraMap A (ResidueField A)) = P)
    [IsLocalRing (AdjoinRoot f)]
    [IsLocalHom (algebraMap A (AdjoinRoot f))]
    [Fact (Irreducible P)] :
    (adjoinRoot_residueField_equiv_of_irreducible_reduction A f P hP).toRingHom.comp
        (ResidueField.map (algebraMap A (AdjoinRoot f))) =
      algebraMap (ResidueField A) (AdjoinRoot P) := by
  let J : Ideal (AdjoinRoot f) :=
    Ideal.map (AdjoinRoot.of f) (maximalIdeal A)
  have hJ :
      J = maximalIdeal (AdjoinRoot f) := by
    -- This is exactly the maximal-ideal identification proved for the algebraic branch.
    simpa [J, AdjoinRoot.algebraMap_eq] using
      adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction A f P hP
  -- Compare the two maps on residue classes coming from elements of the base local ring.
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
  -- Route correction: avoid the broad quotient simplifier that previously timed out, and instead
  -- evaluate the chosen quotient equivalence only on the residue class coming from `C a`.
  calc
    adjoinRoot_residueField_equiv_of_irreducible_reduction A f P hP
        (residue (AdjoinRoot f) (algebraMap A (AdjoinRoot f) a))
        =
      adjoinRoot_quotient_by_mapped_maximalIdeal_equiv A f P hP
        ((Ideal.quotEquivOfEq hJ).symm
          (residue (AdjoinRoot f) (algebraMap A (AdjoinRoot f) a))) := by
            rfl
    _ =
      adjoinRoot_quotient_by_mapped_maximalIdeal_equiv A f P hP
        (Ideal.Quotient.mk J (AdjoinRoot.of f a)) := by
          rw [show residue (AdjoinRoot f) (algebraMap A (AdjoinRoot f) a) =
              Ideal.Quotient.mk (maximalIdeal (AdjoinRoot f)) (AdjoinRoot.of f a) by
                rfl,
            Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
    _ = algebraMap (ResidueField A) (AdjoinRoot P) (residue A a) := by
          -- Evaluate the quotient equivalence on the constant polynomial `C a`.
          subst hP
          change
            (AdjoinRoot.quotEquivQuotMap f (maximalIdeal A)).toRingEquiv
              (Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of f) (maximalIdeal A))
                (AdjoinRoot.mk f (Polynomial.C a)))
              =
            Ideal.Quotient.mk
              (Ideal.span
                ({Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) f} :
                  Set (Polynomial (A ⧸ maximalIdeal A))))
              (Polynomial.C (Ideal.Quotient.mk (maximalIdeal A) a))
          rw [← Polynomial.map_C]
          exact AdjoinRoot.quotEquivQuotMap_apply_mk f (Polynomial.C a) (maximalIdeal A)

/-- Helper for Lemma 10.159.1: over any local base ring `A`, localizing `A[X]` at the extension
of the maximal ideal realizes the transcendental simple residue-field extension. This is the
source proof's transcendental monogenic branch in the form needed for later stage extensions. -/
theorem exists_transcendental_localAlgebra_with_ratFunc_maximalIdealResidueField_equiv_of
    (A : Type u) [CommRing A] [IsLocalRing A] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : Algebra A A')
      (_ : IsLocalHom (algebraMap A A')) (_ : (algebraMap A A').Flat)
      (_ : ResidueField A' ≃+* RatFunc ((maximalIdeal A).ResidueField)),
        Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A' := by
  let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
  letI : J.IsPrime := by
    dsimp [J]
    infer_instance
  letI : J.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    simpa [J, Ideal.under] using
      (Ideal.comap_map_eq_self_of_isMaximal (Polynomial.C : A →+* Polynomial A)
        (p := maximalIdeal A) (show J ≠ ⊤ by
          exact Ideal.IsPrime.ne_top (I := J) inferInstance)).symm
  let A' := Localization.AtPrime J
  letI : CommRing A' := inferInstance
  letI : IsLocalRing A' := inferInstance
  letI : Algebra A A' := inferInstance
  have hmap : Ideal.map (algebraMap A A') (maximalIdeal A) = maximalIdeal A' := by
    -- The defining prime of the localization is exactly the extension of the maximal ideal.
    calc
      Ideal.map (algebraMap A A') (maximalIdeal A)
          = Ideal.map ((algebraMap (Polynomial A) A').comp (algebraMap A (Polynomial A)))
              (maximalIdeal A) := by
              rfl
      _ = Ideal.map (algebraMap (Polynomial A) A')
            (Ideal.map (algebraMap A (Polynomial A)) (maximalIdeal A)) := by
            rw [Ideal.map_map]
      _ = maximalIdeal A' := by
            simpa [J] using (Localization.AtPrime.map_eq_maximalIdeal (I := J))
  have hlocal : IsLocalHom (algebraMap A A') := by
    -- The maximal-ideal equality is the local-hom criterion for the localization map.
    exact ((IsLocalRing.local_hom_TFAE (algebraMap A A')).out 2 0).mp (le_of_eq hmap)
  have hflat_poly : (algebraMap A (Polynomial A)).Flat := by
    -- Polynomial algebras are flat over their coefficient ring.
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat_loc : (algebraMap (Polynomial A) A').Flat := by
    -- Localizations are flat over the source ring.
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat : (algebraMap A A').Flat := by
    -- Flatness composes along the polynomial ring and the localization map.
    simpa [A'] using RingHom.Flat.comp hflat_poly hflat_loc
  have e : J.ResidueField ≃+* RatFunc ((maximalIdeal A).ResidueField) :=
    (Polynomial.residueFieldMapCAlgEquiv (I := maximalIdeal A) (J := J) rfl).toRingEquiv
  refine ⟨A', inferInstance, inferInstance, inferInstance, hlocal, hflat, ?_, hmap⟩
  simpa [A', Ideal.ResidueField] using e

/-- Helper for Lemma 10.159.1: localizing `R[X]` at the prime `(maximalIdeal R) R[X]` gives a flat
local `R`-algebra whose residue field is the rational function field of the residue field at the
maximal ideal. This is the transcendental monogenic branch of the source proof. -/
theorem exists_transcendental_localAlgebra_with_ratFunc_maximalIdealResidueField_equiv :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : ResidueField R' ≃+* RatFunc ((maximalIdeal R).ResidueField)),
        Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R' := by
  -- Specialize the general transcendental construction to the ambient local ring `R`.
  simpa using
    exists_transcendental_localAlgebra_with_ratFunc_maximalIdealResidueField_equiv_of (A := R)

/-- Helper for Lemma 10.159.1: in the transcendental localization model over a local ring `A`,
the residue field of the localization `A[X]_(mA[X])` is identified with the rational function
field over the maximal-ideal residue field of `A`. -/
noncomputable def localization_residueField_equiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
    ResidueField (Localization.AtPrime J) ≃+* RatFunc ((maximalIdeal A).ResidueField) := by
  let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
  letI : J.IsPrime := by
    dsimp [J]
    infer_instance
  letI : J.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    simpa [J, Ideal.under] using
      (Ideal.comap_map_eq_self_of_isMaximal (Polynomial.C : A →+* Polynomial A)
        (p := maximalIdeal A) (show J ≠ ⊤ by
          exact Ideal.IsPrime.ne_top (I := J) inferInstance)).symm
  -- This is the explicit localization residue-field model from
  -- `Polynomial.residueFieldMapCAlgEquiv`.
  simpa [J, Ideal.ResidueField] using
    (Polynomial.residueFieldMapCAlgEquiv (I := maximalIdeal A) (J := J) rfl).toRingEquiv

/-- Helper for Lemma 10.159.1: in the transcendental localization model over a local ring `A`,
the chosen residue-field equivalence sends the residue class of a coefficient `a : A` to the
corresponding constant rational function over the maximal-ideal residue field. -/
theorem localization_residueField_equiv_apply_residue
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
    let B : Type u := Localization.AtPrime J
    let e : ResidueField B ≃+* RatFunc ((maximalIdeal A).ResidueField) :=
      localization_residueField_equiv A
    e (residue B (algebraMap A B a)) =
      algebraMap (Polynomial ((maximalIdeal A).ResidueField))
        (RatFunc ((maximalIdeal A).ResidueField))
        (Polynomial.C (algebraMap A (maximalIdeal A).ResidueField a)) := by
  let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
  letI : J.IsPrime := by
    dsimp [J]
    infer_instance
  letI : J.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    simpa [J, Ideal.under] using
      (Ideal.comap_map_eq_self_of_isMaximal (Polynomial.C : A →+* Polynomial A)
        (p := maximalIdeal A) (show J ≠ ⊤ by
          exact Ideal.IsPrime.ne_top (I := J) inferInstance)).symm
  let B : Type u := Localization.AtPrime J
  let e : ResidueField B ≃+* RatFunc ((maximalIdeal A).ResidueField) :=
    localization_residueField_equiv A
  -- Rewrite the residue class from `A` as the image of the constant polynomial `C a`, then apply
  -- the explicit computation for `Polynomial.residueFieldMapCAlgEquiv`.
  change
    e (algebraMap (Polynomial A) (ResidueField B) (Polynomial.C a)) =
      algebraMap (Polynomial ((maximalIdeal A).ResidueField))
        (RatFunc ((maximalIdeal A).ResidueField))
        (Polynomial.C (algebraMap A (maximalIdeal A).ResidueField a))
  -- Unfold the chosen equivalence back to the polynomial residue-field equivalence.
  dsimp [e, localization_residueField_equiv, B, J]
  simpa [Polynomial.map_C] using
    (Polynomial.residueFieldMapCAlgEquiv_algebraMap
      (I := maximalIdeal A) (J := J) rfl (Polynomial.C a))

/-- Helper for Lemma 10.159.1: for the canonical localization of `A[X]` at the extension of the
maximal ideal of a local ring `A`, the maximal ideal of the localization is exactly the image of
the maximal ideal of `A`. This isolates the base-to-localization local-ring comparison used in the
transcendental successor step. -/
theorem localization_map_maximalIdeal_eq_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
    let B : Type u := Localization.AtPrime J
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
  let B : Type u := Localization.AtPrime J
  letI : CommRing B := inferInstance
  letI : IsLocalRing B := inferInstance
  letI : Algebra A B := inferInstance
  -- Rewrite the base algebra map through the polynomial ring and then use the standard
  -- localization-at-prime maximal-ideal computation.
  calc
    Ideal.map (algebraMap A B) (maximalIdeal A)
        = Ideal.map ((algebraMap (Polynomial A) B).comp (algebraMap A (Polynomial A)))
            (maximalIdeal A) := by
            rfl
    _ = Ideal.map (algebraMap (Polynomial A) B)
          (Ideal.map (algebraMap A (Polynomial A)) (maximalIdeal A)) := by
          rw [Ideal.map_map]
    _ = maximalIdeal B := by
          simpa [J] using (Localization.AtPrime.map_eq_maximalIdeal (I := J))

/-- Helper for Lemma 10.159.1: the canonical map from a local ring `A` to the localization of
`A[X]` at the extension of its maximal ideal is a local ring homomorphism. This packages the
local-hom consequence of the preceding maximal-ideal identity for later stage bookkeeping. -/
theorem localization_isLocalHom
    (A : Type u) [CommRing A] [IsLocalRing A] :
    let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
    let B : Type u := Localization.AtPrime J
    IsLocalHom (algebraMap A B) := by
  let J : Ideal (Polynomial A) := Ideal.map (Polynomial.C) (maximalIdeal A)
  let B : Type u := Localization.AtPrime J
  letI : CommRing B := inferInstance
  letI : IsLocalRing B := inferInstance
  letI : Algebra A B := inferInstance
  have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    localization_map_maximalIdeal_eq_maximalIdeal A
  -- The maximal-ideal equality is exactly the local-hom criterion for the canonical map.
  exact ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 2 0).mp (le_of_eq hmap)

/-- Helper for Lemma 10.159.1: a partial stage of the source proof consists of a local flat
`R`-algebra whose residue field has already been identified with an intermediate field of `K`. -/
structure ResidueExtensionStage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (L : IntermediateField (ResidueField R) K) where
  A : Type*
  commRing : CommRing A
  localRing : IsLocalRing A
  algebra : Algebra R A
  localHom : IsLocalHom (algebraMap R A)
  flat : (algebraMap R A).Flat
  map_maximalIdeal : Ideal.map (algebraMap R A) (maximalIdeal R) = maximalIdeal A
  residueEquiv : ResidueField A ≃+* L

attribute [instance] ResidueExtensionStage.commRing
attribute [instance] ResidueExtensionStage.localRing
attribute [instance] ResidueExtensionStage.algebra
attribute [instance] ResidueExtensionStage.localHom

namespace ResidueExtensionStage

variable {K : Type v} [Field K] [Algebra (ResidueField R) K]
variable {L M N : IntermediateField (ResidueField R) K}

/-- Helper for Lemma 10.159.1: the residue-field identification of a stage induces the canonical
map from the stage residue field into the ambient field `K`. -/
noncomputable def residueToAmbient
    (S : ResidueExtensionStage (R := R) K L) :
    ResidueField S.A →+* K :=
  L.val.toRingHom.comp S.residueEquiv.toRingHom

/-- Helper for Lemma 10.159.1: a stage already carries a canonical surjective ring map onto the
intermediate field it realizes. This is the stage-level quotient map needed for the later
direct-limit kernel argument. -/
noncomputable def toIntermediateFieldHom
    (S : ResidueExtensionStage (R := R) K L) :
    S.A →+* L :=
  S.residueEquiv.toRingHom.comp (algebraMap S.A (ResidueField S.A))

/-- Helper for Lemma 10.159.1: the stage map to its intermediate field is surjective because the
residue map is surjective and the chosen residue-field equivalence is bijective. -/
theorem toIntermediateFieldHom_surjective
    (S : ResidueExtensionStage (R := R) K L) :
    Function.Surjective S.toIntermediateFieldHom := by
  -- Lift an intermediate-field element to the stage residue field and then to the stage ring.
  intro x
  obtain ⟨y, rfl⟩ := S.residueEquiv.surjective x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨a, ?_⟩
  rfl

/-- Helper for Lemma 10.159.1: the canonical quotient map from a stage onto its intermediate
field kills exactly the maximal ideal. This is the residue-field kernel computation needed for the
later direct-limit local-ring argument. -/
theorem ker_toIntermediateFieldHom
    (S : ResidueExtensionStage (R := R) K L) :
    RingHom.ker S.toIntermediateFieldHom = maximalIdeal S.A := by
  -- Compare vanishing in `L` with vanishing in the stage residue field through the chosen
  -- residue-field equivalence.
  ext a
  change S.toIntermediateFieldHom a = 0 ↔ a ∈ maximalIdeal S.A
  change S.residueEquiv (residue S.A a) = 0 ↔ a ∈ maximalIdeal S.A
  rw [S.residueEquiv.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]

/-- Helper for Lemma 10.159.1: the ambient residue-field map of a stage factors through the
canonical quotient map onto the realized intermediate field. -/
noncomputable def toAmbientRingHom
    (S : ResidueExtensionStage (R := R) K L) :
    S.A →+* K :=
  S.residueToAmbient.comp (algebraMap S.A (ResidueField S.A))

/-- Helper for Lemma 10.159.1: the canonical residue-field map of a stage is injective because
it factors through the embedding of the intermediate field into `K`. -/
theorem residueToAmbient_injective
    (S : ResidueExtensionStage (R := R) K L) :
    Function.Injective S.residueToAmbient := by
  -- First recover equality in the intermediate field `L`, then use the stage residue-field
  -- equivalence.
  intro x y hxy
  have hL : S.residueEquiv x = S.residueEquiv y := Subtype.ext hxy
  exact S.residueEquiv.injective hL

/-- Helper for Lemma 10.159.1: the transcendental branch only differs by transporting the
coefficient field from the maximal-ideal residue field of `S.A` to the ordinary residue field of
`S.A`. This isolates the one `RatFunc` transport used in the source proof's successor step. -/
noncomputable def ratFunc_residueField_transport
    (S : ResidueExtensionStage (R := R) K L) :
    RatFunc ((maximalIdeal S.A).ResidueField) ≃+* RatFunc (ResidueField S.A) :=
  -- Transport the coefficient field first, then pass to the fraction field of the polynomial ring.
  IsFractionRing.ringEquivOfRingEquiv
    (Polynomial.mapEquiv (maximalIdealResidueFieldEquiv S.A))

/-- Helper for Lemma 10.159.1: the `RatFunc` transport from
`(maximalIdeal S.A).ResidueField` to `ResidueField S.A` sends constant polynomials to the
corresponding constant polynomials via the canonical residue-field equivalence. -/
theorem ratFunc_residueField_transport_C
    (S : ResidueExtensionStage (R := R) K L)
    (x : (maximalIdeal S.A).ResidueField) :
    S.ratFunc_residueField_transport
        (algebraMap (Polynomial ((maximalIdeal S.A).ResidueField))
          (RatFunc ((maximalIdeal S.A).ResidueField)) (Polynomial.C x)) =
      algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
        (Polynomial.C (maximalIdealResidueFieldEquiv S.A x)) := by
  -- Rewrite the constant rational function as an `algebraMap`, then apply the fraction-field
  -- transport compatibility for the coefficient-ring equivalence.
  simpa [ResidueExtensionStage.ratFunc_residueField_transport, Polynomial.mapEquiv] using
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (K := RatFunc ((maximalIdeal S.A).ResidueField))
      (L := RatFunc (ResidueField S.A))
      (h := Polynomial.mapEquiv (maximalIdealResidueFieldEquiv S.A))
      (a := Polynomial.C x))

/-- Helper for Lemma 10.159.1: if a transcendental element `α` generates `Lx` over the residue
field of a stage, then `Lx` is canonically the rational function field on `α`. This isolates the
field-theoretic part of the transcendental successor step. -/
noncomputable def ratFunc_algEquiv_of_transcendental_generator
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      RatFunc (ResidueField S.A) ≃ₐ[ResidueField S.A] Lx :=
  fun α hgen htrans ↦
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    -- First identify `Lx` with the simple transcendental extension generated by `α`, then
    -- compose with the standard rational-function-field equivalence.
    (RatFunc.algEquivOfTranscendental α htrans).trans eTop

/-- Helper for Lemma 10.159.1: the transcendental generator equivalence sends a constant rational
function to the corresponding scalar in `Lx`. This is the constant-term computation needed when
comparing residue-field maps in the transcendental successor stage. -/
theorem ratFunc_algEquiv_of_transcendental_generator_C
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      ∀ x : ResidueField S.A,
      ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
          (Polynomial.C x)) =
        algebraMap (ResidueField S.A) Lx x := by
  intro α hgen htrans x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Evaluate the rational-function equivalence on constants before transporting along the
  -- generator identification `ResidueField S.A(α) = Lx`.
  calc
    ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
          (Polynomial.C x))
      =
        eTop
          (RatFunc.algEquivOfTranscendental α htrans
            (algebraMap (Polynomial (ResidueField S.A)) (RatFunc (ResidueField S.A))
              (Polynomial.C x))) := by
            simp [ratFunc_algEquiv_of_transcendental_generator, eTop]
    _ =
        eTop
          (Polynomial.aeval (IntermediateField.AdjoinSimple.gen (ResidueField S.A) α)
            (Polynomial.C x)) := by
          rw [RatFunc.algEquivOfTranscendental_algebraMap]
    _ = algebraMap (ResidueField S.A) Lx x := by
          simp [eTop]

/-- Helper for Lemma 10.159.1: after transporting coefficients from the maximal-ideal residue
field of `S.A` to the ordinary residue field of `S.A`, the transcendental generator equivalence
still sends constants to the expected scalars in `Lx`. -/
theorem ratFunc_transport_then_transcendental_generator_C
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (α : Lx),
      (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤) →
      (htrans : Transcendental (ResidueField S.A) α) →
      ∀ x : (maximalIdeal S.A).ResidueField,
      ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans
        (S.ratFunc_residueField_transport
          (algebraMap (Polynomial ((maximalIdeal S.A).ResidueField))
            (RatFunc ((maximalIdeal S.A).ResidueField)) (Polynomial.C x))) =
        algebraMap (ResidueField S.A) Lx (maximalIdealResidueFieldEquiv S.A x) := by
  intro α hgen htrans x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Rewrite the transported constant in `RatFunc (ResidueField S.A)`, then invoke the constant
  -- computation for the transcendental generator equivalence.
  rw [ratFunc_residueField_transport_C]
  simpa using
    ratFunc_algEquiv_of_transcendental_generator_C (S := S) hLLx α hgen htrans
      (maximalIdealResidueFieldEquiv S.A x)

/-- Helper for Lemma 10.159.1: a morphism of stages is an `R`-algebra map compatible with the
chosen embeddings of the stage residue fields into `K`. -/
structure Hom (hLM : L ≤ M)
    (S : ResidueExtensionStage (R := R) K L)
    (T : ResidueExtensionStage (R := R) K M) where
  toAlgHom : S.A →ₐ[R] T.A
  isLocalHom : IsLocalHom toAlgHom.toRingHom
  residue_comm :
      T.residueToAmbient.comp (ResidueField.map toAlgHom.toRingHom) =
        S.residueToAmbient

attribute [instance] ResidueExtensionStage.Hom.isLocalHom

/-- Helper for Lemma 10.159.1: stage morphisms compose by composing the underlying algebra maps,
and the residue-field compatibility squares compose with them. -/
noncomputable def Hom.comp
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    {U : ResidueExtensionStage (R := R) K N}
    {hLM : L ≤ M} {hMN : M ≤ N}
    (f : Hom hLM S T) (g : Hom hMN T U) :
    Hom (hLM.trans hMN) S U where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  isLocalHom := by
    -- Composition of local ring maps is again a local ring map.
    simpa using
      (inferInstance :
        IsLocalHom ((g.toAlgHom.toRingHom).comp f.toAlgHom.toRingHom))
  residue_comm := by
    -- Evaluate the commutative squares on residue-field elements and compose the two
    -- compatibility identities already stored in `f` and `g`.
    ext x
    calc
      U.residueToAmbient
          (ResidueField.map (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom) x)
          =
        U.residueToAmbient
          (ResidueField.map g.toAlgHom.toRingHom
            (ResidueField.map f.toAlgHom.toRingHom x)) := by
              simpa using
                (IsLocalRing.ResidueField.map_map
                  f.toAlgHom.toRingHom g.toAlgHom.toRingHom x)
      _ =
        T.residueToAmbient
          (ResidueField.map f.toAlgHom.toRingHom x) := by
            simpa [RingHom.comp_apply] using
              congrArg (fun φ : ResidueField T.A →+* K ↦ φ (ResidueField.map f.toAlgHom.toRingHom x))
                g.residue_comm
      _ = S.residueToAmbient x := by
            simpa [RingHom.comp_apply] using
              congrArg (fun φ : ResidueField S.A →+* K ↦ φ x) f.residue_comm

/-- Helper for Lemma 10.159.1: every stage carries the identity morphism to itself, providing
the base case for later prefix-system transition maps. -/
noncomputable def Hom.id
    (S : ResidueExtensionStage (R := R) K L) :
    Hom (show L ≤ L by exact le_rfl) S S where
  toAlgHom := AlgHom.id R S.A
  isLocalHom := by
    -- The identity of a local ring is a local ring homomorphism.
    simpa using (inferInstance : IsLocalHom (RingHom.id S.A))
  residue_comm := by
    -- The residue-field comparison square is definitionally the identity square.
    ext x
    simp

/-- Helper for Lemma 10.159.1: a stage morphism already commutes with the chosen residue-field
equivalences before passing to the ambient field `K`. This is the intrinsic square needed for the
later direct-limit comparison on residue fields. -/
theorem Hom.residueEquiv_comm
    {hLM : L ≤ M}
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    (f : Hom hLM S T) :
    T.residueEquiv.toRingHom.comp (ResidueField.map f.toAlgHom.toRingHom) =
      (IntermediateField.inclusion hLM).toRingHom.comp S.residueEquiv.toRingHom := by
  -- Forget the subtype structure and compare the two maps after evaluating in the ambient field.
  ext x
  simpa [ResidueExtensionStage.residueToAmbient, RingHom.comp_apply] using
    congrArg (fun φ : ResidueField S.A →+* K ↦ φ x) f.residue_comm

/-- Helper for Lemma 10.159.1: stage morphisms commute with the canonical quotient maps onto the
realized intermediate fields. This is the ring-level compatibility needed to pass the stage maps
to the later direct limit. -/
theorem Hom.toIntermediateFieldHom_comm
    {hLM : L ≤ M}
    {S : ResidueExtensionStage (R := R) K L}
    {T : ResidueExtensionStage (R := R) K M}
    (f : Hom hLM S T) :
    T.toIntermediateFieldHom.comp f.toAlgHom.toRingHom =
      (IntermediateField.inclusion hLM).toRingHom.comp S.toIntermediateFieldHom := by
  -- This is the intrinsic residue-field square for `f`, precomposed with the residue maps from
  -- the stage rings.
  ext a
  simpa [ResidueExtensionStage.toIntermediateFieldHom, RingHom.comp_apply,
    IsLocalRing.ResidueField.map_residue] using
    congrArg Subtype.val <|
      congrArg
        (fun φ : ResidueField S.A →+* M ↦ φ (residue S.A a))
        f.residueEquiv_comm

/-- Helper for Lemma 10.159.1: the trivial stage at the bottom intermediate field is the original
local ring `R` itself. This is the verified starting point of the transfinite construction. -/
noncomputable def base
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ResidueExtensionStage (R := R) K (⊥ : IntermediateField (ResidueField R) K) where
  A := R
  commRing := inferInstance
  localRing := inferInstance
  algebra := inferInstance
  localHom := by
    -- The identity map of a local ring is a local ring homomorphism.
    simpa using (inferInstance : IsLocalHom (RingHom.id R))
  flat := by
    -- The identity map is flat.
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  map_maximalIdeal := by
    -- The maximal ideal is unchanged under the identity algebra map.
    simp
  residueEquiv := by
    -- The residue field of the base stage is the bottom intermediate field.
    refine
      { toFun := fun x ↦
          ⟨algebraMap (ResidueField R) K x, by
            rw [IntermediateField.mem_bot]
            exact ⟨x, rfl⟩⟩
        invFun := fun x ↦ IntermediateField.botEquiv (ResidueField R) K x
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_
        map_add' := ?_ }
    · intro x
      exact IntermediateField.botEquiv_def (F := ResidueField R) (E := K) x
    · intro x
      change (IntermediateField.botEquiv (ResidueField R) K).symm
          (IntermediateField.botEquiv (ResidueField R) K x) = x
      exact (IntermediateField.botEquiv (ResidueField R) K).symm_apply_apply x
    · intro x y
      ext
      simp
    · intro x y
      ext
      simp

/-- Helper for Lemma 10.159.1: the ambient residue-field map of the base stage is the original
scalar map from `ResidueField R` into `K`. -/
theorem base_residueToAmbient_eq_algebraMap
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    (base (R := R) K).residueToAmbient = algebraMap (ResidueField R) K := by
  -- The base stage residue-field equivalence is the bottom-field embedding, so the induced ambient
  -- map is definitionally the original scalar map into `K`.
  ext x
  rfl

/-- Helper for Lemma 10.159.1: after transporting the stage residue-field algebra onto the
one-generator extension `L(x)`, the adjoined element still generates the whole field over the new
base residue field. This isolates the source proof's simple-extension input before the
transcendental/algebraic branch split. -/
theorem stage_adjoin_singleton_top
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (show L ≤ Lx by
          intro y hy
          change y ∈ IntermediateField.adjoin L ({x} : Set K)
          simpa using
            (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K))
              ⟨y, hy⟩))).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    ∃ α : Lx, IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤ := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx :=
    (IntermediateField.inclusion
      (show L ≤ Lx by
        intro y hy
        change y ∈ IntermediateField.adjoin L ({x} : Set K)
        simpa using
          (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K))
            ⟨y, hy⟩))
      ).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let α : Lx :=
    ⟨x, by
      change x ∈ IntermediateField.adjoin L ({x} : Set K)
      exact IntermediateField.mem_adjoin_of_mem (F := L) (S := ({x} : Set K)) (by simp)⟩
  refine ⟨α, ?_⟩
  let e : ResidueField S.A ≃ₐ[ResidueField S.A] L :=
    { toRingEquiv := S.residueEquiv
      commutes' := fun a ↦ rfl }
  have hL_top : IntermediateField.adjoin L ({α} : Set Lx) = ⊤ := by
    -- Every element of `Lx = L(x)` is a rational expression in the chosen generator `α`.
    apply eq_top_iff.mpr
    intro y hy
    exact
      IntermediateField.adjoin_induction (F := L) (s := ({x} : Set K))
        (p := fun z hz ↦
          (⟨z, by
            simpa [Lx] using hz⟩ : Lx) ∈ IntermediateField.adjoin L ({α} : Set Lx))
        (fun z hz ↦ by
          have hz' : z = x := by simpa using hz
          subst z
          simpa using
            (show α ∈ IntermediateField.adjoin L ({α} : Set Lx) from
              IntermediateField.mem_adjoin_of_mem (F := L) (S := ({α} : Set Lx)) (by simp)))
        (fun z ↦ by
          exact IntermediateField.algebraMap_mem (IntermediateField.adjoin L ({α} : Set Lx)) z)
        (fun z w hz hw hzmem hwmem ↦ by
          simpa using
            IntermediateField.add_mem (IntermediateField.adjoin L ({α} : Set Lx)) hzmem hwmem)
        (fun z hz hzmem ↦ by
          change ((⟨z, by simpa [Lx] using hz⟩ : Lx)⁻¹) ∈
              IntermediateField.adjoin L ({α} : Set Lx)
          exact IntermediateField.inv_mem (IntermediateField.adjoin L ({α} : Set Lx)) hzmem)
        (fun z w hz hw hzmem hwmem ↦ by
          simpa using
            IntermediateField.mul_mem (IntermediateField.adjoin L ({α} : Set Lx)) hzmem hwmem)
        y.2
  have htransport :
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) =
        (IntermediateField.adjoin L ({α} : Set Lx)).restrictScalars (ResidueField S.A) := by
    -- Transport the base field from `L` to `ResidueField S.A` through the stage residue-field
    -- identification, which was chosen as the scalar action on `L`.
    simpa using
      (IntermediateField.restrictScalars_adjoin_of_algEquiv
        (F := ResidueField S.A) (E := Lx) e rfl ({α} : Set Lx))
  rw [htransport, hL_top]
  simp

/-- Helper for Lemma 10.159.1: any local flat extension of a stage whose residue field is already
identified with a larger intermediate field packages into the next source-faithful stage. This
factors the common bookkeeping needed in both the transcendental and algebraic successor steps. -/
theorem of_local_extension
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [Algebra R B]
    [IsScalarTower R S.A B] [IsLocalHom (algebraMap S.A B)]
    (hflatB : (algebraMap S.A B).Flat)
    (hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B)
    (eB : ResidueField B ≃+* Lx)
    (hcompat :
      (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
        S.residueToAmbient) :
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx, Nonempty (Hom hLLx S T) := by
  let T : ResidueExtensionStage.{u, v, w} (R := R) K Lx :=
    { A := B
      commRing := inferInstance
      localRing := inferInstance
      algebra := inferInstance
      localHom := by
        -- The composite local map `R → S.A → B` is definitionally the ambient algebra map `R → B`.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using
          (inferInstance : IsLocalHom ((algebraMap S.A B).comp (algebraMap R S.A)))
      flat := by
        -- Flatness composes along the tower of local extensions.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using RingHom.Flat.comp S.flat hflatB
      map_maximalIdeal := by
        -- Push the maximal ideal through the old stage and then through the new local extension.
        calc
          Ideal.map (algebraMap R B) (maximalIdeal R)
              = Ideal.map ((algebraMap S.A B).comp (algebraMap R S.A)) (maximalIdeal R) := by
                  rw [IsScalarTower.algebraMap_eq R S.A B]
          _ = Ideal.map (algebraMap S.A B) (Ideal.map (algebraMap R S.A) (maximalIdeal R)) := by
                rw [Ideal.map_map]
          _ = Ideal.map (algebraMap S.A B) (maximalIdeal S.A) := by
                rw [S.map_maximalIdeal]
          _ = maximalIdeal B := hmapB
      residueEquiv := eB }
  refine ⟨T, ?_⟩
  refine ⟨{ toAlgHom := IsScalarTower.toAlgHom R S.A B, isLocalHom := ?_, residue_comm := ?_ }⟩
  · -- The canonical map in the tower is the given local ring map `S.A → B`.
    simpa using (inferInstance : IsLocalHom (algebraMap S.A B))
  -- The required residue-field square is exactly the compatibility hypothesis for the new stage.
  simpa [T, ResidueExtensionStage.residueToAmbient] using hcompat

/-- Helper for Lemma 10.159.1: package an explicit local extension on carrier `B` as the next
stage together with its canonical morphism from the previous stage. This keeps the successor-step
construction on the concrete ring `B` instead of asking elaboration to rediscover that carrier
through an existential witness. -/
theorem stage_and_hom_of_local_extension
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [Algebra R B]
    [IsScalarTower R S.A B] [IsLocalHom (algebraMap S.A B)]
    (hflatB : (algebraMap S.A B).Flat)
    (hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B)
    (eB : ResidueField B ≃+* Lx)
    (hcompat :
      (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
        S.residueToAmbient) :
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx,
      Nonempty (Hom hLLx S T) ∧ T.A = B := by
  let T : ResidueExtensionStage.{u, v, w} (R := R) K Lx :=
    { A := B
      commRing := inferInstance
      localRing := inferInstance
      algebra := inferInstance
      localHom := by
        -- The composite local map `R → S.A → B` is definitionally the ambient algebra map `R → B`.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using
          (inferInstance : IsLocalHom ((algebraMap S.A B).comp (algebraMap R S.A)))
      flat := by
        -- Flatness of the ambient map comes from composing the old stage with the new extension.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using RingHom.Flat.comp S.flat hflatB
      map_maximalIdeal := by
        -- Push the maximal ideal first through the old stage and then through the new local map.
        calc
          Ideal.map (algebraMap R B) (maximalIdeal R)
              = Ideal.map ((algebraMap S.A B).comp (algebraMap R S.A)) (maximalIdeal R) := by
                  rw [IsScalarTower.algebraMap_eq R S.A B]
          _ = Ideal.map (algebraMap S.A B) (Ideal.map (algebraMap R S.A) (maximalIdeal R)) := by
                rw [Ideal.map_map]
          _ = Ideal.map (algebraMap S.A B) (maximalIdeal S.A) := by
                rw [S.map_maximalIdeal]
          _ = maximalIdeal B := hmapB
      residueEquiv := eB }
  let f : Hom hLLx S T :=
    { toAlgHom := IsScalarTower.toAlgHom R S.A B
      isLocalHom := by
        -- The canonical map in the scalar tower is exactly the given local ring map `S.A → B`.
        simpa using (inferInstance : IsLocalHom (algebraMap S.A B))
      residue_comm := by
        -- The stored compatibility square already is the residue-field square required for `f`.
        simpa [T, ResidueExtensionStage.residueToAmbient] using hcompat }
  exact ⟨T, ⟨f⟩, rfl⟩

/-- Helper for Lemma 10.159.1: after transporting scalars along the residue-field identification
of a stage and then along an inclusion `L ≤ Lx`, the induced map into the ambient field `K` is
still the original residue-field comparison map of the stage. -/
theorem residueToAmbient_comp_algebraMap
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient := by
  -- Evaluate both maps on residue-field elements and unfold the chosen scalar tower.
  ext x
  rfl

/-- Helper for Lemma 10.159.1: evaluating the scalar-compatibility identity
`residueToAmbient_comp_algebraMap` on a residue-field element gives the pointwise formula used in
the transcendental successor branch. -/
theorem residueToAmbient_algebraMap_apply
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx) :
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    ∀ x : ResidueField S.A,
      Lx.val.toRingHom (algebraMap (ResidueField S.A) Lx x) = S.residueToAmbient x := by
  intro x
  -- With the scalar tower fixed as above, both sides are definitionally the same map into `K`.
  rfl

/-- Helper for Lemma 10.159.1: the simple extension `L(x)` always contains the previous stage
field `L` after restricting scalars back to `ResidueField R`. This is the canonical inclusion
used in the source proof's successor step. -/
theorem le_restrictScalars_adjoin_singleton
    (L : IntermediateField (ResidueField R) K) (x : K) :
    L ≤ (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R) := by
  -- Elements already in `L` lie in the field generated by adjoining `x`.
  intro y hy
  change y ∈ IntermediateField.adjoin L ({x} : Set K)
  simpa using
    (IntermediateField.adjoin.algebraMap_mem (F := L) (S := ({x} : Set K)) ⟨y, hy⟩)

/-- Helper for Lemma 10.159.1: over a field, the negation of transcendence is exactly
integrality. This is the field-theoretic dichotomy used when the source proof passes from a
simple extension to its transcendental/algebraic cases. -/
theorem isIntegral_of_not_transcendental
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {x : E} (h : ¬ Transcendental F x) :
    IsIntegral F x := by
  -- Over a field, algebraicity and integrality coincide.
  have halg : IsAlgebraic F x := by
    simpa [Transcendental] using h
  exact halg.isIntegral

/-- Helper for Lemma 10.159.1: the simple algebraic generator equivalence respects coefficients
from the base residue field after transporting along the top-field identification. -/
theorem adjoinRootEquivAdjoin_topEquiv_apply_algebraMap
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    [Algebra (ResidueField S.A) L]
    [Algebra L Lx]
    [Algebra (ResidueField S.A) Lx]
    [IsScalarTower (ResidueField S.A) L Lx]
    (α : Lx)
    (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (hint : IsIntegral (ResidueField S.A) α)
    (x : ResidueField S.A) :
    let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
      (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
    eTop
        ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint)
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)) x)) =
      algebraMap (ResidueField S.A) Lx x := by
  let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  calc
    eTop
        ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint)
          (algebraMap (ResidueField S.A)
            (AdjoinRoot (minpoly (ResidueField S.A) α)) x))
      =
        eTop
          (algebraMap (ResidueField S.A)
            (IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx)) x) := by
          rw [AlgEquiv.commutes]
    _ = algebraMap (ResidueField S.A) Lx x := by
          simpa using eTop.commutes x

/-- Helper for Lemma 10.159.1: the algebraic `AdjoinRoot` model carries the same map into the
ambient field `K` as the previous stage, once its residue field is identified with the simple
extension generated by `α`. -/
theorem algebraic_local_extension_compat
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    [Algebra (ResidueField S.A) L]
    [Algebra L Lx]
    [Algebra (ResidueField S.A) Lx]
    [IsScalarTower (ResidueField S.A) L Lx]
    (hambient :
      Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient)
    (α : Lx)
    (hgen : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (hint : IsIntegral (ResidueField S.A) α)
    (P : Polynomial (ResidueField S.A))
    (hP : P = minpoly (ResidueField S.A) α)
    (hPirred : Irreducible P)
    (f : Polynomial S.A)
    (hf : f.Monic)
    (hfmap : f.map (algebraMap S.A (ResidueField S.A)) = P) :
    letI : Fact (Irreducible P) := Fact.mk hPirred
    letI : IsLocalRing (AdjoinRoot f) :=
      adjoinRoot_isLocalRing_of_irreducible_reduction S.A f hf P hfmap
    letI : IsLocalHom (algebraMap S.A (AdjoinRoot f)) :=
      adjoinRoot_isLocalHom_of_irreducible_reduction S.A f P hfmap
    ∃ eB : ResidueField (AdjoinRoot f) ≃+* Lx,
      (Lx.val.toRingHom.comp eB.toRingHom).comp
          (ResidueField.map (algebraMap S.A (AdjoinRoot f))) =
        S.residueToAmbient := by
  -- Rewrite immediately to the canonical minimal polynomial so every later map sees the same
  -- simple algebraic extension.
  subst hP
  letI : Fact (Irreducible (minpoly (ResidueField S.A) α)) := Fact.mk hPirred
  letI : IsLocalRing (AdjoinRoot f) :=
    adjoinRoot_isLocalRing_of_irreducible_reduction
      S.A f hf (minpoly (ResidueField S.A) α) hfmap
  letI : IsLocalHom (algebraMap S.A (AdjoinRoot f)) :=
    adjoinRoot_isLocalHom_of_irreducible_reduction
      S.A f (minpoly (ResidueField S.A) α) hfmap
  let eTop : IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) ≃ₐ[ResidueField S.A] Lx :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  let eAdjoin :
      AdjoinRoot (minpoly (ResidueField S.A) α) ≃+* Lx :=
    ((IntermediateField.adjoinRootEquivAdjoin (ResidueField S.A) hint).trans eTop).toRingEquiv
  let eB : ResidueField (AdjoinRoot f) ≃+* Lx :=
    (adjoinRoot_residueField_equiv_of_irreducible_reduction
      S.A f (minpoly (ResidueField S.A) α) hfmap).trans eAdjoin
  refine ⟨eB, ?_⟩
  have hcoeff :
      (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α))) =
        S.residueToAmbient := by
    -- The algebraic generator identification sends coefficients to coefficients in `Lx`, and
    -- `hambient` identifies those with the old stage map into `K`.
    calc
      (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)))
        = Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) := by
            ext x
            apply congrArg Subtype.val
            simpa [eAdjoin, eTop, RingHom.comp_apply] using
              (adjoinRootEquivAdjoin_topEquiv_apply_algebraMap
                (S := S) (Lx := Lx) α hgen hint x)
      _ = S.residueToAmbient := hambient
  have hres :
      (adjoinRoot_residueField_equiv_of_irreducible_reduction
          S.A f (minpoly (ResidueField S.A) α) hfmap).toRingHom.comp
          (ResidueField.map (algebraMap S.A (AdjoinRoot f))) =
        algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α)) := by
    -- The explicit `AdjoinRoot` residue-field equivalence already computes the coefficient map.
    simpa using
      (adjoinRoot_residueField_equiv_of_irreducible_reduction_comp_residueFieldMap
        S.A f (minpoly (ResidueField S.A) α) hfmap)
  -- Compose the coefficient computation for the explicit `AdjoinRoot` residue field with the
  -- simple-generator identification into `Lx`.
  calc
    (Lx.val.toRingHom.comp eB.toRingHom).comp
        (ResidueField.map (algebraMap S.A (AdjoinRoot f)))
      =
        (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          ((adjoinRoot_residueField_equiv_of_irreducible_reduction
            S.A f (minpoly (ResidueField S.A) α) hfmap).toRingHom.comp
            (ResidueField.map (algebraMap S.A (AdjoinRoot f)))) := by
              rfl
    _ =
        (Lx.val.toRingHom.comp eAdjoin.toRingHom).comp
          (algebraMap (ResidueField S.A) (AdjoinRoot (minpoly (ResidueField S.A) α))) := by
            rw [hres]
    _ = S.residueToAmbient := hcoeff

/-- Helper for Lemma 10.159.1: the canonical transcendental localization over a stage `S`
identifies its residue field with the simple transcendental extension generated by `α`, and this
identification preserves the ambient residue-field map into `K`. -/
theorem transcendental_local_extension_compat_canonical
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K} (hLLx : L ≤ Lx)
    (α : Lx)
    (hgen :
      letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
      letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
      letI : Algebra (ResidueField S.A) Lx :=
        RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
      letI : IsScalarTower (ResidueField S.A) L Lx :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤)
    (htrans :
      letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
      letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
      letI : Algebra (ResidueField S.A) Lx :=
        RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
      letI : IsScalarTower (ResidueField S.A) L Lx :=
        IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      Transcendental (ResidueField S.A) α) :
    let J : Ideal (Polynomial S.A) := Ideal.map (Polynomial.C) (maximalIdeal S.A)
    let B : Type _ := Localization.AtPrime J
    ∃ eB : ResidueField B ≃+* Lx,
      ∀ a : S.A,
        Lx.val.toRingHom (eB (residue B (algebraMap S.A B a))) =
          S.residueToAmbient (residue S.A a) := by
  let J : Ideal (Polynomial S.A) := Ideal.map (Polynomial.C) (maximalIdeal S.A)
  let B : Type _ := Localization.AtPrime J
  letI : CommRing B := inferInstance
  letI : IsLocalRing B := inferInstance
  letI : Algebra S.A B := inferInstance
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eRat : RatFunc (ResidueField S.A) ≃+* Lx :=
    (ratFunc_algEquiv_of_transcendental_generator (S := S) hLLx α hgen htrans).toRingEquiv
  let eB : ResidueField B ≃+* Lx :=
    (localization_residueField_equiv S.A).trans (S.ratFunc_residueField_transport.trans eRat)
  refine ⟨eB, ?_⟩
  intro a
  -- Route correction: rewrite the canonical localization residue class through the residue-field
  -- model and only then evaluate the transported constant in `K`.
  calc
    Lx.val.toRingHom (eB (residue B (algebraMap S.A B a)))
        =
      Lx.val.toRingHom
        (eRat
          (S.ratFunc_residueField_transport
            (localization_residueField_equiv S.A
              (residue B (algebraMap S.A B a))))) := by
              rfl
    _ =
      Lx.val.toRingHom
        (eRat
          (S.ratFunc_residueField_transport
            (algebraMap (Polynomial ((maximalIdeal S.A).ResidueField))
              (RatFunc ((maximalIdeal S.A).ResidueField))
              (Polynomial.C (algebraMap S.A (maximalIdeal S.A).ResidueField a))))) := by
                rw [localization_residueField_equiv_apply_residue]
    _ =
      Lx.val.toRingHom
        (eRat
          (algebraMap (Polynomial (ResidueField S.A))
            (RatFunc (ResidueField S.A))
            (Polynomial.C
              (maximalIdealResidueFieldEquiv S.A
                (algebraMap S.A (maximalIdeal S.A).ResidueField a))))) := by
                  rw [ratFunc_residueField_transport_C]
    _ =
      Lx.val.toRingHom
        (algebraMap (ResidueField S.A) Lx
          (maximalIdealResidueFieldEquiv S.A
            (algebraMap S.A (maximalIdeal S.A).ResidueField a))) := by
              simpa [eRat] using
                congrArg Lx.val.toRingHom
                  (ratFunc_algEquiv_of_transcendental_generator_C
                    (S := S) hLLx α hgen htrans
                    (maximalIdealResidueFieldEquiv S.A
                      (algebraMap S.A (maximalIdeal S.A).ResidueField a)))
    _ =
      Lx.val.toRingHom (algebraMap (ResidueField S.A) Lx (residue S.A a)) := by
          rw [maximalIdealResidueFieldEquiv_apply_algebraMap]
    _ = S.residueToAmbient (residue S.A a) := by
          -- Finish by the pointwise scalar-compatibility formula just proved above.
          simpa using
            residueToAmbient_algebraMap_apply (S := S) (Lx := Lx) hLLx (residue S.A a)

/-- Helper for Lemma 10.159.1: a pointwise residue-class computation for a local extension over
`S.A` upgrades to the full residue-field square needed to package the next stage. -/
theorem transcendental_residue_class_bridge
    (S : ResidueExtensionStage (R := R) K L)
    {Lx : IntermediateField (ResidueField R) K}
    (B : Type w) [CommRing B] [IsLocalRing B] [Algebra S.A B] [IsLocalHom (algebraMap S.A B)]
    (eB : ResidueField B ≃+* Lx)
    (hclass :
      ∀ a : S.A,
        Lx.val.toRingHom (eB (residue B (algebraMap S.A B a))) =
          S.residueToAmbient (residue S.A a)) :
    (Lx.val.toRingHom.comp eB.toRingHom).comp (ResidueField.map (algebraMap S.A B)) =
      S.residueToAmbient := by
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  -- Reduce the ring-hom equality to residue classes of elements of `S.A`.
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
  exact hclass a

/-- Helper for Lemma 10.159.1: adjoining one element `x : K` to the intermediate field realized
by a stage `S` produces the next source-faithful stage together with its canonical morphism from
`S`. This packages the algebraic/transcendental successor split from the source proof. -/
theorem extend_stage_by_element
    (S : ResidueExtensionStage.{u, v, w} (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lx,
      Nonempty (Hom (le_restrictScalars_adjoin_singleton (R := R) L x) S T) := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  let hLLx : L ≤ Lx := le_restrictScalars_adjoin_singleton (R := R) L x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨α, hgen⟩ := stage_adjoin_singleton_top (S := S) x
  by_cases htrans : Transcendental (ResidueField S.A) α
  · let J : Ideal (Polynomial S.A) := Ideal.map (Polynomial.C) (maximalIdeal S.A)
    let B : Type w := Localization.AtPrime J
    letI : CommRing B := inferInstance
    letI : IsLocalRing B := inferInstance
    letI : Algebra S.A B := inferInstance
    letI : Algebra R B := inferInstance
    letI : IsScalarTower R S.A B := inferInstance
    letI : IsLocalHom (algebraMap S.A B) := localization_isLocalHom S.A
    have hflatB : (algebraMap S.A B).Flat := by
      -- The transcendental successor ring is a localization, hence flat over the previous stage.
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    have hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B :=
      localization_map_maximalIdeal_eq_maximalIdeal S.A
    obtain ⟨eB, hclass⟩ :=
      transcendental_local_extension_compat_canonical
        (S := S) (Lx := Lx) hLLx α hgen htrans
    have hcompat :
        (Lx.val.toRingHom.comp eB.toRingHom).comp
            (ResidueField.map (algebraMap S.A B)) =
          S.residueToAmbient :=
      transcendental_residue_class_bridge (S := S) (B := B) eB hclass
    -- Package the canonical localization branch as the next stage over the simple extension `L(x)`.
    simpa [Lx] using
      of_local_extension (S := S) (Lx := Lx) hLLx B hflatB hmapB eB hcompat
  · have hint : IsIntegral (ResidueField S.A) α :=
      isIntegral_of_not_transcendental htrans
    let P : Polynomial (ResidueField S.A) := minpoly (ResidueField S.A) α
    have hPirred : Irreducible P := minpoly.irreducible hint
    obtain ⟨f, hf, hfmap⟩ :=
      exists_monic_lift_of_residueField S.A P (minpoly.monic hint)
    let B : Type w := AdjoinRoot f
    letI : CommRing B := inferInstance
    letI : Algebra S.A B := inferInstance
    letI : Algebra R B := inferInstance
    letI : IsScalarTower R S.A B := inferInstance
    letI : Fact (Irreducible P) := Fact.mk hPirred
    letI : IsLocalRing B :=
      adjoinRoot_isLocalRing_of_irreducible_reduction S.A f hf P hfmap
    letI : IsLocalHom (algebraMap S.A B) :=
      adjoinRoot_isLocalHom_of_irreducible_reduction S.A f P hfmap
    letI : Module.Free S.A B := hf.free_adjoinRoot
    have hflatB : (algebraMap S.A B).Flat := by
      -- A monic `AdjoinRoot` algebra is free over the coefficient ring, hence flat.
      rw [RingHom.flat_algebraMap_iff]
      infer_instance
    have hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B :=
      adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction S.A f P hfmap
    have hambient :
        Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) =
          S.residueToAmbient :=
      residueToAmbient_comp_algebraMap (S := S) (Lx := Lx) hLLx
    obtain ⟨eB, hcompat⟩ :=
      algebraic_local_extension_compat
        (S := S) (Lx := Lx) hambient α hgen hint P rfl hPirred f hf hfmap
    -- Package the `AdjoinRoot` branch as the next stage over the same simple extension `L(x)`.
    simpa [Lx] using
      of_local_extension (S := S) (Lx := Lx) hLLx B hflatB hmapB eB hcompat

/-- Helper for Lemma 10.159.1: on a top stage, the ambient residue-field map is just the chosen
residue-field equivalence followed by the canonical identification with `K`. -/
theorem top_residueToAmbient_eq
    (T : ResidueExtensionStage (R := R) K (⊤ : IntermediateField (ResidueField R) K)) :
    T.residueToAmbient =
      IntermediateField.topEquiv.toRingHom.comp T.residueEquiv.toRingHom := by
  -- Unfolding the definition shows that the inclusion of the top intermediate field is the
  -- canonical equivalence to `K`.
  ext x
  rfl

end ResidueExtensionStage

/-- Helper for Lemma 10.159.1: the well-ordered element of `K` with ordinal rank `α`. -/
noncomputable def wellOrder_prefixElement
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K)) : K :=
  Ordinal.enum WellOrderingRel (Ordinal.ToType.mk ⟨α, hα⟩)

/-- Helper for Lemma 10.159.1: the prefix set at ordinal `α` consists of all well-ordered
elements of `K` whose rank is `< α`. -/
noncomputable def wellOrder_prefixSet
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) : Set K :=
  Set.range fun β : {γ // γ < α} ↦
    wellOrder_prefixElement (R := R) (K := K) (hα := lt_of_lt_of_le β.2 hα)

/-- Helper for Lemma 10.159.1: the prefix field at ordinal `α` is generated by all well-ordered
elements of rank `< α`. This is the field-theoretic side of the source proof's transfinite
construction. -/
noncomputable def wellOrder_prefixField
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    IntermediateField (ResidueField R) K :=
  IntermediateField.adjoin (ResidueField R) (wellOrder_prefixSet (R := R) (K := K) α hα)

/-- Helper for Lemma 10.159.1: the initial well-ordered prefix field is the bottom intermediate
field, because there are no elements of rank `< 0`. -/
theorem wellOrder_prefixField_zero
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    wellOrder_prefixField (R := R) (K := K) 0
      (show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) by simp) = ⊥ := by
  -- The prefix set at `0` is empty, so adjoining it gives the bottom intermediate field.
  have hset :
      wellOrder_prefixSet (R := R) (K := K) 0
        (show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) by simp) = ∅ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨β, _⟩
      exact (not_lt_of_ge (show (0 : Ordinal) ≤ β.1 by simp)) β.2
    · intro hx
      cases hx
  rw [wellOrder_prefixField, hset, IntermediateField.adjoin_empty]

/-- Helper for Lemma 10.159.1: passing from ordinal `α` to `α + 1` adds exactly the next
well-ordered element of `K` to the prefix set. -/
theorem wellOrder_prefixSet_succ
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K)) :
    wellOrder_prefixSet (R := R) (K := K) (α + 1) (Order.succ_le_of_lt hα) =
      insert (wellOrder_prefixElement (R := R) (K := K) hα)
        (wellOrder_prefixSet (R := R) (K := K) α (le_of_lt hα)) := by
  -- A rank `< α + 1` is either exactly `α` or already `< α`.
  ext x
  constructor
  · intro hx
    rcases hx with ⟨⟨γ, hγ⟩, rfl⟩
    have hle : γ ≤ α := by
      simpa [Order.lt_succ_iff] using hγ
    rcases lt_or_eq_of_le hle with hlt | hEq
    · right
      refine ⟨⟨γ, hlt⟩, ?_⟩
      simp [wellOrder_prefixElement]
    · left
      cases hEq
      simp [wellOrder_prefixElement]
  · intro hx
    rcases hx with rfl | hx
    · refine ⟨⟨α, Order.lt_succ α⟩, ?_⟩
      simp [wellOrder_prefixElement]
    · rcases hx with ⟨⟨γ, hγ⟩, rfl⟩
      refine ⟨⟨γ, ?_⟩, ?_⟩
      · simpa [Order.lt_succ_iff] using hγ.le
      · simp [wellOrder_prefixElement]

/-- Helper for Lemma 10.159.1: the well-ordered prefix fields form an increasing chain. This is
the field-level compatibility needed before one packages the stage recursion above them. -/
theorem wellOrder_prefixField_mono
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α β : Ordinal}
    (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hβ : β ≤ Ordinal.type (@WellOrderingRel K))
    (hαβ : α ≤ β) :
    wellOrder_prefixField (R := R) (K := K) α hα ≤
      wellOrder_prefixField (R := R) (K := K) β hβ := by
  -- Every generator appearing before stage `α` also appears before stage `β`.
  refine IntermediateField.adjoin.mono
    (F := ResidueField R)
    (S := wellOrder_prefixSet (R := R) (K := K) α hα)
    (T := wellOrder_prefixSet (R := R) (K := K) β hβ) ?_
  rintro x ⟨γ, rfl⟩
  exact ⟨⟨γ.1, lt_of_lt_of_le γ.2 hαβ⟩, rfl⟩

/-- Helper for Lemma 10.159.1: at a limit ordinal, the prefix field is the supremum of the
earlier prefix fields. This is the exact field-level limit rewrite used in the source proof's
direct-limit stage. -/
theorem wellOrder_prefixField_limit_eq_iSup_lt
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal}
    (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α) :
    wellOrder_prefixField (R := R) (K := K) α hα =
      ⨆ β : Set.Iio α,
        wellOrder_prefixField (R := R) (K := K) β.1
          (le_trans (le_of_lt β.2) hα) := by
  -- At a limit stage, each generator already appears strictly earlier, and conversely every
  -- earlier stage sits inside the limit stage by monotonicity.
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x ⟨γ, rfl⟩
    let β : Set.Iio α := ⟨γ.1 + 1, hlimit.succ_lt γ.2⟩
    have hxβ :
        wellOrder_prefixElement (R := R) (K := K)
            (hα := lt_of_lt_of_le γ.2 hα) ∈
          wellOrder_prefixField (R := R) (K := K) β.1
            (le_trans (le_of_lt β.2) hα) := by
      exact IntermediateField.subset_adjoin (ResidueField R)
        (wellOrder_prefixSet (R := R) (K := K) β.1 (le_trans (le_of_lt β.2) hα))
        ⟨⟨γ.1, by exact Order.lt_succ γ.1⟩, rfl⟩
    exact
      (le_iSup
        (fun β : Set.Iio α ↦
          wellOrder_prefixField (R := R) (K := K) β.1
            (le_trans (le_of_lt β.2) hα))
        β) hxβ
  · refine iSup_le fun β ↦ ?_
    exact wellOrder_prefixField_mono (R := R) (K := K)
      (le_trans (le_of_lt β.2) hα) hα β.2.le

/-- Helper for Lemma 10.159.1: the successor prefix field is obtained by adjoining the unique new
well-ordered element at rank `α` to the previous prefix field. This is the exact field-theoretic
rewrite used in the source proof's successor stage. -/
theorem wellOrder_prefixField_succ
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K)) :
    wellOrder_prefixField (R := R) (K := K) (α + 1) (Order.succ_le_of_lt hα) =
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R) := by
  -- Rewrite the successor prefix set as one new element adjoined to the previous prefix field.
  rw [wellOrder_prefixField, wellOrder_prefixSet_succ (R := R) (K := K) (hα := hα)]
  calc
    IntermediateField.adjoin (ResidueField R)
        ({wellOrder_prefixElement (R := R) (K := K) hα} ∪
          wellOrder_prefixSet (R := R) (K := K) α (le_of_lt hα))
      =
        IntermediateField.adjoin (ResidueField R)
          (wellOrder_prefixSet (R := R) (K := K) α (le_of_lt hα) ∪
            ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)) := by
            rw [Set.union_comm]
    _ =
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R) := by
            simpa [wellOrder_prefixField] using
              (IntermediateField.adjoin_adjoin_left
                (F := ResidueField R)
                (S := wellOrder_prefixSet (R := R) (K := K) α (le_of_lt hα))
                (T := ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K))).symm

/-- Helper for Lemma 10.159.1: the terminal well-ordered prefix field is all of `K`. This
discharges the source proof's claim that the transfinite recursion eventually reaches the whole
residue-field extension. -/
theorem wellOrder_prefixField_top
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    wellOrder_prefixField (R := R) (K := K) (Ordinal.type (@WellOrderingRel K)) le_rfl = ⊤ := by
  -- Every element of `K` appears at its own well-order rank, so the full prefix field is all of
  -- `K`.
  apply eq_top_iff.mpr
  intro x hx
  have hxmem :
      x ∈ wellOrder_prefixSet (R := R) (K := K) (Ordinal.type (@WellOrderingRel K)) le_rfl := by
    refine ⟨⟨Ordinal.typein WellOrderingRel x, Ordinal.typein_lt_type WellOrderingRel x⟩, ?_⟩
    simpa [wellOrder_prefixElement] using (Ordinal.enum_typein WellOrderingRel x)
  exact IntermediateField.subset_adjoin (ResidueField R)
    (wellOrder_prefixSet (R := R) (K := K) (Ordinal.type (@WellOrderingRel K)) le_rfl) hxmem

/-- Helper for Lemma 10.159.1: the well-ordered prefix field does not depend on the chosen proof
that the stage ordinal lies below the ambient well-order type. This keeps the later recursive
packaging stable under proof irrelevance. -/
@[simp] theorem wellOrder_prefixField_proof_irrel
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal}
    (h₁ h₂ : α ≤ Ordinal.type (@WellOrderingRel K)) :
    wellOrder_prefixField (R := R) (K := K) α h₁ =
      wellOrder_prefixField (R := R) (K := K) α h₂ := by
  -- The ordinal bound witnesses live in a subsingleton, so the generated prefix field is the same.
  cases Subsingleton.elim h₁ h₂
  rfl

/-- Helper for Lemma 10.159.1: the bottom intermediate field sits inside every well-ordered
prefix field. This is the field-side inclusion attached to the canonical base-stage map. -/
theorem base_le_prefixField
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    (⊥ : IntermediateField (ResidueField R) K) ≤
      wellOrder_prefixField (R := R) (K := K) α hα := by
  -- Compare the zero prefix field with the `α`-prefix field and rewrite the zero stage as `⊥`.
  simpa [wellOrder_prefixField_zero (R := R) (K := K)] using
    (wellOrder_prefixField_mono (R := R) (K := K)
      (show (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K) from bot_le) hα
      (show (0 : Ordinal) ≤ α from bot_le))

/-- Helper for Lemma 10.159.1: the zero prefix field is already realized by the base stage, after
identifying `wellOrder_prefixField 0` with `⊥`. This verifies the starting point of the source
proof's transfinite construction. -/
theorem exists_zero_prefix_stage
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, v, u} (R := R) K
        (⊥ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by rfl)
          (ResidueExtensionStage.base (R := R) K) T) := by
  refine ⟨?_, ?_⟩
  · -- The base stage already realizes the bottom intermediate field.
    exact ResidueExtensionStage.base (R := R) K
  · refine ⟨?_⟩
    -- The comparison map is the identity on the base stage.
    simpa using (ResidueExtensionStage.Hom.id (ResidueExtensionStage.base (R := R) K))

/-- Helper for Lemma 10.159.1: once a prefix field at stage `α` is realized by a source-faithful
stage, adjoining the next well-ordered element yields a realizing stage for the corresponding
one-element extension. Combined with `wellOrder_prefixField_succ`, this is exactly the solved
successor case of the source proof. -/
theorem exists_adjoin_singleton_stage_of_prefix_stage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (S : ResidueExtensionStage.{u, v, w} (R := R) K
      (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))) :
    let Lsucc : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, v, w} (R := R) K Lsucc,
      Nonempty
        (ResidueExtensionStage.Hom
          (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R)
            (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
            (wellOrder_prefixElement (R := R) (K := K) hα))
          S T) := by
  -- This is exactly the one-element extension theorem specialized to the next well-ordered
  -- generator of `K`.
  exact ResidueExtensionStage.extend_stage_by_element
    (S := S)
    (wellOrder_prefixElement (R := R) (K := K) hα)

/-- Helper for Lemma 10.159.1: the closed prefix field indexed by `β ≤ α`. This keeps the later
chain packaging from repeatedly re-elaborating the same proof-dependent field expression. -/
noncomputable def closedPrefixField
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (β : Set.Iic α) :
    IntermediateField (ResidueField R) K :=
  wellOrder_prefixField (R := R) (K := K) β.1 (le_trans β.2 hα)

/-- Helper for Lemma 10.159.1: the open prefix field indexed by `β < α`. This is the field
appearing in the limit-stage cover statement. -/
noncomputable def openPrefixField
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (β : Set.Iio α) :
    IntermediateField (ResidueField R) K :=
  wellOrder_prefixField (R := R) (K := K) β.1 (le_trans β.2.le hα)

/-- Helper for Lemma 10.159.1: a coherent prefix chain stores, for every ordinal stage up to `α`,
a realizing local flat stage together with compatible transition morphisms. This is the exact
payload needed to feed the source proof's direct-limit construction at limit ordinals. -/
structure PrefixStageChain
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) where
  stage :
    (β : Set.Iic α) →
      ResidueExtensionStage.{u, v, max u v} (R := R) K (closedPrefixField (R := R) K hα β)
  hom :
    {β γ : Set.Iic α} →
      (hβγ : β ≤ γ) →
        ResidueExtensionStage.Hom.{u, v, max u v, max u v}
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2 hα) (le_trans γ.2 hα) hβγ)
          (stage β) (stage γ)
  hom_id :
    ∀ β,
      (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (stage β).A
  hom_comp :
    ∀ {β γ δ : Set.Iic α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
      ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
          (hom (β := β) (γ := γ) hβγ).toAlgHom) =
        (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom

/-- Helper for Lemma 10.159.1: the stage indexed by the top ordinal in a coherent prefix chain is
the distinguished realizing object for the terminal prefix field of that chain. -/
noncomputable def PrefixStageChain.topStage
    {K : Type v} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    (C : PrefixStageChain (R := R) K α hα) :
    ResidueExtensionStage.{u, v, max u v} (R := R) K
      (closedPrefixField (R := R) K hα ⟨α, show α ≤ α from le_rfl⟩) :=
  C.stage ⟨α, show α ≤ α from le_rfl⟩

/-- Helper for Lemma 10.159.1: at a limit ordinal, every element of the prefix field already
lies in the supremum of the earlier prefix stages. This is the direct field-side rewrite used
before extracting an actual stage witness. -/
theorem mem_limit_prefixField_iSup_lt
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    {y : K}
    (hy : y ∈ wellOrder_prefixField (R := R) (K := K) α hα) :
    y ∈
      ⨆ β : Set.Iio α, openPrefixField (R := R) K hα β := by
  -- Rewrite the limit prefix field as the supremum of the earlier stages.
  simpa [wellOrder_prefixField_limit_eq_iSup_lt (R := R) (K := K) hα hlimit] using hy

/-- Helper for Lemma 10.159.1: at a limit ordinal, every element of the prefix field already
appears in one earlier prefix stage. This is the field-side union statement needed for the later
direct-limit residue-field comparison. -/
theorem limit_prefixField_stagewise_cover
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (y : wellOrder_prefixField (R := R) (K := K) α hα) :
    ∃ β : Set.Iio α,
      ∃ yβ : openPrefixField (R := R) K hα β,
        IntermediateField.inclusion
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) hα β.2.le) yβ =
          y := by
  have hySup :
      (y : K) ∈ ⨆ β : Set.Iio α, openPrefixField (R := R) K hα β :=
    mem_limit_prefixField_iSup_lt (R := R) (K := K) hα hlimit y.2
  -- Compactness of `IntermediateField` reduces membership in the limit supremum to finitely many
  -- earlier stages.
  obtain ⟨s, hs⟩ := IntermediateField.exists_finset_of_mem_iSup hySup
  by_cases hsne : s.Nonempty
  · let β : Set.Iio α := s.max' hsne
    have hs_le :
        (⨆ γ ∈ s, openPrefixField (R := R) K hα γ) ≤
          openPrefixField (R := R) K hα β := by
      -- Collapse the finite union to the maximal earlier stage using monotonicity of the prefix
      -- fields along the well-order.
      refine iSup₂_le fun γ hγ ↦ ?_
      exact wellOrder_prefixField_mono (R := R) (K := K)
        (le_trans γ.2.le hα) (le_trans β.2.le hα) (Finset.le_max' s γ hγ)
    have hyβ :
        (y : K) ∈ openPrefixField (R := R) K hα β :=
      hs_le hs
    refine ⟨β, ⟨⟨(y : K), hyβ⟩, ?_⟩⟩
    -- Both subtype elements have the same underlying element of `K`, so the inclusion is
    -- definitionally the original `y`.
    ext
    rfl
  · obtain ⟨β, hβ⟩ := hlimit.nonempty_Iio
    have hsempty : s = ∅ := by
      simpa using hsne
    have hybot : (y : K) ∈ (⊥ : IntermediateField (ResidueField R) K) := by
      -- If the finite support is empty, the element already lies in the base field, hence in
      -- every earlier prefix stage.
      simpa [hsempty] using hs
    have hyβ :
        (y : K) ∈ openPrefixField (R := R) K hα ⟨β, hβ⟩ :=
      base_le_prefixField (R := R) (K := K) (hα := le_trans hβ.le hα) hybot
    refine ⟨⟨β, hβ⟩, ⟨⟨(y : K), hyβ⟩, ?_⟩⟩
    -- Route correction: even the empty-support case follows the source route, because the base
    -- field sits inside every earlier prefix stage.
    ext
    rfl

/- Domain-style sampling:
* primary domain: local commutative algebra of flat local extensions and induced residue-field
  maps;
* source-facing layer: the existential construction of a flat local `R`-algebra with prescribed
  residue field `K`;
* core/canonical owners inspected:
  - `(algebraMap R S).Flat` for flatness of an `R`-algebra, matching the chapter-wide ring-map
    flatness API;
  - `IsLocalHom (algebraMap R S)` and `IsLocalRing.ResidueField.map` for local maps and residue
    fields;
  - `IsHenselizationOf R S` and `IsStrictHenselizationOf R S` in Lemmas `10.155.1` and `10.155.2`
    as examples where extra packaging carries real additional mathematics.

Owner-abstraction decision: there is no upstream owner object for arbitrary flat local extensions
with prescribed residue field, so this item should stay as a source-facing existential built from
the canonical owners above rather than introducing a new wrapper structure.

Primitive data vs derived API: the public outputs are exactly the extension ring, its `R`-algebra
structure, the local and flat ring-map conditions, the maximal-ideal compatibility, and the
residue-field equivalence. The module-level flatness view is derived from the ring-map owner, so
it should not remain the primitive public field. No extra package, chosen presentation, or
compatibility wrapper should be made public.
-/

-- Proof sketch: construct the extension first for a monogenic residue-field extension by either
-- localizing `R[X]` at `maximalIdeal R` in the transcendental case or adjoining a root of a lifted
-- minimal polynomial in the algebraic case. Then build the general extension by transfinite
-- recursion along a well-ordering of `K`, taking directed colimits at limit stages; flatness is
-- preserved by the colimit construction, the map remains local, and the residue field grows to `K`.
/-- Helper for Lemma 10.159.1: the source proof's transfinite recursion should eventually produce
the stage over the terminal prefix field `⊤`, together with the canonical morphism from the base
stage. The remaining unresolved work is the limit-stage direct-limit package for
`PrefixStageChain`. -/
theorem exists_top_stage_via_well_order_recursion
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) T) := by
  -- TODO: recurse on ordinals with `PrefixStageChain`, using `exists_zero_prefix_stage` and
  -- `exists_adjoin_singleton_stage_of_prefix_stage` for the zero and successor steps, and a
  -- direct-limit constructor at limit ordinals whose field-side surjectivity is controlled by
  -- `limit_prefixField_stagewise_cover`.
  sorry

/-- Helper for Lemma 10.159.1: once the source-faithful recursion has produced a stage whose
intermediate field is `⊤` together with the canonical map from the base stage, the public theorem
is just an unpacking step. -/
theorem exists_flat_localAlgebra_with_residueField_equiv_of_top_stage
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (hT :
      ∃ T : ResidueExtensionStage.{u, v, max u v} (R := R) K
          (⊤ : IntermediateField (ResidueField R) K),
        Nonempty
          (ResidueExtensionStage.Hom
            (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
            (ResidueExtensionStage.base (R := R) K) T)) :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (_ : ResidueField R' ≃ₐ[ResidueField R] K),
        Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R' := by
  rcases hT with ⟨T, ⟨f⟩⟩
  let eRing : ResidueField T.A ≃+* K :=
    T.residueEquiv.trans IntermediateField.topEquiv.toRingEquiv
  refine ⟨T.A, inferInstance, inferInstance, inferInstance, inferInstance, T.flat, ?_, T.map_maximalIdeal⟩
  refine
    { toRingEquiv := eRing
      commutes' := ?_ }
  intro a
  -- The residue-field square for the morphism from the base stage identifies the induced map on
  -- `ResidueField R` with the original scalar map into `K`.
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective a
  have hcomm :
      T.residueToAmbient
          (ResidueField.map (algebraMap R T.A) (residue R r)) =
        algebraMap (ResidueField R) K (residue R r) := by
    have hbasecomm :
        T.residueToAmbient
            (ResidueField.map (algebraMap R T.A) (residue R r)) =
          (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := by
      have hbasecomm₀ :
          T.residueToAmbient (ResidueField.map f.toAlgHom.toRingHom (residue R r)) =
            (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := by
        simpa [RingHom.comp_apply] using
          congrArg (fun φ : ResidueField R →+* K ↦ φ (residue R r)) f.residue_comm
      have hbasecomm₁ :
          T.residueToAmbient (residue T.A (f.toAlgHom r)) =
            (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := by
        simpa [IsLocalRing.ResidueField.map_residue] using hbasecomm₀
      calc
        T.residueToAmbient (ResidueField.map (algebraMap R T.A) (residue R r))
            = T.residueToAmbient (residue T.A ((algebraMap R T.A) r)) := by
                rw [IsLocalRing.ResidueField.map_residue]
        _ = T.residueToAmbient
              (residue T.A
                (f.toAlgHom ((algebraMap R (ResidueExtensionStage.base (R := R) K).A) r))) := by
              rw [← f.toAlgHom.commutes r]
        _ = T.residueToAmbient (residue T.A (f.toAlgHom r)) := by
              rfl
        _ = (ResidueExtensionStage.base (R := R) K).residueToAmbient (residue R r) := hbasecomm₁
    simpa [ResidueExtensionStage.base_residueToAmbient_eq_algebraMap] using hbasecomm
  calc
    eRing (algebraMap (ResidueField R) (ResidueField T.A) a)
        = eRing (algebraMap (ResidueField R) (ResidueField T.A) (residue R r)) := by
            rw [hr]
    _ = algebraMap (ResidueField R) K (residue R r) := by
          simpa [eRing, ResidueExtensionStage.top_residueToAmbient_eq, RingHom.comp_apply] using
            hcomm
    _ = algebraMap (ResidueField R) K a := by
          rw [hr]

/-- Lemma 10.159.1: for any field extension `K / ResidueField R`, there exists a commutative local
`R`-algebra `R'` such that `R → R'` is flat and local, the maximal ideal of `R` extends to the
maximal ideal of `R'`, and the residue field of `R'` is isomorphic to `K` over `ResidueField R`.
-/
theorem exists_flat_localAlgebra_with_residueField_equiv
    (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : (algebraMap R R').Flat)
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
        Ideal.map (algebraMap R R') (maximalIdeal R) = maximalIdeal R' := by
  -- Route correction: the theorem is now cleanly reduced to the top-stage recursion statement,
  -- while the coherent chain payload and the field-side limit cover lemma are isolated above.
  have hT := exists_top_stage_via_well_order_recursion (R := R) K
  exact exists_flat_localAlgebra_with_residueField_equiv_of_top_stage (R := R) K hT

end
