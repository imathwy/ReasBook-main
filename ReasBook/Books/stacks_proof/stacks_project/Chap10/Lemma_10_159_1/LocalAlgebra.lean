import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_3
import stacks_proof.stacks_project.Chap10.Lemma_10_144_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing
open CategoryTheory Limits
open scoped RatFunc

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Chap10 Lemma 10 159 1: an object under `CommRingCat.of R` carries the
canonical `R`-algebra structure induced by its structure map. -/
private instance underAlgebra (R : Type u) [CommRing R] (B : Under (CommRingCat.of R)) :
    Algebra R B.right :=
  B.hom.hom.toAlgebra

/-- Helper for Chap10 Lemma 10 159 1: an object under `CommRingCat.of R` carries the canonical
`R`-module structure induced by its structure map. -/
private instance underModule (R : Type u) [CommRing R] (B : Under (CommRingCat.of R)) :
    Module R B.right :=
  inferInstance

/-- Helper for Chap10 Lemma 10 159 1: forgetting a commutative ring under `R` to its underlying
`R`-module. This is the fixed-base bridge used to import filtered-colimit flatness from modules
back to rings under `R`. -/
private abbrev underForgetToModule (R : Type u) [CommRing R] :
    Under (CommRingCat.of R) ⥤ ModuleCat R where
  obj B := ModuleCat.of R B.right
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Chap10 Lemma 10 159 1: a filtered colimit in `Under (CommRingCat.of R)` is flat
over the fixed base ring `R` once every stage is flat over `R`. This isolates the ring-side
flatness bridge needed in the limit-step package. -/
theorem underFlatOfIsColimitFilteredSystem
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j).right] :
    Module.Flat R c.pt.right := by
  let cM := (underForgetToModule R).mapCocone c
  letI : ∀ j, Module.Flat R ((F ⋙ underForgetToModule R).obj j) :=
    fun j ↦ by
      -- Forgetting from rings under `R` to `R`-modules does not change the stage module.
      simpa [underForgetToModule] using (inferInstance : Module.Flat R (F.obj j).right)
  have hcM : IsColimit cM := by
    -- Forget to additive groups, where filtered colimits are preserved, and reflect back to
    -- `ModuleCat R`.
    apply isColimitOfReflects (forget₂ (ModuleCat R) AddCommGrpCat)
    simpa [underForgetToModule] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of R) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- The fixed-base filtered-colimit flatness theorem now applies to the forgotten module diagram.
  simpa [cM, underForgetToModule] using
    flat_of_isColimit_filtered_system
      (F := F ⋙ underForgetToModule R) cM hcM

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

end
