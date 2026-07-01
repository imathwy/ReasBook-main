import stacks_project.Chap10.Lemma_10_154_2
import stacks_project.Chap10.Lemma_10_154_3
import stacks_project.Chap10.Lemma_10_159_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Domain-style sampling:
* primary domain: local commutative algebra of filtered colimits of étale `R`-algebras and the
  induced residue-field extension on a local target;
* owner declarations inspected:
  - `CategoryTheory.MorphismProperty.ind`;
  - `CommRingCat.etale`;
  - `RingHom.IsFilteredColimitOfEtale`;
  - `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
  - `IsStrictHenselizationOf.isFilteredColimitOfEtale`;
  - `exists_flat_localAlgebra_with_residueField_equiv`.
* owner decision:
  - `source-facing`: the existence of a local `R`-algebra whose residue field realizes the given
    separable algebraic extension;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the hidden `ULift`-based same-universe presentation packaged by the source-facing
    owner `(algebraMap R R').IsFilteredColimitOfEtale`.

Primitive data are the local `R`-algebra itself, the locality of `R → R'`, and the owner-level
filtered-colimit-of-étale hypothesis. A chosen directed system of finite étale local stages is
derived bridge data, so it should not remain the main public output. Likewise the residue-field
comparison should be a direct existential `AlgEquiv` over `ResidueField R`, not a `Nonempty`
wrapper. The witness ring should range over the same ambient universe as in
`exists_flat_localAlgebra_with_residueField_equiv`, namely `Type (max u w)`. The universe-lift
needed to express the canonical owner should stay inside the owner wrapper rather than appearing in
the public theorem statement.
-/

variable (R)

-- Proof sketch: start from the flat local extension `R → R'` with residue field `K` from
-- Lemma `10.159.1`. Because `K / ResidueField R` is separable algebraic, the construction may be
-- arranged so that every finite subset of `R'` lies in a finite étale local `R`-subalgebra.
-- Those stages yield a filtered colimit presentation of `R'` by étale `R`-algebras. The chapter
-- owner `(algebraMap R R').IsFilteredColimitOfEtale` packages the same-universe `CommRingCat`
-- presentation internally, so the public statement can stay source-facing. The induced
-- residue-field comparison is then best expressed directly as a `ResidueField R`-algebra
-- equivalence.
/-- Helper for Lemma 10.159.2: an étale structural map is already a filtered colimit of étale
algebras via the trivial one-object filtered presentation. -/
lemma isFilteredColimitOfEtale_of_etale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : (algebraMap A B).Etale) :
    (algebraMap A B).IsFilteredColimitOfEtale := by
  -- Translate to the raw categorical owner and use the canonical one-object ind-presentation.
  rw [← RingHom.raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale]
  exact
    (CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale))
      (CommRingCat.ofHom (algebraMap A B))
      (by simpa [CommRingCat.etale] using hAB)

/-- Helper for Lemma 10.159.2: once the source-faithful recursion has produced a top stage whose
structural map from `R` is ind-étale, the public theorem is only an unpacking step. -/
theorem exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv_of_top_stage
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    (hT :
      ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
          (⊤ : IntermediateField (ResidueField R) K),
        Nonempty
          (ResidueExtensionStage.Hom
            (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
            (ResidueExtensionStage.base (R := R) K) T) ∧
          (algebraMap R T.A).IsFilteredColimitOfEtale) :
    ∃ (R' : Type (max u w)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
      (algebraMap R R').IsFilteredColimitOfEtale := by
  rcases hT with ⟨T, ⟨f⟩, hcolim⟩
  let eRing : ResidueField T.A ≃+* K :=
    T.residueEquiv.trans IntermediateField.topEquiv.toRingEquiv
  refine ⟨T.A, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hcolim⟩
  refine
    { toRingEquiv := eRing
      commutes' := ?_ }
  intro a
  -- The residue-field comparison is the same top-stage computation as in Lemma `10.159.1`.
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

/-- Helper for Lemma 10.159.2: after transporting the stage residue field to the current
intermediate field `L`, the one-element extension `L(x)` remains separable over the stage residue
field. -/
lemma adjoin_singleton_isSeparable_over_stage_residue
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x)).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    Algebra.IsSeparable (ResidueField S.A) Lx := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx :=
    (IntermediateField.inclusion
      (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x)).toAlgebra
  letI : IsScalarTower (ResidueField R) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : ResidueField S.A ≃ₐ[ResidueField S.A] L :=
    { toRingEquiv := S.residueEquiv
      commutes' := fun a ↦ rfl }
  haveI : Algebra.IsSeparable (ResidueField S.A) L := by
    simpa using
      (AlgEquiv.Algebra.isSeparable (F := ResidueField S.A) (K := ResidueField S.A)
        (E := L) e)
  haveI : Algebra.IsSeparable L Lx :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField R) L Lx
  -- The separability of `L(x)` over the stage residue field is the transitive closure of
  -- `ResidueField S.A ≃ L` and the separability of `L(x) / L`.
  simpa [Lx] using
    (Algebra.IsSeparable.trans (ResidueField S.A) L Lx :
      Algebra.IsSeparable (ResidueField S.A) Lx)

/-- Helper for Lemma 10.159.2: the generator provided by `stage_adjoin_singleton_top` is integral
over the stage residue field when the ambient extension is algebraic. -/
lemma stage_adjoin_singleton_top_isIntegral_over_stage_residue
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsAlgebraic (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x)).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∃ α : Lx,
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤ ∧
        IsIntegral (ResidueField S.A) α := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx :=
    (IntermediateField.inclusion
      (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x)).toAlgebra
  letI : IsScalarTower (ResidueField R) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨α, hgen⟩ := ResidueExtensionStage.stage_adjoin_singleton_top (S := S) x
  have hα_base : IsIntegral (ResidueField R) α := by
    letI : Algebra.IsAlgebraic (ResidueField R) Lx := by infer_instance
    letI : Algebra.IsIntegral (ResidueField R) Lx := by infer_instance
    exact Algebra.IsIntegral.isIntegral (R := ResidueField R) α
  have hα_L : IsIntegral L α :=
    IsIntegral.tower_top (R := ResidueField R) (A := L) hα_base
  have hcompat :
      (algebraMap L Lx).comp S.residueEquiv.toRingHom = algebraMap (ResidueField S.A) Lx := by
    -- The `ResidueField S.A`-algebra structure on `Lx` factors through `L`.
    rfl
  have hα_stage : IsIntegral (ResidueField S.A) α :=
    (RingEquiv.isIntegral_iff S.residueEquiv hcompat α).2 hα_L
  -- Pair the source-faithful generator statement with the integrality needed for the algebraic branch.
  exact ⟨α, hgen, hα_stage⟩

/-- Helper for Lemma 10.159.2: for a finite-presentation local map, flatness together with the
maximal-ideal equality and separable residue-field extension already gives global étaleness. -/
lemma etale_of_flat_local_extension_of_map_eq_maximalIdeal_of_separable_residue
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.FinitePresentation A B]
    (hflat : (algebraMap A B).Flat)
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    (algebraMap A B).Etale := by
  have hformallyUnramified : (algebraMap A B).FormallyUnramified := by
    -- Over local rings, the separable residue-field criterion identifies formal unramifiedness.
    rw [RingHom.formallyUnramified_algebraMap]
    exact
      (Algebra.FormallyUnramified.iff_map_maximalIdeal_eq (R := A) (S := B)).2
        ⟨inferInstance, hmap⟩
  have hfp : (algebraMap A B).FinitePresentation := by
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  -- The standard owner criterion `flat + formally unramified + finite presentation = étale`
  -- closes the local-to-global bridge.
  exact (RingHom.Etale.iff_flat_and_formallyUnramified).2 ⟨hflat, hformallyUnramified, hfp⟩

/-- Helper for Lemma 10.159.2: adjoining one separable algebraic element to a stage preserves the
filtered-colimit-of-étale invariant on the ambient map from `R`. -/
lemma extend_stage_by_separable_element_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K]
    [Algebra.IsAlgebraic (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (S : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (hS : (algebraMap R S.A).IsFilteredColimitOfEtale)
    (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K Lx,
      Nonempty
        (ResidueExtensionStage.Hom
          (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x) S T) ∧
      (algebraMap R T.A).IsFilteredColimitOfEtale := by
  let Lx : IntermediateField (ResidueField R) K :=
    (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
  let hLLx : L ≤ Lx := ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x
  letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
  letI : Algebra L Lx := (IntermediateField.inclusion hLLx).toAlgebra
  letI : Algebra (ResidueField S.A) Lx :=
    RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
  letI : IsScalarTower (ResidueField S.A) L Lx :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.IsSeparable (ResidueField S.A) Lx :=
    adjoin_singleton_isSeparable_over_stage_residue (R := R) S x
  obtain ⟨α, hgen, hint⟩ :=
    stage_adjoin_singleton_top_isIntegral_over_stage_residue (R := R) S x
  let P : Polynomial (ResidueField S.A) := minpoly (ResidueField S.A) α
  have hPirred : Irreducible P := minpoly.irreducible hint
  obtain ⟨f, hf, hfmap⟩ :=
    exists_monic_lift_of_residueField S.A P (minpoly.monic hint)
  let B : Type (max u w) := AdjoinRoot f
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
    -- A monic `AdjoinRoot` algebra is free over the stage ring, hence flat.
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hmapB : Ideal.map (algebraMap S.A B) (maximalIdeal S.A) = maximalIdeal B :=
    adjoinRoot_map_maximalIdeal_eq_maximalIdeal_of_irreducible_reduction
      S.A f P hfmap
  have hambient :
      Lx.val.toRingHom.comp (algebraMap (ResidueField S.A) Lx) = S.residueToAmbient :=
    ResidueExtensionStage.residueToAmbient_comp_algebraMap (R := R) (K := K) (S := S)
      (Lx := Lx) hLLx
  obtain ⟨eB, hcompat⟩ :=
    ResidueExtensionStage.algebraic_local_extension_compat
      (R := R) (K := K) (S := S) (Lx := Lx) hambient α hgen hint P rfl hPirred f hf hfmap
  have hcoeff :
      eB.toRingHom.comp (ResidueField.map (algebraMap S.A B)) =
        algebraMap (ResidueField S.A) Lx := by
    apply RingHom.ext
    intro a
    apply Subtype.ext
    exact
      (congrArg (fun φ : ResidueField S.A →+* K ↦ φ a) hcompat).trans
        (congrArg (fun φ : ResidueField S.A →+* K ↦ φ a) hambient).symm
  let eBAlg : ResidueField B ≃ₐ[ResidueField S.A] Lx :=
    { toRingEquiv := eB
      commutes' := by
        intro a
        simpa [RingHom.comp_apply] using RingHom.congr_fun hcoeff a }
  haveI : Algebra.IsSeparable (ResidueField S.A) (ResidueField B) :=
    AlgEquiv.Algebra.isSeparable eBAlg.symm
  have hEtaleB : (algebraMap S.A B).Etale :=
    etale_of_flat_local_extension_of_map_eq_maximalIdeal_of_separable_residue
      (hflat := hflatB) (hmap := hmapB)
  have hSB : (algebraMap S.A B).IsFilteredColimitOfEtale :=
    isFilteredColimitOfEtale_of_etale hEtaleB
  have hRB : (algebraMap R B).IsFilteredColimitOfEtale := by
    -- Compose the old ind-étale stage map with the new étale successor map.
    simpa [IsScalarTower.algebraMap_eq R S.A B] using
      RingHom.isFilteredColimitOfEtale_comp (algebraMap R S.A) (algebraMap S.A B) hS hSB
  let T : ResidueExtensionStage.{u, w, max u w} (R := R) K Lx :=
    { A := B
      commRing := inferInstance
      localRing := inferInstance
      algebra := inferInstance
      localHom := by
        -- The ambient map `R → B` is the composite of the old stage map and the successor map.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using
          (inferInstance : IsLocalHom ((algebraMap S.A B).comp (algebraMap R S.A)))
      flat := by
        -- Flatness of `R → B` is inherited from the previous stage and the finite étale successor.
        simpa [IsScalarTower.algebraMap_eq R S.A B] using RingHom.Flat.comp S.flat hflatB
      map_maximalIdeal := by
        -- Push the maximal ideal first to `S.A`, then across the algebraic successor step.
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
  let i : ResidueExtensionStage.Hom hLLx S T :=
    { toAlgHom := IsScalarTower.toAlgHom R S.A B
      isLocalHom := by
        -- The transition map in the scalar tower is the given local map `S.A → B`.
        simpa using (inferInstance : IsLocalHom (algebraMap S.A B))
      residue_comm := by
        -- The residue-field square is the compatibility built for the algebraic local extension.
        simpa [T, ResidueExtensionStage.residueToAmbient] using hcompat }
  -- Package the explicit `AdjoinRoot` successor stage together with the carried ind-étale owner.
  refine ⟨T, ⟨i⟩, ?_⟩
  simpa [T] using hRB

/-- Helper for Lemma 10.159.2: the zero prefix stage already carries the ind-étale owner, because
the base map `R → R` is étale. -/
theorem exists_zero_prefix_stage_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K] :
    ∃ S : ResidueExtensionStage.{u, w, u} (R := R) K
        (⊥ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by simp)
          (ResidueExtensionStage.base (R := R) K) S) ∧
      (algebraMap R S.A).IsFilteredColimitOfEtale := by
  refine ⟨ResidueExtensionStage.base (R := R) K, ?_, ?_⟩
  · -- The zero stage is the base stage from Lemma `10.159.1`.
    simpa using
      (show Nonempty
          (ResidueExtensionStage.Hom
            (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by simp)
            (ResidueExtensionStage.base (R := R) K)
            (ResidueExtensionStage.base (R := R) K)) from
        ⟨ResidueExtensionStage.Hom.id (ResidueExtensionStage.base (R := R) K)⟩)
  · -- The identity `R`-algebra is étale, hence already a filtered colimit of étale `R`-algebras.
    have hIdEtale : (algebraMap R R).Etale := by
      exact RingHom.etale_algebraMap.mpr inferInstance
    simpa using isFilteredColimitOfEtale_of_etale (A := R) (B := R) hIdEtale

/-- Helper for Lemma 10.159.2: an index below the successor ordinal `α + 1` is either the new top
index or it already lies in the previous closed prefix `Set.Iic α`. -/
lemma iic_succ_eq_top_or_le
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (β : Set.Iic (α + 1)) :
    β.1 = α + 1 ∨ β.1 ≤ α := by
  -- Split according to whether the index is the successor top or a genuinely earlier stage.
  by_cases hβ : β.1 = α + 1
  · exact Or.inl hβ
  · exact Or.inr (by simpa [Order.lt_succ_iff] using lt_of_le_of_ne β.2 hβ)

/-- Helper for Lemma 10.159.2: the source-proof successor step upgrades the top stage of a closed
prefix chain by adjoining the next well-ordered residue-field generator, before transporting the
target field along `wellOrder_prefixField_succ`. -/
theorem exists_successor_adjoin_top_stage_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (howner : ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale) :
    let Lsucc : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K Lsucc,
      Nonempty
        (ResidueExtensionStage.Hom
          (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R)
            (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
            (wellOrder_prefixElement (R := R) (K := K) hα))
          C.topStage T) ∧
      (algebraMap R T.A).IsFilteredColimitOfEtale := by
  let βtop : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  have htopOwner : (algebraMap R C.topStage.A).IsFilteredColimitOfEtale := by
    -- Read the ind-étale owner from the old top stage of the chain.
    simpa [βtop, PrefixStageChain.topStage] using howner βtop
  -- Keep the successor stage in the raw adjoin-field form; the remaining blocker is the transport
  -- from this canonical field to the proof-dependent `closedPrefixField` at `α + 1`.
  simpa [PrefixStageChain.topStage] using
    extend_stage_by_separable_element_with_filteredColimit (R := R) (S := C.topStage)
      htopOwner (wellOrder_prefixElement (R := R) (K := K) hα)

/-- Helper for Lemma 10.159.2: the successor step already produces a top stage whose structural
map from `R` is ind-étale, after rewriting the target field with
`wellOrder_prefixField_succ`. -/
theorem successor_top_stage_exists_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (howner : ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale) :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
          ⟨α + 1, show α + 1 ≤ α + 1 from le_rfl⟩),
      (algebraMap R T.A).IsFilteredColimitOfEtale := by
  -- Rewrite the successor target field once; after that, the raw successor-stage theorem already
  -- has the required existential shape.
  rw [closedPrefixField, wellOrder_prefixField_succ (R := R) (K := K) hα]
  rcases exists_successor_adjoin_top_stage_with_filteredColimit
      (R := R) (K := K) hα C howner with ⟨T, -, hT⟩
  exact ⟨T, hT⟩

/-- Helper for Lemma 10.159.2: the successor closed-prefix field is exactly the one-element
adjoin field used by the raw successor-stage theorem. -/
theorem successor_closedPrefixField_eq_adjoin
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K)) :
    closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩ =
      (IntermediateField.adjoin
        (wellOrder_prefixField (R := R) (K := K) α (le_of_lt hα))
        ({wellOrder_prefixElement (R := R) (K := K) hα} : Set K)).restrictScalars
          (ResidueField R) := by
  -- Rewrite the closed-prefix field through its underlying well-ordered prefix-field definition.
  simpa [closedPrefixField] using
    wellOrder_prefixField_succ (R := R) (K := K) hα

/-- Helper for Lemma 10.159.2: every successor-stage index strictly below the new top already
uses the old closed-prefix field. -/
theorem closedPrefixField_succ_below_top_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β =
      closedPrefixField (R := R) K (le_of_lt hα) ⟨β.1, hβ⟩ := by
  -- Both sides are the same well-ordered prefix field; only the proof of the ambient bound
  -- changes.
  simpa [closedPrefixField] using
    (wellOrder_prefixField_proof_irrel (R := R) (K := K)
      (α := β.1)
      (h₁ := le_trans β.2 (Order.succ_le_of_lt hα))
      (h₂ := le_trans hβ (le_of_lt hα)))

/-- Helper for Lemma 10.159.2: below the new successor top, the normalized stage is just the old
stage transported along `closedPrefixField_succ_below_top_eq`. -/
noncomputable abbrev successor_stage_of_below_top
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) β) :=
  Eq.ndrec
    (motive := fun L ↦
      ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (C.stage ⟨β.1, hβ⟩)
    (closedPrefixField_succ_below_top_eq (R := R) (K := K) hα β hβ).symm

/-- Helper for Lemma 10.159.2: between two indices that both stay below the successor top, the
successor-chain transition map is exactly the inherited map from the old chain. -/
theorem successor_hom_of_below_below
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    {β γ : Set.Iic (α + 1)} (hβ : β.1 ≤ α) (hγ : γ.1 ≤ α) (hβγ : β ≤ γ) :
    Nonempty
      (ResidueExtensionStage.Hom
        (wellOrder_prefixField_mono (R := R) (K := K)
          (le_trans β.2 (Order.succ_le_of_lt hα))
          (le_trans γ.2 (Order.succ_le_of_lt hα)) hβγ)
        (successor_stage_of_below_top (R := R) (K := K) hα C β hβ)
        (successor_stage_of_below_top (R := R) (K := K) hα C γ hγ)) := by
  -- Normalize both successor endpoints back to the old chain, where the required map is already
  -- stored as `C.hom`.
  refine ⟨?_⟩
  simpa [successor_stage_of_below_top, closedPrefixField_succ_below_top_eq] using
    (C.hom (β := ⟨β.1, hβ⟩) (γ := ⟨γ.1, hγ⟩) hβγ)

/-- Helper for Lemma 10.159.2: from an old stage below the successor top, the successor-chain map
to the new top stage is the inherited old map into `C.topStage`, followed by `htop`. -/
theorem successor_hom_of_below_top
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (htop :
      Nonempty
        (ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_of_lt hα) (Order.succ_le_of_lt hα) (show α ≤ α + 1 by simp))
          C.topStage Ttop))
    (β : Set.Iic (α + 1)) (hβ : β.1 ≤ α) :
    Nonempty
      (ResidueExtensionStage.Hom
        (wellOrder_prefixField_mono (R := R) (K := K)
          (le_trans β.2 (Order.succ_le_of_lt hα))
          (Order.succ_le_of_lt hα) (show β.1 ≤ α + 1 from β.2))
        (successor_stage_of_below_top (R := R) (K := K) hα C β hβ)
        Ttop) := by
  classical
  let htop' := Classical.choice htop
  -- Compose the inherited map into the old top stage with the chosen successor top map.
  have hOld :
      ResidueExtensionStage.Hom
        (wellOrder_prefixField_mono (R := R) (K := K)
          (le_trans hβ (le_of_lt hα))
          (le_of_lt hα) hβ)
        (C.stage ⟨β.1, hβ⟩) C.topStage := by
    simpa [PrefixStageChain.topStage] using
      (C.hom (β := ⟨β.1, hβ⟩) (γ := ⟨α, by simp⟩) hβ)
  -- After normalizing the source field, the composite is exactly the desired below-top branch.
  refine ⟨?_⟩
  simpa [successor_stage_of_below_top, closedPrefixField_succ_below_top_eq] using
    ResidueExtensionStage.Hom.comp hOld htop'

/-
Route correction: the detailed successor transport API above turned into a large block of
proof-irrelevant endpoint bookkeeping. For the present item, the only mathematically meaningful
successor-side frontier is the final chain constructor `prefixStageChain_succ_of_top_hom` below.
-/
/-- Helper for Lemma 10.159.2: a stage over one target intermediate field, together with an
incoming morphism and the carried ind-étale owner, can be transported across an equality of target
fields without changing the underlying ring data. -/
theorem hom_transport_target_of_eq
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M M' : IntermediateField (ResidueField R) K}
    {hLM : L ≤ M} {hLM' : L ≤ M'}
    (S : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K M)
    (e : M' = M)
    (hHom : Nonempty (ResidueExtensionStage.Hom hLM S T))
    (howner : (algebraMap R T.A).IsFilteredColimitOfEtale) :
    ∃ T' : ResidueExtensionStage.{u, w, max u w} (R := R) K M',
      Nonempty (ResidueExtensionStage.Hom hLM' S T') ∧
      (algebraMap R T'.A).IsFilteredColimitOfEtale := by
  -- Rewrite the target field first so the only remaining change is proof-irrelevant data in the
  -- inclusion proof carried by the morphism witness.
  subst M'
  exact ⟨T, by simpa using hHom, howner⟩

/-- Helper for Lemma 10.159.2: after transporting the successor top field to
`closedPrefixField ... ⟨α + 1, le_rfl⟩`, the raw successor-stage existence theorem still provides
the incoming morphism from the previous top stage together with the ind-étale owner. -/
theorem successor_top_stage_hom_exists_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (howner : ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale) :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩),
      Nonempty
        (ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_of_lt hα) (Order.succ_le_of_lt hα) (show α ≤ α + 1 by simp))
          C.topStage T) ∧
      (algebraMap R T.A).IsFilteredColimitOfEtale := by
  -- Route correction: transport the whole successor package at theorem level, rather than trying
  -- to cast the raw `ResidueExtensionStage.Hom` witness inside a term.
  rcases exists_successor_adjoin_top_stage_with_filteredColimit
      (R := R) (K := K) hα C howner with ⟨T, hHom, hT⟩
  exact
    hom_transport_target_of_eq (R := R) (K := K) C.topStage T
      (successor_closedPrefixField_eq_adjoin (R := R) (K := K) hα)
      hHom hT

/-- Helper for Lemma 10.159.2: once a successor top stage with an incoming morphism from the old
top stage is known, the full closed prefix chain on `α + 1` is obtained by keeping the old stages
below `α` and composing their maps into the new top stage. -/
theorem prefixStageChain_succ_of_top_hom
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)))
    (howner :
      ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale)
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K (Order.succ_le_of_lt hα) ⟨α + 1, by simp⟩))
    (htop :
      Nonempty
        (ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_of_lt hα) (Order.succ_le_of_lt hα) (show α ≤ α + 1 by simp))
          C.topStage Ttop))
    (htopOwner : (algebraMap R Ttop.A).IsFilteredColimitOfEtale) :
    ∃ Csucc : PrefixStageChain (R := R) K (α + 1) (Order.succ_le_of_lt hα),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (Csucc.stage ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩)) ∧
      ∀ β : Set.Iic (α + 1), (algebraMap R (Csucc.stage β).A).IsFilteredColimitOfEtale := by
  -- TODO: this is the remaining successor-side transport package. Mathematically it just keeps the
  -- old stages below `α`, inserts `Ttop` at `α + 1`, and uses the inherited maps together with
  -- `htop` for transitions into the new top stage. The blocker is Lean's proof-irrelevant
  -- endpoint transport, not the algebraic structure of the argument.
  sorry

/-- Helper for Lemma 10.159.2: once the source-proof successor stage has been upgraded, the full
closed prefix chain on `α + 1` is obtained by keeping the old chain below `α` and composing the
old transition maps into the new top stage. -/
theorem exists_prefixStageChain_succ_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α < Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α (le_of_lt hα))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)))
    (howner :
      ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale) :
    ∃ Csucc : PrefixStageChain (R := R) K (α + 1) (Order.succ_le_of_lt hα),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (Order.succ_le_of_lt hα)
                ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (Csucc.stage ⟨0, show (0 : Ordinal) ≤ α + 1 from bot_le⟩)) ∧
      ∀ β : Set.Iic (α + 1), (algebraMap R (Csucc.stage β).A).IsFilteredColimitOfEtale := by
  -- The successor chain is now a thin wrapper around the transported top-stage package and the
  -- structural constructor that inserts this new top stage.
  rcases successor_top_stage_hom_exists_with_filteredColimit
      (R := R) (K := K) hα C howner with ⟨Ttop, htop, htopOwner⟩
  exact
    prefixStageChain_succ_of_top_hom (R := R) (K := K) hα C hbase howner Ttop htop htopOwner

/-- Helper for Lemma 10.159.2: a coherent tower remembers, for each `β ≤ α`, a full closed prefix
chain up to `β`, together with the base-stage map, the ind-étale owner on every stage, and the
restriction compatibilities needed to compare the same transition map inside larger chains. -/
structure PrefixStageTower
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) where
  chain :
    (β : Set.Iic α) →
      PrefixStageChain (R := R) K β.1 (le_trans β.2 hα)
  base :
    ∀ β : Set.Iic α,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K (le_trans β.2 hα)
                ⟨0, show (0 : Ordinal) ≤ β.1 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          ((chain β).stage ⟨0, show (0 : Ordinal) ≤ β.1 from bot_le⟩))
  owner :
    ∀ β : Set.Iic α,
      ∀ δ : Set.Iic β.1, (algebraMap R ((chain β).stage δ).A).IsFilteredColimitOfEtale
  stage_restrict :
    ∀ {β γ : Set.Iic α} (hβγ : β ≤ γ) (δ : Set.Iic β.1),
      (chain γ).stage
          ⟨δ.1, show δ.1 ≤ γ.1 from
            le_trans δ.2 (show β.1 ≤ γ.1 from hβγ)⟩ =
        (chain β).stage δ
  hom_restrict :
    ∀ {β γ : Set.Iic α} (hβγ : β ≤ γ) {δ ε : Set.Iic β.1} (hδε : δ ≤ ε),
      HEq
        (((chain γ).hom
          (β := ⟨δ.1, show δ.1 ≤ γ.1 from
            le_trans δ.2 (show β.1 ≤ γ.1 from hβγ)⟩)
          (γ := ⟨ε.1, show ε.1 ≤ γ.1 from
            le_trans ε.2 (show β.1 ≤ γ.1 from hβγ)⟩) hδε).toAlgHom)
        (((chain β).hom (β := δ) (γ := ε) hδε).toAlgHom)

/-- Helper for Lemma 10.159.2: a recursive family of closed prefix chains yields the open system
of top stages on `Set.Iio α`, together with explicit transition maps, the identity law on each
open stage, and the carried ind-etale owners available before the final limit-stage coherence is
packaged. -/
theorem limit_recursive_family_to_open_top_stage_system
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (C : ∀ β : Set.Iio α,
      PrefixStageChain (R := R) K β.1 (le_trans β.2.le hα))
    (hrestrict :
      ∀ {β γ : Set.Iio α} (hβγ : β ≤ γ),
        (C γ).stage ⟨β.1, hβγ⟩ =
          by
            simpa [PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
              (C β).topStage)
    (howner :
      ∀ β : Set.Iio α,
        ∀ δ : Set.Iic β.1, (algebraMap R ((C β).stage δ).A).IsFilteredColimitOfEtale) :
    ∃ S : (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β),
      ∃ hom :
        {β γ : Set.Iio α} →
          (hβγ : β ≤ γ) →
            ResidueExtensionStage.Hom
              (wellOrder_prefixField_mono (R := R) (K := K)
                (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
              (S β) (S γ),
        (∀ β : Set.Iio α,
          (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A) ∧
        ∀ β : Set.Iio α, (algebraMap R (S β).A).IsFilteredColimitOfEtale := by
  let S :
      (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β) :=
    fun β ↦ by
      -- Reinterpret the top stage of the recursive chain at `β` as the open stage indexed by `β`.
      simpa [PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
        (C β).topStage
  let hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ) :=
    fun {β γ} hβγ ↦ by
      -- The transition map from `β` to `γ` is already stored inside the larger chain `C γ`.
      simpa [S, PrefixStageChain.topStage, openPrefixField, closedPrefixField, hrestrict hβγ] using
        (C γ).hom (β := ⟨β.1, hβγ⟩) (γ := ⟨γ.1, show γ.1 ≤ γ.1 from le_rfl⟩) hβγ
  refine ⟨S, hom, ?_, ?_⟩
  · intro β
    -- At a fixed open stage, the chosen transition map is the identity map stored in `C β`.
    dsimp [hom]
    simpa [S, PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
      (C β).hom_id ⟨β.1, show β.1 ≤ β.1 from le_rfl⟩
  · intro β
    -- Read the ind-étale owner off the top stage of the recursive chain at `β`.
    simpa [S, PrefixStageChain.topStage, openPrefixField, closedPrefixField] using
      howner β ⟨β.1, show β.1 ≤ β.1 from le_rfl⟩

/-- Helper for Lemma 10.159.2: a coherent prefix-stage tower yields the open-stage system below a
limit ordinal, now with the composition law needed for the direct-limit package. -/
theorem coherent_prefixStageTower_to_open_top_stage_system
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (T : PrefixStageTower (R := R) K α hα) :
    ∃ S : (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β),
      ∃ hom :
        {β γ : Set.Iio α} →
          (hβγ : β ≤ γ) →
            ResidueExtensionStage.Hom
              (wellOrder_prefixField_mono (R := R) (K := K)
                (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
              (S β) (S γ),
        (∀ β : Set.Iio α,
          (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A) ∧
        (∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
          ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
              (hom (β := β) (γ := γ) hβγ).toAlgHom) =
            (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom) ∧
        ∀ β : Set.Iio α, (algebraMap R (S β).A).IsFilteredColimitOfEtale := by
  let _ := hlimit
  let top : Set.Iic α := ⟨α, show α ≤ α from le_rfl⟩
  let S :
      (β : Set.Iio α) →
        ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β) :=
    fun β ↦ by
      -- Read the open stage directly from the top closed chain stored in the tower.
      simpa [top, openPrefixField, closedPrefixField] using
        (T.chain top).stage ⟨β.1, show β.1 ≤ α from β.2.le⟩
  let hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ) :=
    fun {β γ} hβγ ↦ by
      -- Every open transition map is already present in the top closed chain.
      simpa [top, S, openPrefixField, closedPrefixField] using
        (T.chain top).hom
          (β := ⟨β.1, show β.1 ≤ α from β.2.le⟩)
          (γ := ⟨γ.1, show γ.1 ≤ α from γ.2.le⟩) hβγ
  refine ⟨S, hom, ?_, ?_, ?_⟩
  · intro β
    -- The self-map at an open stage is the identity map stored in the top closed chain.
    dsimp [hom]
    simpa [top, S, openPrefixField, closedPrefixField] using
      (T.chain top).hom_id ⟨β.1, show β.1 ≤ α from β.2.le⟩
  · intro β γ δ hβγ hγδ
    -- Route correction: work entirely inside the top closed chain, where the composition law is
    -- already part of the stored `PrefixStageChain` data.
    simpa [top, S, openPrefixField, closedPrefixField] using
      (T.chain top).hom_comp
        (β := ⟨β.1, show β.1 ≤ α from β.2.le⟩)
        (γ := ⟨γ.1, show γ.1 ≤ α from γ.2.le⟩)
        (δ := ⟨δ.1, show δ.1 ≤ α from δ.2.le⟩) hβγ hγδ
  · intro β
    -- Read the ind-étale owner off the corresponding stage of the top closed chain.
    simpa [top, S, openPrefixField, closedPrefixField] using
      T.owner top ⟨β.1, show β.1 ≤ α from β.2.le⟩

/-- Helper for Lemma 10.159.2: a coherent family of open-stage morphisms yields the directed
system of the underlying stage rings needed for `Ring.DirectLimit`. -/
theorem open_top_stage_transition_directedSystem
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} {hα : α ≤ Ordinal.type (@WellOrderingRel K)}
    {S : (β : Set.Iio α) →
      ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β)}
    (hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ))
    (hom_id : ∀ β : Set.Iio α,
      (hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A)
    (hom_comp :
      ∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
        ((hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
            (hom (β := β) (γ := γ) hβγ).toAlgHom) =
          (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom) :
    DirectedSystem
      (fun β : Set.Iio α ↦ (S β).A)
      (fun β γ hβγ ↦ (hom (β := β) (γ := γ) hβγ).toAlgHom.toRingHom) := by
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro β x
    -- The chosen self-map is definitionally the identity on the underlying stage ring.
    change (hom (β := β) (γ := β) le_rfl).toAlgHom x = x
    simpa using congrArg (fun f : (S β).A →ₐ[R] (S β).A ↦ f x) (hom_id β)
  · intro δ γ β hβγ hγδ x
    -- Composition in the directed system is the underlying ring-hom form of the stored
    -- algebra-hom composition law.
    change (hom (β := γ) (γ := δ) hγδ).toAlgHom
        ((hom (β := β) (γ := γ) hβγ).toAlgHom x) =
      (hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom x
    exact congrArg (fun f : (S β).A →ₐ[R] (S δ).A ↦ f x) (hom_comp hβγ hγδ)

/-- Helper for Lemma 10.159.2: after composing each open-stage quotient map with the canonical
inclusion into the limit prefix field, the resulting maps are compatible with the open-stage
transition morphisms. This is the field-side descent datum needed for the later direct-limit
comparison map. -/
theorem limit_stage_toIntermediateFieldHom_comm
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    {S : (β : Set.Iio α) →
      ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β)}
    (hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ))
    {β γ : Set.Iio α} (hβγ : β ≤ γ) :
    (((IntermediateField.inclusion
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans γ.2.le hα) hα γ.2.le)).toRingHom).comp
        (S γ).toIntermediateFieldHom).comp
          (hom (β := β) (γ := γ) hβγ).toAlgHom.toRingHom
      =
    ((IntermediateField.inclusion
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) hα β.2.le)).toRingHom).comp
        (S β).toIntermediateFieldHom := by
  -- TODO: this is the field-side compatibility square for the coherent open-stage system. The
  -- statement is correct, but the rewrite route needs a more careful normalization of nested
  -- `RingHom.comp` than the current one-line `rw` script.
  sorry

/-- Helper for Lemma 10.159.2: once the limit branch already has a coherent open-stage system
below `α`, a compatible top stage, and the stagewise ind-étale owners, those data assemble into
the closed prefix chain required at the limit ordinal itself. -/
theorem assemble_limit_prefixStageChain_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (S : (β : Set.Iio α) →
      ResidueExtensionStage.{u, w, max u w} (R := R) K (openPrefixField (R := R) K hα β))
    (open_hom :
      {β γ : Set.Iio α} →
        (hβγ : β ≤ γ) →
          ResidueExtensionStage.Hom
            (wellOrder_prefixField_mono (R := R) (K := K)
              (le_trans β.2.le hα) (le_trans γ.2.le hα) hβγ)
            (S β) (S γ))
    (open_hom_id : ∀ β : Set.Iio α,
      (open_hom (β := β) (γ := β) le_rfl).toAlgHom = AlgHom.id R (S β).A)
    (open_hom_comp :
      ∀ {β γ δ : Set.Iio α} (hβγ : β ≤ γ) (hγδ : γ ≤ δ),
        ((open_hom (β := γ) (γ := δ) hγδ).toAlgHom.comp
            (open_hom (β := β) (γ := γ) hβγ).toAlgHom) =
          (open_hom (β := β) (γ := δ) (le_trans hβγ hγδ)).toAlgHom)
    (Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K hα
        (⟨α, show α ≤ α from le_rfl⟩ : Set.Iic α)))
    (top_hom :
      (β : Set.Iio α) →
        ResidueExtensionStage.Hom
          (wellOrder_prefixField_mono (R := R) (K := K)
            (le_trans β.2.le hα) hα β.2.le)
          (S β) Ttop)
    (top_hom_comp :
      ∀ {β γ : Set.Iio α} (hβγ : β ≤ γ),
        ((top_hom γ).toAlgHom.comp (open_hom (β := β) (γ := γ) hβγ).toAlgHom) =
          (top_hom β).toAlgHom)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              openPrefixField (R := R) K hα ⟨0, hlimit.bot_lt⟩ by
              simpa [openPrefixField, closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (S ⟨0, hlimit.bot_lt⟩)))
    (howner_open : ∀ β : Set.Iio α, (algebraMap R (S β).A).IsFilteredColimitOfEtale)
    (howner_top : (algebraMap R Ttop.A).IsFilteredColimitOfEtale) :
    ∃ C : PrefixStageChain (R := R) K α hα,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)) ∧
      ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale := by
  -- TODO: the stage-by-stage case split is mathematically routine now: stages below `α` come from
  -- `S`, the top stage is `Ttop`, open-transition maps stay unchanged, and maps into the top stage
  -- use `top_hom`. The remaining work is to make those definitional transports between
  -- `openPrefixField` and `closedPrefixField` elaborate efficiently enough for Lean.
  sorry

/-- Helper for Lemma 10.159.2: once a single closed prefix chain has been constructed together
with the base map and the ind-étale owner on every stage, restricting that chain to smaller
ordinals already provides the full coherent tower required by the strengthened recursion. -/
theorem exists_prefixStageTower_of_prefixStageChain_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (C : PrefixStageChain (R := R) K α hα)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)))
    (howner :
      ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale) :
    ∃ T : PrefixStageTower (R := R) K α hα, True := by
  -- TODO: the restricted-chain tower is a proof-irrelevant repackaging of `C`. The current term
  -- proof fails only on subtype elaboration, so keep the mathematically correct statement as the
  -- reusable frontier.
  sorry

/-- Helper for Lemma 10.159.2: the zero closed-prefix chain has only the base stage, and that
single stage already carries the ind-étale owner. -/
theorem exists_zero_prefixStageChain_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    (h0 : (0 : Ordinal) ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ C : PrefixStageChain (R := R) K 0 h0,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K h0 ⟨0, show (0 : Ordinal) ≤ 0 from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ 0 from bot_le⟩)) ∧
      ∀ β : Set.Iic (0 : Ordinal), (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale := by
  -- TODO: the zero-stage constructor is mathematically trivial, but the current explicit subtype
  -- eliminations are not stable. Record the theorem boundary and let the next plan reuse the
  -- existing zero-stage witness without redoing bookkeeping here.
  sorry

/-- Helper for Lemma 10.159.2: at a succ-limit ordinal, the recursive family of smaller coherent
towers should be assembled into a single closed prefix chain whose stages still carry the
ind-étale owner. -/
theorem exists_prefixStageChain_limit_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    {α : Ordinal} (hα : α ≤ Ordinal.type (@WellOrderingRel K))
    (hlimit : Order.IsSuccLimit α)
    (IH :
      ∀ β : Set.Iio α,
        ∃ T : PrefixStageTower (R := R) K β.1 (le_trans β.2.le hα), True) :
    ∃ C : PrefixStageChain (R := R) K α hα,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)) ∧
      ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale := by
  -- TODO: the source-faithful limit step now has its first field-side compatibility lemma
  -- (`limit_stage_toIntermediateFieldHom_comm`), and the final closed-chain assembly has been
  -- isolated in `assemble_limit_prefixStageChain_with_filteredColimit`. The remaining blocker is
  -- structural: the current hypothesis only supplies existential towers on each `β < α`,
  -- whereas the direct-limit package needs one coherent open-stage family on `Set.Iio α` and a
  -- compatible top stage before that assembly lemma can be applied.
  sorry

/-- Helper for Lemma 10.159.2: the source-proof transfinite recursion from Lemma `10.159.1`
should first be strengthened to a coherent closed prefix chain whose stage maps from `R` are
already filtered colimits of étale `R`-algebras, and whose zero stage is reached from the base
stage. -/
theorem exists_prefixStageTower_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ T : PrefixStageTower (R := R) K α hα, True := by
  -- TODO: this is the global recursion wrapper. The source-faithful decomposition is already in
  -- place, but the file is not yet back to a stable compiling frontier for the zero, successor,
  -- and limit constructor helpers it depends on.
  sorry

/-- Helper for Lemma 10.159.2: once the stronger coherent tower exists, the old chain-valued
statement is just its top-index projection. -/
theorem exists_prefixStageChain_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K]
    (α : Ordinal) (hα : α ≤ Ordinal.type (@WellOrderingRel K)) :
    ∃ C : PrefixStageChain (R := R) K α hα,
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K hα ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩ by
              simpa [closedPrefixField, wellOrder_prefixField_zero])
          (ResidueExtensionStage.base (R := R) K)
          (C.stage ⟨0, show (0 : Ordinal) ≤ α from bot_le⟩)) ∧
      ∀ β : Set.Iic α, (algebraMap R (C.stage β).A).IsFilteredColimitOfEtale := by
  rcases exists_prefixStageTower_with_filteredColimit (R := R) K α hα with ⟨T, -⟩
  let top : Set.Iic α := ⟨α, by simp⟩
  refine ⟨T.chain top, T.base top, ?_⟩
  intro β
  -- The stronger tower stores the ind-étale owner on every stage of the top chain.
  simpa [top] using T.owner top β

/-- Helper for Lemma 10.159.2: the terminal closed prefix field is `⊤`. This isolates the
one dependent cast needed when extracting the final stage from the recursive chain. -/
theorem closedPrefixField_top_eq_top
    (K : Type w) [Field K] [Algebra (ResidueField R) K] :
    closedPrefixField (R := R) K le_rfl
      (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
        Set.Iic (Ordinal.type (@WellOrderingRel K))) =
      (⊤ : IntermediateField (ResidueField R) K) := by
  -- Rewrite the proof-dependent closed prefix field to the terminal well-ordered prefix field.
  dsimp [closedPrefixField]
  rw [wellOrder_prefixField_proof_irrel (R := R) (K := K)
    (h₁ := le_trans (show Ordinal.type (@WellOrderingRel K) ≤
      Ordinal.type (@WellOrderingRel K) by exact le_rfl) le_rfl)
    (h₂ := le_rfl)]
  -- The source well-order construction reaches all of `K` at the terminal ordinal.
  simpa using wellOrder_prefixField_top (R := R) (K := K)

/-- Helper for Lemma 10.159.2: once the recursive chain has produced the terminal closed-prefix
stage, transporting that stage across `closedPrefixField_top_eq_top` gives the required stage over
`⊤` without changing the ring or its ind-étale owner. -/
theorem stage_transport_to_top
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (hL : L = (⊤ : IntermediateField (ResidueField R) K))
    {hbaseL : (⊥ : IntermediateField (ResidueField R) K) ≤ L}
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T))
    (howner : (algebraMap R T.A).IsFilteredColimitOfEtale) :
    ∃ Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) Ttop) ∧
      (algebraMap R Ttop.A).IsFilteredColimitOfEtale := by
  -- Rewrite the target field through the explicit variable `L`, so the dependent transport stays
  -- confined to this small helper.
  subst L
  refine ⟨T, ?_, howner⟩
  -- After the field rewrite, the base morphism is the original map with only proof-irrelevant data changed.
  simpa using hbase

/-- Helper for Lemma 10.159.2: once the recursive chain has produced the terminal closed-prefix
stage, transporting that stage across `closedPrefixField_top_eq_top` gives the required stage over
`⊤` without changing the ring or its ind-étale owner. -/
theorem closedPrefixField_top_stage_transport
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    {hbaseL :
      (⊥ : IntermediateField (ResidueField R) K) ≤
        closedPrefixField (R := R) K le_rfl
          (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
            Set.Iic (Ordinal.type (@WellOrderingRel K)))}
    (T : ResidueExtensionStage.{u, w, max u w} (R := R) K
      (closedPrefixField (R := R) K le_rfl
        (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
          Set.Iic (Ordinal.type (@WellOrderingRel K)))))
    (hbase :
      Nonempty
        (ResidueExtensionStage.Hom hbaseL
          (ResidueExtensionStage.base (R := R) K) T))
    (howner : (algebraMap R T.A).IsFilteredColimitOfEtale) :
    ∃ Ttop : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) Ttop) ∧
      (algebraMap R Ttop.A).IsFilteredColimitOfEtale := by
  -- Route correction: use the generic field-transport helper so the dependent cast happens on an
  -- explicit field variable rather than on the closed-prefix expression itself.
  exact
    stage_transport_to_top (R := R) (K := K)
      (L := closedPrefixField (R := R) K le_rfl
        (⟨Ordinal.type (@WellOrderingRel K), by simp⟩ :
          Set.Iic (Ordinal.type (@WellOrderingRel K))))
      (hL := closedPrefixField_top_eq_top (R := R) (K := K))
      (T := T) hbase howner

/-- Helper for Lemma 10.159.2: once the strengthened prefix-chain recursion is available, the
top-stage theorem is just the terminal-stage extraction from that chain. -/
theorem exists_top_stage_with_filteredColimit_via_well_order_recursion
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K] :
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
        (⊤ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
          (ResidueExtensionStage.base (R := R) K) T) ∧
      (algebraMap R T.A).IsFilteredColimitOfEtale := by
  let αtop : Ordinal := Ordinal.type (@WellOrderingRel K)
  let βzero : Set.Iic αtop := ⟨0, by simp⟩
  let βtop : Set.Iic αtop := ⟨αtop, by simp⟩
  rcases exists_prefixStageChain_with_filteredColimit (R := R) K αtop le_rfl with
    ⟨C, hbase₀, howner⟩
  rcases hbase₀ with ⟨f₀⟩
  have hbaseTop :
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤
              closedPrefixField (R := R) K le_rfl βtop by
                simpa [βtop, closedPrefixField] using
                  (base_le_prefixField (R := R) (K := K) (hα := le_rfl)))
          (ResidueExtensionStage.base (R := R) K)
          (C.stage βtop)) := by
    -- Follow the source route: first reach the zero stage from the base stage, then move along
    -- the coherent chain to the terminal stage.
    refine ⟨?_⟩
    simpa [βzero, βtop, closedPrefixField, wellOrder_prefixField_zero] using
      (f₀.comp (C.hom (β := βzero) (γ := βtop) bot_le))
  -- The terminal closed-prefix stage is now transported once to a stage over `⊤`.
  exact
    closedPrefixField_top_stage_transport (R := R) (K := K) (T := C.stage βtop)
      hbaseTop (howner βtop)

/-- Lemma 10.159.2: for a separable algebraic extension `K / ResidueField R`, there exists a
local `R`-algebra `R'` such that `R → R'` is a local map, `R'` is a filtered colimit of étale
`R`-algebras, and the residue field of `R'` is isomorphic to `K` over `ResidueField R`. -/
theorem exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K] [Algebra.IsAlgebraic (ResidueField R) K] :
    ∃ (R' : Type (max u w)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
      (algebraMap R R').IsFilteredColimitOfEtale := by
  -- Route correction: the public theorem is reduced to the strengthened top-stage recursion, and
  -- the residue-field unpacking is isolated in the helper above.
  have hT := exists_top_stage_with_filteredColimit_via_well_order_recursion (R := R) K
  exact
    exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv_of_top_stage
      (R := R) K hT

end
