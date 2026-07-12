import StacksProject_2024.Chap10.Lemma_10_154_2
import StacksProject_2024.Chap10.Lemma_10_154_3
import StacksProject_2024.Chap10.Lemma_10_159_1.Index
import Mathlib.Tactic.StacksAttribute

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

variable (R)

/-- Helper for Chap10 Lemma 10 159 2: changing only the proof of the intermediate-field
inclusion in a stage morphism does not change its underlying algebra map. -/
theorem ResidueExtensionStage.Hom.toAlgHom_cast_le
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (f : ResidueExtensionStage.Hom h S T) :
    (cast (by rw [Subsingleton.elim h h']) f :
        ResidueExtensionStage.Hom h' S T).toAlgHom = f.toAlgHom := by
  -- Proof irrelevance identifies the two inclusion witnesses, so the dependent cast is trivial.
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 10.159.2: an étale structural map is already a filtered colimit of étale
algebras via the trivial one-object filtered presentation. -/
lemma isFilteredColimitOfEtale_of_etale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : (algebraMap A B).Etale) :
    RingHom.IsFilteredColimitOfEtale.{u, u, v} (algebraMap A B) := by
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
          RingHom.IsFilteredColimitOfEtale.{u, max u w, max u w} (algebraMap R T.A)) :
    ∃ (R' : Type (max u w)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
      RingHom.IsFilteredColimitOfEtale.{u, max u w, max u w} (algebraMap R R') := by
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
    (hS : RingHom.IsFilteredColimitOfEtale.{u, max u w, max u w} (algebraMap R S.A))
    (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K Lx,
      Nonempty
        (ResidueExtensionStage.Hom
          (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x) S T) ∧
      RingHom.IsFilteredColimitOfEtale.{u, max u w, max u w} (algebraMap R T.A) := by
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
  have hSB :
      RingHom.IsFilteredColimitOfEtale.{max u w, max u w, u} (algebraMap S.A B) :=
    isFilteredColimitOfEtale_of_etale hEtaleB
  have hRB : RingHom.IsFilteredColimitOfEtale.{u, max u w, max u w} (algebraMap R B) := by
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

end
