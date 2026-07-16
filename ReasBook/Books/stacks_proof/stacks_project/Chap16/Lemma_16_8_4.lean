import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_40_4
import stacks_proof.stacks_project.Chap10.Lemma_10_147_5
import stacks_proof.stacks_project.Chap15.Definition_15_41_1
import stacks_proof.stacks_project.Chap16.Definition_16_2_1
import stacks_proof.stacks_project.Chap16.Lemma_16_4_6
import stacks_proof.stacks_project.Chap16.Lemma_16_5_1
import stacks_proof.stacks_project.Chap16.Lemma_16_5_2
import stacks_proof.stacks_project.Chap16.Situation_16_8_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

open scoped SingularIdealNotation

universe u

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing R] [IsNoetherianRing Λ] [(algebraMap R Λ).IsRegularRingMap]

/- Domain-style sampling:
- primary domain: regular ring maps of Noetherian commutative rings and the PT property
  `RingHom.IsFilteredColimitOfSmooth`;
- sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `IsRegularRingMap`,
  `RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers`,
  `RingHom.IsFilteredColimitOfSmooth.prodMap`;
- best owner abstraction: PT is already owned by
  `(algebraMap R Λ).IsFilteredColimitOfSmooth`, while Situation `16.8.1` itself is owned by the
  ambient instance `[IsRegularRingMap R Λ]`;
- primitive vs. derived: the only primitive input of the reduction theorem is the field-case PT
  hypothesis phrased directly at that owner. Any chosen presentation of a filtered diagram of
  smooth algebras is derived API already packaged by `RingHom.IsFilteredColimitOfSmooth`.

Source/core/bridge triage:
- `source-facing`: the reduction from arbitrary regular maps to the case where the source is a
  field;
- `core/canonical`: `[IsRegularRingMap R Λ]` for the ambient situation and
  `(algebraMap R Λ).IsFilteredColimitOfSmooth` for PT;
- `bridge/view`: the auxiliary reductions through quotients, total quotient rings, and product
  decompositions used in the proof sketch.
-/

-- Proof sketch: for an arbitrary regular map `R → Λ`, consider the set of ideals `I ⊆ R` for
-- which the quotient map `R / I → Λ / IΛ` does not satisfy PT, and choose a maximal such ideal if
-- any exist. After replacing the situation by this quotient, every nonzero quotient satisfies PT,
-- so Proposition `16.5.3` shows `R` is reduced. Localizing at the nonzerodivisors reduces to the
-- total ring of fractions, which is a finite product of fields; apply Lemmas `16.8.2`, `16.8.3`,
-- `16.6.1`, and `16.7.2` to descend the field-case smooth factorization back to `Λ`.

/-- Helper for Lemma 16.8.4: a smooth finitely presented algebra has unit singular ideal. -/
lemma singularIdeal_eq_top_of_smooth
    {S : Type u} {T : Type u}
    [CommRing S] [CommRing T] [Algebra S T]
    [FinitePresentation S T] [Smooth S T] :
    H[T⁄S] = ⊤ := by
  -- Proof comment: smoothness makes the smooth locus all of `Spec(T)`, so the singular ideal has
  -- empty zero locus and is therefore the unit ideal.
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  rw [Algebra.zeroLocus_singularIdeal_eq_compl_smoothLocus, Algebra.smoothLocus_eq_univ, Set.compl_univ]

/-- Helper for Lemma 16.8.4: if an ideal already contains the kernel of a quotient map and its
image in the quotient is the unit ideal, then the ideal itself is the unit ideal. -/
lemma ideal_eq_top_of_quotient_map_eq_top
    (I J : Ideal Λ) (hIJ : I ≤ J)
    (hmap : Ideal.map (Ideal.Quotient.mk I) J = ⊤) :
    J = ⊤ := by
  -- Proof comment: pull the quotient-level unit-ideal statement back along the surjective quotient
  -- map; the resulting supremum collapses because `I ≤ J`.
  have hComapTop :
      Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = ⊤ := by
    rw [hmap, Ideal.comap_top]
  have hSupTop : J ⊔ Ideal.comap (Ideal.Quotient.mk I) ⊥ = ⊤ := by
    simpa [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective] using hComapTop
  have hSupTop' : J ⊔ I = ⊤ := by
    simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hSupTop
  rwa [sup_eq_left.2 hIJ] at hSupTop'

/-- Helper for Lemma 16.8.4: in the square-zero case, every finitely presented algebra map to the
target factors through a smooth algebra. -/
private theorem finitelyPresentedFactorization_of_squareZero
    {S : Type*} {T : Type*} {A : Type*}
    [CommRing S] [CommRing T] [CommRing A]
    [Algebra S T] [Algebra S A] [Module.Flat S T] [FinitePresentation S A]
    (I : Ideal S) (hSq : I ^ 2 = ⊥)
    (hquot : (algebraMap (S ⧸ I) (T ⧸ I.map (algebraMap S T))).IsFilteredColimitOfSmooth)
    (φ : A →ₐ[S] T) :
    ∃ (B' : Type*) (_ : CommRing B') (_ : Algebra S B') (_ : Smooth S B')
      (f : A →ₐ[S] B') (g : B' →ₐ[S] T),
      g.comp f = φ := by
  -- Proof comment: first factor `φ` through a smooth quotient stage `B ⧸ J` using the repaired
  -- square-zero quotient API from Lemma `16.5.1`.
  obtain ⟨B, _, _, hBsmooth, J, hJ, hJfg, f, g, hgf⟩ :=
    exists_smooth_quotient_factorization_of_square_zero
      (R := S) (A := A) (Λ := T) (I := I) hSq hquot φ
  let _ : Smooth S B := hBsmooth
  let φB : B →ₐ[S] T := g.comp (Ideal.Quotient.mkₐ S J)
  have hφJ : J ≤ RingHom.ker φB := by
    intro x hx
    rw [RingHom.mem_ker]
    have hx0 : Ideal.Quotient.mk J x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    simpa [φB, hx0]
  -- Proof comment: then kill the quotient ideal inside a second smooth algebra by Lemma `16.5.2`.
  obtain ⟨B', _, _, hB'smooth, α, β, hαJ, hβα⟩ :=
    exists_smooth_factorization_killing_ideal_of_square_zero
      (R := S) (B := B) (Λ := T) (I := I) hSq hquot
      (φ := φB) (J := J) hJ hJfg hφJ
  have hαQuot : ∀ x, x ∈ J → α x = 0 := by
    intro x hx
    simpa [RingHom.mem_ker] using hαJ hx
  let δ : B ⧸ J →ₐ[S] B' :=
    Ideal.Quotient.liftₐ J α hαQuot
  have hδ : δ.comp (Ideal.Quotient.mkₐ S J) = α := by
    simpa [δ] using (Ideal.Quotient.liftₐ_comp (R₁ := S) J α hαQuot)
  have hβδ : β.comp δ = g := by
    apply Ideal.Quotient.algHom_ext
    calc
      (β.comp δ).comp (Ideal.Quotient.mkₐ S J)
          = β.comp (δ.comp (Ideal.Quotient.mkₐ S J)) := by
              rw [AlgHom.comp_assoc]
      _ = β.comp α := by rw [hδ]
      _ = φB := hβα
      _ = g.comp (Ideal.Quotient.mkₐ S J) := rfl
  refine ⟨B', inferInstance, inferInstance, hB'smooth, δ.comp f, β, ?_⟩
  -- Proof comment: descend the original map through `B ⧸ J` and close by associativity.
  calc
    β.comp (δ.comp f) = (β.comp δ).comp f := by rw [AlgHom.comp_assoc]
    _ = g.comp f := by rw [hβδ]
    _ = φ := hgf

/-- Helper for Lemma 16.8.4: quotienting a flat algebra map by the induced ideal preserves
flatness. -/
private theorem quotientMapFlatOfFlat
    {S : Type*} {T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (I : Ideal S) (hφ : φ.Flat) :
    (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).Flat := by
  let _ : Algebra S T := φ.toAlgebra
  let e : T ⧸ Ideal.map φ I ≃+* ((S ⧸ I) ⊗[S] T) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).toRingEquiv).trans
      (Algebra.TensorProduct.comm S T (S ⧸ I)).toRingEquiv
  -- Proof comment: base change flatness to `S ⧸ I`, then transport it across the quotient-tensor
  -- equivalence.
  have hφ_alg : (algebraMap S T).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hbaseModule : Module.Flat (S ⧸ I) ((S ⧸ I) ⊗[S] T) := by
    let _ : Module.Flat S T := RingHom.flat_algebraMap_iff.mp hφ_alg
    simpa using (Module.Flat.baseChange (R := S) (S := S ⧸ I) (M := T))
  have hbase : (algebraMap (S ⧸ I) ((S ⧸ I) ⊗[S] T)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hbaseModule
  have he : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  have hcomp :
      (e.symm.toRingHom.comp (algebraMap (S ⧸ I) ((S ⧸ I) ⊗[S] T))).Flat :=
    RingHom.Flat.comp hbase he
  have hEq :
      e.symm.toRingHom.comp (algebraMap (S ⧸ I) ((S ⧸ I) ⊗[S] T)) =
        Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map := by
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm
          ((Algebra.TensorProduct.comm S T (S ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[S] (1 : T))) =
        (Ideal.Quotient.mk (Ideal.map φ I)) (φ x)
    have hcomm :
        (Algebra.TensorProduct.comm S T (S ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[S] (1 : T)) =
          (1 : T) ⊗ₜ[S] (Ideal.Quotient.mk I x) := by
      simpa using
        (Algebra.TensorProduct.comm_symm_tmul (R := S) (a := (1 : T))
          (b := Ideal.Quotient.mk I x))
    rw [hcomm, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : T) = φ x := by
      change (algebraMap S T x) * 1 = φ x
      simpa [RingHom.algebraMap_toAlgebra]
    simpa [RingHom.algebraMap_toAlgebra, hs]
  rw [← hEq]
  exact hcomp

/-- Helper for Lemma 16.8.4: the induced target ideal in the double-quotient step agrees with the
direct quotient ideal obtained from the larger source ideal. -/
lemma quotientStepTargetIdeal_eq
    {S : Type u} {T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (J K : Ideal S) :
    Ideal.map
        (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
        (Ideal.map (Ideal.Quotient.mk J) K) =
      Ideal.map (Ideal.Quotient.mk (J.map (algebraMap S T))) (K.map (algebraMap S T)) := by
  -- Proof comment: rewrite the quotient algebra map as the composite of the original algebra map
  -- with the source quotient map, then the target ideal identity is exactly `Ideal.map_map`.
  have hcomp :
      (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).comp (Ideal.Quotient.mk J) =
        algebraMap S (T ⧸ J.map (algebraMap S T)) := by
    ext x
    rfl
  simpa [Ideal.map_map, hcomp]

/-- Helper for Lemma 16.8.4: the quotient PT hypothesis transports across the standard
double-quotient equivalences. -/
private theorem quotientHypothesisOfQuotientStep
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    {J K : Ideal S} (hJK : J ≤ K)
    (hquotK :
      (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T))).IsFilteredColimitOfSmooth) :
    (algebraMap
        ((S ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) K)
        ((T ⧸ J.map (algebraMap S T)) ⧸
          Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
            (Ideal.map (Ideal.Quotient.mk J) K))).IsFilteredColimitOfSmooth := by
  let eS :
      ((S ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) K) ≃+*
        (S ⧸ K) :=
    DoubleQuot.quotQuotEquivQuotOfLE (R := S) (I := J) (J := K) hJK
  let eT :
      ((T ⧸ J.map (algebraMap S T)) ⧸
          Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
            (Ideal.map (Ideal.Quotient.mk J) K)) ≃+*
        (T ⧸ K.map (algebraMap S T)) :=
    (Ideal.quotEquivOfEq
        (quotientStepTargetIdeal_eq (S := S) (T := T) J K)).trans
      (DoubleQuot.quotQuotEquivQuotOfLE
        (R := T) (I := J.map (algebraMap S T)) (J := K.map (algebraMap S T))
        (Ideal.map_mono hJK))
  have hComm :
      eS.toRingHom.comp
          (algebraMap
            ((S ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) K)
            ((T ⧸ J.map (algebraMap S T)) ⧸
              Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
                (Ideal.map (Ideal.Quotient.mk J) K))) =
        (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T))).comp eT.toRingHom := by
    -- Proof comment: both composites are quotient maps out of `S`, so generatorwise comparison
    -- on the double quotient is enough.
    apply Ideal.Quotient.ringHom_ext
    ext s
    simp [eS, eT]
  have hArrowIso :
      CategoryTheory.Arrow.mk
          (CommRingCat.ofHom
            (algebraMap
              ((S ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) K)
              ((T ⧸ J.map (algebraMap S T)) ⧸
                Ideal.map (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T)))
                  (Ideal.map (Ideal.Quotient.mk J) K)))) ≅
        CategoryTheory.Arrow.mk
          (CommRingCat.ofHom (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T)))) :=
    CategoryTheory.Arrow.isoMk
      (RingEquiv.toCommRingCatIso eS)
      (RingEquiv.toCommRingCatIso eT)
      (by
        ext s
        exact DFunLike.congr_fun hComm s)
  have hptArrow :
      CategoryTheory.MorphismProperty.ind
        (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T)))) := by
    -- Proof comment: unwrap the source-facing PT hypothesis once before transporting it through
    -- the quotient-step arrow isomorphism.
    simpa [RingHom.IsFilteredColimitOfSmooth] using hquotK
  exact
    (CategoryTheory.MorphismProperty.ind
        (RingHom.toMorphismProperty RingHom.Smooth)).prop_of_iso
      hArrowIso.symm hptArrow

/-- Helper for Lemma 16.8.4: the square-zero quotient hypothesis already upgrades to PT for the
original flat map. -/
private theorem isFilteredColimitOfSmooth_of_squareZeroQuotient
    {S : Type*} {T : Type*} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (I : Ideal S) (hSq : I ^ 2 = ⊥)
    (hquot : (algebraMap (S ⧸ I) (T ⧸ I.map (algebraMap S T))).IsFilteredColimitOfSmooth) :
    (algebraMap S T).IsFilteredColimitOfSmooth := by
  let _ : Algebra S T := (algebraMap S T).toAlgebra
  let _ : Algebra S (ULift T) := ULift.algebra
  let _ : Algebra (ULift S) (ULift T) := ULift.algebra' S (ULift T)
  -- Route correction: unfold the owner once and reduce to the categorical finite-stage
  -- factorization criterion.
  dsimp [RingHom.IsFilteredColimitOfSmooth]
  refine
    (CategoryTheory.MorphismProperty.ind_iff_exists
      (C := CommRingCat)
      (P := RingHom.toMorphismProperty RingHom.Smooth)
      (H := commRingCatIsFinitelyPresentableHom_of_smooth)
      (CommRingCat.ofHom (algebraMap (ULift S) (ULift T)))).2 ?_
  intro Z p g hp hpg
  obtain ⟨A, hAfp, uA, huA, hpA⟩ :=
    existsFinitePresentationStageFactorization (R := S) (Λ := T) p g hp hpg
  let fS : S →+* ULift S :=
    (ULift.ringEquiv.symm : S ≃+* ULift S).toRingHom
  let _ : Algebra S A.left := ((algebraMap (ULift S) A.left).comp fS).toAlgebra
  have hAfpS : (algebraMap S A.left).FinitePresentation := by
    -- Proof comment: finite presentation over `ULift S` transports across the bijective base-ring
    -- equivalence `S ≃ ULift S`.
    let hfS : fS.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective
        (ULift.ringEquiv.symm : S ≃+* ULift S).bijective
    simpa [fS, RingHom.algebraMap_toAlgebra] using
      RingHom.FinitePresentation.comp hAfp hfS
  let _ : Algebra.FinitePresentation S A.left := by
    simpa [RingHom.finitePresentation_algebraMap] using hAfpS
  let φ : A.left →ₐ[S] T :=
    { toRingHom := (ULift.ringEquiv : ULift T ≃+* T).toRingHom.comp A.hom.toRingHom
      commutes' := by
        intro s
        change
          (ULift.ringEquiv : ULift T ≃+* T)
              (A.hom ((algebraMap (ULift S) A.left) (ULift.up s))) =
            algebraMap S T s
        simpa [fS, RingHom.algebraMap_toAlgebra] using
          congrArg ULift.down (A.hom.commutes (ULift.up s)) }
  obtain ⟨B', _, _, hB'smooth, f, β, hβf⟩ :=
    finitelyPresentedFactorization_of_squareZero
      (S := S) (T := T) (A := A.left) (I := I) hSq hquot φ
  let βup : B' →+* ULift T :=
    (ULift.ringEquiv.symm : T ≃+* ULift T).toRingHom.comp β.toRingHom
  have hβupf :
      βup.comp f.toRingHom = A.hom.toRingHom := by
    -- Proof comment: transport the smooth factorization target back across `ULift T ≃ T`.
    ext a
    change ULift.up (β (f a)) = A.hom a
    have hEq : β (f a) = φ a := by
      simpa using congrArg (fun ψ : A.left →ₐ[S] T => ψ a) hβf
    cases hA : A.hom a with
    | up x =>
        change ULift.up (β (f a)) = ULift.up x
        apply congrArg ULift.up
        simpa [φ, hA] using hEq
  let sourceToB' : ULift S →+* B' :=
    (algebraMap S B').comp (ULift.ringEquiv : ULift S ≃+* S).toRingHom
  have hsourceSmooth : sourceToB'.Smooth := by
    -- Proof comment: smoothness over `S` survives precomposition with the bijective source-ring
    -- equivalence `ULift S ≃ S`.
    let hbase : ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).Smooth :=
      RingHom.Smooth.of_bijective (ULift.ringEquiv : ULift S ≃+* S).bijective
    have htarget : (algebraMap S B').Smooth := by
      simpa [RingHom.smooth_algebraMap] using hB'smooth
    simpa [sourceToB'] using RingHom.Smooth.comp hbase htarget
  refine ⟨CommRingCat.of B', CommRingCat.ofHom (uA.hom.comp f.toRingHom),
    CommRingCat.ofHom βup, hsourceSmooth, ?_, ?_⟩
  · -- Proof comment: compare the concrete smooth factorization with the original stage map on
    -- each element of `Z`.
    apply CommRingCat.hom_ext_iff.mpr
    intro z
    change βup (f (uA.hom z)) = g.hom z
    have hu := CommRingCat.hom_ext_iff.mp huA z
    change A.hom (uA.hom z) = g.hom z at hu
    have hstage : βup (f (uA.hom z)) = A.hom (uA.hom z) := by
      change (βup.comp f.toRingHom) (uA.hom z) = A.hom (uA.hom z)
      rw [hβupf]
    exact hstage.trans hu
  · -- Proof comment: the source-compatibility equation is exactly the transported algebra-map
    -- identity for the extracted finitely presented stage.
    apply CommRingCat.hom_ext_iff.mpr
    intro s
    have hpAs := CommRingCat.hom_ext_iff.mp hpA s
    change f (uA.hom (p.hom s)) = sourceToB' s
    change f ((algebraMap (ULift S) A.left) s) = sourceToB' s at hpAs ⊢
    cases s
    simpa [sourceToB', fS, RingHom.algebraMap_toAlgebra] using
      congrArg f hpAs

/-- Helper for Lemma 16.8.4: lift PT across a nilpotent quotient. -/
theorem isFilteredColimitOfSmooth_of_nilpotent_quotient
    (I : Ideal R) (hI : IsNilpotent I)
    (hquot : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  let P : ∀ ⦃S : Type _⦄ [CommRing S], Ideal S → Prop :=
    fun {S} _ J =>
      ∀ {T : Type _} [CommRing T] [Algebra S T] [Module.Flat S T],
        (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).IsFilteredColimitOfSmooth →
          (algebraMap S T).IsFilteredColimitOfSmooth
  -- Proof comment: apply nilpotent-ideal induction, using the square-zero case as the base and
  -- the standard quotient-of-quotient transport as the induction step.
  exact
    Ideal.IsNilpotent.induction_on (S := R) I hI
      (P := P)
      (fun {S} _ J hJsq {T} _ _ _ ↦
        fun hquotJ ↦
          isFilteredColimitOfSmooth_of_squareZeroQuotient
            (S := S) (T := T) (I := J) hJsq hquotJ)
      (fun {S} _ J K hJK hJ hKquot {T} _ _ _ ↦
        fun hquotK ↦ by
          have hflat : (algebraMap S T).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
          have hquotFlat :
              (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).Flat := by
            simpa [RingHom.algebraMap_toAlgebra] using
              quotientMapFlatOfFlat (φ := algebraMap S T) J hflat
          let _ : Module.Flat (S ⧸ J) (T ⧸ J.map (algebraMap S T)) :=
            RingHom.flat_algebraMap_iff.mp hquotFlat
          have hquotJ :
              (algebraMap (S ⧸ J) (T ⧸ J.map (algebraMap S T))).IsFilteredColimitOfSmooth := by
            -- Proof comment: transport the quotient PT hypothesis from `K` down to the quotient by
            -- `J` using the standard double-quotient equivalences.
            exact
              hKquot
                (T := T ⧸ J.map (algebraMap S T))
                (quotientHypothesisOfQuotientStep
                  (S := S) (T := T) (J := J) (K := K) hJK hquotK)
          -- Proof comment: once the quotient by `J` satisfies PT, invoke the induction
          -- hypothesis for the smaller ideal.
          exact hJ (T := T) hquotJ)
      (T := Λ) hquot

/-- Helper for Lemma 16.8.4: a quotient-minimal counterexample has reduced source ring. -/
lemma isReduced_of_counterexample_minimal_under_nonzero_quotients
    (hbad : ¬ (algebraMap R Λ).IsFilteredColimitOfSmooth)
    (hquot :
      ∀ I : Ideal R, I ≠ ⊥ →
        (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    IsReduced R := by
  -- Proof comment: if the nilradical were nonzero, the quotient hypothesis would make the
  -- nilradical quotient satisfy PT, and Proposition `16.5.3` would lift PT back to `R → Λ`,
  -- contradicting the assumed minimal counterexample.
  rw [← nilradical_eq_bot_iff]
  by_contra hnil
  exact hbad <|
    isFilteredColimitOfSmooth_of_nilpotent_quotient
      (R := R) (Λ := Λ) (I := nilradical R)
      (IsNoetherianRing.isNilpotent_nilradical R)
      (hquot (nilradical R) hnil)

/-- Helper for Lemma 16.8.4: the induction hypothesis on larger ideals of `R` descends to every
nonzero quotient of `R ⧸ I`. -/
lemma quotientPt_of_inductionStep
    (I : Ideal R)
    (hind :
      ∀ J : Ideal R, I < J →
        (algebraMap (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (K : Ideal (R ⧸ I)) (hK : K ≠ ⊥) :
    (algebraMap
        ((R ⧸ I) ⧸ K)
        ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
          Ideal.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) K)).IsFilteredColimitOfSmooth := by
  let J : Ideal R := Ideal.comap (Ideal.Quotient.mk I) K
  have hIleJ : I ≤ J := by
    -- Proof comment: every element of `I` vanishes in `R ⧸ I`, so it lands in the preimage of
    -- any ideal of the quotient.
    exact RingHom.ker_le_comap (Ideal.Quotient.mk I)
  have hJne : J ≠ I := by
    -- Proof comment: if `J = I`, then `K` would be the zero ideal because ideals of a quotient
    -- are recovered by mapping their preimages along the quotient map.
    intro hJI
    apply hK
    refine le_antisymm ?_ bot_le
    rw [← Ideal.map_quotient_self I]
    simpa [J, hJI] using
      (Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective K)
  have hIJ : I < J := lt_of_le_of_ne hIleJ hJne
  have hptJ :
      (algebraMap (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ))).IsFilteredColimitOfSmooth :=
    hind J hIJ
  let eS :
      ((R ⧸ I) ⧸ K) ≃+* (R ⧸ J) :=
    DoubleQuot.quotQuotEquivQuotOfLE (R := R) (I := I) (J := J) hIleJ
  let eT :
      ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
          Ideal.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) K) ≃+*
        (Λ ⧸ J.map (algebraMap R Λ)) :=
    (Ideal.quotEquivOfEq
        (quotientStepTargetIdeal_eq (S := R) (T := Λ) I J)).trans
      (DoubleQuot.quotQuotEquivQuotOfLE
        (R := Λ) (I := I.map (algebraMap R Λ)) (J := J.map (algebraMap R Λ))
        (Ideal.map_mono hIleJ))
  have hComm :
      eS.toRingHom.comp
          (algebraMap
            ((R ⧸ I) ⧸ K)
            ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
              Ideal.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) K)) =
        (algebraMap (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ))).comp eT.toRingHom := by
    -- Proof comment: both composites are quotient maps out of `R`, so it suffices to compare
    -- them on the canonical double-quotient generators.
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp [eS, eT, J]
  have hArrowIso :
      CategoryTheory.Arrow.mk
          (CommRingCat.ofHom
            (algebraMap
              ((R ⧸ I) ⧸ K)
              ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
                Ideal.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) K))) ≅
        CategoryTheory.Arrow.mk
          (CommRingCat.ofHom (algebraMap (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ)))) :=
    CategoryTheory.Arrow.isoMk
      (RingEquiv.toCommRingCatIso eS)
      (RingEquiv.toCommRingCatIso eT)
      (by
        ext r
        exact DFunLike.congr_fun hComm r)
  have hptArrow :
      CategoryTheory.MorphismProperty.ind
        (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom (algebraMap (R ⧸ J) (Λ ⧸ J.map (algebraMap R Λ)))) := by
    simpa [RingHom.IsFilteredColimitOfSmooth] using hptJ
  -- Route correction: after normalizing the quotient ideal by its preimage in `R`, PT is purely
  -- an owner-level arrow property transported across the standard source and target equivalences.
  exact
    (CategoryTheory.MorphismProperty.ind
        (RingHom.toMorphismProperty RingHom.Smooth)).prop_of_iso
      hArrowIso.symm hptArrow

/-- Helper for Lemma 16.8.4: a positive power of a nonzerodivisor generates a nonzero principal
ideal. -/
lemma span_singleton_pow_ne_bot_of_mem_nonZeroDivisors
    {S : Type u} [CommRing S] [Nontrivial S] {π : S} {n : ℕ}
    (hπ : π ∈ nonZeroDivisors S) :
    Ideal.span ({π ^ n} : Set S) ≠ ⊥ := by
  -- Proof comment: a nonzerodivisor has nonzero positive powers, so the principal ideal generated
  -- by such a power cannot be the zero ideal.
  intro hspan
  have hpow : π ^ n ∈ nonZeroDivisors S := pow_mem hπ n
  have hpow_cancel : ∀ x : S, π ^ n * x = 0 → x = 0 := (mem_nonZeroDivisors_iff.mp hpow).1
  have hpow_ne : π ^ n ≠ 0 := by
    intro hzero
    have hone : (1 : S) = 0 := hpow_cancel 1 (by simpa [hzero])
    exact one_ne_zero hone
  apply hpow_ne
  have hmem : π ^ n ∈ Ideal.span ({π ^ n} : Set S) :=
    Ideal.mem_span_singleton_self (π ^ n)
  simpa [hspan, Ideal.mem_bot] using hmem

/-- Helper for Lemma 16.8.4: the induction-step quotient PT applies to the principal quotient by
`π⁸` as soon as `π` is a nonzerodivisor. -/
lemma quotientPt_at_piPowEight_of_nonZeroDivisor
    {S : Type u} {T : Type u}
    [CommRing S] [Nontrivial S] [CommRing T] [Algebra S T]
    (hquot :
      ∀ K : Ideal S, K ≠ ⊥ →
        (algebraMap (S ⧸ K) (T ⧸ K.map (algebraMap S T))).IsFilteredColimitOfSmooth)
    {π : S} (hπ : π ∈ nonZeroDivisors S) :
    (algebraMap
        (S ⧸ Ideal.span ({π ^ 8} : Set S))
        (T ⧸ Ideal.map (algebraMap S T) (Ideal.span ({π ^ 8} : Set S)))).IsFilteredColimitOfSmooth := by
  -- Proof comment: `π⁸` remains a nonzerodivisor, hence nonzero, so the principal ideal `(π⁸)`
  -- is a genuine nonzero quotient to which the induction-step PT hypothesis applies.
  apply hquot
  exact span_singleton_pow_ne_bot_of_mem_nonZeroDivisors hπ

/-- Helper for Lemma 16.8.4: a nonzerodivisor has trivial self-torsion ideal. -/
lemma torsionOf_eq_bot_of_mem_nonZeroDivisors
    {S : Type u} [CommRing S] {x : S}
    (hx : x ∈ nonZeroDivisors S) :
    Ideal.torsionOf S S x = ⊥ := by
  ext a
  constructor
  · intro ha
    -- Proof comment: membership in the torsion ideal means `a * x = 0`, and the right-regularity
    -- half of `hx` forces `a = 0`.
    rw [Ideal.mem_bot]
    exact (mem_nonZeroDivisors_iff.mp hx).2 a (by simpa [Ideal.mem_torsionOf_iff, smul_eq_mul] using ha)
  · intro ha
    -- Proof comment: once `a = 0`, the torsion equation is immediate.
    rw [Ideal.mem_bot] at ha
    simpa [Ideal.mem_torsionOf_iff, smul_eq_mul, ha]

/-- Helper for Lemma 16.8.4: a nonzerodivisor satisfies the square-step annihilator equality
`Ann(π) = Ann(π²)` in its own ring. -/
lemma torsionOf_squareStep_of_mem_nonZeroDivisors
    {S : Type u} [CommRing S] {π : S}
    (hπ : π ∈ nonZeroDivisors S) :
    Ideal.torsionOf S S π = Ideal.torsionOf S S (π ^ 2) := by
  -- Proof comment: both torsion ideals are already zero because `π` and `π²` are nonzerodivisors.
  rw [torsionOf_eq_bot_of_mem_nonZeroDivisors hπ,
    torsionOf_eq_bot_of_mem_nonZeroDivisors (pow_mem hπ 2)]

/-- Helper for Lemma 16.8.4: flat base change transports the square-step annihilator equality
`Ann(π) = Ann(π²)`. -/
lemma torsionOf_squareStep_of_flat_algebra
    {S : Type u} {T : Type u}
    [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    {π : S}
    (hAnnS : Ideal.torsionOf S S π = Ideal.torsionOf S S (π ^ 2)) :
    Ideal.torsionOf T T (algebraMap S T π) =
      Ideal.torsionOf T T (algebraMap S T (π ^ 2)) := by
  let e := TensorProduct.AlgebraTensorModule.rid S T T
  have htransport :
      ∀ r : S,
        Ideal.torsionOf T (TensorProduct S T S) ((1 : T) ⊗ₜ[S] r) =
          Ideal.torsionOf T T (algebraMap S T r) := by
    intro r
    ext x
    rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    constructor
    · intro hx
      -- Proof comment: compare the tensor torsion equation with the scalar one through the
      -- right-unit tensor equivalence.
      have hx' := congrArg e hx
      simpa [e, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm,
        mul_left_comm, mul_assoc] using hx'
    · intro hx
      -- Proof comment: the same equivalence transports the scalar torsion equation back to the
      -- tensor-product model.
      apply e.injective
      simpa [e, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm,
        mul_left_comm, mul_assoc] using hx
  calc
    Ideal.torsionOf T T (algebraMap S T π) =
        Ideal.map (algebraMap S T) (Ideal.torsionOf S S π) := by
          symm
          calc
            Ideal.map (algebraMap S T) (Ideal.torsionOf S S π) =
                Ideal.torsionOf T (TensorProduct S T S) ((1 : T) ⊗ₜ[S] π) := by
                  simpa using
                    (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
                      (R := S) (S := T) (M := S) π)
            _ = Ideal.torsionOf T T (algebraMap S T π) := htransport π
    _ = Ideal.map (algebraMap S T) (Ideal.torsionOf S S (π ^ 2)) := by rw [hAnnS]
    _ = Ideal.torsionOf T T (algebraMap S T (π ^ 2)) := by
          calc
            Ideal.map (algebraMap S T) (Ideal.torsionOf S S (π ^ 2)) =
                Ideal.torsionOf T (TensorProduct S T S) ((1 : T) ⊗ₜ[S] (π ^ 2)) := by
                  simpa using
                    (Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat
                      (R := S) (S := T) (M := S) (π ^ 2))
            _ = Ideal.torsionOf T T (algebraMap S T (π ^ 2)) := htransport (π ^ 2)

/-- Lemma 16.8.4: if PT, namely `RingHom.IsFilteredColimitOfSmooth`, holds for every
Situation 16.8.1 whose source ring is a field, then PT holds for every Situation 16.8.1. -/
@[stacks 07F5]
theorem isFilteredColimitOfSmooth_of_forall_field_cases
    (hfield :
      ∀ {K A : Type u} [Field K] [CommRing A] [Algebra K A]
        [IsNoetherianRing A] [(algebraMap K A).IsRegularRingMap],
        (algebraMap K A).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  -- Route correction: the nilpotent-thickening reduction is now restored locally through the
  -- square-zero and nilpotent PT package above.
  -- Proof comment: the remaining route is still the textbook one: choose a quotient-minimal bad
  -- counterexample, prove the source reduced by the nilpotent theorem above, pass to the total
  -- quotient ring and its product-of-fields presentation, then descend the localized smooth
  -- factorization back through the `π⁸` desingularization package.
  --
  -- TODO: finish the reduced-source descent by importing the product PT bridge from
  -- `RingHom.IsFilteredColimitOfSmooth.prodMap`, the localized-to-global descent theorem
  -- `Algebra.exists_factorization_with_elementaryStandard_of_localized_smooth_factorization`,
  -- and the `π⁸` factorization package from Lemma `16.7.3`; the first unresolved blocker is that
  -- the owner proofs in `Chap16/Lemma_16_8_2.lean` and `Chap16/Lemma_16_8_3.lean` still end in
  -- `sorry`, so the reduced total-quotient descent cannot yet be executed locally in this file.
  let _ := hfield
  sorry

end

end Algebra
