import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap10.Lemma_10_97_2
import stacks_proof.stacks_project.Chap10.Lemma_10_97_7
import stacks_proof.stacks_project.Chap10.Lemma_10_99_11
import stacks_proof.stacks_project.Chap15.Lemma_15_3_5
import stacks_proof.stacks_project.Chap15.Lemma_15_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "BCompletion" => AdicCompletion (maximalIdeal B) B
local notation "CompletionMap" => maximalIdealCompletionMap (algebraMap A B)
set_option quotPrecheck false in
local notation "Tor₁[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/-- Helper for Lemma 15.43.9: the maximal-ideal completion of a Noetherian local ring remains
Noetherian. -/
local instance source_completion_isNoetherianRing : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

/-- Helper for Lemma 15.43.9: the target maximal-ideal completion remains Noetherian. -/
local instance target_completion_isNoetherianRing : IsNoetherianRing BCompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal B)

/- The comparison map on maximal-ideal completions is the owner theorem
`maximalIdealCompletionMap_comp` from Lemma `10.97.7`, specialized to `algebraMap A B`. -/
recall maximalIdealCompletionMap_comp

/-- Helper for Lemma 15.43.9: the maximal-ideal completion map of any local ring is a local
homomorphism. -/
private theorem completion_isLocalHom_of_local_ring
    {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  let φ : AdicCompletion (maximalIdeal R) R →+* R ⧸ maximalIdeal R :=
    (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom
  have hcomp :
      φ.comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
        Ideal.Quotient.mk (maximalIdeal R) := by
    -- Evaluating a completed element modulo the closed point recovers the quotient map.
    ext x
    simp [φ]
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
    simpa [hcomp]
  exact isLocalHom_of_comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) φ

/-- Helper for Lemma 15.43.9: the comparison map on maximal-ideal completions is a local
homomorphism. -/
local instance completion_comparison_isLocalHom :
    IsLocalHom CompletionMap := by
  -- TODO: deduce locality of `CompletionMap` by composing with the surjective evaluation map
  -- `B^∧ -> B / m_B` and comparing with the local quotient map of `A -> B`.
  sorry

/-- Helper for Lemma 15.43.9: in the maximal-ideal completion of a Noetherian local ring, the
extended maximal ideal agrees with the actual maximal ideal. -/
lemma completion_map_maximalIdeal_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R) =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  let RCompletion := AdicCompletion (maximalIdeal R) R
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  letI : Field (R ⧸ (maximalIdeal R) ^ 1) := by
    let e : R ⧸ (maximalIdeal R) ^ 1 ≃+* R ⧸ maximalIdeal R :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal R))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  have hker :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) 1
  have hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) := by
    simpa [hker] using
      (RingHom.ker_isMaximal_of_surjective
        (AdicCompletion.evalₐ (maximalIdeal R) 1)
        (AdicCompletion.surjective_evalₐ (maximalIdeal R) 1) :
          Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1)))
  letI :
      Ideal.IsMaximal (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) := hmax
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Lemma 15.43.9: a surjective local homomorphism induces a bijection on residue
fields. -/
lemma residueField_bijective_of_surjective_localHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Nontrivial S]
    (f : R →+* S) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · exact RingHom.injective (ResidueField.map f)
  · intro z
    -- Lift a residue-class target element back through the surjective local map `f`.
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, rfl⟩ := hf_surj s
    refine ⟨residue R r, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f r

/-- Helper for Lemma 15.43.9: the maximal-ideal completion map of a Noetherian local ring induces
an isomorphism on residue fields. -/
lemma maximalIdealCompletion_residueField_bijective
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Function.Bijective (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  let RCompletion := AdicCompletion (maximalIdeal R) R
  let φ : RCompletion →+* R ⧸ maximalIdeal R :=
    (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom
  have hφ_surj : Function.Surjective φ :=
    AdicCompletion.evalOneₐ_surjective (maximalIdeal R)
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  letI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom φ := Function.Surjective.isLocalHom _ hφ_surj
  have hquot :
      Function.Bijective (ResidueField.map (Ideal.Quotient.mk (maximalIdeal R))) :=
    residueField_bijective_of_surjective_localHom
      (f := Ideal.Quotient.mk (maximalIdeal R)) Ideal.Quotient.mk_surjective
  have hφ :
      Function.Bijective (ResidueField.map φ) :=
    residueField_bijective_of_surjective_localHom (f := φ) hφ_surj
  have hcomp :
      (ResidueField.map φ).comp (ResidueField.map (algebraMap R RCompletion)) =
        ResidueField.map (Ideal.Quotient.mk (maximalIdeal R)) := by
    -- Evaluating the completion modulo the closed point recovers the ordinary quotient map.
    ext x
    simp [φ]
  constructor
  · intro x y hxy
    apply hquot.1
    simpa [Function.comp, hcomp] using congrArg (ResidueField.map φ) hxy
  · intro z
    obtain ⟨x, hx⟩ := hquot.2 ((ResidueField.map φ) z)
    refine ⟨x, ?_⟩
    apply hφ.1
    simpa [Function.comp, hcomp] using hx

/-- Helper for Lemma 15.43.9: quotienting a local ring by its maximal ideal gives the usual
residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    R ⧸ maximalIdeal R ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).trans
      ((RingEquiv.ofBijective
        (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm)

/-- Helper for Lemma 15.43.9: under the quotient-to-residue-field identification, the class of
`a` is its ordinary residue class. -/
private theorem maximalIdealQuotientResidueFieldEquiv_apply_mk
    (R : Type u) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdealQuotientResidueFieldEquiv R (Ideal.Quotient.mk (maximalIdeal R) a) =
      residue R a := by
  -- TODO: verify that the quotient-to-residue-field equivalence sends the class of `a` to
  -- the ordinary residue class of `a`.
  sorry

/-- Helper for Lemma 15.43.9: quotient maps to residue fields commute with local homomorphisms. -/
private theorem maximalIdealQuotientResidueFieldEquiv_comp_quotientMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    (maximalIdealQuotientResidueFieldEquiv S).toRingHom.comp
        ((Ideal.Quotient.mk (maximalIdeal S)).comp f) =
      (ResidueField.map f).comp
        ((maximalIdealQuotientResidueFieldEquiv R).toRingHom.comp
          (Ideal.Quotient.mk (maximalIdeal R))) := by
  -- TODO: compare the quotient-to-residue-field identifications on representatives and use
  -- `ResidueField.map_residue`.
  sorry

/-- Helper for Lemma 15.43.9: the quotient ring `S / IS` is the same `R`-module quotient as
`S / I • S`. -/
private noncomputable abbrev ideal_quotient_equiv_module_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) :
    (S ⧸ Ideal.map (algebraMap R S) I) ≃ₗ[R]
      (S ⧸ ((I • (⊤ : Submodule R S)) : Submodule R S)) :=
  (Submodule.Quotient.restrictScalarsEquiv R (Ideal.map (algebraMap R S) I : Ideal S)).symm.trans
    (Submodule.quotEquivOfEq
      (Submodule.restrictScalars R (Ideal.map (algebraMap R S) I : Submodule S S))
      ((I • (⊤ : Submodule R S)) : Submodule R S)
      (Ideal.smul_top_eq_map I).symm)

/-- Helper for Lemma 15.43.9: the quotient-model bridge sends an ideal quotient class to the
corresponding module quotient class. -/
private theorem ideal_quotient_equiv_module_quotient_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (x : S) :
    ideal_quotient_equiv_module_quotient (R := R) (S := S) I
        ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) x) =
      ((I • (⊤ : Submodule R S)) : Submodule R S).mkQ x := by
  have hrestrict :
      (Submodule.Quotient.restrictScalarsEquiv R (Ideal.map (algebraMap R S) I : Ideal S)).symm
          ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) x) =
        Submodule.Quotient.mk x := by
    -- Forgetting from the ring quotient to the matching module quotient fixes quotient generators.
    apply (Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.map (algebraMap R S) I : Ideal S)).injective
    simpa [Ideal.Quotient.mk_eq_mk] using
      (Submodule.Quotient.restrictScalarsEquiv_mk R
        (Ideal.map (algebraMap R S) I : Ideal S) x)
  -- Compute the bridge one quotient-model change at a time.
  calc
    ideal_quotient_equiv_module_quotient (R := R) (S := S) I
        ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) x)
      = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars R
            (Ideal.map (algebraMap R S) I : Submodule S S))
          ((I • (⊤ : Submodule R S)) : Submodule R S)
          (Ideal.smul_top_eq_map I).symm)
          ((Submodule.Quotient.restrictScalarsEquiv R
            (Ideal.map (algebraMap R S) I : Ideal S)).symm
            ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) x)) := by
            rfl
    _ = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars R
            (Ideal.map (algebraMap R S) I : Submodule S S))
          ((I • (⊤ : Submodule R S)) : Submodule R S)
          (Ideal.smul_top_eq_map I).symm)
          (Submodule.Quotient.mk x) := by
            rw [hrestrict]
    _ = ((I • (⊤ : Submodule R S)) : Submodule R S).mkQ x := by
            simpa using
              (Submodule.quotEquivOfEq_mk
                (Submodule.restrictScalars R
                  (Ideal.map (algebraMap R S) I : Submodule S S))
                ((I • (⊤ : Submodule R S)) : Submodule R S)
                (Ideal.smul_top_eq_map I).symm x)

/-- Helper for Lemma 15.43.9: evaluating an induced quotient map on a quotient class amounts to
first applying the linear map and then quotienting. -/
private theorem quotientMapByIdeal_apply_mkQ
    {R : Type u}
    {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    f.quotientMapByIdeal I ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := by
  -- Unfold the induced quotient map through the defining `mapQ_mkQ` square.
  simpa [LinearMap.quotientMapByIdeal] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) f) x

/-- Helper for Lemma 15.43.9: quotienting a flat ring map by a source ideal preserves flatness. -/
private theorem quotientMap_flat_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (hφ : φ.Flat) :
    (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).Flat := by
  let _ : Algebra R S := φ.toAlgebra
  let e : S ⧸ Ideal.map φ I ≃+* ((R ⧸ I) ⊗[R] S) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv).trans
      (Algebra.TensorProduct.comm R S (R ⧸ I)).toRingEquiv
  -- First rewrite flatness of `φ` into the canonical algebra-map form and base change to `R ⧸ I`.
  have hφ_alg : (algebraMap R S).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hbaseModule : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := by
    let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hφ_alg
    simpa using (Module.Flat.baseChange (R := R) (S := R ⧸ I) (M := S))
  have hbase :
      (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hbaseModule
  -- Then transport flatness across the canonical quotient/tensor ring equivalence.
  have he : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  have hcomp :
      (e.symm.toRingHom.comp (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S))).Flat :=
    RingHom.Flat.comp hbase he
  have hEq :
      e.symm.toRingHom.comp (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] S)) =
        Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map := by
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
          ((Algebra.TensorProduct.comm R S (R ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[R] (1 : S))) =
        (Ideal.Quotient.mk (Ideal.map φ I)) (φ x)
    have hcomm :
        (Algebra.TensorProduct.comm R S (R ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[R] (1 : S)) =
          (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I x) := by
      simpa using
        (Algebra.TensorProduct.comm_symm_tmul (R := R) (a := (1 : S))
          (b := Ideal.Quotient.mk I x))
    rw [hcomm, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : S) = φ x := by
      change (algebraMap R S x) * 1 = φ x
      simpa [RingHom.algebraMap_toAlgebra]
    simpa [RingHom.algebraMap_toAlgebra, hs]
  rw [← hEq]
  exact hcomp

/-- Helper for Lemma 15.43.9: if a local homomorphism identifies the maximal ideal and induces a
bijection on residue fields, then the induced map on the closed-point quotients is surjective. -/
lemma quotientMap_surjective_of_maximalIdeal_map_eq_and_residueField_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    (hmax : Ideal.map f (maximalIdeal R) = maximalIdeal S)
    (hres : Function.Bijective (ResidueField.map f)) :
    Function.Surjective
      (Ideal.quotientMap (Ideal.map f (maximalIdeal R)) f Ideal.le_comap_map) := by
  -- TODO: identify the closed-point quotient with `ResidueField S`, pull back along the residue
  -- field bijection, and descend to a quotient preimage.
  let _ := hmax
  let _ := hres
  sorry

/-- Helper for Lemma 15.43.9: the closed-point quotient is finite over the source residue field,
and the corresponding module quotient is flat over that field. -/
private theorem closed_point_quotient_finite_and_mod_flat
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Module.Finite (A ⧸ maximalIdeal A) (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ∧
      Module.Flat (A ⧸ maximalIdeal A)
        (B ⧸ ((maximalIdeal A) • (⊤ : Submodule A B))) := by
  -- TODO: re-establish the closed-fiber finiteness and flatness package from the quotient
  -- surjectivity statement induced by `hmax` and `hres`.
  let _ := hmax
  let _ := hres
  sorry

/-- Helper for Lemma 15.43.9: the source proof first makes the `m_A`-adic completion of `B`
flat over `A^∧`, and the only remaining gap is transporting that flatness across the comparison
equivalence from Lemma `10.97.7`. -/
private theorem completion_comparison_comp_source_completion_map
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    let hclosed := closed_point_quotient_finite_and_mod_flat (A := A) (B := B) hmax hres
    let hfiniteQuotient :
        Module.Finite (A ⧸ maximalIdeal A)
          (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := hclosed.1
    let eCompletion :=
      maximalIdealCompletionAlgEquivMadicCompletion
        (R := A) (S := B)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) hfiniteQuotient
    eCompletion.toRingHom.comp CompletionMap =
      algebraMap ACompletion (AdicCompletion (Ideal.map (algebraMap A B) (maximalIdeal A)) B) := by
  -- TODO: compare the algebra structures on the completion comparison by evaluating both sides on
  -- the dense image of `A` inside `A^∧`.
  let _ := hmax
  let _ := hres
  sorry

/-- Helper for Lemma 15.43.9: the comparison equivalence from Lemma `10.97.7` is linear over the
source completion `A^∧`. -/
private noncomputable def completion_comparison_linearEquiv_over_source_completion
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    BCompletion ≃ₗ[ACompletion] AdicCompletion (Ideal.map (algebraMap A B) (maximalIdeal A)) B :=
  -- TODO: promote the comparison ring equivalence to an `A^∧`-linear equivalence once the source
  -- completion algebra comparison is restored.
  sorry

/-- Helper for Lemma 15.43.9: the completion comparison is flat over `A^∧`, proved by checking
flatness on all quotients by powers of the maximal ideal of `A^∧`. -/
private theorem completion_comparison_flat
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Module.Flat ACompletion BCompletion := by
  -- TODO: finish the quotientwise local-criterion route. The stabilized frontier is the explicit
  -- normalization of completion quotients to the source quotients `A / m_A^n`; the remaining
  -- blocker is transporting those normalized quotient maps into the module-quotient flatness
  -- hypothesis required by `flat_of_isLocalRing_and_flat_quotients_by_ideal_powers`.
  sorry

/-- Helper for Lemma 15.43.9: the completion comparison induces the expected residue-field
bijection after composing the canonical residue-field isomorphisms on both sides. -/
private theorem completion_comparison_residueField_bijective
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Bijective (ResidueField.map CompletionMap) := by
  -- TODO: compose the original residue-field bijection with the canonical residue-field
  -- bijections of `A -> A^∧` and `B -> B^∧`, after first fixing the local-hom instance plumbing
  -- for `CompletionMap`.
  let _ := hmax
  let _ := hres
  sorry

/-- Helper for Lemma 15.43.9: the completion comparison carries the maximal ideal of the source
completion onto the maximal ideal of the target completion. -/
private theorem completion_comparison_maximalIdeal_eq
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    Ideal.map CompletionMap (maximalIdeal ACompletion) = maximalIdeal BCompletion := by
  -- TODO: push the hypothesis `m_A B = m_B` through the completion comparison and identify the
  -- resulting target ideal with `maximalIdeal BCompletion`.
  let _ := hmax
  sorry

/-- Helper for Lemma 15.43.9: after identifying the closed-point quotient with the common residue
field, the induced quotient linear map of a local algebra map is bijective. -/
private theorem quotient_algebraLinearMap_bijective_of_maximalIdeal_map_eq_and_residueField_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (hmax : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S)
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    Function.Bijective ((Algebra.linearMap R S).quotientMapByIdeal (maximalIdeal R)) := by
  -- TODO: complete the bridge from the ring-quotient bijection
  -- `R / m_R ≃ S / m_R S` to the module-quotient map used by
  -- `bijective_of_bijective_mod_jacobson_of_finite_projective`.
  let _ := hmax
  let _ := hres
  sorry

/-- Helper for Lemma 15.43.9: a finite free local algebra map whose closed fiber is identified
with the residue field is already bijective. -/
private theorem bijective_of_finite_free_and_maximalIdeal_map_eq_and_residueField_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [Module.Free R S]
    (hmax : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S)
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    Function.Bijective (algebraMap R S) := by
  let _ : Module.Projective R S := inferInstance
  have hquot :
      Function.Bijective ((Algebra.linearMap R S).quotientMapByIdeal (maximalIdeal R)) :=
    quotient_algebraLinearMap_bijective_of_maximalIdeal_map_eq_and_residueField_bijective
      (R := R) (S := S) hmax hres
  have hJac : maximalIdeal R ≤ Ring.jacobson R := by
    simpa [Ideal.jacobson_bot] using (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  -- Route correction: use the chapter-level Jacobson-radical lifting theorem instead of a new
  -- rank-one basis count on the free module.
  simpa using
    bijective_of_bijective_mod_jacobson_of_finite_projective
      (R := R) (P := R) (P' := S) (I := maximalIdeal R)
      hJac (Algebra.linearMap R S) hquot

-- Proof sketch: apply Lemma `10.97.7` to identify `B^∧` with the completion of `B` along
-- `maximalIdeal A`, package the source flatness step through Lemma `15.43.8`, then invoke
-- `Module.free_of_flat_of_isLocalRing` from Lemma `10.78.5`. The residue-field bijectivity
-- hypothesis shows that the closed fiber has dimension one over the residue field, so the free
-- module has rank `1`, forcing the canonical completion map to be bijective.
/-- Lemma 15.43.9: if `A → B` is a flat local homomorphism of Noetherian local rings, the
maximal ideal of `B` is the extension of the maximal ideal of `A`, and the induced map on residue
fields is bijective, then the induced map `A^∧ → B^∧` on maximal-ideal completions is
bijective. -/
@[stacks 0AGX]
theorem maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Bijective (maximalIdealCompletionMap (algebraMap A B)) := by
  -- Route correction: follow the source proof through the finite/flat/free structure on
  -- completions, rather than the abandoned quotient-power injectivity route.
  have hclosed := closed_point_quotient_finite_and_mod_flat (A := A) (B := B) hmax hres
  have hfiniteCompletion : Module.Finite ACompletion BCompletion :=
    maximalIdealCompletion_finite
      (R := A) (S := B)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) hclosed.1
  have hflatCompletion : Module.Flat ACompletion BCompletion :=
    completion_comparison_flat (A := A) (B := B) hmax hres
  let _ : Module.Finite ACompletion BCompletion := hfiniteCompletion
  let _ : Module.Flat ACompletion BCompletion := hflatCompletion
  let _ : Module.Free ACompletion BCompletion := Module.free_of_flat_of_isLocalRing
  have hmaxCompletion :
      Ideal.map CompletionMap (maximalIdeal ACompletion) = maximalIdeal BCompletion :=
    completion_comparison_maximalIdeal_eq (A := A) (B := B) hmax
  have hresCompletion :
      Function.Bijective (ResidueField.map CompletionMap) :=
    completion_comparison_residueField_bijective (A := A) (B := B) hmax hres
  -- The finite free completion map is bijective once its closed fiber is the common residue field.
  change Function.Bijective (algebraMap ACompletion BCompletion)
  exact
    bijective_of_finite_free_and_maximalIdeal_map_eq_and_residueField_bijective
      (R := ACompletion) (S := BCompletion) hmaxCompletion hresCompletion

end
