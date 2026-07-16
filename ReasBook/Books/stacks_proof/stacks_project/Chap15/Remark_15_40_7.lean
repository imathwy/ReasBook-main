import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_1
import stacks_proof.stacks_project.Chap10.Lemma_10_99_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_8
import stacks_proof.stacks_project.Chap10.Lemma_10_160_2
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Lemma_15_40_6
import stacks_proof.stacks_project.Chap15.Proposition_15_40_5

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open AdicCompletion
open IsLocalRing
open scoped TensorProduct Pointwise

universe u v w

section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing A'] [IsCompleteLocalRing A']
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]

local notation "κA" => ResidueField A
local notation "κA'" => ResidueField A'
local notation "ClosedFiberB" => Ideal.Fiber (maximalIdeal A') B
local notation "𝔪ClosedFiberB" => Ideal.map (algebraMap B ClosedFiberB) (maximalIdeal B)

variable (A) (A') in
private abbrev completedBaseChangeIdeal [CommRing A] [CommRing A'] [Algebra A A'] [IsLocalRing A]
    (C : Type*) [CommRing C] [Algebra A C] :
    Ideal (C ⊗[A] A') :=
  Ideal.map (algebraMap A (C ⊗[A] A')) (maximalIdeal A)

/-- The completed base change of an `A`-algebra `C` along the local map `A → A'`, completed with
respect to the ideal induced by `maximalIdeal A`. -/
abbrev completedBaseChange (A : Type u) (A' : Type v) [CommRing A] [CommRing A']
    [Algebra A A'] [IsLocalRing A] (C : Type*) [CommRing C] [Algebra A C] :=
  AdicCompletion (completedBaseChangeIdeal A A' C) (C ⊗[A] A')

/- Domain-style sampling for Remark 15.40.7:
- primary domain: complete local lifts with prescribed formally smooth closed fiber under a local
  base change with residue-field identification;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Ideal.ResidueField.mapₐ`,
  `Algebra.TensorProduct.productMap`,
  `algebraMap A (C ⊗[A] A')`,
  `RingHom.adicCompletionMap`,
  `AdicCompletion.ofAlgEquiv`,
  `RingHom.formally_smooth_for_adic`,
  `exists_completeLocal_formallySmooth_lift_with_closedFiber`;
- best owner abstraction: the closed fiber should stay on the canonical owner
  `ClosedFiberB = Ideal.Fiber (maximalIdeal A') B`, and the comparison with
  the completed base change of `C` along `A → A'` should be the canonical `maximalIdeal A`-adic
  completion of `C ⊗[A] A'`, with comparison map induced by `algebraMap C B` and
  `algebraMap A' B`, not a separate wrapper predicate;
- primitive data: the local maps `A → A' → B`, the induced residue-field comparison
  on the maximal-ideal residue fields, and the adic formal smoothness of
  `κ(A') → ClosedFiberB`;
- derived API: the lifted complete local `A`-algebra `C`, the canonical completed base-change map
  `completedBaseChange C → B`, its surjectivity, and the surjective/finite/flat consequences.

Source/core/bridge triage:
- `source-facing`: the base-change variant of the complete-local lifting statement;
- `core/canonical`: `Ideal.Fiber`, `RingHom.formally_smooth_for_adic`, and
  `exists_completeLocal_formallySmooth_lift_with_closedFiber`, together with the completion owner
  `RingHom.adicCompletionMap`;
- `bridge/view`: the residue-field comparison on the closed fiber and the tensor-product
  presentation of the `maximalIdeal A`-adic completed base change before completion.
-/

variable (A) (A') (B) in
private abbrev tensorProductToTarget
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    C ⊗[A] A' →+* B :=
  (Algebra.TensorProduct.productMap
    ((Algebra.ofId C B).restrictScalars A)
    ((Algebra.ofId A' B).restrictScalars A)).toRingHom

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A'] [IsCompleteLocalRing A']
  [IsNoetherianRing B] [IsCompleteLocalRing B] [IsLocalHom (algebraMap A A')]
  [IsLocalHom (algebraMap A' B)] in
private theorem tensorProductToTarget_comp_algebraMap
    {C : Type*} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    (tensorProductToTarget A A' B C).comp
        (algebraMap A (C ⊗[A] A')) =
      algebraMap A B := by
  ext x
  simp [tensorProductToTarget]

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A']
  [IsCompleteLocalRing A'] [IsNoetherianRing B] [IsCompleteLocalRing B] in
private theorem baseChangeIdeal_le_comap_maximalIdeal
    {C : Type*} [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B] [hAA' : IsLocalHom (algebraMap A A')]
    [hA'B : IsLocalHom (algebraMap A' B)] :
    completedBaseChangeIdeal A A' C ≤
      Ideal.comap (tensorProductToTarget A A' B C)
        (maximalIdeal B) := by
  let _ : IsLocalHom (algebraMap A A') := hAA'
  let _ : IsLocalHom (algebraMap A' B) := hA'B
  letI : IsLocalHom (algebraMap A B) := by
    simpa [IsScalarTower.algebraMap_eq A A' B] using
      (RingHom.isLocalHom_comp (algebraMap A' B) (algebraMap A A') :
        IsLocalHom ((algebraMap A' B).comp (algebraMap A A')))
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, tensorProductToTarget_comp_algebraMap]
  exact Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le (algebraMap A B))

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A']
  [IsCompleteLocalRing A'] [IsNoetherianRing B] [IsCompleteLocalRing B]
  [IsLocalHom (algebraMap A A')] in
private theorem tensorProductToTarget_continuous
    {C : Type*} [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B] [hAA' : IsLocalHom (algebraMap A A')]
    [hA'B : IsLocalHom (algebraMap A' B)] :
    letI : TopologicalSpace (C ⊗[A] A') :=
      Ideal.adicTopology (completedBaseChangeIdeal A A' C)
    letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
    Continuous (tensorProductToTarget A A' B C) := by
  let _ : IsLocalHom (algebraMap A A') := hAA'
  let _ : IsLocalHom (algebraMap A' B) := hA'B
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  have hle :
      completedBaseChangeIdeal A A' C ≤
        Ideal.comap (tensorProductToTarget A A' B C) (maximalIdeal B) :=
    baseChangeIdeal_le_comap_maximalIdeal
  simpa [pow_one] using Ideal.map_le_iff_le_comap.mpr hle

/-- The canonical completed base-change map
`completedBaseChange C → B` induced by `C → B` and `A' → B`. -/
noncomputable def completedBaseChangeMap (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B]
    [IsScalarTower A A' B] [IsLocalRing A] [IsCompleteLocalRing B]
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    completedBaseChange A A' C →+* B :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal B)).symm.toRingHom.comp
    (RingHom.adicCompletionMap
      (tensorProductToTarget A A' B C)
      (completedBaseChangeIdeal A A' C) (maximalIdeal B)
      tensorProductToTarget_continuous)

/-- Helper for Remark 15.40.7: a ring equivalence is topologically formally smooth for the
discrete topologies on source and target. -/
private theorem ringEquiv_formallySmoothTopologically
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S) :
    letI : TopologicalSpace R := ⊥
    letI : TopologicalSpace S := ⊥
    RingHom.FormallySmoothTopologically.{u, v, 0} e.toRingHom := by
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  refine
    { toContinuous := continuous_of_discreteTopology
      lift_condition := ?_ }
  intro A _ _ _ J _ hJ g hg g0 hg0 hcomm
  -- Proof comment: precompose the given source map with the inverse equivalence; the two
  -- required identities are just the commutative square rewritten through `e.symm`.
  refine ⟨g0.comp e.symm.toRingHom, continuous_of_discreteTopology, ?_, ?_⟩
  · ext s
    have hs := DFunLike.congr_fun hcomm (e.symm s)
    simpa using hs
  · ext r
    simp

/-- Helper for Remark 15.40.7: transport the adic formal smoothness of the closed fiber from the
target residue field `κ(A')` to the source residue field `κ(A)` using the residue-field
isomorphism induced by `A → A'`. -/
private theorem closedFiber_formally_smooth_over_source_residue
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hfs :
      (algebraMap κA' ClosedFiberB).formally_smooth_for_adic 𝔪ClosedFiberB) :
    let eκ : κA ≃+* κA' :=
      RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ
    letI : Algebra κA ClosedFiberB :=
      ((algebraMap κA' ClosedFiberB).comp eκ.toRingHom).toAlgebra
    (algebraMap κA ClosedFiberB).formally_smooth_for_adic 𝔪ClosedFiberB := by
  let eκ : κA ≃+* κA' :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ
  letI : Algebra κA ClosedFiberB :=
    ((algebraMap κA' ClosedFiberB).comp eκ.toRingHom).toAlgebra
  -- Proof comment: after switching the `κ(A)`-algebra structure on the closed fiber through the
  -- residue-field equivalence, the desired map is literally the composite
  -- `κ(A) --eκ--> κ(A') --> ClosedFiberB`.
  rw [RingHom.formally_smooth_for_adic_iff] at hfs ⊢
  letI : TopologicalSpace κA := ⊥
  letI : DiscreteTopology κA := ⟨rfl⟩
  letI : TopologicalSpace κA' := ⊥
  letI : DiscreteTopology κA' := ⟨rfl⟩
  letI : TopologicalSpace ClosedFiberB := Ideal.adicTopology 𝔪ClosedFiberB
  -- Proof comment: composition preserves topological formal smoothness, so the transported
  -- source-residue map inherits the same lifting property.
  simpa [eκ] using
    RingHom.FormallySmoothTopologically.comp
      (ringEquiv_formallySmoothTopologically eκ) hfs

/-- Helper for Remark 15.40.7: a closed-fiber identification yields the corresponding quotient
equivalence `C / 𝔪_A C ≃ B / 𝔪_{A'} B`. -/
private noncomputable def closedFiber_identification_to_target_quotient_equiv
    {C : Type*} [CommRing C] [Algebra A C] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    C ⧸ Ideal.map (algebraMap A C) (maximalIdeal A) ≃+*
      B ⧸ Ideal.map (algebraMap A' B) (maximalIdeal A') :=
  ((closedFiberQuotAlgEquiv (R := A) (S := C)).symm.toRingEquiv.trans e.toRingEquiv).trans
    (closedFiberQuotAlgEquiv (R := A') (S := B)).toRingEquiv

/-- Helper for Remark 15.40.7: the canonical quotient presentation of a closed fiber agrees with
the target algebra map into the tensor-product model. -/
private theorem closedFiber_quotient_comp_eq_algebraMap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    ((closedFiberQuotAlgEquiv (R := R) (S := S)).symm.toRingHom).comp
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R))) =
      algebraMap S (Ideal.Fiber (maximalIdeal R) S) := by
  -- Proof comment: this is the owner-level bridge between the source proof's quotient model
  -- `S / m_R S` and the canonical tensor closed fiber `Ideal.Fiber (maximalIdeal R) S`.
  ext s
  -- Proof comment: after rewriting the closed-fiber algebra map as the tensor `includeRight`
  -- branch, the quotient/tensor equivalence sends the class of `s` to the same pure tensor.
  change
    ((closedFiberQuotAlgEquiv (R := R) (S := S)).symm
      ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R))) s)) =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] Ideal.Fiber (maximalIdeal R) S) s
  simp [closedFiberQuotAlgEquiv]

/-- Helper for Remark 15.40.7: a closed-fiber identification induces a canonical surjective map
from `C` onto the quotient `B / 𝔪_{A'} B`. -/
private noncomputable def closedFiber_identification_to_target_quotient
    {C : Type*} [CommRing C] [Algebra A C] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    C →+* B ⧸ Ideal.map (algebraMap A' B) (maximalIdeal A') :=
  (closedFiber_identification_to_target_quotient_equiv (A := A) (A' := A') (B := B) e).toRingHom.comp
    (Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A)))

/-- Helper for Remark 15.40.7: the quotient map induced by a closed-fiber identification is
surjective because both quotient presentations are canonical closed-fiber models. -/
private theorem closedFiber_identification_to_target_quotient_surjective
    {C : Type*} [CommRing C] [Algebra A C] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    Function.Surjective
      (closedFiber_identification_to_target_quotient (A := A) (A' := A') (B := B) e) := by
  intro y
  -- Proof comment: lift `y` first through the quotient of `C`, then through the quotient map
  -- `C → C / 𝔪_A C`.
  obtain ⟨x, rfl⟩ :=
    (closedFiber_identification_to_target_quotient_equiv (A := A) (A' := A') (B := B) e).surjective y
  obtain ⟨c, rfl⟩ :=
    Ideal.Quotient.mk_surjective x
  refine ⟨c, ?_⟩
  rfl

/-- Helper for Remark 15.40.7: after transporting the `κ(A)`-algebra structure on the target
closed fiber through the residue-field isomorphism induced by `A → A'`, residue classes from `A`
map to the same element whether one first passes through `κ(A)` or through `κ(A')`. -/
private theorem closedFiber_transport_residue_eq
    [Algebra κA ClosedFiberB]
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hBalg :
      algebraMap κA ClosedFiberB =
        (algebraMap κA' ClosedFiberB).comp
          (RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ).toRingHom)
    (a : A) :
    algebraMap κA ClosedFiberB (residue A a) =
      algebraMap κA' ClosedFiberB (residue A' (algebraMap A A' a)) := by
  let eκ : κA ≃+* κA' :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ
  -- Proof comment: evaluate the transported-algebra identity on the residue class of `a`, then
  -- rewrite the middle term with `ResidueField.map_residue`.
  have htransport :=
    congrArg (fun f : κA →+* ClosedFiberB ↦ f (residue A a)) hBalg
  simpa [eκ, RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] using htransport

/-- Helper for Remark 15.40.7: the quotient-model point corresponding to a residue class is the
usual quotient class of the original element. -/
private theorem residue_to_quotient_class
    {R : Type*} [CommRing R] [IsLocalRing R]
    (a : R) :
    (RingEquiv.ofBijective
      (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R a)) =
    (Ideal.Quotient.mk (maximalIdeal R)) a := by
  -- Proof comment: rewrite the residue-class element through the quotient model of the residue
  -- field and then apply the inverse of the canonical quotient/residue-field equivalence.
  rw [show algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R a) =
      algebraMap R (maximalIdeal R).ResidueField a by rfl]
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField
        ((Ideal.Quotient.mk (maximalIdeal R)) a) by rfl]
  exact
    (RingEquiv.ofBijective
      (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm_apply_apply
      ((Ideal.Quotient.mk (maximalIdeal R)) a)

/-- Helper for Remark 15.40.7: under the canonical quotient presentation of the closed fiber, the
image of a residue class is the quotient class of the original element of the source ring. -/
private theorem closedFiberQuotAlgEquiv_apply_residue
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    (a : R) :
    closedFiberQuotAlgEquiv (R := R) (S := S)
      (algebraMap (ResidueField R) (Ideal.Fiber (maximalIdeal R) S) (residue R a)) =
    algebraMap S (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) (algebraMap R S a) := by
  -- Proof comment: unfold the quotient model once, convert the residue-class coordinate into the
  -- actual quotient class of `a`, and finish with the tensor/quotient comparison.
  simp [closedFiberQuotAlgEquiv]
  change
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm
      (1 ⊗ₜ[R]
        (RingEquiv.ofBijective
          (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
          (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm
          (algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R a))) =
      algebraMap R (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) a
  rw [residue_to_quotient_class (R := R) a]
  simp [Algebra.smul_def]

/-- Helper for Remark 15.40.7: in the canonical tensor model of a closed fiber, the image of an
element coming from the source ring agrees with the image of its residue class. -/
private theorem closedFiber_algebraMap_eq_residue
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    (a : R) :
    algebraMap S (Ideal.Fiber (maximalIdeal R) S) (algebraMap R S a) =
      algebraMap (ResidueField R) (Ideal.Fiber (maximalIdeal R) S) (residue R a) := by
  -- Proof comment: in the tensor-model closed fiber, both sides are the same pure tensor coming
  -- from `a`, viewed either through the right factor `S` or through the left residue-field factor.
  change (Algebra.TensorProduct.includeRight : S →ₐ[R] Ideal.Fiber (maximalIdeal R) S)
      (algebraMap R S a) =
    (Algebra.TensorProduct.includeLeft : (maximalIdeal R).ResidueField →ₐ[R]
      Ideal.Fiber (maximalIdeal R) S) (algebraMap R (maximalIdeal R).ResidueField a)
  simp

/-- Helper for Remark 15.40.7: the quotient map induced by a closed-fiber identification makes
the `A`-algebra square commute modulo `Ideal.map (algebraMap A' B) (maximalIdeal A')`. -/
private theorem closedFiber_identification_to_target_quotient_comp_algebraMap
    {C : Type*} [CommRing C] [Algebra A C] [IsLocalRing C] [IsLocalHom (algebraMap A C)]
    [Algebra κA ClosedFiberB]
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hBalg :
      algebraMap κA ClosedFiberB =
        (algebraMap κA' ClosedFiberB).comp
          (RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ).toRingHom)
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    (closedFiber_identification_to_target_quotient (A := A) (A' := A') (B := B) e).comp
        (algebraMap A C) =
      (Ideal.Quotient.mk (Ideal.map (algebraMap A' B) (maximalIdeal A'))).comp
        (algebraMap A B) := by
  let eκ : κA ≃+* κA' :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ
  ext a
  -- Proof comment: pass to the canonical closed-fiber model on the target quotient. The source
  -- and target quotient presentations reduce to residue classes, and the transported scalar
  -- identity from `closedFiber_transport_residue_eq` closes the remaining comparison.
  apply (closedFiberQuotAlgEquiv (R := A') (S := B)).symm.injective
  simp [closedFiber_identification_to_target_quotient,
    closedFiber_identification_to_target_quotient_equiv, RingHom.comp_apply]
  have hsource :=
    congrArg
      (fun f : C →+* Ideal.Fiber (maximalIdeal A) C ↦ f ((algebraMap A C) a))
      (closedFiber_quotient_comp_eq_algebraMap (R := A) (S := C))
  have htarget :=
    congrArg
      (fun f : B →+* ClosedFiberB ↦ f ((algebraMap A B) a))
      (closedFiber_quotient_comp_eq_algebraMap (R := A') (S := B))
  calc
    e
        (((closedFiberQuotAlgEquiv (R := A) (S := C)).symm.toRingHom.comp
            (Ideal.Quotient.mk (Ideal.map (algebraMap A C) (maximalIdeal A))))
          ((algebraMap A C) a)) =
      e ((algebraMap C (Ideal.Fiber (maximalIdeal A) C)) ((algebraMap A C) a)) := by
        simpa [RingHom.comp_apply] using hsource
    _ = e (algebraMap κA (Ideal.Fiber (maximalIdeal A) C) (residue A a)) := by
        congr 1
        simpa using closedFiber_algebraMap_eq_residue (R := A) (S := C) a
    _ = algebraMap κA ClosedFiberB (residue A a) := by
      simpa using e.commutes (residue A a)
    _ = algebraMap κA' ClosedFiberB (residue A' (algebraMap A A' a)) := by
      simpa [eκ] using
        closedFiber_transport_residue_eq (A := A) (A' := A') (B := B) hκ hBalg a
    _ = (algebraMap B ClosedFiberB) ((algebraMap A' B) ((algebraMap A A') a)) := by
        simpa using
          (closedFiber_algebraMap_eq_residue (R := A') (S := B) ((algebraMap A A') a)).symm
    _ = (algebraMap B ClosedFiberB) ((algebraMap A B) a) := by
        simp [IsScalarTower.algebraMap_eq A A' B]
    _ =
      ((closedFiberQuotAlgEquiv (R := A') (S := B)).symm.toRingHom.comp
          (Ideal.Quotient.mk (Ideal.map (algebraMap A' B) (maximalIdeal A'))))
        ((algebraMap A B) a) := by
        simpa [RingHom.comp_apply] using htarget.symm

/-- Helper for Remark 15.40.7: a local homomorphism between local rings is continuous for the
maximal-ideal-adic topologies. -/
private theorem continuous_of_isLocalHom_adic_maximalIdeal
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    letI : TopologicalSpace R := Ideal.adicTopology (maximalIdeal R)
    letI : TopologicalSpace S := Ideal.adicTopology (maximalIdeal S)
    Continuous f := by
  -- Proof comment: continuity for adic topologies is equivalent to sending a power of the source
  -- maximal ideal into the target maximal ideal, and locality gives this already for the first
  -- power.
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  simpa [pow_one] using
    (IsLocalRing.map_maximalIdeal_le f : Ideal.map f (maximalIdeal R) ≤ maximalIdeal S)

/-- Helper for Remark 15.40.7: the source quotient map `C → C / 𝔪_A C` is continuous for the
maximal-ideal-adic topologies. -/
private theorem source_closedFiber_quotient_continuous
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] :
    let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
    letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
    letI : TopologicalSpace (C ⧸ JC) :=
      Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C))
    Continuous (Ideal.Quotient.mk JC : C →+* C ⧸ JC) := by
  let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
  -- Proof comment: for the target adic topology defined by the image of `maximalIdeal C`, the
  -- quotient map is continuous with exponent `1` by construction.
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  simpa [pow_one] using
    (le_rfl : Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C) ≤
      Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C))

/-- Helper for Remark 15.40.7: the quotient equivalence induced by a closed-fiber identification
is continuous for the maximal-ideal-adic topologies on the source and target quotients. -/
private theorem closedFiber_identification_to_target_quotient_equiv_continuous_adic
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
    let JB : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
    letI : TopologicalSpace (C ⧸ JC) :=
      Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C))
    letI : TopologicalSpace (B ⧸ JB) :=
      Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JB) (maximalIdeal B))
    Continuous (closedFiber_identification_to_target_quotient_equiv
      (A := A) (A' := A') (B := B) e).toRingHom := by
  let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
  let JB : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
  have hJC_ne_top : JC ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A C)).ne
  have hJB_ne_top : JB ≠ ⊤ := (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A' B)).ne
  letI : Nontrivial (C ⧸ JC) := Ideal.Quotient.nontrivial_iff.2 hJC_ne_top
  letI : Nontrivial (B ⧸ JB) := Ideal.Quotient.nontrivial_iff.2 hJB_ne_top
  letI : IsLocalRing (C ⧸ JC) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk JC) Ideal.Quotient.mk_surjective
  letI : IsLocalRing (B ⧸ JB) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk JB) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk JC) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk JB) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  have hmaxC :
      Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C) = maximalIdeal (C ⧸ JC) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk JC) Ideal.Quotient.mk_surjective
  have hmaxB :
      Ideal.map (Ideal.Quotient.mk JB) (maximalIdeal B) = maximalIdeal (B ⧸ JB) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk JB) Ideal.Quotient.mk_surjective
  letI : IsLocalHom
      (closedFiber_identification_to_target_quotient_equiv
        (A := A) (A' := A') (B := B) e).toRingHom :=
    Function.Surjective.isLocalHom _
      (closedFiber_identification_to_target_quotient_equiv
        (A := A) (A' := A') (B := B) e).surjective
  -- Proof comment: the quotient equivalence is a surjective local map between local quotient
  -- rings, so the same maximal-ideal-adic continuity criterion applies directly.
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  have hle :
      Ideal.map
          ((closedFiber_identification_to_target_quotient_equiv
            (A := A) (A' := A') (B := B) e).toRingHom)
          (Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C)) ≤
        Ideal.map (Ideal.Quotient.mk JB) (maximalIdeal B) := by
    rw [hmaxC, hmaxB]
    exact
      (IsLocalRing.map_maximalIdeal_le
        ((closedFiber_identification_to_target_quotient_equiv
          (A := A) (A' := A') (B := B) e).toRingHom) :
        Ideal.map
            ((closedFiber_identification_to_target_quotient_equiv
              (A := A) (A' := A') (B := B) e).toRingHom)
            (maximalIdeal (C ⧸ JC)) ≤
          maximalIdeal (B ⧸ JB))
  simpa [pow_one] using hle

/-- Helper for Remark 15.40.7: modulo the remaining quotient-topology identification, the map
`C → B / 𝔪_{A'} B` attached to a closed-fiber identification is already continuous for the adic
topologies on source and target. -/
private theorem closedFiber_identification_to_target_quotient_continuous_adic
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    let JB : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
    letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
    letI : TopologicalSpace (B ⧸ JB) :=
      Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JB) (maximalIdeal B))
    Continuous (closedFiber_identification_to_target_quotient
      (A := A) (A' := A') (B := B) e) := by
  -- Proof comment: the map factors through the quotient `C → C / 𝔪_A C`, followed by the quotient
  -- equivalence coming from the chosen closed-fiber identification.
  have hquot :
      let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
      letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
      letI : TopologicalSpace (C ⧸ JC) :=
        Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C))
      Continuous (Ideal.Quotient.mk JC : C →+* C ⧸ JC) :=
    source_closedFiber_quotient_continuous (A := A) (C := C)
  have hequiv :
      let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
      let JB : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
      letI : TopologicalSpace (C ⧸ JC) :=
        Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C))
      letI : TopologicalSpace (B ⧸ JB) :=
        Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JB) (maximalIdeal B))
      Continuous (closedFiber_identification_to_target_quotient_equiv
        (A := A) (A' := A') (B := B) e).toRingHom :=
    closedFiber_identification_to_target_quotient_equiv_continuous_adic
      (A := A) (A' := A') (B := B) e
  let JC : Ideal C := Ideal.map (algebraMap A C) (maximalIdeal A)
  let JB : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
  letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
  letI : TopologicalSpace (C ⧸ JC) :=
    Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JC) (maximalIdeal C))
  letI : TopologicalSpace (B ⧸ JB) :=
    Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk JB) (maximalIdeal B))
  have hequiv' :
      Continuous (closedFiber_identification_to_target_quotient_equiv
        (A := A) (A' := A') (B := B) e).toRingHom := by
    simpa [JB] using hequiv
  have hquot' : Continuous (Ideal.Quotient.mk JC : C →+* C ⧸ JC) := by
    simpa [JC] using hquot
  -- Proof comment: after fixing the local adic topologies on the source quotient and the target
  -- quotient, the desired continuity is just continuity of a composition.
  simpa [closedFiber_identification_to_target_quotient, JC, JB] using hequiv'.comp hquot'

/-- Helper for Remark 15.40.7: the ideal
`Ideal.map (algebraMap A' B) (maximalIdeal A')` is closed in the `maximalIdeal B`-adic topology. -/
private theorem target_quotient_ideal_isClosed :
    let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
    letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
    IsClosed (J : Set B) := by
  let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  have hJ_le : J ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le (algebraMap A' B)
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ_le
  have hJ_jac : J ≤ (⊥ : Ideal B).jacobson := by
    simpa [Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal B) bot_ne_top] using
      hJ_le
  let _ : IsLocalHom (Ideal.Quotient.mk J) :=
    isLocalHom_of_le_jacobson_bot J hJ_jac
  let _ : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ_ne_top
  let _ : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmaxQ :
      Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B) = maximalIdeal (B ⧸ J) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  -- Proof comment: prove openness of the complement directly. For `x ∉ J`, its image in the
  -- quotient `Q = B / J` is nonzero, hence by Krull intersection it avoids some power of the
  -- maximal ideal of `Q`. The corresponding coset `x + 𝔪_B^n` is then an open neighborhood
  -- disjoint from `J`.
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro b hbJ
  have hb_not_J : b ∉ J := by
    simpa using hbJ
  have hbQ_ne : (Ideal.Quotient.mk J) b ≠ (0 : B ⧸ J) := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hb_not_J
  have hiInf_bot : (⨅ n : ℕ, maximalIdeal (B ⧸ J) ^ n) = (⊥ : Ideal (B ⧸ J)) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (B ⧸ J))
      (maximalIdeal.isMaximal (B ⧸ J)).ne_top
  have hb_not_mem_all : ¬ ∀ n : ℕ, (Ideal.Quotient.mk J) b ∈ maximalIdeal (B ⧸ J) ^ n := by
    intro hb_all
    have hb_inf : (Ideal.Quotient.mk J) b ∈ ⨅ n : ℕ, maximalIdeal (B ⧸ J) ^ n := by
      simpa [Ideal.mem_iInf] using hb_all
    have hb_zero : (Ideal.Quotient.mk J) b = (0 : B ⧸ J) := by
      rw [hiInf_bot] at hb_inf
      simpa using hb_inf
    exact hbQ_ne hb_zero
  classical
  obtain ⟨n, hb_not_mem_n⟩ :=
    not_forall.mp hb_not_mem_all
  let U : Set B := ({b} : Set B) + (↑(maximalIdeal B ^ n) : Set B)
  have hOpenPow : IsOpen ((maximalIdeal B ^ n : Ideal B) : Set B) := by
    have hAdic : IsAdic (maximalIdeal B) := rfl
    exact (isAdic_iff.mp hAdic).1 n
  have hU_open : IsOpen U := by
    simpa [U] using IsOpen.add_left (s := ({b} : Set B)) hOpenPow
  have hbU : b ∈ U := by
    refine Set.mem_add.2 ?_
    refine ⟨b, by simp, 0, by simpa using (show (0 : B) ∈ maximalIdeal B ^ n from (maximalIdeal B ^ n).zero_mem), by simp⟩
  have hU_disjoint : U ⊆ (J : Set B)ᶜ := by
    intro y hyU
    intro hyJ
    rcases Set.mem_add.1 hyU with ⟨u, hu, z, hz, hsum⟩
    have hu' : u = b := by simpa using hu
    subst u
    have hb_mem_sup : b ∈ J ⊔ maximalIdeal B ^ n := by
      rw [Submodule.mem_sup]
      refine ⟨y, hyJ, -z, (maximalIdeal B ^ n).neg_mem hz, ?_⟩
      rw [← hsum]
      abel
    have hbQ_mem_pow :
        (Ideal.Quotient.mk J) b ∈ maximalIdeal (B ⧸ J) ^ n := by
      have hbQ_mem_map :
          (Ideal.Quotient.mk J) b ∈ Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n) := by
        rw [Submodule.mem_sup] at hb_mem_sup
        rcases hb_mem_sup with ⟨j, hj, m, hm, hbm⟩
        rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
        refine ⟨m, hm, ?_⟩
        rw [← hbm, RingHom.map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add]
      simpa [Ideal.map_pow, hmaxQ] using hbQ_mem_map
    exact hb_not_mem_n hbQ_mem_pow
  refine Filter.mem_of_superset (IsOpen.mem_nhds hU_open hbU) ?_
  exact hU_disjoint

/-- Helper for Remark 15.40.7: the quotient topology on `B / J` induced from the
`maximalIdeal B`-adic topology is itself adic for the image of `maximalIdeal B`. -/
private theorem target_quotient_isAdic :
    let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
    let K : Ideal (B ⧸ J) := Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B)
    letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
    IsAdic K := by
  let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
  let K : Ideal (B ⧸ J) := Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B)
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  rw [isAdic_iff]
  refine ⟨?_, ?_⟩
  · intro n
    -- Proof comment: openness on the quotient is checked on the coinduced topology by pulling
    -- back along the quotient map, where the pullback is the open thickening `J + 𝔪_B^n`.
    rw [show K ^ n = Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n) by
      simp [K, Ideal.map_pow]]
    rw [isOpen_coinduced]
    change IsOpen ((Ideal.Quotient.mk J) ⁻¹'
      ((((Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n)) :
        Ideal (B ⧸ J)) : Set (B ⧸ J))))
    have hOpenPow : IsOpen ((maximalIdeal B ^ n : Ideal B) : Set B) := by
      exact (isAdic_iff.mp (show IsAdic (maximalIdeal B) by rfl)).1 n
    have hpreimage :
        (Ideal.Quotient.mk J) ⁻¹'
            (((Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n)) :
              Ideal (B ⧸ J)) : Set (B ⧸ J)) =
          ((J : Set B) + ((maximalIdeal B ^ n : Ideal B) : Set B)) := by
      ext b
      constructor
      · intro hb
        change (Ideal.Quotient.mk J) b ∈
          (Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n) : Ideal (B ⧸ J)) at hb
        rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
          at hb
        rcases hb with ⟨x, hx, hxb⟩
        refine Set.mem_add.2 ?_
        refine ⟨b - x, ?_, x, hx, by abel⟩
        have hzero : (Ideal.Quotient.mk J) (b - x) = 0 := by
          rw [RingHom.map_sub, hxb, sub_self]
        exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp hzero
      · intro hb
        rcases Set.mem_add.2 hb with ⟨j, hj, x, hx, rfl⟩
        change (Ideal.Quotient.mk J) (j + x) ∈
          (Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n) : Ideal (B ⧸ J))
        rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
        refine ⟨x, hx, ?_⟩
        have hjzero : (Ideal.Quotient.mk J) j = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hj
        rw [RingHom.map_add, hjzero, zero_add]
    have hOpenPreimage :
        IsOpen (((J : Set B) + ((maximalIdeal B ^ n : Ideal B) : Set B)) : Set B) := by
      simpa using IsOpen.add_left (s := (J : Set B)) hOpenPow
    rw [hpreimage]
    exact hOpenPreimage
  · intro s hs
    -- Proof comment: a neighborhood of `0` downstairs pulls back to a neighborhood of `0` in
    -- `B`, and the `𝔪_B`-adic neighborhood basis then descends through the quotient map.
    have hs_preimage :
        (Ideal.Quotient.mk J) ⁻¹' s ∈ nhds (0 : B) := by
      exact continuous_quot_mk.continuousAt.preimage_mem_nhds hs
    obtain ⟨n, hn⟩ :=
      (isAdic_iff.mp (show IsAdic (maximalIdeal B) by rfl)).2 _ hs_preimage
    refine ⟨n, ?_⟩
    intro y hy
    rw [show K ^ n = Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n) by
      simp [K, Ideal.map_pow]] at hy
    change y ∈ (Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B ^ n)) at hy
    rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hn hx

/-- Helper for Remark 15.40.7: the quotient map induced by a closed-fiber identification is
continuous for the actual quotient topology on `B / 𝔪_{A'} B`. -/
private theorem closedFiber_identification_to_target_quotient_continuous
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
    letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
    letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
    Continuous (closedFiber_identification_to_target_quotient
      (A := A) (A' := A') (B := B) e) := by
  let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
  letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  have hJ_le : J ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le (algebraMap A' B)
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ_le
  letI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ_ne_top
  letI : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : IsLocalHom
      (closedFiber_identification_to_target_quotient (A := A) (A' := A') (B := B) e) :=
    Function.Surjective.isLocalHom _
      (closedFiber_identification_to_target_quotient_surjective
        (A := A) (A' := A') (B := B) e)
  let tQ : TopologicalSpace (B ⧸ J) := inferInstance
  have hmaxQ :
      Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B) = maximalIdeal (B ⧸ J) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hQadic :
      tQ = Ideal.adicTopology (maximalIdeal (B ⧸ J)) := by
    calc
      tQ = Ideal.adicTopology (Ideal.map (Ideal.Quotient.mk J) (maximalIdeal B)) := by
        exact target_quotient_isAdic (A' := A') (B := B)
      _ = Ideal.adicTopology (maximalIdeal (B ⧸ J)) := by
        rw [hmaxQ]
  have hcont_adic :
      @Continuous C (B ⧸ J)
        (Ideal.adicTopology (maximalIdeal C))
        (Ideal.adicTopology (maximalIdeal (B ⧸ J)))
        (closedFiber_identification_to_target_quotient
          (A := A) (A' := A') (B := B) e) := by
    exact continuous_of_isLocalHom_adic_maximalIdeal
      (f := closedFiber_identification_to_target_quotient
        (A := A) (A' := A') (B := B) e)
  change @Continuous C (B ⧸ J)
    (Ideal.adicTopology (maximalIdeal C))
    tQ
    (closedFiber_identification_to_target_quotient
      (A := A) (A' := A') (B := B) e)
  rw [hQadic]
  exact hcont_adic

/-- Helper for Remark 15.40.7: the chosen closed-fiber identification lifts to a continuous local
map `C → B`. -/
private theorem exists_local_map_to_target_of_closedFiber_identification
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra κA ClosedFiberB]
    (hfsC : (algebraMap A C).formally_smooth_for_adic (maximalIdeal C))
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hBalg :
      algebraMap κA ClosedFiberB =
        (algebraMap κA' ClosedFiberB).comp
          (RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ).toRingHom)
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB) :
    ∃ φ : C →+* B,
      (Ideal.Quotient.mk (Ideal.map (algebraMap A' B) (maximalIdeal A'))).comp φ =
        closedFiber_identification_to_target_quotient (A := A) (A' := A') (B := B) e ∧
      φ.comp (algebraMap A C) = algebraMap A B ∧
      IsLocalHom φ := by
  let J : Ideal B := Ideal.map (algebraMap A' B) (maximalIdeal A')
  letI : TopologicalSpace C := Ideal.adicTopology (maximalIdeal C)
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  have hBAdic : IsAdic (maximalIdeal B) := rfl
  have hJClosed : IsClosed (J : Set B) := by
    simpa [J] using target_quotient_ideal_isClosed (A' := A') (B := B)
  have hψ :
      Continuous (closedFiber_identification_to_target_quotient
        (A := A) (A' := A') (B := B) e) := by
    simpa [J] using
      closedFiber_identification_to_target_quotient_continuous
        (A := A) (A' := A') (B := B) e
  have hpow : ∃ t : ℕ+, J ^ (t : ℕ) ≤ maximalIdeal B := by
    refine ⟨1, ?_⟩
    simpa [J, pow_one] using
      (IsLocalRing.map_maximalIdeal_le (algebraMap A' B) :
        Ideal.map (algebraMap A' B) (maximalIdeal A') ≤ maximalIdeal B)
  obtain ⟨φ, hφquot, hφbase, _⟩ :=
    (algebraMap A C).exists_continuous_lift_of_formally_smooth_for_adic
      (maximalIdeal C) hfsC
      (show IsAdic (maximalIdeal C) by rfl)
      (maximalIdeal B) J hBAdic hJClosed hpow
      (closedFiber_identification_to_target_quotient
        (A := A) (A' := A') (B := B) e)
      hψ
      (algebraMap A B)
      (closedFiber_identification_to_target_quotient_comp_algebraMap
        (A := A) (A' := A') (B := B) hκ hBalg e).symm
  have hJ_le : J ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le (algebraMap A' B)
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ_le
  letI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ_ne_top
  letI : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hcomp_local :
      IsLocalHom ((Ideal.Quotient.mk J).comp φ) := by
    simpa [J, hφquot] using
      (Function.Surjective.isLocalHom _
        (closedFiber_identification_to_target_quotient_surjective
          (A := A) (A' := A') (B := B) e) :
        IsLocalHom (closedFiber_identification_to_target_quotient
          (A := A) (A' := A') (B := B) e))
  have hlocal : IsLocalHom φ := by
    refine ⟨?_⟩
    intro c hc
    exact hcomp_local.map_nonunit c <| IsUnit.map (Ideal.Quotient.mk J) hc
  -- Proof comment: Lemma `15.37.5` gives the algebraic lift, and locality of `φ` is recovered by
  -- reflecting units through the local quotient map `B → B / J`.
  exact ⟨φ, by simpa [J] using hφquot, hφbase, hlocal⟩

/-- Helper for Remark 15.40.7: once the closed-fiber lift `C → B` is constructed, surjectivity of
the canonical completed base-change map reduces to the quotient stage modulo the closed point. -/
private theorem completedBaseChangeMap_surjective_of_lift_to_target
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra κA ClosedFiberB]
    (e : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] ClosedFiberB)
    (φ : C →+* B) [Algebra C B] [IsScalarTower A C B]
    (hφquot :
      (Ideal.Quotient.mk (Ideal.map (algebraMap A' B) (maximalIdeal A'))).comp φ =
        closedFiber_identification_to_target_quotient (A := A) (A' := A') (B := B) e) :
    Function.Surjective (completedBaseChangeMap A A' B C) := by
  -- Proof comment: the remaining source-faithful step is to prove surjectivity after reducing the
  -- tensor-product map modulo the closed point of `Spec B`, then pass to the completion map via
  -- `AdicCompletion.map_surjective_of_mkQ_comp_surjective`.
  -- TODO: factor `closedFiber_identification_to_target_quotient e` through
  -- `B ⧸ maximalIdeal B`, identify that quotient-stage map with the reduction of
  -- `tensorProductToTarget A A' B C`, and apply the standard completion-surjectivity criterion.
  sorry

-- Proof sketch: apply Lemma `15.40.6` to the formally smooth special fiber over the common residue
-- field, obtaining a Noetherian complete local `A`-algebra `C` with the required closed fiber.
-- Then use Lemma `15.37.5` to lift the special-fiber map into `B`, producing the arrow `C → B`,
-- hence the canonical `maximalIdeal A`-adic completed base-change map `completedBaseChange C → B`.
/-- Remark 15.40.7: for local homomorphisms `A → A' → B` of Noetherian complete local rings, if
`A → A'` induces an isomorphism on residue fields and the special fiber
`ClosedFiberB = Ideal.Fiber (maximalIdeal A') B`, canonically presented by `κ(A') ⊗[A'] B`, is
formally smooth over `κ(A')` for the adic topology defined by
`𝔪ClosedFiberB = Ideal.map (algebraMap B ClosedFiberB) (maximalIdeal B)`, then there exists a
Noetherian complete local `A`-algebra `C` together with a local map `C → B` such that `A → C` is
formally smooth for the `maximalIdeal C`-adic topology and the canonical
`maximalIdeal A`-adic completed base-change map `completedBaseChange C → B` is surjective. -/
@[stacks 07NS]
theorem exists_completeLocal_formallySmooth_lift_over_local_baseChange
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hfs :
      (algebraMap κA' ClosedFiberB).formally_smooth_for_adic 𝔪ClosedFiberB) :
    ∃ (C : Type*) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C)) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (_ : IsLocalHom (algebraMap C B)),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) ∧
        Function.Surjective (completedBaseChangeMap A A' B C) := by
  let eκ : κA ≃+* κA' :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap A A')) hκ
  letI : Algebra κA ClosedFiberB :=
    ((algebraMap κA' ClosedFiberB).comp eκ.toRingHom).toAlgebra
  have hBalg :
      algebraMap κA ClosedFiberB =
        (algebraMap κA' ClosedFiberB).comp eκ.toRingHom := rfl
  have hfsSource :
      (algebraMap κA ClosedFiberB).formally_smooth_for_adic 𝔪ClosedFiberB :=
    closedFiber_formally_smooth_over_source_residue (A := A) (A' := A') (B := B) hκ hfs
  let _ := hfsSource
  -- Route correction: the proven prefix is the residue-field transport reducing the problem to the
  -- `κ(A)`-linear closed fiber. The remaining source-faithful step is to apply Lemma `15.40.6`,
  -- turn the resulting closed-fiber identification into `C → B / m_{A'} B`, lift it to `C → B`
  -- via Lemma `15.37.5`, and then prove surjectivity of `completedBaseChangeMap`.
  -- TODO: instantiate `exists_completeLocal_formallySmooth_lift_with_closedFiber` with the
  -- transported closed fiber, use
  -- `exists_local_map_to_target_of_closedFiber_identification` to obtain `C → B`, and finish with
  -- `completedBaseChangeMap_surjective_of_lift_to_target`.
  sorry

-- Proof sketch: Nakayama's lemma applied to the identified closed fibers shows that the map on
-- successive quotients modulo powers of `maximalIdeal A` are surjective. When `A → A'` itself is
-- surjective, the zeroth stage already forces `C → B` to be surjective.
/-- If the base change `A → A'` is surjective, then surjectivity of the canonical completed
base-change map `completedBaseChange C → B` forces `C → B` to be surjective. -/
theorem surjective_of_surjective_base_of_completedBaseChangeMap
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C))
    (hAA' : Function.Surjective (algebraMap A A')) :
    Function.Surjective (algebraMap C B) := sorry

-- Proof sketch: first obtain surjectivity on all Artinian quotients from the closed-fiber
-- surjectivity of the completed base-change map by Nakayama. If `A'` is finite over `A`, the
-- completed-quotient argument identifies `B` as a finite `C`-module.
/-- If the intermediate extension `A → A'` is finite, then surjectivity of the canonical
completed base-change map makes `B` finite over `C`. -/
theorem finite_of_finite_base_of_completedBaseChangeMap
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C))
    [Module.Finite A A'] :
    Module.Finite C B := sorry

-- Proof sketch: once the completed base-change map is surjective, flatness of `A' → B` kills its
-- kernel on all Artinian quotients, so the map is bijective.
/-- If `A' → B` is flat, then a surjective canonical completed base-change map is bijective. -/
theorem completedBaseChangeMap_bijective_of_flat
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C)) :
    Function.Bijective (completedBaseChangeMap A A' B C) := sorry

/-- In the flat case, the canonical completed base-change map is an isomorphism. -/
noncomputable def completedBaseChangeRingEquivOfFlat
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C)) :
    completedBaseChange A A' C ≃+* B :=
  RingEquiv.ofBijective (completedBaseChangeMap A A' B C)
    (completedBaseChangeMap_bijective_of_flat hflat hbaseChange)

end
