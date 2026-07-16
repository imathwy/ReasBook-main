import stacks_proof.stacks_project.Chap10.Lemma_10_127_13.Index
import Mathlib.Tactic.StacksAttribute

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] ulift_isLocalRing

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- Helper for Chap10 Lemma 10 127 13: an essentially finite-type algebra over a small base has
a carrier small in the same universe as the base. -/
theorem small_of_essFiniteType_of_small_base {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [Small.{w} A] [Algebra.EssFiniteType A B] :
    Small.{w} B := by
  let B₀ := Algebra.EssFiniteType.subalgebra A B
  let M₀ := Algebra.EssFiniteType.submonoid A B
  have hsmallB₀ : Small.{w} B₀ := by
    letI : Algebra.FiniteType A B₀ := inferInstance
    -- Proof comment: the finite-type subalgebra is a quotient of a finite polynomial algebra over
    -- the already-small base.
    rcases (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B₀)).mp
        (inferInstance : Algebra.FiniteType A B₀) with
      ⟨n, π, hπ⟩
    exact small_of_surjective hπ
  letI : Small.{w} B₀ := hsmallB₀
  have hsmallLoc : Small.{w} (Localization M₀) := by
    -- Proof comment: localizing a small ring is a quotient of a small presentation of fractions.
    exact small_of_surjective Localization.mkHom_surjective
  letI : Small.{w} (Localization M₀) := hsmallLoc
  let eLoc : Localization M₀ ≃+* B :=
    (IsLocalization.algEquiv M₀ (Localization M₀) B).toRingEquiv
  -- Proof comment: the canonical essential-finite-type localization is ring-equivalent to `B`.
  exact small_map eLoc.symm.toEquiv

/-- Helper for Chap10 Lemma 10 127 13: precomposing the target with the inverse of a local ring
equivalence preserves the local-homomorphism property. -/
theorem ringHom_comp_ringEquiv_symm_isLocalHom
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (g : A →+* B) [IsLocalHom g] (e : C ≃+* B) :
    IsLocalHom (e.symm.toRingHom.comp g) := by
  letI : IsLocalHom e.symm.toRingHom :=
    Function.Surjective.isLocalHom _ e.symm.surjective
  -- Proof comment: the transported map is the original local homomorphism followed by a local
  -- ring equivalence.
  exact RingHom.isLocalHom_comp _ _

/-- Helper for Chap10 Lemma 10 127 13: postcomposing an essentially finite-presentation map with
the inverse of a ring equivalence preserves essential finite presentation. -/
theorem ringHom_comp_ringEquiv_symm_essFinitePresentation
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (e : C ≃+* B) (hg : g.EssFinitePresentation) :
    (e.symm.toRingHom.comp g).EssFinitePresentation := by
  have htarget : e.symm.toRingHom.EssFinitePresentation := by
    letI : Algebra B C := e.symm.toRingHom.toAlgebra
    have hfp : e.symm.toRingHom.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective e.symm.bijective
    letI : Algebra.FinitePresentation B C := hfp
    -- Proof comment: a ring equivalence is finitely presented, hence essentially finitely
    -- presented as a ring homomorphism.
    rw [RingHom.EssFinitePresentation]
    exact Algebra.EssFinitePresentation.of_finitePresentation B C
  -- Proof comment: essential finite presentation is stable under composition.
  exact hg.comp htarget

/-- Helper for Chap10 Lemma 10 127 13: transport a ring homomorphism through canonical small
models of source and target. -/
noncomputable def smallModelRingHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Small.{w} A] [Small.{w} B]
    (φ : A →+* B) :
    Shrink.{w} A →+* Shrink.{w} B :=
  (Shrink.ringEquiv B).symm.toRingHom.comp (φ.comp (Shrink.ringEquiv A).toRingHom)

/-- Helper for Chap10 Lemma 10 127 13: the small-model homomorphism is the conjugate of the
original homomorphism by the shrink equivalences. -/
@[simp] theorem smallModelRingHom_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Small.{w} A] [Small.{w} B]
    (φ : A →+* B) (x : Shrink.{w} A) :
    smallModelRingHom φ x = (Shrink.ringEquiv B).symm (φ ((Shrink.ringEquiv A) x)) := by
  rfl

/-- Helper for Chap10 Lemma 10 127 13: small-model transport preserves identity homomorphisms. -/
theorem smallModelRingHom_id
    {A : Type u} [CommRing A] [Small.{w} A] :
    smallModelRingHom (RingHom.id A) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  -- Proof comment: after unshrinking, the conjugated identity is the original element.
  apply (Shrink.ringEquiv A).injective
  simp [smallModelRingHom]

/-- Helper for Chap10 Lemma 10 127 13: small-model transport preserves composition of
homomorphisms. -/
theorem smallModelRingHom_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Small.{uM} A] [Small.{uM} B] [Small.{uM} C]
    (φ : A →+* B) (ψ : B →+* C) :
    smallModelRingHom (ψ.comp φ) =
      (smallModelRingHom ψ).comp (smallModelRingHom φ) := by
  apply RingHom.ext
  intro x
  -- Proof comment: compare after unshrinking the codomain, where both sides are `ψ (φ x)`.
  apply (Shrink.ringEquiv C).injective
  simp [smallModelRingHom, RingHom.comp_apply]

/-- Helper for Chap10 Lemma 10 127 13: a directed ring system remains directed after replacing
all stages by their small models. -/
theorem smallModelDirectedSystem
    {ι : Type u} [Preorder ι] {T : ι → Type v} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)] [∀ i, Small.{w} (T i)] :
    DirectedSystem (fun i ↦ Shrink.{w} (T i)) (fun i j h ↦ smallModelRingHom (τ i j h)) where
  map_self := by
    intro i x
    -- Proof comment: the transported self-map reduces to the original directed-system self-map.
    apply (Shrink.ringEquiv (T i)).injective
    simpa [smallModelRingHom, RingHom.comp_apply] using
      DirectedSystem.map_self (f := fun i j h ↦ τ i j h) ((Shrink.ringEquiv (T i)) x)
  map_map := by
    intro k j i hij hjk x
    -- Proof comment: after unshrinking, composition is the original directed-system composition.
    apply (Shrink.ringEquiv (T k)).injective
    simpa [smallModelRingHom, RingHom.comp_apply] using
      DirectedSystem.map_map (f := fun i j h ↦ τ i j h) hij hjk
        ((Shrink.ringEquiv (T i)) x)

/-- Helper for Chap10 Lemma 10 127 13: the direct limit of a stagewise small-model replacement is
canonically ring-equivalent to the original direct limit. -/
noncomputable def directLimit_smallModelRingEquiv
    {ι : Type u} [Preorder ι] {T : ι → Type v} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)] [∀ i, Small.{w} (T i)] :
    Ring.DirectLimit (fun i ↦ Shrink.{w} (T i)) (fun i j h ↦ smallModelRingHom (τ i j h)) ≃+*
      Ring.DirectLimit T (fun i j h ↦ τ i j h) := by
  letI : DirectedSystem (fun i ↦ Shrink.{w} (T i))
      (fun i j h ↦ smallModelRingHom (τ i j h)) :=
    smallModelDirectedSystem τ
  let toOriginal :
      Ring.DirectLimit (fun i ↦ Shrink.{w} (T i)) (fun i j h ↦ smallModelRingHom (τ i j h)) →+*
        Ring.DirectLimit T (fun i j h ↦ τ i j h) :=
    Ring.DirectLimit.map (fun i ↦ (Shrink.ringEquiv (T i)).toRingHom)
      (fun i j h ↦ by
        -- Proof comment: unshrinking commutes with the transported transition maps.
        ext x
        simp [smallModelRingHom, RingHom.comp_apply])
  let toSmall :
      Ring.DirectLimit T (fun i j h ↦ τ i j h) →+*
        Ring.DirectLimit (fun i ↦ Shrink.{w} (T i)) (fun i j h ↦ smallModelRingHom (τ i j h)) :=
    Ring.DirectLimit.map (fun i ↦ (Shrink.ringEquiv (T i)).symm.toRingHom)
      (fun i j h ↦ by
        -- Proof comment: shrinking the original transition is the transported transition.
        ext x
        simp [smallModelRingHom, RingHom.comp_apply])
  refine RingEquiv.ofRingHom toOriginal toSmall ?_ ?_
  ·
    -- Proof comment: both composites agree on every original-stage generator.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toSmall, RingHom.comp_apply]
  ·
    -- Proof comment: the same generator check proves the inverse law for small-model generators.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toSmall, RingHom.comp_apply]

/-- Helper for Chap10 Lemma 10 127 13: the direct-limit small-model equivalence sends each
small-stage generator to the corresponding original-stage generator. -/
@[simp] theorem directLimit_smallModelRingEquiv_of
    {ι : Type u} [Preorder ι] {T : ι → Type v} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)] [∀ i, Small.{w} (T i)]
    (i : ι) (x : Shrink.{w} (T i)) :
    directLimit_smallModelRingEquiv (T := T) τ
        (Ring.DirectLimit.of (fun j ↦ Shrink.{w} (T j))
          (fun j k h ↦ smallModelRingHom (τ j k h)) i x) =
      Ring.DirectLimit.of T (fun j k h ↦ τ j k h) i ((Shrink.ringEquiv (T i)) x) := by
  -- Proof comment: the forward map is induced by unshrinking each stage.
  rfl

/-- Helper for Chap10 Lemma 10 127 13: postcomposing a local homomorphism with the inverse
small-model equivalence preserves locality. -/
theorem smallModelCodomainRingHom_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Small.{w} B] (φ : A →+* B) [IsLocalHom φ] :
    IsLocalHom ((Shrink.ringEquiv B).symm.toRingHom.comp φ) := by
  letI : IsLocalRing (Shrink.{w} B) := RingEquiv.isLocalRing (Shrink.ringEquiv B).symm
  -- Proof comment: this is locality of the original map followed by a local ring equivalence.
  exact ringHom_comp_ringEquiv_symm_isLocalHom φ (Shrink.ringEquiv B)

/-- Helper for Chap10 Lemma 10 127 13: postcomposing an essentially finite-type map with the
inverse small-model equivalence preserves essential finite type. -/
theorem smallModelCodomainRingHom_essFiniteType
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Small.{w} B]
    (φ : A →+* B) (hφ : φ.EssFiniteType) :
    ((Shrink.ringEquiv B).symm.toRingHom.comp φ).EssFiniteType := by
  have htarget : (Shrink.ringEquiv B).symm.toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (Shrink.ringEquiv B).symm.surjective).essFiniteType
  -- Proof comment: essential finite type is stable under composition.
  exact hφ.comp htarget

namespace DirectedLocalHomApproximation

/-- Helper for Chap10 Lemma 10 127 13: after shrinking target stages, the original source-stage
commutative square remains commutative. -/
theorem targetShrink_comm
    {T : Type uR} [CommRing T] [IsLocalRing T] {g : R →+* T}
    (A : DirectedLocalHomApproximation.{uR, uR, uR} g)
    [∀ i : A.Λ, Small.{uS} (A.SStage i)] {i j : A.Λ} (h : i ≤ j) :
    ((Shrink.ringEquiv (A.SStage j)).symm.toRingHom.comp (A.stageMap j)).comp (A.map i j h) =
      (smallModelRingHom (A.targetMap i j h)).comp
        ((Shrink.ringEquiv (A.SStage i)).symm.toRingHom.comp (A.stageMap i)) := by
  apply RingHom.ext
  intro x
  -- Proof comment: compare after unshrinking the later target stage, where this is exactly
  -- `A.comm h` evaluated at `x`.
  apply (Shrink.ringEquiv (A.SStage j)).injective
  have hcomm := congrArg (fun φ : A.RStage i →+* A.SStage j ↦ φ x) (A.comm h)
  simpa [smallModelRingHom, RingHom.comp_apply] using hcomm

/-- Helper for Chap10 Lemma 10 127 13: the target colimit square survives shrinking the target
stages and then applying a target ring equivalence. -/
theorem targetShrink_colimit_comm
    {T : Type uR} [CommRing T] [IsLocalRing T] (e : T ≃+* S)
    (A : DirectedLocalHomApproximation.{uR, uR, uR} (e.symm.toRingHom.comp f))
    [∀ i : A.Λ, Small.{uS} (A.SStage i)] :
    ((directLimit_smallModelRingEquiv (T := A.SStage)
        (fun i j h ↦ A.targetMap i j h)).trans A.targetColimit |>.trans e).toRingHom.comp
        (Ring.DirectLimit.map
          (fun i ↦ (Shrink.ringEquiv (A.SStage i)).symm.toRingHom.comp (A.stageMap i))
          (fun _ _ h ↦ A.targetShrink_comm h)) =
      f.comp A.colimitIso.toRingHom := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  have hA :=
    congrArg
      (fun φ : Ring.DirectLimit A.RStage (fun j k h ↦ A.map j k h) →+* T ↦
        e (φ (Ring.DirectLimit.of A.RStage (fun j k h ↦ A.map j k h) i x)))
      A.colimit_comm
  -- Proof comment: on a source-stage generator, the shrunken target direct limit first restores
  -- the original target generator; the original colimit square then gives `e (e.symm (f _))`.
  simpa [RingHom.comp_apply, Ring.DirectLimit.map_apply_of] using hA

/-- Helper for Chap10 Lemma 10 127 13: shrink only the target stages of a same-universe
approximation and compose its target colimit with a target ring equivalence. -/
noncomputable def targetShrinkSameIndex
    {T : Type uR} [CommRing T] [IsLocalRing T] (e : T ≃+* S)
    (A : DirectedLocalHomApproximation.{uR, uR, uR} (e.symm.toRingHom.comp f))
    (hsmall : ∀ i : A.Λ, Small.{uS} (A.SStage i)) :
    DirectedLocalHomApproximation.{uR, uS, uR} f :=
  letI : ∀ i : A.Λ, Small.{uS} (A.SStage i) := hsmall
  { Λ := A.Λ
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := inferInstance
    RStage := A.RStage
    instCommRingRStage := fun i ↦ A.instCommRingRStage i
    map := A.map
    instDirectedSystemRStage := inferInstance
    colimitIso := A.colimitIso
    instIsLocalRingRStage := fun i ↦ A.instIsLocalRingRStage i
    SStage := fun i ↦ Shrink.{uS} (A.SStage i)
    instCommRingSStage := fun _ ↦ inferInstance
    instIsLocalRingSStage := fun i ↦ RingEquiv.isLocalRing (Shrink.ringEquiv (A.SStage i)).symm
    stageMap := fun i ↦ (Shrink.ringEquiv (A.SStage i)).symm.toRingHom.comp (A.stageMap i)
    stageMap_isLocalHom := fun i ↦ smallModelCodomainRingHom_isLocalHom (A.stageMap i)
    targetMap := fun i j h ↦ smallModelRingHom (A.targetMap i j h)
    instDirectedSystemTarget := smallModelDirectedSystem (fun i j h ↦ A.targetMap i j h)
    comm := fun {_ _} h ↦ A.targetShrink_comm h
    targetColimit :=
      (directLimit_smallModelRingEquiv (T := A.SStage)
        (fun i j h ↦ A.targetMap i j h)).trans A.targetColimit |>.trans e
    colimit_comm := A.targetShrink_colimit_comm (f := f) e
    source_essFiniteType := fun i ↦ A.source_essFiniteType i
    target_essFiniteType := fun i ↦
      smallModelCodomainRingHom_essFiniteType (A.stageMap i) (A.target_essFiniteType i) }

end DirectedLocalHomApproximation

/-- Helper for Chap10 Lemma 10 127 13: composing a localization map with the inverse of a
codomain ring equivalence preserves the localization-map property. -/
theorem isLocalizationMap_comp_ringEquiv_symm
    {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
    (M : Submonoid A) (γ : A →+* B) (e : C ≃+* B)
    (hγ : M.IsLocalizationMap γ) :
    M.IsLocalizationMap (e.symm.toRingHom.comp γ) := by
  letI : Algebra A B := γ.toAlgebra
  have hloc : IsLocalization M B :=
    (isLocalization_iff_isLocalizationMap (M := M) (S := B)).mpr hγ
  let γ' : A →+* C := e.symm.toRingHom.comp γ
  letI : Algebra A C := γ'.toAlgebra
  let eAlg : B ≃ₐ[A] C :=
    { e.symm with
      commutes' := by
        intro x
        rfl }
  letI : IsLocalization M C := IsLocalization.isLocalization_of_algEquiv M eAlg
  -- Proof comment: convert the explicit map witness to an `IsLocalization` instance, transport it
  -- across the target equivalence, and convert back to the explicit map formulation.
  simpa [γ'] using
    (isLocalization_iff_isLocalizationMap (M := M) (S := C)).mp
      (show IsLocalization M C by infer_instance)

namespace DirectedLocalHomApproximation

/-- Helper for Chap10 Lemma 10 127 13: the target-shrink base-change source is ring-equivalent
to the original base-change source, and under this equivalence the shrunken base-change map is the
original one followed by the inverse shrink equivalence on the target. -/
theorem targetShrinkSameIndex_stageBaseChangeMap_comp
    {T : Type uR} [CommRing T] [IsLocalRing T] (e : T ≃+* S)
    (A : DirectedLocalHomApproximation.{uR, uR, uR} (e.symm.toRingHom.comp f))
    (hsmall : ∀ i : A.Λ, Small.{uS} (A.SStage i))
    {i j : A.Λ} (h : i ≤ j) :
    ∃ eSrc : (A.targetShrinkSameIndex (f := f) e hsmall).targetStageBaseChange h ≃+*
      A.targetStageBaseChange h,
      ((A.targetShrinkSameIndex (f := f) e hsmall).stageBaseChangeMap h).comp
          eSrc.symm.toRingHom =
        (Shrink.ringEquiv (A.SStage j)).symm.toRingHom.comp (A.stageBaseChangeMap h) := by
  let B := A.targetShrinkSameIndex (f := f) e hsmall
  letI : ∀ i : A.Λ, Small.{uS} (A.SStage i) := hsmall
  letI : Algebra (A.RStage i) (B.SStage i) := (B.stageMap i).toAlgebra
  letI : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  letI : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
  let eLeft : B.SStage i ≃ₐ[A.RStage i] A.SStage i :=
    AlgEquiv.ofRingEquiv (f := Shrink.ringEquiv (A.SStage i)) (by
      intro x
      change (Shrink.ringEquiv (A.SStage i))
          (((Shrink.ringEquiv (A.SStage i)).symm.toRingHom.comp (A.stageMap i)) x) =
        A.stageMap i x
      simp)
  let eSrc0 : B.SStage i ⊗[A.RStage i] A.RStage j ≃+*
      A.SStage i ⊗[A.RStage i] A.RStage j :=
    (Algebra.TensorProduct.congr eLeft
      (AlgEquiv.refl : A.RStage j ≃ₐ[A.RStage i] A.RStage j)).toRingEquiv
  let eSrc : B.targetStageBaseChange h ≃+* A.targetStageBaseChange h := by
    simpa [B, targetShrinkSameIndex, DirectedLocalHomApproximation.targetStageBaseChange] using
      eSrc0
  refine ⟨eSrc, ?_⟩
  apply RingHom.ext
  intro z
  -- Proof comment: it suffices to compare the two maps on pure tensors; both sides are ring
  -- homomorphisms out of the same tensor product.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    have hB_tmul := DirectedLocalHomApproximation.stageBaseChangeMap_tmul' B h
      ((Shrink.ringEquiv (A.SStage i)).symm x) y
    have htarget :
        (Shrink.ringEquiv (A.SStage j))
          ((B.targetMap i j h) ((Shrink.ringEquiv (A.SStage i)).symm x)) =
        (A.targetMap i j h) x := by
      dsimp [B, targetShrinkSameIndex, smallModelRingHom]
      change (Shrink.ringEquiv (A.SStage j))
          ((Shrink.ringEquiv (A.SStage j)).symm
            ((A.targetMap i j h) ((Shrink.ringEquiv (A.SStage i))
              ((Shrink.ringEquiv (A.SStage i)).symm x)))) =
        (A.targetMap i j h) x
      simp
    have hstage :
        (Shrink.ringEquiv (A.SStage j)) ((B.stageMap j) y) = (A.stageMap j) y := by
      dsimp [B, targetShrinkSameIndex]
      change (Shrink.ringEquiv (A.SStage j))
          ((Shrink.ringEquiv (A.SStage j)).symm (A.stageMap j y)) = A.stageMap j y
      simp
    have hmul :
        (B.targetMap i j h) ((Shrink.ringEquiv (A.SStage i)).symm x) * (B.stageMap j) y =
          ((Shrink.ringEquiv (A.SStage j)).symm.toRingHom.comp (A.stageBaseChangeMap h))
            (x ⊗ₜ[A.RStage i] y) := by
      apply (Shrink.ringEquiv (A.SStage j)).injective
      simp only [RingHom.comp_apply]
      rw [DirectedLocalHomApproximation.stageBaseChangeMap_tmul' A h x y]
      calc
        (Shrink.ringEquiv (A.SStage j))
            ((B.targetMap i j h) ((Shrink.ringEquiv (A.SStage i)).symm x) *
              (B.stageMap j) y) =
          (Shrink.ringEquiv (A.SStage j))
              ((B.targetMap i j h) ((Shrink.ringEquiv (A.SStage i)).symm x)) *
            (Shrink.ringEquiv (A.SStage j)) ((B.stageMap j) y) := by
            exact (Shrink.ringEquiv (A.SStage j)).map_mul _ _
        _ = (A.targetMap i j h) x * (A.stageMap j) y := by
            rw [htarget, hstage]
        _ = (Shrink.ringEquiv (A.SStage j))
              ((Shrink.ringEquiv (A.SStage j)).symm.toRingHom
                ((A.targetMap i j h) x * (A.stageMap j) y)) := by
            simp
    exact hB_tmul.trans hmul
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 127 13: shrinking only target stages preserves the property that
all transition base changes are localizations at prime ideals. -/
theorem targetShrinkSameIndex_hasPrimeLocalizationTransitions
    {T : Type uR} [CommRing T] [IsLocalRing T] (e : T ≃+* S)
    (A : DirectedLocalHomApproximation.{uR, uR, uR} (e.symm.toRingHom.comp f))
    (hsmall : ∀ i : A.Λ, Small.{uS} (A.SStage i))
    (hA : A.HasPrimeLocalizationTransitions) :
    (A.targetShrinkSameIndex (f := f) e hsmall).HasPrimeLocalizationTransitions := by
  intro i j hij
  let B := A.targetShrinkSameIndex (f := f) e hsmall
  rcases hA (i := i) (j := j) hij with ⟨q, hq, hqmap⟩
  obtain ⟨eSrc, hcomp⟩ :=
    A.targetShrinkSameIndex_stageBaseChangeMap_comp (f := f) e hsmall hij
  have hmapShrink :
      q.primeCompl.IsLocalizationMap
        ((Shrink.ringEquiv (A.SStage j)).symm.toRingHom.comp (A.stageBaseChangeMap hij)) := by
    -- Proof comment: the original localization witness is postcomposed with the inverse shrink
    -- equivalence of the later target stage.
    exact isLocalizationMap_comp_ringEquiv_symm q.primeCompl (A.stageBaseChangeMap hij)
      (Shrink.ringEquiv (A.SStage j)) hqmap
  have hmapTransported :
      q.primeCompl.IsLocalizationMap ((B.stageBaseChangeMap hij).comp eSrc.symm.toRingHom) := by
    have hmapTransported0 :
        q.primeCompl.IsLocalizationMap
          (((A.targetShrinkSameIndex (f := f) e hsmall).stageBaseChangeMap hij).comp
            eSrc.symm.toRingHom) := by
      rw [hcomp]
      exact hmapShrink
    simpa [B] using hmapTransported0
  let qB : Ideal (B.targetStageBaseChange hij) := Ideal.comap eSrc.toRingHom q
  have hqB : qB.IsPrime := by
    -- Proof comment: the transported prime on the shrunken base-change source is the pullback of
    -- the original prime along a ring equivalence.
    simpa [qB] using Ideal.comap_isPrime eSrc.toRingHom q
  letI : qB.IsPrime := hqB
  letI : Algebra (A.targetStageBaseChange hij) (B.SStage j) :=
    ((B.stageBaseChangeMap hij).comp eSrc.symm.toRingHom).toAlgebra
  have hlocOld : IsLocalization q.primeCompl (B.SStage j) :=
    (isLocalization_iff_isLocalizationMap
      (M := q.primeCompl) (S := B.SStage j)).mpr hmapTransported
  have hpmap : qB.primeCompl.map eSrc.toMonoidHom = q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [qB, Ideal.mem_comap] using hy
    · intro hx
      refine ⟨eSrc.symm x, ?_, by simp⟩
      exact fun hmem ↦ hx (by simpa [qB, Ideal.mem_comap] using hmem)
  letI : Algebra (B.targetStageBaseChange hij) (B.SStage j) :=
    (B.stageBaseChangeMap hij).toAlgebra
  have hlocNew : IsLocalization qB.primeCompl (B.SStage j) := by
    -- Proof comment: the localization instance on the original source is transported back across
    -- the source ring equivalence `eSrc`.
    exact IsLocalization.of_ringEquiv_left
      (e := eSrc)
      hpmap
      (fun x ↦ by
        change B.stageBaseChangeMap hij x =
          ((B.stageBaseChangeMap hij).comp eSrc.symm.toRingHom) (eSrc x)
        simp)
  exact ⟨qB, hqB,
    (isLocalization_iff_isLocalizationMap
      (M := qB.primeCompl) (S := B.SStage j)).mp hlocNew⟩

end DirectedLocalHomApproximation

/-- Helper for Chap10 Lemma 10 127 13: `ULift` of a directed order is directed in any target
index universe. -/
private instance uliftAny_isDirectedOrder {ι : Type uM} [Preorder ι] [IsDirectedOrder ι] :
    IsDirectedOrder (ULift.{uN} ι) := by
  refine ⟨?_⟩
  intro i j
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.down j.down
  exact ⟨ULift.up k, hik, hjk⟩

/-- Helper for Chap10 Lemma 10 127 13: a directed ring system stays directed after reindexing by
`ULift.down`. -/
private instance uliftAny_directedSystem {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    DirectedSystem (fun i : ULift.{uN} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) where
  map_self := by
    intro i x
    -- Proof comment: the lifted self-map is the original self-map at the underlying index.
    simpa using DirectedSystem.map_self (f := fun i j h ↦ φ i j h) x
  map_map := by
    intro i j k hij hjk x
    -- Proof comment: the lifted composition law is exactly the original composition law at
    -- underlying indices.
    simpa using DirectedSystem.map_map (f := fun i j h ↦ φ i j h) hij hjk x

/-- Helper for Chap10 Lemma 10 127 13: the direct limit of a `ULift`-reindexed system maps to the
original direct limit by forgetting the lifted index. -/
private noncomputable def directLimit_uliftAnyToOriginal {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit (fun i : ULift.{uN} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) →+*
      Ring.DirectLimit G (fun i j h ↦ φ i j h) :=
  Ring.DirectLimit.lift
    (fun i : ULift.{uN} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h)
    (Ring.DirectLimit G (fun i j h ↦ φ i j h))
    (fun i ↦ Ring.DirectLimit.of G (fun i j h ↦ φ i j h) i.down)
    (by
      intro i j hij x
      simpa using (Ring.DirectLimit.of_f hij x))

/-- Helper for Chap10 Lemma 10 127 13: forgetting the lifted index sends a lifted stage generator
to the corresponding original stage generator. -/
@[simp] private theorem directLimit_uliftAnyToOriginal_of {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ULift.{uN} ι) (x : G i.down) :
    directLimit_uliftAnyToOriginal (G := G) (φ := φ)
        (Ring.DirectLimit.of (fun j : ULift.{uN} ι ↦ G j.down)
          (fun j k h ↦ φ j.down k.down h) i x) =
      Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i.down x := by
  -- Proof comment: this is the universal property computation for the direct-limit lift.
  simpa [directLimit_uliftAnyToOriginal] using
    (Ring.DirectLimit.lift_of
      (G := fun j : ULift.{uN} ι ↦ G j.down)
      (f := fun j k h ↦ φ j.down k.down h)
      (P := Ring.DirectLimit G (fun j k h ↦ φ j k h))
      (g := fun j ↦ Ring.DirectLimit.of G (fun j k h ↦ φ j k h) j.down)
      (Hg := by intro i j hij y; rfl)
      i x)

/-- Helper for Chap10 Lemma 10 127 13: the original direct limit maps to the `ULift`-reindexed
direct limit by lifting each index. -/
private noncomputable def directLimit_originalToUliftAny {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit G (fun i j h ↦ φ i j h) →+*
      Ring.DirectLimit (fun i : ULift.{uN} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) :=
  Ring.DirectLimit.lift
    G (fun i j h ↦ φ i j h)
    (Ring.DirectLimit (fun i : ULift.{uN} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h))
    (fun i ↦ Ring.DirectLimit.of (fun j : ULift.{uN} ι ↦ G j.down)
      (fun j k h ↦ φ j.down k.down h) (ULift.up i))
    (by
      intro i j hij x
      simpa using (Ring.DirectLimit.of_f hij x))

/-- Helper for Chap10 Lemma 10 127 13: lifting an original stage generator gives the corresponding
generator in the lifted-index direct limit. -/
@[simp] private theorem directLimit_originalToUliftAny_of {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ι) (x : G i) :
    directLimit_originalToUliftAny (G := G) (φ := φ)
        (Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i x) =
      Ring.DirectLimit.of (fun j : ULift.{uN} ι ↦ G j.down)
        (fun j k h ↦ φ j.down k.down h) (ULift.up i) x := by
  -- Proof comment: this is again the defining computation for the direct-limit lift.
  simpa [directLimit_originalToUliftAny] using
    (Ring.DirectLimit.lift_of
      (G := G)
      (f := fun j k h ↦ φ j k h)
      (P := Ring.DirectLimit (fun j : ULift.{uN} ι ↦ G j.down)
        (fun j k h ↦ φ j.down k.down h))
      (g := fun i ↦ Ring.DirectLimit.of (fun j : ULift.{uN} ι ↦ G j.down)
        (fun j k h ↦ φ j.down k.down h) (ULift.up i))
      (Hg := by intro i j hij y; rfl)
      i x)

/-- Helper for Chap10 Lemma 10 127 13: reindexing a directed ring system by `ULift` does not
change its direct limit. -/
private noncomputable def directLimit_uliftAnyRingEquiv {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)] :
    Ring.DirectLimit (fun i : ULift.{uN} ι ↦ G i.down) (fun i j h ↦ φ i.down j.down h) ≃+*
      Ring.DirectLimit G (fun i j h ↦ φ i j h) :=
  RingEquiv.ofRingHom
    (directLimit_uliftAnyToOriginal (G := G) (φ := φ))
    (directLimit_originalToUliftAny (G := G) (φ := φ))
    (by
      apply Ring.DirectLimit.hom_ext
      intro i
      ext x
      simp [directLimit_uliftAnyToOriginal, directLimit_originalToUliftAny])
    (by
      apply Ring.DirectLimit.hom_ext
      intro i
      ext x
      simp [directLimit_uliftAnyToOriginal, directLimit_originalToUliftAny])

/-- Helper for Chap10 Lemma 10 127 13: the direct-limit equivalence for arbitrary `ULift`
reindexing sends each lifted generator to its original generator. -/
@[simp] private theorem directLimit_uliftAnyRingEquiv_of {ι : Type uM} [Preorder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)]
    (φ : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h ↦ φ i j h)]
    (i : ULift.{uN} ι) (x : G i.down) :
    directLimit_uliftAnyRingEquiv (G := G) (φ := φ)
        (Ring.DirectLimit.of (fun j : ULift.{uN} ι ↦ G j.down)
          (fun j k h ↦ φ j.down k.down h) i x) =
      Ring.DirectLimit.of G (fun j k h ↦ φ j k h) i.down x := by
  -- Proof comment: the forward map of the equivalence is the index-forgetting direct-limit map.
  exact directLimit_uliftAnyToOriginal_of (G := G) (φ := φ) i x

namespace DirectedLocalHomApproximation

/-- Helper for Chap10 Lemma 10 127 13: the `ULift`-reindexed approximation inherits the original
colimit square on stage generators. -/
private theorem reindexULiftAny_colimit_comm {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation.{u, v, uM} f) :
    ((directLimit_uliftAnyRingEquiv (G := A.SStage) (φ := A.targetMap)).trans
          A.targetColimit).toRingHom.comp
        (Ring.DirectLimit.map (fun i : ULift.{uN} A.Λ ↦ A.stageMap i.down)
          (fun _ _ h ↦ A.comm h)) =
      f.comp
        ((directLimit_uliftAnyRingEquiv (G := A.RStage) (φ := A.map)).trans
          A.colimitIso).toRingHom := by
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  have hA :=
    congrArg
      (fun g : Ring.DirectLimit A.RStage (fun j k h ↦ A.map j k h) →+* S =>
        g (Ring.DirectLimit.of A.RStage (fun j k h ↦ A.map j k h) i.down x))
      A.colimit_comm
  -- Proof comment: after collapsing the lifted direct limits to the original direct limits, this
  -- is exactly the original colimit square of `A`.
  simpa [RingHom.comp_apply] using hA

/-- Helper for Chap10 Lemma 10 127 13: reindex an approximation by `ULift` into any requested
index universe. -/
noncomputable def reindexULiftAny {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    (A : DirectedLocalHomApproximation.{u, v, uM} f) :
    DirectedLocalHomApproximation.{u, v, max uM uN} f :=
  { Λ := ULift.{uN} A.Λ
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := inferInstance
    RStage := fun i ↦ A.RStage i.down
    instCommRingRStage := fun i ↦ A.instCommRingRStage i.down
    map := fun i j h ↦ A.map i.down j.down h
    instDirectedSystemRStage := uliftAny_directedSystem A.RStage A.map
    colimitIso := (directLimit_uliftAnyRingEquiv (G := A.RStage) (φ := A.map)).trans
      A.colimitIso
    instIsLocalRingRStage := fun i ↦ A.instIsLocalRingRStage i.down
    SStage := fun i ↦ A.SStage i.down
    instCommRingSStage := fun i ↦ A.instCommRingSStage i.down
    instIsLocalRingSStage := fun i ↦ A.instIsLocalRingSStage i.down
    stageMap := fun i ↦ A.stageMap i.down
    stageMap_isLocalHom := fun i ↦ A.stageMap_isLocalHom i.down
    targetMap := fun i j h ↦ A.targetMap i.down j.down h
    instDirectedSystemTarget := uliftAny_directedSystem A.SStage A.targetMap
    comm := fun {_ _} h ↦ A.comm h
    targetColimit := (directLimit_uliftAnyRingEquiv (G := A.SStage) (φ := A.targetMap)).trans
      A.targetColimit
    colimit_comm := reindexULiftAny_colimit_comm A
    source_essFiniteType := fun i ↦ A.source_essFiniteType i.down
    target_essFiniteType := fun i ↦ A.target_essFiniteType i.down }

/-- Helper for Chap10 Lemma 10 127 13: prime-localization transitions persist after arbitrary
`ULift` reindexing. -/
theorem hasPrimeLocalizationTransitions_reindexULiftAny {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, uM} f}
    (hA : A.HasPrimeLocalizationTransitions) :
    (A.reindexULiftAny :
      DirectedLocalHomApproximation.{u, v, max uM uN} f).HasPrimeLocalizationTransitions := by
  intro i j hij
  -- Proof comment: a lifted transition is literally the original transition between the
  -- underlying indices.
  simpa [DirectedLocalHomApproximation.reindexULiftAny] using hA (i := i.down) (j := j.down) hij

end DirectedLocalHomApproximation

/-- Chap10 Lemma 10 127 13: the mixed-universe ring approximation provides a directed local
approximation of `f` with prime-localization transitions. -/
theorem exists_localEssFinitePresentationApproximation_mixed_universe
    (hf : f.EssFinitePresentation) :
    ∃ A : DirectedLocalHomApproximation.{uR, uS, max uR uS} f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := by
  classical
  -- Route correction: the earlier same-universe `ULift` approximation has arbitrary common-
  -- universe stages, so it cannot be lowered to the required source and target universes.  We
  -- instead start from the descended source model and build the mixed tail data directly.
  obtain
    ⟨A₀, _hA₀map, _hA₀lim, P, hPcomm, hPalgInst, g, _hgfp, hPalg, q, hq, hPSalg,
      hlocq, hfg, _hqR, i₀, P₀, hP₀comm, hP₀alg, hP₀fp, ⟨e⟩⟩ :=
    exists_descended_local_finitePresentation_model_mixed_universe (f := f) hf
  letI : CommRing P := hPcomm
  letI : Algebra R P := hPalgInst
  letI : q.IsPrime := hq
  letI : Algebra P S := hPSalg
  letI : CommRing P₀ := hP₀comm
  letI : Algebra (A₀.RStage i₀) P₀ := hP₀alg
  letI : Algebra.FinitePresentation (A₀.RStage i₀) P₀ := hP₀fp
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso
      i₀).toAlgebra
  have hRalg : algebraMap (A₀.RStage i₀) R =
      Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i₀ := by
    rfl
  have hfg_alg : f = (algebraMap P S).comp (algebraMap R P) := by
    -- Proof comment: replace the named finite-presentation map `g` by the canonical algebra map
    -- before passing to the joint-universe tail API.
    rw [hPalg]
    exact hfg
  have hσ_raw_comp :
      ∀ (j k : Set.Ici i₀) (hjk : j ≤ k),
        descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e j =
          (descendedTailSigmaJointUniverse (S := S) A₀ i₀ P₀ hRalg e k).comp
            (descendedTailRawMap A₀ i₀ P₀ j k hjk) := by
    intro j k hjk
    -- Proof comment: compatibility of the raw descended comparisons is inherited from the
    -- directed source system after rebuilding the comparison in the ambient target universe.
    exact descended_tail_sigma_joint_universe_comp (S := S) A₀ i₀ P₀ hRalg e j k hjk
  let bundle :
      JointUniverseTargetTailData (f := f) (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp :=
    joint_universe_target_tail_data (f := f) (S := S) A₀ i₀ P₀ hfg_alg hRalg e
      hσ_raw_comp
  letI : IsDirectedOrder (Set.Ici i₀) := bundle.instTailDirected
  letI : DirectedSystem (descendedTailRawStage A₀ i₀ P₀)
      (fun j k h ↦ descendedTailRawMap A₀ i₀ P₀ j k h) :=
    bundle.instDirectedSystemRaw
  letI : DirectedSystem (descendedTailSStageJointUniverse (S := S) A₀ i₀ P₀ hRalg e)
      (fun j k h ↦ descendedTailTargetMapJointUniverse
        (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp j k h) :=
    bundle.instDirectedSystemTarget
  obtain ⟨eTail, hTail⟩ :=
    joint_universe_target_colimit_equiv_from_bundle (f := f) (S := S) A₀ g q hlocq hfg i₀
      P₀ hRalg hPalg e hσ_raw_comp bundle
  -- Proof comment: at this point the source model, target tail data, and target colimit
  -- comparison are fixed.  The remaining missing API must package these data into a
  -- `DirectedLocalHomApproximation` with target stages in `Type uS` and transport the
  -- prime-localization transition witnesses to that owner.
  -- TODO: prove the mixed-universe owner construction from `bundle`, `eTail`, and `hTail`.
  have howner :
      ∃ A : DirectedLocalHomApproximation.{uR, uS, max uR uS} f,
        DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := by
    let T : Type uR :=
      descendedTailTargetLimitJointUniverse (S := S) A₀ i₀ P₀ hRalg e hσ_raw_comp
    letI : CommRing T := inferInstance
    letI : IsLocalRing T := RingEquiv.isLocalRing eTail.symm
    let fT : R →+* T := eTail.symm.toRingHom.comp f
    letI : IsLocalHom fT :=
      ringHom_comp_ringEquiv_symm_isLocalHom f eTail
    have hfT : fT.EssFinitePresentation :=
      ringHom_comp_ringEquiv_symm_essFinitePresentation f eTail hf
    obtain ⟨A, hA⟩ := exists_localEssFinitePresentationApproximation (f := fT) hfT
    have hsmallTarget : ∀ i : A.Λ, Small.{uS} (A.SStage i) := by
      intro i
      letI : Small.{uS} ℤ := Small.mk' ((Equiv.ulift : ULift.{uS} ℤ ≃ ℤ).symm)
      letI : Algebra ℤ (A.RStage i) := (Int.castRingHom (A.RStage i)).toAlgebra
      have hR : Algebra.EssFiniteType ℤ (A.RStage i) := by
        rw [← RingHom.essFiniteType_algebraMap]
        exact A.source_essFiniteType i
      letI : Algebra.EssFiniteType ℤ (A.RStage i) := hR
      have hsmallR : Small.{uS} (A.RStage i) :=
        small_of_essFiniteType_of_small_base (A := ℤ) (B := A.RStage i)
      letI : Small.{uS} (A.RStage i) := hsmallR
      letI : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
      have hS : Algebra.EssFiniteType (A.RStage i) (A.SStage i) := by
        rw [← RingHom.essFiniteType_algebraMap]
        exact A.target_essFiniteType i
      letI : Algebra.EssFiniteType (A.RStage i) (A.SStage i) := hS
      -- Proof comment: the target stage is essentially finite type over a small source stage, so
      -- it has a model in the target universe.
      exact small_of_essFiniteType_of_small_base (A := A.RStage i) (B := A.SStage i)
    -- Route correction: the old target-stage `ULift` route has the wrong carrier universe.
    -- The verified replacement prefix constructs a same-universe approximation of
    -- `fT : R → T`, where `T` is the joint-universe target colimit ring-equivalent to `S`, and
    -- proves all of its target stages are small in `uS`.  The remaining structural step is a
    -- generic transport theorem: shrink the target stages of `A`, compose the target colimit with
    -- `eTail`, and transport `hA` across the stagewise shrink equivalences.
    let Bsame : DirectedLocalHomApproximation.{uR, uS, uR} f :=
      A.targetShrinkSameIndex (f := f) eTail hsmallTarget
    -- Proof comment: the same-index target-shrunk owner is now constructed.  The remaining
    -- step transports the prime-localization witnesses across target shrink and then lifts its
    -- index type from `Type uR` to `Type (max uR uS)`.
    have hBsame : Bsame.HasPrimeLocalizationTransitions :=
      A.targetShrinkSameIndex_hasPrimeLocalizationTransitions (f := f) eTail hsmallTarget hA
    refine ⟨(Bsame.reindexULiftAny :
      DirectedLocalHomApproximation.{uR, uS, max uR uS} f), ?_⟩
    exact DirectedLocalHomApproximation.hasPrimeLocalizationTransitions_reindexULiftAny hBsame
  exact howner

-- source stages are essentially of finite type over `ℤ` and whose target stages are essentially
-- of finite type over the source stages. Then descend a finite presentation matrix for `M` to a
-- sufficiently large target stage, define the stage modules by cokernels of the descended
-- matrices, and use finite presentation to obtain the base-change isomorphisms between stages and
-- after passage to the colimit.
/-- Lemma 10.127.13: if `f : R →+* S` is a local homomorphism of local rings, `S` is essentially
of finite presentation over `R`, and `M` is a finitely presented `S`-module, then there is a
directed approximation of `f` by local ring maps whose source stages are essentially of finite
type over `ℤ`, whose target stages are essentially of finite type over the corresponding source
stages, whose transition base changes are localizations at prime ideals, together with finite
stage modules whose base changes recover the later stages and the limiting module `M`. -/
@[stacks 00QX]
theorem exists_localEssFinitePresentationModuleApproximation
    [Module.FinitePresentation S M]
    (hf : f.EssFinitePresentation) :
    Nonempty
      (DirectedLocalEssFinitePresentationModuleApproximation.{uR, uS, uM, uS, max uR uS} f M) := by
  obtain ⟨A, hA⟩ := exists_localEssFinitePresentationApproximation_mixed_universe (f := f) hf
  obtain ⟨i₀, M₀, _, _, _, ⟨eM⟩⟩ := descend_module_to_target_stage (f := f) (A := A) (M := M)
  -- Proof comment: Lemma `10.127.11` provides the ring approximation, Lemma `10.127.6` descends
  -- the finitely presented module to one target stage, and the only remaining source-faithful
  -- step is the textbook tail construction from that descended stage.
  simpa using tail_module_system_from_descended_stage (f := f) (M := M) A hA i₀ eM

end
