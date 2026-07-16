import stacks_proof.stacks_project.Chap10.Lemma_10_127_6
import stacks_proof.stacks_project.Chap10.Lemma_10_127_11
import stacks_proof.stacks_project.Chap10.Remark_10_127_12
import stacks_proof.stacks_project.Chap10.Lemma_10_6_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w uR uS uM uN

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for essentially finitely presented local
  homomorphisms together with descended finite stage modules.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.HasPrimeLocalizationTransitions`
  - `exists_localEssFinitePresentationApproximation`
  - `DirectedFinitePresentationModuleApproximation`
  - `DirectedFinitePresentationModuleColimitApproximation`
  - `finitelyPresented_module_descends_to_stage`
* Best owner abstraction: the public owner for this source-facing module approximation should be a
  structure extending `DirectedLocalHomApproximation f`, exactly as the finite-presentation and
  colimit variants elsewhere in the chapter extend their ring-approximation owners.
* Layer targeted here: `source-facing` owner built over the chapter's `core/canonical`
  approximation owner `DirectedLocalHomApproximation f`.
* Primitive vs. derived: the source-facing primitive data are the stage modules `M_λ`, their
  finite `S_λ`-module structures, and the canonical transition/final base-change linear
  equivalences. Prime-localization transitions and the induced `R_λ`-module structures are
  derived from the inherited ring-approximation owner.
-/

variable (f : R →+* S) [IsLocalHom f]
variable {M : Type uM} [AddCommGroup M] [Module S M]

local notation "same_universe_localEssFinitePresentationApproximation" =>
  exists_localEssFinitePresentationApproximation

/- A directed approximation of a finitely presented `S`-module along an essentially finitely
presented local homomorphism `f : R →+* S`, with finite stage modules and canonical base-change
identifications along transitions and at the limit. -/
structure DirectedLocalEssFinitePresentationModuleApproximation
    (f : R →+* S) (M : Type uM) [AddCommGroup M] [Module S M]
    extends DirectedLocalHomApproximation f where
  hasPrimeLocalizationTransitions :
    DirectedLocalHomApproximation.HasPrimeLocalizationTransitions
      toDirectedLocalHomApproximation
  moduleStage : Λ → Type uN
  instAddCommGroupModuleStage : ∀ i, AddCommGroup (moduleStage i)
  instModuleModuleStage : ∀ i, Module (SStage i) (moduleStage i)
  instModuleFiniteModuleStage : ∀ i, Module.Finite (SStage i) (moduleStage i)
  transitionBaseChange :
    ∀ {i j : Λ} (h : i ≤ j),
      let _ : Algebra (SStage i) (SStage j) := (targetMap i j h).toAlgebra
      SStage j ⊗[SStage i] moduleStage i ≃ₗ[SStage j] moduleStage j
  finalBaseChange :
    ∀ i : Λ,
      let _ : Algebra (SStage i) S :=
        (DirectedLocalHomApproximation.targetStageToLimitHom
          toDirectedLocalHomApproximation i).toAlgebra
      S ⊗[SStage i] moduleStage i ≃ₗ[S] M

attribute [instance]
  DirectedLocalEssFinitePresentationModuleApproximation.instAddCommGroupModuleStage
attribute [instance]
  DirectedLocalEssFinitePresentationModuleApproximation.instModuleModuleStage
attribute [instance]
  DirectedLocalEssFinitePresentationModuleApproximation.instModuleFiniteModuleStage

namespace DirectedLocalEssFinitePresentationModuleApproximation

instance stageModuleSource
    (A : DirectedLocalEssFinitePresentationModuleApproximation f M) (i : A.Λ) :
    Module (A.RStage i) (A.moduleStage i) :=
  Module.compHom (A.moduleStage i) (A.stageMap i)

end DirectedLocalEssFinitePresentationModuleApproximation

/-- Helper for Lemma 10.127.13: restricting a directed local approximation to the tail above a
fixed stage keeps the same source and target stage data and only replaces the two colimit
identifications by the canonical tail direct-limit equivalences. -/
noncomputable def tail_local_hom_approximation
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ) :
    DirectedLocalHomApproximation f where
  Λ := Set.Ici i₀
  instPreorder := inferInstance
  instNonempty := inferInstance
  instDirectedOrder := tail_index_isDirected i₀
  RStage := fun j ↦ A.RStage j.1
  instCommRingRStage := fun _ ↦ inferInstance
  map := fun j k h ↦ A.map j.1 k.1 h
  instDirectedSystemRStage := inferInstance
  colimitIso :=
    tail_directLimitIso A.RStage (fun i j h ↦ A.map i j h) i₀ A.colimitIso
  instIsLocalRingRStage := fun _ ↦ inferInstance
  SStage := fun j ↦ A.SStage j.1
  instCommRingSStage := fun _ ↦ inferInstance
  instIsLocalRingSStage := fun _ ↦ inferInstance
  stageMap := fun j ↦ A.stageMap j.1
  stageMap_isLocalHom := fun j ↦ A.stageMap_isLocalHom j.1
  targetMap := fun j k h ↦ A.targetMap j.1 k.1 h
  instDirectedSystemTarget := inferInstance
  comm := fun {j k} h ↦ A.comm h
  targetColimit :=
    tail_directLimitIso A.SStage (fun i j h ↦ A.targetMap i j h) i₀ A.targetColimit
  colimit_comm := by
    -- Proof comment: both sides agree on every tail-stage generator, and on generators the tail
    -- colimit maps are just the original colimit maps after forgetting that the index lies in the
    -- tail.
    apply Ring.DirectLimit.hom_ext
    intro j
    ext x
    have hfull :=
      congrArg
        (fun g : Ring.DirectLimit A.RStage (fun i j h ↦ A.map i j h) →+* S ↦
          g (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.map i j h) j.1 x))
        A.colimit_comm
    -- Proof comment: after evaluating on one generator, the tail-to-full maps disappear and the
    -- result is exactly the original colimit comparison at the underlying stage.
    simpa [tail_directLimitIso, tail_directLimit_to_full, RingHom.comp_apply,
      Ring.DirectLimit.map_apply_of] using hfull
  source_essFiniteType := fun j ↦ A.source_essFiniteType j.1
  target_essFiniteType := fun j ↦ A.target_essFiniteType j.1

/-- Helper for Lemma 10.127.13: prime-localization transitions are inherited unchanged by the tail
restriction. -/
theorem tail_local_hom_approximation_hasPrimeLocalizationTransitions
    (A : DirectedLocalHomApproximation f)
    (hA : DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A)
    (i₀ : A.Λ) :
    DirectedLocalHomApproximation.HasPrimeLocalizationTransitions
      (tail_local_hom_approximation (f := f) A i₀) := by
  intro j k hjk
  -- Proof comment: the tail transition `j ≤ k` is literally the original transition on the
  -- underlying indices `j.1 ≤ k.1`.
  exact hA hjk

/-- Helper for Lemma 10.127.13: the canonical map from a later target stage to the limit ring
commutes with the target transition maps. -/
theorem targetStageToLimitHom_comp_targetMap
    (A : DirectedLocalHomApproximation f) {i j : A.Λ} (h : i ≤ j) :
    (DirectedLocalHomApproximation.targetStageToLimitHom A j).comp (A.targetMap i j h) =
      DirectedLocalHomApproximation.targetStageToLimitHom A i := by
  ext x
  -- Proof comment: both composites are the same direct-limit cocone morphism evaluated on the
  -- stage generator coming from `x`.
  simp [DirectedLocalHomApproximation.targetStageToLimitHom, RingHom.comp_apply,
    Ring.DirectLimit.of_f]

/-- Helper for Lemma 10.127.13: after restricting to a tail, the stage-to-limit map is the
original one on the underlying stage. -/
theorem tail_targetStageToLimitHom_eq
    (A : DirectedLocalHomApproximation f) (i₀ : A.Λ) (j : Set.Ici i₀) :
    DirectedLocalHomApproximation.targetStageToLimitHom
        (tail_local_hom_approximation (f := f) A i₀) j =
      DirectedLocalHomApproximation.targetStageToLimitHom A j.1 := by
  ext x
  -- Proof comment: the tail colimit is identified with the original colimit by forgetting that
  -- the stage lies in the tail, and on one generator this forgetful map is `tail_directLimit_to_full`.
  change
    (tail_directLimitIso A.SStage (fun i j h ↦ A.targetMap i j h) i₀ A.targetColimit)
        (Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A.SStage j.1)
          (fun j k h ↦ A.targetMap j.1 k.1 h) j x) =
      A.targetColimit
        (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) j.1 x)
  simp [DirectedLocalHomApproximation.targetStageToLimitHom, tail_local_hom_approximation,
    tail_directLimitIso, tail_directLimit_to_full_of]

/-- Helper for Lemma 10.127.13: essential finite presentation for a mixed-universe local map
admits a descended finitely presented local model over a stage of an approximation of `id_R`. -/
  theorem exists_descended_local_finitePresentation_model_mixed_universe
    (hf : f.EssFinitePresentation) :
    ∃ (A₀ : DirectedLocalHomApproximation.{uR, uR, uR} (RingHom.id R))
      (_ : ∀ i j (h : i ≤ j), IsLocalHom (A₀.map i j h))
      (_ : ∀ i, IsLocalHom
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso i))
      (P : Type uR) (_ : CommRing P) (_ : Algebra R P) (g : R →+* P) (_ : g.FinitePresentation)
      (_ : algebraMap R P = g)
      (q : Ideal P) (_ : q.IsPrime) (_ : Algebra P S),
      q.primeCompl.IsLocalizationMap (algebraMap P S) ∧
        f = (algebraMap P S).comp g ∧
        Ideal.comap g q = IsLocalRing.maximalIdeal R ∧
        ∃ (i₀ : A₀.Λ) (P₀ : Type uR) (_ : CommRing P₀)
          (_ : Algebra (A₀.RStage i₀) P₀) (_ : Algebra.FinitePresentation (A₀.RStage i₀) P₀),
          letI : Algebra (A₀.RStage i₀) R :=
            (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.map i j h) A₀.colimitIso
              i₀).toAlgebra
          Nonempty (P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] P) := by
  letI : Algebra R S := f.toAlgebra
  have hfAlg : Algebra.EssFinitePresentation R S := hf
  rw [Algebra.essFinitePresentation_iff] at hfAlg
  rcases hfAlg with ⟨n, I, hI, _, _, M, hloc⟩
  let P : Type uR := MvPolynomial (Fin n) R ⧸ I
  let g : R →+* P := algebraMap R P
  have hg : g.FinitePresentation := by
    -- Proof comment: the quotient-model witness is finitely presented over `R`.
    rw [RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
  let q : Ideal P := Ideal.comap (algebraMap P S) (IsLocalRing.maximalIdeal S)
  have hq :
      q.IsPrime ∧ q.primeCompl.IsLocalizationMap (algebraMap P S) := by
    -- Proof comment: replace the raw localization witness by the local prime localization cut out
    -- by the maximal ideal of `S`.
    simpa [q] using
      (local_isLocalization_at_comap_maximalIdeal (P := P) (T := S) (M := M))
  have hfg : f = (algebraMap P S).comp g := by
    -- Proof comment: the algebra tower from the quotient-model witness is exactly the original map
    -- `f`.
    simpa [g, RingHom.algebraMap_toAlgebra] using
      (IsScalarTower.algebraMap_eq R P S)
  have hPalg : algebraMap R P = g := by
    rfl
  have hqR : Ideal.comap g q = IsLocalRing.maximalIdeal R := by
    -- Proof comment: the factored local map pulls the contracted prime back to the maximal ideal
    -- of the local source.
    simpa [q, hfg, Ideal.comap_comap] using IsLocalRing.maximalIdeal_comap f
  have hid : (RingHom.id R).EssFiniteType := by
    -- Proof comment: the identity map is essentially finitely presented, hence essentially of
    -- finite type.
    rw [← Algebra.algebraMap_self (R := R), RingHom.essFiniteType_algebraMap]
    infer_instance
  obtain ⟨A₀, _, hA₀map, hA₀lim⟩ :=
    exists_directed_local_essFiniteType_approximation_isLocalHom (f := RingHom.id R) hid
  have hPfp : Algebra.FinitePresentation R P := by
    dsimp [P]
    exact Algebra.FinitePresentation.quotient (R := R) (A := MvPolynomial (Fin n) R) hI
  letI : Algebra.FinitePresentation R P := hPfp
  obtain ⟨i₀, P₀, _, _, _, e⟩ :=
    finitelyPresented_algebra_descends (R := R) A₀.RStage (fun i j h ↦ A₀.map i j h)
      A₀.colimitIso P
  exact ⟨A₀, hA₀map, hA₀lim, P, inferInstance, inferInstance, g, hg, hPalg, q, hq.1, inferInstance,
    hq.2, hfg, hqR,
    i₀, P₀, inferInstance, inferInstance, inferInstance, e⟩

/-- Helper for Chap10 Lemma 10 127 13: composing the codomain of a local homomorphism with the
canonical `ULift` ring equivalence preserves locality. -/
theorem ringHom_codomainUlift_isLocalHom {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (g : A →+* B)
    [IsLocalHom g] :
    IsLocalHom (((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).comp g) :
      A →+* ULift.{w} B) := by
  letI : IsLocalHom (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.symm.surjective
  -- Proof comment: the codomain lift is just `g` followed by a local ring equivalence.
  exact RingHom.isLocalHom_comp _ _

/-- Helper for Chap10 Lemma 10 127 13: composing the codomain of an essentially finite-type
ring homomorphism with the canonical `ULift` ring equivalence preserves essential finite type. -/
theorem ringHom_codomainUlift_essFiniteType {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (g : A →+* B) (hg : g.EssFiniteType) :
    (((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).comp g) :
      A →+* ULift.{w} B).EssFiniteType := by
  have htarget :
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).EssFiniteType := by
    have hsurj :
        Function.Surjective (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B) := by
      simpa using ULift.ringEquiv.symm.surjective
    -- Proof comment: a surjective ring equivalence is finite type, hence essentially finite type.
    exact (RingHom.FiniteType.of_surjective
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B) hsurj).essFiniteType
  -- Proof comment: essential finite type is stable under postcomposition with the codomain
  -- `ULift` equivalence.
  exact hg.comp htarget

/-- Helper for Chap10 Lemma 10 127 13: forgetting the codomain-only `ULift` of a ring
homomorphism recovers the original value. -/
theorem ringHom_codomainUlift_down {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (g : A →+* B) (x : A) :
    (((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).comp g) x).down = g x := by
  -- Proof comment: the codomain lift is implemented by `ULift.up`, whose projection is identity.
  rfl

/-- Helper for Chap10 Lemma 10 127 13: a commuting square of stage maps remains commuting after
applying `ULift` only to the target stages. -/
theorem ringHom_codomainUlift_comm
    {A₁ A₂ : Type u} {B₁ B₂ : Type v}
    [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    (ρ : A₁ →+* A₂) (φ₁ : A₁ →+* B₁) (φ₂ : A₂ →+* B₂) (τ : B₁ →+* B₂)
    (h : φ₂.comp ρ = τ.comp φ₁) :
    (((ULift.ringEquiv.symm.toRingHom : B₂ →+* ULift.{w} B₂).comp φ₂).comp ρ) =
      (((ULift.ringEquiv.symm.toRingHom : B₂ →+* ULift.{w} B₂).comp τ).comp
        ULift.ringEquiv.toRingHom).comp
        ((ULift.ringEquiv.symm.toRingHom : B₁ →+* ULift.{w} B₁).comp φ₁) := by
  ext x
  -- Proof comment: projecting both lifted target values reduces the lifted square to the
  -- original unlifted commutative square.
  simpa [RingHom.comp_apply] using congrArg (fun g : A₁ →+* B₂ ↦ g x) h

/-- Helper for Chap10 Lemma 10 127 13: applying `RingHom.ulift` to a ring homomorphism preserves
essential finite presentation. -/
theorem ringHom_ulift_essFinitePresentation {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (g : A →+* B) (hg : g.EssFinitePresentation) :
    (RingHom.ulift.{u, v} g).EssFinitePresentation := by
  have hsource :
      (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A).EssFinitePresentation := by
    let φ : ULift.{u} A →+* A := ULift.ringEquiv.toRingHom
    have hφfp : φ.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective
    letI : Algebra (ULift.{u} A) A := φ.toAlgebra
    haveI : Algebra.FinitePresentation (ULift.{u} A) A := hφfp
    -- Proof comment: the source `ULift` equivalence is finitely presented, hence essentially
    -- finitely presented as a ring homomorphism.
    rw [RingHom.EssFinitePresentation]
    exact Algebra.EssFinitePresentation.of_finitePresentation _ _
  have htarget :
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B).EssFinitePresentation := by
    let ψ : B →+* ULift.{v} B := ULift.ringEquiv.symm.toRingHom
    have hψfp : ψ.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective ULift.ringEquiv.symm.bijective
    letI : Algebra B (ULift.{v} B) := ψ.toAlgebra
    haveI : Algebra.FinitePresentation B (ULift.{v} B) := hψfp
    -- Proof comment: the target `ULift` equivalence is handled by the same finite-presentation
    -- bridge.
    rw [RingHom.EssFinitePresentation]
    exact Algebra.EssFinitePresentation.of_finitePresentation _ _
  have hcomp :
      (((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B).comp
          (g.comp (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A))) :
        ULift.{u} A →+* ULift.{v} B).EssFinitePresentation := by
    -- Proof comment: `RingHom.ulift g` is the composite source equivalence, `g`, and target
    -- equivalence; essential finite presentation is stable under composition.
    exact (RingHom.EssFinitePresentation.comp hsource hg).comp htarget
  have hulift_eq :
      RingHom.ulift.{u, v} g =
        ((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{v} B).comp
          (g.comp (ULift.ringEquiv.toRingHom : ULift.{u} A →+* A))) := by
    -- Proof comment: the bundled `RingHom.ulift` is exactly the original map conjugated by the
    -- source and target `ULift` ring equivalences.
    ext x
    rfl
  rw [hulift_eq]
  exact hcomp

/-- Helper for Chap10 Lemma 10 127 13: composing only the codomain with the `ULift`
ring equivalence preserves essential finite presentation. -/
theorem ringHom_codomainUlift_essFinitePresentation {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (g : A →+* B) (hg : g.EssFinitePresentation) :
    (((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{u} B).comp g) :
      A →+* ULift.{u} B).EssFinitePresentation := by
  have htarget :
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{u} B).EssFinitePresentation := by
    let ψ : B →+* ULift.{u} B := ULift.ringEquiv.symm.toRingHom
    have hψfp : ψ.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective ULift.ringEquiv.symm.bijective
    letI : Algebra B (ULift.{u} B) := ψ.toAlgebra
    haveI : Algebra.FinitePresentation B (ULift.{u} B) := hψfp
    -- Proof comment: the codomain `ULift` map is a ring equivalence, hence finitely presented and
    -- therefore essentially finitely presented.
    rw [RingHom.EssFinitePresentation]
    exact Algebra.EssFinitePresentation.of_finitePresentation _ _
  -- Proof comment: the lifted-codomain map is the composite of the original map with this
  -- essentially finitely presented equivalence.
  exact hg.comp htarget

/-- Helper for Chap10 Lemma 10 127 13: applying `RingHom.ulift` with a common target
universe on source and codomain preserves essential finite presentation. -/
theorem ringHom_commonUlift_essFinitePresentation {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (g : A →+* B) (hg : g.EssFinitePresentation) :
    (RingHom.ulift.{w, w} g).EssFinitePresentation := by
  have hsource :
      (ULift.ringEquiv.toRingHom : ULift.{w} A →+* A).EssFinitePresentation := by
    let φ : ULift.{w} A →+* A := ULift.ringEquiv.toRingHom
    have hφfp : φ.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective
    letI : Algebra (ULift.{w} A) A := φ.toAlgebra
    haveI : Algebra.FinitePresentation (ULift.{w} A) A := hφfp
    -- Proof comment: the source `ULift` equivalence is finitely presented, hence essentially
    -- finitely presented.
    rw [RingHom.EssFinitePresentation]
    exact Algebra.EssFinitePresentation.of_finitePresentation _ _
  have htarget :
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).EssFinitePresentation := by
    let ψ : B →+* ULift.{w} B := ULift.ringEquiv.symm.toRingHom
    have hψfp : ψ.FinitePresentation :=
      RingHom.FinitePresentation.of_bijective ULift.ringEquiv.symm.bijective
    letI : Algebra B (ULift.{w} B) := ψ.toAlgebra
    haveI : Algebra.FinitePresentation B (ULift.{w} B) := hψfp
    -- Proof comment: the codomain `ULift` equivalence is handled by the same finite-presentation
    -- bridge.
    rw [RingHom.EssFinitePresentation]
    exact Algebra.EssFinitePresentation.of_finitePresentation _ _
  have hcomp :
      (((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).comp
          (g.comp (ULift.ringEquiv.toRingHom : ULift.{w} A →+* A))) :
        ULift.{w} A →+* ULift.{w} B).EssFinitePresentation := by
    -- Proof comment: the common-universe lift is the original map sandwiched between the two
    -- `ULift` ring equivalences.
    exact (RingHom.EssFinitePresentation.comp hsource hg).comp htarget
  have hulift_eq :
      RingHom.ulift.{w, w} g =
        ((ULift.ringEquiv.symm.toRingHom : B →+* ULift.{w} B).comp
          (g.comp (ULift.ringEquiv.toRingHom : ULift.{w} A →+* A))) := by
    -- Proof comment: on lifted elements both homomorphisms apply `g` after forgetting the source
    -- lift and then restore the codomain lift.
    ext x
    rfl
  rw [hulift_eq]
  exact hcomp

/-- Helper for Lemma 10.127.13: lifting every target stage of a directed ring system by `ULift`
does not change its direct limit. -/
noncomputable def directLimit_target_ulift_ringEquiv
    {ι : Type w} [Preorder ι] {T : ι → Type u} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)] :
    Ring.DirectLimit (fun i ↦ ULift.{v} (T i)) (fun i j h ↦ RingHom.ulift (τ i j h)) ≃+*
      Ring.DirectLimit T (fun i j h ↦ τ i j h) := by
  let toOriginal :
      Ring.DirectLimit (fun i ↦ ULift.{v} (T i)) (fun i j h ↦ RingHom.ulift (τ i j h)) →+*
        Ring.DirectLimit T (fun i j h ↦ τ i j h) :=
    Ring.DirectLimit.map (fun i ↦ (ULift.ringEquiv : ULift.{v} (T i) ≃+* T i).toRingHom)
      (fun i j h ↦ by
        -- Proof comment: forgetting the `ULift` on each stage intertwines the lifted transition
        -- with the original transition on the nose.
        ext x
        rfl)
  let toLifted :
      Ring.DirectLimit T (fun i j h ↦ τ i j h) →+*
        Ring.DirectLimit (fun i ↦ ULift.{v} (T i)) (fun i j h ↦ RingHom.ulift (τ i j h)) :=
    Ring.DirectLimit.map
      (fun i ↦ (ULift.ringEquiv : ULift.{v} (T i) ≃+* T i).symm.toRingHom)
      (fun i j h ↦ by
        -- Proof comment: restoring the `ULift` also commutes with the stage transitions.
        ext x
        rfl)
  refine RingEquiv.ofRingHom toOriginal toLifted ?_ ?_
  ·
    -- Proof comment: both composites are determined by their values on original-stage
    -- generators, where `ULift.down` followed by `ULift.up` is the identity.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toLifted, RingHom.comp_apply]
  ·
    -- Proof comment: the same generator computation proves the inverse law on the lifted-stage
    -- presentation, now using `ULift.up` followed by `ULift.down`.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toLifted, RingHom.comp_apply]

/-- Helper for Lemma 10.127.13: the direct-limit equivalence for a target-only `ULift` sends each
lifted stage generator to the corresponding original stage generator. -/
@[simp] theorem directLimit_target_ulift_ringEquiv_of
    {ι : Type w} [Preorder ι] {T : ι → Type u} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)]
    (i : ι) (x : ULift.{v} (T i)) :
    directLimit_target_ulift_ringEquiv (T := T) τ
        (Ring.DirectLimit.of (fun j ↦ ULift.{v} (T j))
          (fun j k h ↦ RingHom.ulift (τ j k h)) i x) =
      Ring.DirectLimit.of T (fun j k h ↦ τ j k h) i x.down := by
  -- Proof comment: the forward map is the direct-limit morphism induced by forgetting `ULift`
  -- stagewise, so on generators it is computed by `Ring.DirectLimit.map_apply_of`.
  rfl

/-- Helper for Chap10 Lemma 10 127 13: forgetting target-stage `ULift`s after a direct-limit map
recovers the original direct-limit map. -/
theorem directLimit_target_ulift_map_comp_toOriginal
    {ι : Type w} [Preorder ι]
    {G : ι → Type u} {T : ι → Type v} [∀ i, CommRing (G i)] [∀ i, CommRing (T i)]
    (ρ : ∀ i j, i ≤ j → G i →+* G j)
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem G (fun i j h ↦ ρ i j h)]
    [DirectedSystem T (fun i j h ↦ τ i j h)]
    (φ : ∀ i, G i →+* T i)
    (φL : ∀ i, G i →+* ULift.{uM} (T i))
    (hφ : ∀ i j (h : i ≤ j), (φ j).comp (ρ i j h) = (τ i j h).comp (φ i))
    (hφL : ∀ i j (h : i ≤ j), (φL j).comp (ρ i j h) =
      (RingHom.ulift (τ i j h)).comp (φL i))
    (hφL_def : ∀ i x, (φL i x).down = φ i x) :
    (directLimit_target_ulift_ringEquiv (T := T) τ).toRingHom.comp
        (Ring.DirectLimit.map φL (fun _ _ h ↦ hφL _ _ h)) =
      Ring.DirectLimit.map φ (fun _ _ h ↦ hφ _ _ h) := by
  -- Proof comment: direct-limit maps are determined on stage generators, so normalize the
  -- `ULift` transport once at hom level instead of repeating the generator calculation downstream.
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  simp only [RingHom.comp_apply]
  rw [Ring.DirectLimit.map_apply_of, Ring.DirectLimit.map_apply_of]
  simpa [hφL_def i x] using
    (directLimit_target_ulift_ringEquiv_of (T := T) (τ := τ) i (φL i x))

/-- Helper for Chap10 Lemma 10 127 13: a target-colimit square for lifted target stages follows
from the corresponding unlifted square. -/
theorem directLimit_target_ulift_colimit_comm_of_unlifted
    {ι : Type w} [Preorder ι]
    {G : ι → Type u} {T : ι → Type v} {U : Type uN}
    [∀ i, CommRing (G i)] [∀ i, CommRing (T i)] [CommRing U]
    (ρ : ∀ i j, i ≤ j → G i →+* G j)
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem G (fun i j h ↦ ρ i j h)]
    [DirectedSystem T (fun i j h ↦ τ i j h)]
    (φ : ∀ i, G i →+* T i)
    (φL : ∀ i, G i →+* ULift.{uM} (T i))
    (hφ : ∀ i j (h : i ≤ j), (φ j).comp (ρ i j h) = (τ i j h).comp (φ i))
    (hφL : ∀ i j (h : i ≤ j), (φL j).comp (ρ i j h) =
      (RingHom.ulift (τ i j h)).comp (φL i))
    (hφL_def : ∀ i x, (φL i x).down = φ i x)
    (e : Ring.DirectLimit T (fun i j h ↦ τ i j h) ≃+* U)
    (e₀ : Ring.DirectLimit T (fun i j h ↦ τ i j h) →+* U)
    (F : Ring.DirectLimit G (fun i j h ↦ ρ i j h) →+* U)
    (he : e.toRingHom = e₀)
    (hbase : e₀.comp (Ring.DirectLimit.map φ (fun _ _ h ↦ hφ _ _ h)) = F) :
    ((directLimit_target_ulift_ringEquiv (T := T) τ).trans e).toRingHom.comp
        (Ring.DirectLimit.map φL (fun _ _ h ↦ hφL _ _ h)) =
      F := by
  have hforget :
      (directLimit_target_ulift_ringEquiv (T := T) τ).toRingHom.comp
          (Ring.DirectLimit.map φL (fun _ _ h ↦ hφL _ _ h)) =
        Ring.DirectLimit.map φ (fun _ _ h ↦ hφ _ _ h) :=
    directLimit_target_ulift_map_comp_toOriginal ρ τ φ φL hφ hφL hφL_def
  -- Proof comment: once the lifted direct-limit map is normalized, composing with the target
  -- colimit equivalence is exactly the known unlifted colimit square.
  calc
    ((directLimit_target_ulift_ringEquiv (T := T) τ).trans e).toRingHom.comp
        (Ring.DirectLimit.map φL (fun _ _ h ↦ hφL _ _ h)) =
      (e.toRingHom.comp (directLimit_target_ulift_ringEquiv (T := T) τ).toRingHom).comp
        (Ring.DirectLimit.map φL (fun _ _ h ↦ hφL _ _ h)) := by
        rfl
    _ = e.toRingHom.comp
        ((directLimit_target_ulift_ringEquiv (T := T) τ).toRingHom.comp
          (Ring.DirectLimit.map φL (fun _ _ h ↦ hφL _ _ h))) := by
        rw [RingHom.comp_assoc]
    _ = e.toRingHom.comp (Ring.DirectLimit.map φ (fun _ _ h ↦ hφ _ _ h)) := by
        rw [hforget]
    _ = e₀.comp (Ring.DirectLimit.map φ (fun _ _ h ↦ hφ _ _ h)) := by
        rw [he]
    _ = F := hbase

/-- Helper for Lemma 10.127.13: finite presentation transfers across a ring equivalence by
restricting scalars along that equivalence. -/
theorem module_finitePresentation_compHom_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {N : Type*} [AddCommGroup N] [Module B N] [Module.FinitePresentation B N] :
    let _ : Algebra A B := e.toRingHom.toAlgebra
    let _ : Module A N := Module.compHom N e.toRingHom
    let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
    Module.FinitePresentation A N := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : Module A N := Module.compHom N e.toRingHom
  let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
  have hB : Module.FinitePresentation A B := by
    -- Proof comment: via the ring equivalence, `B` is just the free rank-one `A`-module.
    exact Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e)
  -- Proof comment: once the scalar ring `B` itself is finitely presented over `A`, transitivity
  -- upgrades finite presentation of `N` over `B` to finite presentation over `A`.
  exact Module.FinitePresentation.trans (R := A) (S := B) (M := N)

/-- Helper for Lemma 10.127.13: composing a prime-localization map with the codomain `ULift`
equivalence preserves the same prime-localization witness. -/
theorem ulift_isLocalizationMap_of_isLocalizationMap
    {T : Type*} {U : Type*} [CommRing T] [CommRing U]
    (p : Ideal T) [p.IsPrime] (γ : T →+* U)
    (hγ : p.primeCompl.IsLocalizationMap γ) :
    p.primeCompl.IsLocalizationMap
      ((ULift.ringEquiv.symm.toRingHom : U →+* ULift U).comp γ) := by
  letI : Algebra T U := γ.toAlgebra
  have hloc : IsLocalization p.primeCompl U :=
    (isLocalization_iff_isLocalizationMap (M := p.primeCompl) (S := U)).mpr hγ
  let γLift : T →+* ULift U :=
    (ULift.ringEquiv.symm.toRingHom : U →+* ULift U).comp γ
  letI : Algebra T (ULift U) := γLift.toAlgebra
  let eAlg : U ≃ₐ[T] ULift U := (ULift.algEquiv (R := T) (A := U)).symm
  letI : IsLocalization p.primeCompl (ULift U) :=
    IsLocalization.isLocalization_of_algEquiv p.primeCompl eAlg
  -- Proof comment: after identifying `ULift U` with `U` as a `T`-algebra, the localization
  -- instance is transported unchanged and can be repackaged as an explicit localization-map
  -- witness.
  simpa [γLift] using
    (isLocalization_iff_isLocalizationMap (M := p.primeCompl) (S := ULift U)).mp
      (show IsLocalization p.primeCompl (ULift U) by infer_instance)

/-- Helper for Lemma 10.127.13: a prime-localization witness on an owner base-change map
transports across a source ring equivalence when the transported map is given in forward form. -/
private theorem exists_prime_localization_witness_of_domain_equiv_map
    {A : DirectedLocalHomApproximation f} {i j : A.Λ} (h : i ≤ j)
    {T : Type*} [CommRing T] (e : A.targetStageBaseChange h ≃+* T)
    (φ : T →+* A.SStage j)
    (hφ : ∀ z : A.targetStageBaseChange h, A.stageBaseChangeMap h z = φ (e z))
    (ht : A.TransitionIsLocalizationAtPrime h) :
    ∃ p : Ideal T, ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap φ := by
  rcases ht with ⟨q, hq, hmapq⟩
  let p : Ideal T := Ideal.comap e.symm.toRingHom q
  letI : q.IsPrime := hq
  have hp : p.IsPrime := by
    -- Proof comment: prime ideals pull back along ring homomorphisms, so the transported prime
    -- on the equivalent source ring stays prime.
    simpa [p] using Ideal.comap_isPrime e.symm.toRingHom q
  letI : Algebra (A.targetStageBaseChange h) (A.SStage j) := (A.stageBaseChangeMap h).toAlgebra
  haveI hlocq : IsLocalization q.primeCompl (A.SStage j) :=
    (isLocalization_iff_isLocalizationMap
      (M := q.primeCompl) (S := A.SStage j)).mpr hmapq
  letI : Algebra T (A.SStage j) := φ.toAlgebra
  have hpmap : p.primeCompl.map e.symm.toMonoidHom = q.primeCompl := by
    -- Proof comment: `p` was defined as the pullback of `q` along `e.symm`, so complements match
    -- after mapping along the same equivalence.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [p, Ideal.mem_comap] using hy
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      simpa [p, Ideal.mem_comap] using hx
  have htransport :
      IsLocalization p.primeCompl (A.SStage j) := by
    -- Proof comment: reinterpret the transported source algebra as `φ` using the forward
    -- compatibility, then move the localization structure across `e.symm`.
    exact IsLocalization.of_ringEquiv_left
      (e := e.symm)
      hpmap
      (fun x ↦ by
        change φ x = A.stageBaseChangeMap h (e.symm x)
        simpa using (hφ (e.symm x)).symm)
  letI : p.IsPrime := hp
  exact ⟨p, hp,
    (isLocalization_iff_isLocalizationMap
      (M := p.primeCompl) (S := A.SStage j)).mp htransport⟩

/-- Helper for Lemma 10.127.13: a tensor-product ring hom is determined by its values on the left
and right tensor generators. -/
private theorem tensor_ringHom_eq_of_generators
    {R A B C D : Type uR} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (γ : C ⊗[R] B →+* D) (α : A ⊗[R] B →+* C ⊗[R] B)
    (δ : A ⊗[R] B →+* D)
    (hleft : ∀ x : A, γ (α (x ⊗ₜ[R] (1 : B))) = δ (x ⊗ₜ[R] (1 : B)))
    (hright : ∀ y : B, γ (α ((1 : A) ⊗ₜ[R] y)) = δ ((1 : A) ⊗ₜ[R] y)) :
    γ.comp α = δ := by
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro x
    -- Proof comment: the left tensor generator is `x ⊗ 1`, so the left-generator hypothesis
    -- already computes both sides.
    simpa [RingHom.comp_apply] using hleft x
  · apply RingHom.ext
    intro y
    -- Proof comment: the right tensor generator is `1 ⊗ y`, and the right-generator hypothesis
    -- gives the needed equality after expanding the composite.
    simpa [RingHom.comp_apply, Algebra.TensorProduct.includeRight_apply] using hright y

/-- Helper for Lemma 10.127.13: if a localization map factors through a localization tower, then
the intermediate map is itself a prime localization. -/
private theorem isLocalizationMap_of_localization_tower_named
    {T₀ T₁ U : Type uR} [CommRing T₀] [CommRing T₁] [CommRing U] [IsLocalRing U]
    (α : T₀ →+* T₁) (g : T₁ →+* U) (β : T₀ →+* U) (hβ : β = g.comp α)
    (M₀ : Submonoid T₀) (qk' : Ideal T₀) (hqk'_prime : qk'.IsPrime)
    (hM₀ : M₀ ≤ qk'.primeCompl)
    (hT₁ : @IsLocalization T₀ _ M₀ T₁ _ α.toAlgebra)
    (hUmap : qk'.primeCompl.IsLocalizationMap β) :
    ∃ q : Ideal T₁, ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap g := by
  letI : Algebra T₀ U := (g.comp α).toAlgebra
  have hU : @IsLocalization.AtPrime T₀ _ U _ (g.comp α).toAlgebra qk' hqk'_prime := by
    -- Proof comment: reinterpret the named localization-map witness as the corresponding
    -- typeclass localization instance on the composite `g ∘ α`.
    exact (isLocalization_iff_isLocalizationMap qk'.primeCompl U).mpr (by
      rwa [hβ] at hUmap)
  exact isLocalizationMap_of_localization_tower α g M₀ qk' hqk'_prime hM₀ hT₁ hU

/-- Helper for Lemma 10.127.13: if the composite through a tensor-localization tower agrees with
the canonical map on tensor generators, then the top map is a prime localization. -/
private theorem tensor_generators_localization_tower_isLocalizationMap
    {R A B C D E : Type uR} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] [CommRing E] [IsLocalRing D]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (e : A ⊗[R] B ≃+* E) (q : Ideal E) [q.IsPrime]
    [Algebra E D] [IsLocalization.AtPrime D q]
    (α : A ⊗[R] B →+* C ⊗[R] B) (γ : C ⊗[R] B →+* D)
    (M₀ : Submonoid (A ⊗[R] B)) (qk' : Ideal (A ⊗[R] B))
    (hqk'_prime : qk'.IsPrime)
    (hqk' : qk' = Ideal.comap e.toRingHom q)
    (hM₀ : M₀ ≤ qk'.primeCompl)
    (hT₁ : @IsLocalization (A ⊗[R] B) _ M₀ (C ⊗[R] B) _ α.toAlgebra)
    (hleft : ∀ x : A,
      γ (α (x ⊗ₜ[R] (1 : B))) = algebraMap E D (e (x ⊗ₜ[R] (1 : B))))
    (hright : ∀ y : B,
      γ (α ((1 : A) ⊗ₜ[R] y)) = algebraMap E D (e ((1 : A) ⊗ₜ[R] y))) :
    ∃ p : Ideal (C ⊗[R] B), ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap γ := by
  have hcomp : γ.comp α = (algebraMap E D).comp e.toRingHom :=
    tensor_ringHom_eq_of_generators γ α ((algebraMap E D).comp e.toRingHom) hleft hright
  have hUmap0 :
      (Ideal.comap e.toRingHom q).primeCompl.IsLocalizationMap (γ.comp α) := by
    -- Proof comment: after identifying the tensor source with the localization source `E`,
    -- the composite `γ ∘ α` is the canonical localization map.
    refine towerLocal_isLocalizationMap_atPrime_of_ringEquiv_source_map e q (γ.comp α) ?_
    exact hcomp
  have hUmap : qk'.primeCompl.IsLocalizationMap (γ.comp α) := by
    cases hqk'
    exact hUmap0
  exact isLocalizationMap_of_localization_tower_named α γ (γ.comp α) rfl
    M₀ qk' hqk'_prime hM₀ hT₁ hUmap

namespace DirectedLocalHomApproximation

/-- Helper for Chap10 Lemma 10 127 13: prime-localization transitions persist after reindexing
the owner by `ULift`. -/
theorem hasPrimeLocalizationTransitions_reindex_ulift
    {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {f : R →+* S}
    {A : DirectedLocalHomApproximation.{u, v, 0} f}
    (hA : A.HasPrimeLocalizationTransitions) :
    (A.reindex_ulift : DirectedLocalHomApproximation.{u, v, w} f).HasPrimeLocalizationTransitions := by
  intro i j hij
  -- Proof comment: the reindexed transition at lifted indices is definitionally the original
  -- transition at their underlying indices.
  simpa [DirectedLocalHomApproximation.reindex_ulift] using hA (i := i.down) (j := j.down) hij

end DirectedLocalHomApproximation

end
