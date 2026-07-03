import stacks_project.Chap10.Lemma_10_127_6
import stacks_project.Chap10.Lemma_10_127_11
import stacks_project.Chap10.Lemma_10_6_4

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
  exact ⟨A₀, hA₀map, hA₀lim, P, inferInstance, inferInstance, g, hg, q, hq.1, inferInstance,
    hq.2, hfg, hqR,
    i₀, P₀, inferInstance, inferInstance, inferInstance, e⟩

/-- Helper for Lemma 10.127.13: locality transfers from a local ring to its `ULift`. -/
local instance ulift_isLocalRing (A : Type*) [CommRing A] [IsLocalRing A] :
    IsLocalRing (ULift A) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    -- Proof comment: descend the equation `a + b = 1` to the underlying local ring and lift the
    -- resulting unit witness back along `ULift.ringEquiv`.
    have hdown : a.down + b.down = 1 := by
      simpa using congrArg ULift.down h
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := a.down) (b := b.down) hdown with
      ha | hb
    · left
      exact ha.map (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)
    · right
      exact hb.map (ULift.ringEquiv.symm.toRingHom : A →+* ULift A)

/-- Helper for Lemma 10.127.13: `RingHom.ulift` preserves the local-hom property. -/
theorem ringHom_ulift_isLocalHom {A : Type*} {B : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (g : A →+* B)
    [IsLocalHom g] :
    IsLocalHom (RingHom.ulift g) := by
  letI : IsLocalHom (ULift.ringEquiv.toRingHom : ULift A →+* A) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.surjective
  letI : IsLocalHom (ULift.ringEquiv.symm.toRingHom : B →+* ULift B) :=
    Function.Surjective.isLocalHom _ ULift.ringEquiv.symm.surjective
  -- Proof comment: the lifted map is the original map sandwiched between the two canonical ring
  -- equivalences for `ULift`.
  simpa [RingHom.ulift] using
    (RingHom.isLocalHom_comp (ULift.ringEquiv.symm.toRingHom)
      (g.comp ULift.ringEquiv.toRingHom))

/-- Helper for Lemma 10.127.13: `RingHom.ulift` preserves essential finite type. -/
theorem ringHom_ulift_essFiniteType {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] (g : A →+* B) (hg : g.EssFiniteType) :
    (RingHom.ulift g).EssFiniteType := by
  have hsource_surj :
      Function.Surjective (ULift.ringEquiv.toRingHom : ULift A →+* A) := by
    simpa using ULift.ringEquiv.surjective
  have hsource :
      (ULift.ringEquiv.toRingHom : ULift A →+* A).EssFiniteType := by
    -- Proof comment: surjective ring maps are finite type, hence essentially of finite type.
    simpa using
      (RingHom.FiniteType.of_surjective
        (ULift.ringEquiv.toRingHom : ULift A →+* A) hsource_surj).essFiniteType
  have htarget_surj :
      Function.Surjective (ULift.ringEquiv.symm.toRingHom : B →+* ULift B) := by
    simpa using ULift.ringEquiv.symm.surjective
  have htarget :
      (ULift.ringEquiv.symm.toRingHom : B →+* ULift B).EssFiniteType := by
    -- Proof comment: the inverse `ULift` equivalence is also surjective, so the same argument
    -- applies on the target side.
    simpa using
      (RingHom.FiniteType.of_surjective
        (ULift.ringEquiv.symm.toRingHom : B →+* ULift B) htarget_surj).essFiniteType
  -- Proof comment: `RingHom.ulift g` is the composite of the two `ULift` equivalences with `g`.
  simpa [RingHom.ulift] using hsource.comp (hg.comp htarget)

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

/-- Helper for Lemma 10.127.13: the mixed-universe ring approximation should be obtained by
reusing the already packaged source-faithful approximation theorem from Lemma `10.127.11` at the
joint universe of `R` and `S`. -/
theorem exists_localEssFinitePresentationApproximation_mixed_universe
    (hf : f.EssFinitePresentation) :
    ∃ A : DirectedLocalHomApproximation.{uR, uS, max uR uS} f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := by
  -- Route correction: the direct adaptation of the Lemma `10.127.11` owner still fails because
  -- `DirectedLocalHomApproximation` fixes the target-stage universe to the universe of `S`,
  -- while the descended local stages from the source-faithful construction naturally live in the
  -- source universe.  The remaining work is to package that descended tail into this owner.
  -- TODO: finish the mixed-universe owner-level wrapper for the descended tail from
  -- `Lemma 10.127.11`, rather than switching to a different ring approximation route.
  sorry

/-- Helper for Lemma 10.127.13: after restricting scalars along the target-colimit equivalence, a
finitely presented `S`-module descends to one target stage of the approximation system. -/
theorem descend_module_to_target_stage
    (A : DirectedLocalHomApproximation f) [Module.FinitePresentation S M] :
    let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
    let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
    ∃ (i₀ : A.Λ) (M₀ : Type uS) (_ : AddCommGroup M₀) (_ : Module (A.SStage i₀) M₀)
      (_ : Module.FinitePresentation (A.SStage i₀) M₀),
      Nonempty (D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) := by
  let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
  let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
  let _ : Module.FinitePresentation D M := by
    -- Proof comment: finite presentation transfers from `S` back to the target direct limit
    -- along the colimit ring equivalence.
    simpa [D] using
      (module_finitePresentation_compHom_of_ringEquiv (e := A.targetColimit) (N := M))
  -- Proof comment: once the target system is viewed as a directed system with colimit ring `D`,
  -- the generic descent theorem from Lemma `10.127.6` applies directly.
  simpa [D] using
    (finitelyPresented_module_descends_to_stage
      (R := A.SStage) (f := fun i j h ↦ A.targetMap i j h) (M := M))

/-- Helper for Lemma 10.127.13: once a stage module has been descended to one target stage of the
ring approximation, the remaining source-faithful step is to restrict to the tail and define each
later stage by scalar extension from that fixed descended module. -/
theorem tail_module_system_from_descended_stage
    (A : DirectedLocalHomApproximation f)
    (hA : DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A)
    (i₀ : A.Λ)
    {M₀ : Type uS} [AddCommGroup M₀] [Module (A.SStage i₀) M₀]
    [Module.FinitePresentation (A.SStage i₀) M₀]
    (eM :
      let D := Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h)
      let _ : Module D M := Module.compHom M A.targetColimit.toRingHom
      D ⊗[A.SStage i₀] M₀ ≃ₗ[D] M) :
    Nonempty (DirectedLocalEssFinitePresentationModuleApproximation f M) := by
  -- Proof comment: the textbook's last step is purely module-theoretic.  One restricts the ring
  -- approximation to the tail above `i₀`, sets the stage module at `j` to
  -- `A.SStage j.1 ⊗[A.SStage i₀] M₀`, transports the descended limit equivalence from the target
  -- direct limit ring to `S`, and then proves the transition/final base-change formulas by the
  -- canonical tensor associativity and right-unitor equivalences.
  -- TODO: package the tail owner, use `TensorProduct.assoc` for transition base change, use
  -- `A.targetColimit` to transport the descended `D`-linear equivalence to an `S`-linear one,
  -- use `tail_targetStageToLimitHom_eq` and `targetStageToLimitHom_comp_targetMap` to normalize
  -- the final tensor base change on the tail, and then assemble the record.
  sorry

-- Proof sketch: first approximate the local map `R → S` by a directed system of local maps whose
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
theorem exists_localEssFinitePresentationModuleApproximation
    [Module.FinitePresentation S M]
    (hf : f.EssFinitePresentation) :
    Nonempty (DirectedLocalEssFinitePresentationModuleApproximation f M) := by
  obtain ⟨A, hA⟩ := exists_localEssFinitePresentationApproximation_mixed_universe (f := f) hf
  obtain ⟨i₀, M₀, _, _, _, ⟨eM⟩⟩ := descend_module_to_target_stage (f := f) (A := A) (M := M)
  -- Proof comment: Lemma `10.127.11` provides the ring approximation, Lemma `10.127.6` descends
  -- the finitely presented module to one target stage, and the only remaining source-faithful
  -- step is the textbook tail construction from that descended stage.
  exact tail_module_system_from_descended_stage (f := f) (M := M) A hA i₀ eM

end
