import StacksProject_2024.Chap10.Lemma_10_127_17.RangeTail

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Chap10 Lemma 10 127 17: every finite-type algebra over `ℤ` has a small carrier in
any target universe. -/
theorem small_of_finiteType_int
    {A : Type u} [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A] :
    Small.{v} A := by
  -- Proof comment: a finite-type `ℤ`-algebra is a quotient of a finite-variable polynomial ring,
  -- and that source is small in any universe.
  rcases (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := ℤ) (S := A)).mp
      (inferInstance : Algebra.FiniteType ℤ A) with ⟨n, f, hf⟩
  exact small_of_surjective hf

/-- Helper for Chap10 Lemma 10 127 17: each raw descended tail stage has a small carrier in the
universe of `S`. -/
theorem raw_tail_stage_small
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) :
    Small.{v} (raw_tail_stage A₀ i₀ P₀ j) := by
  let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  letI hRj : Algebra.FiniteType ℤ (A₀.RStage j.1) :=
    RingHom.finiteType_algebraMap.mp (A₀.source_finiteType j.1)
  letI hRaw : Algebra.FiniteType (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
    RingHom.finiteType_algebraMap.mp (descended_tail_raw_stage_finiteType A₀ i₀ (P₀ := P₀) j)
  have hTower : IsScalarTower ℤ (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by simp
  letI : IsScalarTower ℤ (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) := hTower
  letI : Algebra.FiniteType ℤ (raw_tail_stage A₀ i₀ P₀ j) :=
    @Algebra.FiniteType.trans ℤ (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      hTower hRj hRaw
  -- Proof comment: finite type over `ℤ` now supplies a universe-`v` small model.
  exact small_of_finiteType_int

attribute [local instance] raw_tail_stage_small

/-- Helper for Chap10 Lemma 10 127 17: transport a ring homomorphism through canonical small
models of source and target. -/
noncomputable def shrinkRingHom
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Small.{v} A] [Small.{v} B]
    (φ : A →+* B) :
    Shrink.{v} A →+* Shrink.{v} B :=
  (Shrink.ringEquiv B).symm.toRingHom.comp (φ.comp (Shrink.ringEquiv A).toRingHom)

/-- Helper for Chap10 Lemma 10 127 17: the shrunken homomorphism is the conjugate of the
original homomorphism by the stagewise shrink equivalences. -/
@[simp] theorem shrinkRingHom_apply
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Small.{v} A] [Small.{v} B]
    (φ : A →+* B) (x : Shrink.{v} A) :
    shrinkRingHom φ x = (Shrink.ringEquiv B).symm (φ ((Shrink.ringEquiv A) x)) := by
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the shrunken homomorphism evaluates by applying the
original homomorphism and shrinking the result. -/
@[simp] theorem shrinkRingHom_equivShrink
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Small.{v} A] [Small.{v} B]
    (φ : A →+* B) (x : A) :
    shrinkRingHom φ (equivShrink A x) = equivShrink B (φ x) := by
  -- Proof comment: compare after unshrinking the codomain, where both sides are `φ x`.
  apply (Shrink.ringEquiv B).injective
  simp [shrinkRingHom_apply, Shrink.ringEquiv]

/-- Helper for Chap10 Lemma 10 127 17: the inverse shrink equivalence commutes with a chosen
base algebra structure on the codomain. -/
theorem shrinkCodomainAlgHom_commutes
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A] :
    let _ : Algebra R (Shrink.{v} A) :=
      ((Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)).toAlgebra
    ∀ r : R, (Shrink.ringEquiv A).symm.toRingHom (algebraMap R A r) =
      algebraMap R (Shrink.{v} A) r := by
  intro _inst r
  -- Proof comment: the codomain algebra structure was defined by this exact composite.
  rfl

/-- Helper for Chap10 Lemma 10 127 17: a base algebra maps surjectively to the shrink of its
codomain when the shrink carries the induced base algebra structure. -/
noncomputable def shrinkCodomainAlgHom
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A] :
    let _ : Algebra R (Shrink.{v} A) :=
      ((Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)).toAlgebra
    A →ₐ[R] Shrink.{v} A :=
  let _ : Algebra R (Shrink.{v} A) :=
    ((Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)).toAlgebra
  { toRingHom := (Shrink.ringEquiv A).symm.toRingHom
    commutes' := shrinkCodomainAlgHom_commutes }

/-- Helper for Chap10 Lemma 10 127 17: the codomain-shrink algebra hom sends an element to its
canonical small representative. -/
@[simp] theorem shrinkCodomainAlgHom_apply
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A]
    (x : A) :
    (let _ : Algebra R (Shrink.{v} A) :=
      ((Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)).toAlgebra
    shrinkCodomainAlgHom (R := R) (A := A) x) = equivShrink A x := by
  -- Proof comment: both sides are the inverse of the same shrink equivalence.
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the codomain-shrink algebra hom is surjective. -/
theorem shrinkCodomainAlgHom_surjective
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A] :
    Function.Surjective
      (let _ : Algebra R (Shrink.{v} A) :=
        ((Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)).toAlgebra
      shrinkCodomainAlgHom (R := R) (A := A)) := by
  intro x
  -- Proof comment: every shrunken point is the shrink of its unshrunk representative.
  refine ⟨(Shrink.ringEquiv A) x, ?_⟩
  change (Shrink.ringEquiv A).symm ((Shrink.ringEquiv A) x) = x
  exact (Shrink.ringEquiv A).left_inv x

/-- Helper for Chap10 Lemma 10 127 17: the inverse shrink equivalence respects any active base
algebra structure whose algebra map is the induced shrink composite. -/
theorem shrinkCodomainAlgHomOfAlgebra_commutes
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A]
    [Algebra R (Shrink.{v} A)]
    (h : algebraMap R (Shrink.{v} A) =
      (Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)) :
    ∀ r : R, (Shrink.ringEquiv A).symm.toRingHom (algebraMap R A r) =
      algebraMap R (Shrink.{v} A) r := by
  intro r
  -- Proof comment: rewrite the active algebra map to the stated inverse-shrink composite.
  rw [h]
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the inverse shrink equivalence as an algebra hom for an
already-active induced codomain algebra structure. -/
noncomputable def shrinkCodomainAlgHomOfAlgebra
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A]
    [Algebra R (Shrink.{v} A)]
    (h : algebraMap R (Shrink.{v} A) =
      (Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)) :
    A →ₐ[R] Shrink.{v} A :=
  { toRingHom := (Shrink.ringEquiv A).symm.toRingHom
    commutes' := shrinkCodomainAlgHomOfAlgebra_commutes h }

/-- Helper for Chap10 Lemma 10 127 17: the active-instance codomain-shrink algebra hom evaluates
as the canonical small representative. -/
@[simp] theorem shrinkCodomainAlgHomOfAlgebra_apply
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A]
    [Algebra R (Shrink.{v} A)]
    (h : algebraMap R (Shrink.{v} A) =
      (Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A))
    (x : A) :
    shrinkCodomainAlgHomOfAlgebra h x = equivShrink A x := by
  -- Proof comment: the algebra proof changes only the scalar-compatibility field, not the
  -- underlying inverse shrink equivalence.
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the active-instance codomain-shrink algebra hom is
surjective. -/
theorem shrinkCodomainAlgHomOfAlgebra_surjective
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Small.{v} A]
    [Algebra R (Shrink.{v} A)]
    (h : algebraMap R (Shrink.{v} A) =
      (Shrink.ringEquiv A).symm.toRingHom.comp (algebraMap R A)) :
    Function.Surjective (shrinkCodomainAlgHomOfAlgebra h) := by
  intro x
  -- Proof comment: use the unshrunk representative supplied by the shrink equivalence.
  refine ⟨(Shrink.ringEquiv A) x, ?_⟩
  change (Shrink.ringEquiv A).symm ((Shrink.ringEquiv A) x) = x
  exact (Shrink.ringEquiv A).left_inv x

/-- Helper for Chap10 Lemma 10 127 17: shrinking preserves identity homomorphisms. -/
theorem shrinkRingHom_id
    {A : Type u} [CommRing A] [Small.{v} A] :
    shrinkRingHom (RingHom.id A) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  -- Proof comment: the conjugate of the identity map is the identity on the small model.
  simp [shrinkRingHom_apply]

/-- Helper for Chap10 Lemma 10 127 17: shrinking commutes with composition of ring
homomorphisms. -/
theorem shrinkRingHom_comp
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Small.{v} A] [Small.{v} B] [Small.{v} C]
    (φ : A →+* B) (ψ : B →+* C) :
    shrinkRingHom (ψ.comp φ) =
      (shrinkRingHom ψ).comp (shrinkRingHom φ) := by
  apply RingHom.ext
  intro x
  -- Proof comment: both sides unshrink to `ψ (φ x)`.
  simp [shrinkRingHom_apply]

/-- Helper for Chap10 Lemma 10 127 17: replacing every stage of a directed ring system by its
small model does not change the direct limit. -/
noncomputable def directLimit_shrink_ringEquiv
    {ι : Type w} [Preorder ι] {T : ι → Type u} [∀ i, CommRing (T i)]
    [∀ i, Small.{v} (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)] :
    Ring.DirectLimit (fun i ↦ Shrink.{v} (T i)) (fun i j h ↦ shrinkRingHom (τ i j h)) ≃+*
      Ring.DirectLimit T (fun i j h ↦ τ i j h) := by
  let toOriginal :
      Ring.DirectLimit (fun i ↦ Shrink.{v} (T i)) (fun i j h ↦ shrinkRingHom (τ i j h)) →+*
        Ring.DirectLimit T (fun i j h ↦ τ i j h) :=
    Ring.DirectLimit.map
      (fun i ↦ (Shrink.ringEquiv (T i)).toRingHom)
      (fun i j h ↦ by
        -- Proof comment: the stage equivalence intertwines a shrunken transition with the
        -- original transition by construction.
        ext x
        simp [shrinkRingHom_apply])
  let toShrunk :
      Ring.DirectLimit T (fun i j h ↦ τ i j h) →+*
        Ring.DirectLimit (fun i ↦ Shrink.{v} (T i)) (fun i j h ↦ shrinkRingHom (τ i j h)) :=
    Ring.DirectLimit.map
      (fun i ↦ (Shrink.ringEquiv (T i)).symm.toRingHom)
      (fun i j h ↦ by
        -- Proof comment: the inverse stage equivalence has the same compatibility in the
        -- shrunken spelling.
        ext x
        simp [shrinkRingHom_apply])
  refine RingEquiv.ofRingHom toOriginal toShrunk ?_ ?_
  ·
    -- Proof comment: direct-limit homomorphisms are equal once they agree on every shrunken
    -- stage generator.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toShrunk, RingHom.comp_apply]
  ·
    -- Proof comment: the reverse composite is checked on original stage generators.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    obtain ⟨a, rfl⟩ := (equivShrink (T i)).surjective x
    simp [toOriginal, toShrunk, RingHom.comp_apply]

/-- Helper for Chap10 Lemma 10 127 17: the direct-limit equivalence for shrunken stages sends a
shrunken generator to the corresponding original generator. -/
@[simp] theorem directLimit_shrink_ringEquiv_of
    {ι : Type w} [Preorder ι] {T : ι → Type u} [∀ i, CommRing (T i)]
    [∀ i, Small.{v} (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)]
    (i : ι) (x : Shrink.{v} (T i)) :
    directLimit_shrink_ringEquiv (T := T) τ
        (Ring.DirectLimit.of (fun j ↦ Shrink.{v} (T j))
          (fun j k h ↦ shrinkRingHom (τ j k h)) i x) =
      Ring.DirectLimit.of T (fun j k h ↦ τ j k h) i ((Shrink.ringEquiv (T i)) x) := by
  -- Proof comment: the forward map is induced by the stagewise ring equivalences.
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the raw tail transitions remain a directed system after
shrinking the raw target stages. -/
instance shrinkRawTailDirectedSystem
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [∀ j : Set.Ici i₀, Small.{v} (raw_tail_stage A₀ i₀ P₀ j)] :
    DirectedSystem (fun j : Set.Ici i₀ ↦ Shrink.{v} (raw_tail_stage A₀ i₀ P₀ j))
      (fun j k h ↦ shrinkRingHom (raw_tail_map A₀ i₀ P₀ j k h)) where
  map_self := by
    intro j x
    obtain ⟨a, rfl⟩ := (equivShrink.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).surjective x
    -- Proof comment: after choosing an original-stage representative, the claim is the raw
    -- directed-system identity transported through `equivShrink`.
    rw [shrinkRingHom_equivShrink]
    congr 1
    simpa using
      (DirectedSystem.map_self (f := fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) a)
  map_map := by
    intro k j i hij hjk x
    obtain ⟨a, rfl⟩ := (equivShrink.{v, u} (raw_tail_stage A₀ i₀ P₀ i)).surjective x
    -- Proof comment: composition of shrunken transitions reduces to the raw directed-system
    -- composition law on the chosen representative.
    simp only [shrinkRingHom_equivShrink]
    congr 1
    simpa using
      (DirectedSystem.map_map (f := fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) hij hjk a)

/-- Helper for Chap10 Lemma 10 127 17: the raw stage maps commute with the shrunken raw tail
transitions. -/
theorem shrinkRawTailStageMap_comm
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [∀ j : Set.Ici i₀, Small.{v} (raw_tail_stage A₀ i₀ P₀ j)]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    ((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom.comp
        (raw_tail_stageMap A₀ i₀ P₀ k)).comp (A₀.RMap j.1 k.1 hjk) =
      (shrinkRingHom (raw_tail_map A₀ i₀ P₀ j k hjk)).comp
        ((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm.toRingHom.comp
          (raw_tail_stageMap A₀ i₀ P₀ j)) := by
  apply RingHom.ext
  intro x
  -- Proof comment: apply the raw commutativity relation and then shrink both sides.
  simp only [RingHom.comp_apply, shrinkRingHom_apply]
  apply (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).injective
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
  exact congrArg (fun g : A₀.RStage j.1 →+* raw_tail_stage A₀ i₀ P₀ k ↦ g x)
    (raw_tail_stageMap_comm A₀ i₀ P₀ hjk)

/-- Helper for Chap10 Lemma 10 127 17: shrinking the codomain of a finite-type stage map
preserves finite type. -/
theorem shrinkRawTailTarget_finiteType
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [∀ j : Set.Ici i₀, Small.{v} (raw_tail_stage A₀ i₀ P₀ j)]
    (j : Set.Ici i₀) :
    ((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm.toRingHom.comp
      (raw_tail_stageMap A₀ i₀ P₀ j)).FiniteType := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  -- Proof comment: compose the raw finite-type map with the surjective inverse shrink
  -- equivalence onto the small model.
  exact RingHom.FiniteType.comp
    (RingHom.FiniteType.of_surjective _
      (show Function.Surjective
          ((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm.toRingHom) from
        (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm.surjective))
    (descended_tail_raw_stage_finiteType A₀ i₀ (P₀ := P₀) j)

/-- Helper for Chap10 Lemma 10 127 17: the shrunken raw-tail approximation has target direct
limit `S` through the raw tensor colimit and the chosen algebra equivalence. -/
noncomputable def shrinkRawTailApproximation
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S) :
    DirectedFiniteTypeHomApproximation.{u, v, u} (algebraMap R S) :=
  letI : ∀ j : Set.Ici i₀, Small.{v} (raw_tail_stage A₀ i₀ P₀ j) :=
    fun j ↦ raw_tail_stage_small A₀ i₀ P₀ j
  { Λ := Set.Ici i₀
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := raw_tail_isDirectedOrder A₀ i₀
    RStage := fun j ↦ A₀.RStage j.1
    SStage := fun j ↦ Shrink.{v} (raw_tail_stage A₀ i₀ P₀ j)
    instCommRingRStage := fun j ↦ inferInstance
    instCommRingSStage := fun j ↦ inferInstance
    RMap := fun j k h ↦ A₀.RMap j.1 k.1 h
    SMap := fun j k h ↦ shrinkRingHom (raw_tail_map A₀ i₀ P₀ j k h)
    instDirectedSystemRStage := inferInstance
    instDirectedSystemSStage := shrinkRawTailDirectedSystem A₀ i₀ P₀
    stageMap := fun j ↦ (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm.toRingHom.comp
      (raw_tail_stageMap A₀ i₀ P₀ j)
    comm := fun {j k} h ↦ shrinkRawTailStageMap_comm A₀ i₀ P₀ h
    source_finiteType := fun j ↦ A₀.source_finiteType j.1
    target_finiteType := fun j ↦ shrinkRawTailTarget_finiteType A₀ i₀ P₀ j
    colimitSource := tail_directLimitIso A₀.RStage (fun a b h ↦ A₀.RMap a b h) i₀
      A₀.colimitSource
    colimitTarget := by
      letI : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
      exact (directLimit_shrink_ringEquiv
        (T := raw_tail_stage A₀ i₀ P₀)
        (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h)).trans
        ((raw_tail_directLimit_equiv A₀ i₀ P₀).trans e.toRingEquiv)
    colimit_comm := by
      -- Proof comment: compare the colimit square on tail source generators, where the shrunken
      -- target colimit first unshrinks and then uses the raw-tail colimit computation.
      apply Ring.DirectLimit.hom_ext
      intro j
      ext x
      letI : Algebra (A₀.RStage i₀) R := raw_tail_limitAlgebra A₀ i₀
      -- Proof comment: after the two colimit equivalences, the target side is exactly the
      -- raw stage map followed by `e`; the range-tail compatibility lemma identifies this with
      -- the ambient algebra map from `R`.
      simpa [directLimit_shrink_ringEquiv_of, raw_tail_directLimit_equiv_of,
        raw_tail_stageMap, range_tail_sigma, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
        using (range_tail_sigma_stageMap_eq A₀ i₀ P₀ e j x) }

/-- Helper for Chap10 Lemma 10 127 17: the owner algebra map on a shrunken raw-tail stage is
the inverse-shrink composite of the raw stage map. -/
theorem shrinkRawTailStage_algebraMap
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) :
    let A := shrinkRawTailApproximation A₀ i₀ P₀ e
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    algebraMap (A.RStage j) (A.SStage j) =
      (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm.toRingHom.comp
        (raw_tail_stageMap A₀ i₀ P₀ j) := by
  -- Proof comment: the shrunken approximation stores exactly this composite as its stage map.
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the inverse shrink map is compatible with the owner
algebra structure on a shrunken raw-tail stage. -/
theorem shrinkRawTailStageAlgEquiv_commutes
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) :
    let A := shrinkRawTailApproximation A₀ i₀ P₀ e
    let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    ∀ r : A.RStage j,
      (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm
          (algebraMap (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) r) =
        algebraMap (A.RStage j) (A.SStage j) r := by
  intro A _rawAlg _ownerAlg r
  -- Proof comment: rewrite the owner algebra map to the inverse-shrink composite.
  rw [shrinkRawTailStage_algebraMap A₀ i₀ P₀ e j]
  rfl

/-- Helper for Chap10 Lemma 10 127 17: the raw stage is algebra-equivalent to the owner
shrunken stage over the same source stage. -/
noncomputable def shrinkRawTailStageAlgEquiv
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) :
    let A := shrinkRawTailApproximation A₀ i₀ P₀ e
    let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    raw_tail_stage A₀ i₀ P₀ j ≃ₐ[A.RStage j] A.SStage j :=
  let A := shrinkRawTailApproximation A₀ i₀ P₀ e
  let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  AlgEquiv.ofRingEquiv
    (f := (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ j)).symm)
    (shrinkRawTailStageAlgEquiv_commutes A₀ i₀ P₀ e j)

/-- Helper for Chap10 Lemma 10 127 17: the owner raw-to-shrink stage equivalence evaluates by
choosing the canonical small representative. -/
@[simp] theorem shrinkRawTailStageAlgEquiv_apply
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    (j : Set.Ici i₀) (x : raw_tail_stage A₀ i₀ P₀ j) :
    let A := shrinkRawTailApproximation A₀ i₀ P₀ e
    let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    shrinkRawTailStageAlgEquiv A₀ i₀ P₀ e j x =
      equivShrink.{v, u} (raw_tail_stage A₀ i₀ P₀ j) x := by
  -- Proof comment: the algebra equivalence has inverse-shrink as its underlying ring equivalence.
  rfl

/-- Helper for Chap10 Lemma 10 127 17: tensor the owner raw-to-shrink stage equivalence with the
identity on the later source stage. -/
noncomputable def shrinkRawTailSourceTensorAlgEquiv
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let A := shrinkRawTailApproximation A₀ i₀ P₀ e
    let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    letI : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
    let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
    letI : Module (A.RStage j) (A.RStage k) := Algebra.toModule
    letI : Algebra (A.RStage j) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
    letI : Module (A.RStage j) (A₀.RStage k.1) := Algebra.toModule
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    letI : Module (A.RStage j) (A.SStage j) := Algebra.toModule
    (raw_tail_stage A₀ i₀ P₀ j ⊗[A.RStage j] A.RStage k) ≃ₐ[A.RStage j]
      A.stageBaseChange hjk :=
  let A := shrinkRawTailApproximation A₀ i₀ P₀ e
  let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  letI : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
  letI : Module (A.RStage j) (A.RStage k) := Algebra.toModule
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  letI : Module (A.RStage j) (A.SStage j) := Algebra.toModule
  Algebra.TensorProduct.congr
    (shrinkRawTailStageAlgEquiv A₀ i₀ P₀ e j)
    (AlgEquiv.refl (R := A.RStage j) (A₁ := A.RStage k))

/-- Helper for Chap10 Lemma 10 127 17: after the source tensor equivalence, the shrunken owner
base-change map is raw tensor cancellation followed by target shrinking. -/
theorem shrinkRawTailStageBaseChange_comp_sourceTensorAlgEquiv
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let A := shrinkRawTailApproximation A₀ i₀ P₀ e
    let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
      (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
    letI : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
    let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
    letI : Module (A.RStage j) (A.RStage k) := Algebra.toModule
    letI : Algebra (A.RStage j) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
    letI : Module (A.RStage j) (A₀.RStage k.1) := Algebra.toModule
    let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
    letI : Module (A.RStage j) (A.SStage j) := Algebra.toModule
    let sourceEquiv := shrinkRawTailSourceTensorAlgEquiv A₀ i₀ P₀ e hjk
    let rawCancel_jk :=
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
        j.2 k.2 hjk
        (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom
    (A.stageBaseChangeMap hjk).comp sourceEquiv.toRingHom =
      (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom.comp rawCancel_jk := by
  let A := shrinkRawTailApproximation A₀ i₀ P₀ e
  let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  letI : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
  letI : Module (A.RStage j) (A.RStage k) := Algebra.toModule
  letI : Algebra (A.RStage j) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
  letI : Module (A.RStage j) (A₀.RStage k.1) := Algebra.toModule
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  letI : Module (A.RStage j) (A.SStage j) := Algebra.toModule
  let sourceEquiv := shrinkRawTailSourceTensorAlgEquiv A₀ i₀ P₀ e hjk
  let rawCancel_jk :=
    (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
      j.2 k.2 hjk
      (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom
  -- Proof comment: tensor products are generated by pure tensors, so it is enough to compare
  -- the two composites on `x ⊗ y`.
  apply ringHom_eq_of_tmul
  intro x y
  have hraw :
      rawCancel_jk (x ⊗ₜ[A.RStage j] y) =
        raw_tail_map A₀ i₀ P₀ j k hjk x * raw_tail_stageMap A₀ i₀ P₀ k y := by
    -- Proof comment: normalize the raw side by the existing tensor-cancellation computation.
    simpa [A, rawCancel_jk] using
      (rawTensorCancel_tmul_right
        (RStage := A₀.RStage) (map := fun a b h ↦ A₀.RMap a b h)
        (P₀ := P₀) (hij := j.2) (hik := k.2) (hjk := hjk)
        (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)
        x y)
  calc
    ((A.stageBaseChangeMap hjk).comp sourceEquiv.toRingHom) (x ⊗ₜ[A.RStage j] y) =
        A.SMap j k hjk (equivShrink.{v, u} (raw_tail_stage A₀ i₀ P₀ j) x) *
          A.stageMap k y := by
      -- Proof comment: first apply the source equivalence on a pure tensor, then use the owner
      -- pure-tensor formula for the base-change map.
      rw [RingHom.comp_apply]
      simpa [sourceEquiv, shrinkRawTailSourceTensorAlgEquiv, Algebra.TensorProduct.map_tmul] using
        (DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul A hjk
          (equivShrink.{v, u} (raw_tail_stage A₀ i₀ P₀ j) x) y)
    _ = (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom
            (raw_tail_map A₀ i₀ P₀ j k hjk x) *
          (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom
            (raw_tail_stageMap A₀ i₀ P₀ k y) := by
      -- Proof comment: unfold the shrunken transition and stage maps only at this point.
      have hleft :
          A.SMap j k hjk (equivShrink.{v, u} (raw_tail_stage A₀ i₀ P₀ j) x) =
            (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom
              (raw_tail_map A₀ i₀ P₀ j k hjk x) := by
        simpa [A] using (shrinkRingHom_equivShrink (raw_tail_map A₀ i₀ P₀ j k hjk) x)
      have hright :
          A.stageMap k y =
            (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom
              (raw_tail_stageMap A₀ i₀ P₀ k y) := by
        rfl
      rw [hleft, hright]
      rfl
    _ = (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom
          (raw_tail_map A₀ i₀ P₀ j k hjk x * raw_tail_stageMap A₀ i₀ P₀ k y) := by
      -- Proof comment: shrinking is a ring homomorphism, so it preserves multiplication.
      exact (map_mul (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom
        (raw_tail_map A₀ i₀ P₀ j k hjk x) (raw_tail_stageMap A₀ i₀ P₀ k y)).symm
    _ = ((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom.comp rawCancel_jk)
          (x ⊗ₜ[A.RStage j] y) := by
      -- Proof comment: replace the normalized raw value by `rawCancel_jk` again.
      rw [RingHom.comp_apply, hraw]

/-- Helper for Chap10 Lemma 10 127 17: the shrunken raw-tail base-change map is bijective because
it should compare to the raw tensor-cancellation isomorphism after a source tensor comparison. -/
theorem shrinkRawTailStageBaseChangeMap_bijective
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    [Algebra R S] (e : raw_tail_limitTensor A₀ i₀ P₀ ≃ₐ[R] S)
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    Function.Bijective ((shrinkRawTailApproximation A₀ i₀ P₀ e).stageBaseChangeMap hjk) := by
  let A := shrinkRawTailApproximation A₀ i₀ P₀ e
  let _ : Algebra (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  letI : Module (A.RStage j) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  let _ : Algebra (A.RStage j) (A.RStage k) := (A.RMap j k hjk).toAlgebra
  letI : Module (A.RStage j) (A.RStage k) := Algebra.toModule
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  letI : Module (A.RStage j) (A.SStage j) := Algebra.toModule
  let sourceEquiv := shrinkRawTailSourceTensorAlgEquiv A₀ i₀ P₀ e hjk
  let rawCancel_jk :=
    (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
      j.2 k.2 hjk
      (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).toRingHom
  -- Route correction: the earlier loose tensor-map route drifted to the canonical `Shrink`
  -- algebra instance. The source comparison is now an owner-spelled tensor algebra equivalence,
  -- so bijectivity transfers through a literal conjugation square.
  refine bijective_of_surjective_of_bijective_comp
    sourceEquiv.toRingHom (A.stageBaseChangeMap hjk) ?_ ?_
  · exact sourceEquiv.toRingEquiv.surjective
  · have hcomp :
        (A.stageBaseChangeMap hjk).comp sourceEquiv.toRingHom =
          (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom.comp rawCancel_jk := by
      simpa [A, sourceEquiv, rawCancel_jk] using
        (shrinkRawTailStageBaseChange_comp_sourceTensorAlgEquiv A₀ i₀ P₀ e hjk)
    have hcomp_fun :
        (⇑(A.stageBaseChangeMap hjk) ∘ ⇑sourceEquiv.toRingHom) =
          ⇑((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom.comp
            rawCancel_jk) := by
      funext z
      exact congrArg (fun φ : _ →+* _ ↦ φ z) hcomp
    have hrawShrink :
        Function.Bijective
          (((Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.toRingHom.comp
            rawCancel_jk) : _ → _) :=
      Function.Bijective.comp
        (g := ⇑(Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm)
        (f := ⇑rawCancel_jk)
        (Shrink.ringEquiv.{v, u} (raw_tail_stage A₀ i₀ P₀ k)).symm.bijective
        (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
          j.2 k.2 hjk
          (RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk)).bijective
    rw [hcomp_fun]
    exact hrawShrink
