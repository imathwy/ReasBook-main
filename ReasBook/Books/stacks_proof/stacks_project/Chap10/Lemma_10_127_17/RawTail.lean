import StacksProject_2024.Chap10.Lemma_10_127_17.DescendedStageModel

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.127.17: the descended raw tensor stage over a tail index is finite type
over the corresponding source stage. -/
theorem descended_tail_raw_stage_finiteType
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    {P₀ : Type u} [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀] (j : Set.Ici i₀)
    [Algebra (A₀.RStage i₀) (A₀.RStage j.1)] :
    (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)).FiniteType := by
  let baseChangedStage : Type u := A₀.RStage j.1 ⊗[A₀.RStage i₀] P₀
  let baseChangedComm :
      baseChangedStage ≃+* (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) :=
    (Algebra.TensorProduct.comm
      (R := A₀.RStage i₀) (A := A₀.RStage j.1) (B := P₀)).toRingEquiv
  have hbaseChanged_finiteType :
      (algebraMap (A₀.RStage j.1) baseChangedStage).FiniteType := by
    let _ : Algebra.FinitePresentation (A₀.RStage j.1) baseChangedStage := by
      -- Proof comment: base change preserves the descended finite-presentation model.
      exact Algebra.FinitePresentation.baseChange
        (R := A₀.RStage i₀) (A := P₀) (B := A₀.RStage j.1)
    -- Proof comment: finite presentation over the later source stage implies finite type.
    exact RingHom.finiteType_algebraMap.mpr Algebra.FiniteType.of_finitePresentation
  have hbaseChanged_comp :
      baseChangedComm.toRingHom.comp (algebraMap (A₀.RStage j.1) baseChangedStage) =
        algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) := by
    ext x
    rfl
  -- Proof comment: transport the literal base-change finite-type map across tensor commutation.
  rw [← hbaseChanged_comp]
  exact RingHom.FiniteType.comp
    (RingHom.FiniteType.of_surjective _ baseChangedComm.surjective)
    hbaseChanged_finiteType

/-- Helper for Lemma 10.127.17: replacing a raw tensor stage by its image inside `S` preserves the
finite-type stage map from the corresponding source stage. -/
theorem descended_tail_range_stage_finiteType
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    {P₀ : Type u} [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) [Algebra (A₀.RStage i₀) (A₀.RStage j.1)]
    (σj : (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) →+* S) :
    (((σj).comp (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))).codRestrict
      σj.range (fun x ↦ by
        show ((σj.comp (algebraMap (A₀.RStage j.1)
          (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))) x) ∈ σj.range
        exact ⟨(algebraMap (A₀.RStage j.1)
          (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)) x, rfl⟩)).FiniteType := by
  have hstageMapTail_comp :
      (((σj).comp
          (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))).codRestrict
        σj.range (fun x ↦ by
          show ((σj.comp (algebraMap (A₀.RStage j.1)
            (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1))) x) ∈ σj.range
          exact ⟨(algebraMap (A₀.RStage j.1)
            (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)) x, rfl⟩)) =
        ((σj).rangeRestrict).comp
          (algebraMap (A₀.RStage j.1) (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1)) := by
    ext x
    rfl
  -- Proof comment: pass from the raw tensor stage to its image via the surjective range map.
  rw [hstageMapTail_comp]
  exact RingHom.FiniteType.comp_surjective
    (descended_tail_raw_stage_finiteType A₀ i₀ (P₀ := P₀) j)
    σj.rangeRestrict_surjective

/-- Helper for Lemma 10.127.17: lift the codomain of a ring homomorphism into the target universe
using `ULift`, while keeping the source ring unchanged. -/
noncomputable def codomainULiftRingHom
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    A →+* ULift.{v, u} B :=
  (ULift.ringEquiv : ULift.{v, u} B ≃+* B).symm.toRingHom.comp φ

/-- Helper for Lemma 10.127.17: the codomain-only lift evaluates by applying the original ring
homomorphism and then packaging the result with `ULift.up`. -/
@[simp] theorem codomainULiftRingHom_apply
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (x : A) :
    codomainULiftRingHom φ x = ULift.up (φ x) := by
  rfl

/-- Helper for Lemma 10.127.17: lift both source and target of a ring homomorphism into the target
universe. This is the raw-stage transition map on the universe-lifted tail. -/
noncomputable def uliftRingHom
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    ULift.{v, u} A →+* ULift.{v, u} B :=
  (codomainULiftRingHom φ).comp
    (ULift.ringEquiv : ULift.{v, u} A ≃+* A).toRingHom

/-- Helper for Lemma 10.127.17: the fully lifted ring homomorphism acts on lifted elements by the
obvious formula `up (φ x)`. -/
@[simp] theorem uliftRingHom_up
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (x : A) :
    uliftRingHom φ (ULift.up x) = ULift.up (φ x) := by
  rfl

/-- Helper for Lemma 10.127.17: lifting preserves identity transitions on the raw tail. -/
theorem uliftRingHom_id
    {A : Type u} [CommRing A] :
    uliftRingHom (RingHom.id A) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  cases x
  rfl

/-- Helper for Lemma 10.127.17: lifting commutes with composition of raw tail transition maps. -/
theorem uliftRingHom_comp
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) :
    uliftRingHom (ψ.comp φ) =
      (uliftRingHom ψ).comp (uliftRingHom φ) := by
  apply RingHom.ext
  intro x
  cases x
  rfl

/-- Helper for Lemma 10.127.17: lifting each stage of a directed ring system by `ULift` does not
change its direct limit. -/
noncomputable def directLimit_ulift_ringEquiv
    {ι : Type w} [Preorder ι] {T : ι → Type u} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)] :
    Ring.DirectLimit (fun i ↦ ULift.{v, u} (T i)) (fun i j h ↦ uliftRingHom (τ i j h)) ≃+*
      Ring.DirectLimit T (fun i j h ↦ τ i j h) := by
  let toOriginal :
      Ring.DirectLimit (fun i ↦ ULift.{v, u} (T i)) (fun i j h ↦ uliftRingHom (τ i j h)) →+*
        Ring.DirectLimit T (fun i j h ↦ τ i j h) :=
    Ring.DirectLimit.map
      (fun i ↦ (ULift.ringEquiv : ULift.{v, u} (T i) ≃+* T i).toRingHom)
      (fun i j h ↦ by
        -- Proof comment: forgetting `ULift` intertwines the lifted transition with the original
        -- stage transition on generators.
        ext x
        rfl)
  let toLifted :
      Ring.DirectLimit T (fun i j h ↦ τ i j h) →+*
        Ring.DirectLimit (fun i ↦ ULift.{v, u} (T i)) (fun i j h ↦ uliftRingHom (τ i j h)) :=
    Ring.DirectLimit.map
      (fun i ↦ (ULift.ringEquiv : ULift.{v, u} (T i) ≃+* T i).symm.toRingHom)
      (fun i j h ↦ by
        -- Proof comment: restoring `ULift` is stagewise inverse to forgetting it.
        ext x
        rfl)
  refine RingEquiv.ofRingHom toOriginal toLifted ?_ ?_
  ·
    -- Proof comment: both composites are determined by their values on lifted stage generators.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toLifted, RingHom.comp_apply]
  ·
    -- Proof comment: the same generator computation proves the inverse law in the other
    -- direction.
    apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    simp [toOriginal, toLifted, RingHom.comp_apply]

/-- Helper for Lemma 10.127.17: the direct-limit equivalence for the `ULift`ed raw tail sends a
lifted stage generator to the corresponding raw stage generator. -/
@[simp] theorem directLimit_ulift_ringEquiv_of
    {ι : Type w} [Preorder ι] {T : ι → Type u} [∀ i, CommRing (T i)]
    (τ : ∀ i j, i ≤ j → T i →+* T j)
    [DirectedSystem T (fun i j h ↦ τ i j h)]
    (i : ι) (x : ULift.{v, u} (T i)) :
    directLimit_ulift_ringEquiv (T := T) τ
        (Ring.DirectLimit.of (fun j ↦ ULift.{v, u} (T j))
          (fun j k h ↦ uliftRingHom (τ j k h)) i x) =
      Ring.DirectLimit.of T (fun j k h ↦ τ j k h) i x.down := by
  -- Proof comment: the forward map is induced stagewise by forgetting `ULift`, so the formula on
  -- generators is exactly `Ring.DirectLimit.map_apply_of`.
  rfl

/-- Helper for Lemma 10.127.17: the inverse `ULift` algebra equivalence sends an element to its
canonical lifted representative. -/
@[simp] theorem ulift_algEquiv_symm_apply
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] (x : A) :
    (ULift.algEquiv (R := R) (A := A)).symm x = ULift.up x := by
  rfl

/-- Helper for Lemma 10.127.17: the source-to-target direct-limit map induced by stage maps on a
tail sends a source-stage generator to the corresponding target-stage generator. -/
theorem tail_source_to_target_direct_limit_stage_of
    {ι : Type w} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {RStage : ι → Type u} [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    {B : Type*} [CommRing B]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* B)
    (i₀ : ι)
    (T : Set.Ici i₀ → Type u) [∀ j, CommRing (T j)]
    (targetMap : ∀ j k : Set.Ici i₀, j ≤ k → T j →+* T k)
    [DirectedSystem T (fun j k h ↦ targetMap j k h)]
    (stageMapTail : (j : Set.Ici i₀) → RStage j.1 →+* T j)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (map j.1 k.1 hjk) =
        (targetMap j k hjk).comp (stageMapTail j))
    (i : Set.Ici i₀) (x : RStage i.1) :
    ((Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)).comp
        (tail_directLimitIso RStage map i₀ colimitIso).symm.toRingHom)
      (colimitIso (Ring.DirectLimit.of RStage (fun a b h ↦ map a b h) i.1 x)) =
      Ring.DirectLimit.of T (fun j k h ↦ targetMap j k h) i (stageMapTail i x) := by
  -- Proof comment: the tail direct-limit equivalence sends the ambient source generator back to
  -- the same tail-stage generator, after which `Ring.DirectLimit.map` acts stagewise.
  change (Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h))
      ((tail_directLimitIso RStage map i₀ colimitIso).symm
        (colimitIso (Ring.DirectLimit.of RStage (fun a b h ↦ map a b h) i.1 x))) =
    Ring.DirectLimit.of T (fun j k h ↦ targetMap j k h) i (stageMapTail i x)
  rw [tail_directLimitIso_symm_toLimitHom, Ring.DirectLimit.map_apply_of]

/-- Helper for Lemma 10.127.17: at the minimal tail stage, the source-to-target direct-limit map
sends the ambient source generator back to the corresponding minimal-stage target generator. -/
theorem tail_source_to_target_direct_limit_minimal_stage_of
    {ι : Type w} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {RStage : ι → Type u} [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    {B : Type*} [CommRing B]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* B)
    (i₀ : ι)
    (T : Set.Ici i₀ → Type u) [∀ j, CommRing (T j)]
    (targetMap : ∀ j k : Set.Ici i₀, j ≤ k → T j →+* T k)
    [DirectedSystem T (fun j k h ↦ targetMap j k h)]
    (stageMapTail : (j : Set.Ici i₀) → RStage j.1 →+* T j)
    (hcommTail : ∀ {j k : Set.Ici i₀} (hjk : j ≤ k),
      (stageMapTail k).comp (map j.1 k.1 hjk) =
        (targetMap j k hjk).comp (stageMapTail j))
    (x : RStage i₀) :
    ((Ring.DirectLimit.map stageMapTail (fun _ _ h ↦ hcommTail h)).comp
        (tail_directLimitIso RStage map i₀ colimitIso).symm.toRingHom)
      (colimitIso (Ring.DirectLimit.of RStage (fun a b h ↦ map a b h) i₀ x)) =
      Ring.DirectLimit.of T (fun j k h ↦ targetMap j k h) ⟨i₀, le_rfl⟩
        (stageMapTail ⟨i₀, le_rfl⟩ x) := by
  -- Proof comment: this is the previous stage-generator formula specialized to the initial tail
  -- index `⟨i₀, le_rfl⟩`.
  simpa using
    (tail_source_to_target_direct_limit_stage_of
      (map := map) (colimitIso := colimitIso) (i₀ := i₀) (T := T)
      (targetMap := targetMap) (stageMapTail := stageMapTail)
      (hcommTail := fun {j} {k} hjk ↦ hcommTail hjk) ⟨i₀, le_rfl⟩ x)

/-- Helper for Lemma 10.127.17: the raw descended tail stage over a tail index. -/
abbrev raw_tail_stage
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) : Type u :=
  let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1

/-- Helper for Lemma 10.127.17: the raw tensor transition map on descended tail stages. -/
noncomputable abbrev raw_tail_map
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    raw_tail_stage A₀ i₀ P₀ j →+* raw_tail_stage A₀ i₀ P₀ k :=
  let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  let _ : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
  (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
    { toRingHom := A₀.RMap j.1 k.1 hjk
      commutes' := fun x ↦
        by
          simpa [RingHom.algebraMap_toAlgebra] using
            (DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk x) }).toRingHom

/-- Helper for Lemma 10.127.17: the raw tensor transitions form a directed system. -/
instance raw_tail_directedSystem
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    DirectedSystem (raw_tail_stage A₀ i₀ P₀)
      (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) where
  map_self := by
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    -- Proof comment: both transition maps out of a tensor product are determined by pure tensors.
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [raw_tail_map]
    · intro x y
      simp [raw_tail_map, Algebra.TensorProduct.map_tmul]
      simpa using congrArg (fun t : A₀.RStage j.1 ↦ x ⊗ₜ[A₀.RStage i₀] t)
        (DirectedSystem.map_self (f := fun a b h ↦ A₀.RMap a b h) y)
    · intro x y hx hy
      simp [hx, hy]
  map_map := by
    intro i j k hij hjk
    letI : Algebra (A₀.RStage i₀) (A₀.RStage i.1) := (A₀.RMap i₀ i.1 i.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
    -- Proof comment: tensoring the identity on the descended algebra preserves composition of the
    -- right-factor source transitions.
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [raw_tail_map]
    · intro x y
      simp [raw_tail_map, Algebra.TensorProduct.map_tmul]
      simpa using congrArg (fun t : A₀.RStage i.1 ↦ x ⊗ₜ[A₀.RStage i₀] t)
        (DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) hij hjk y)
    · intro x y hx hy
      simp [hx, hy]

/-- Helper for Lemma 10.127.17: the tail above a fixed source stage is directed. -/
instance raw_tail_isDirectedOrder
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ) :
    IsDirectedOrder (Set.Ici i₀) := by
  refine ⟨?_⟩
  intro j k
  obtain ⟨l, hjl, hkl⟩ := A₀.instDirectedOrder.directed j.1 k.1
  refine ⟨⟨l, le_trans j.2 hjl⟩, hjl, hkl⟩

/-- Helper for Lemma 10.127.17: the canonical raw stage map sends a source-stage element into the
right tensor factor. -/
noncomputable abbrev raw_tail_stageMap
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) :
    A₀.RStage j.1 →+* raw_tail_stage A₀ i₀ P₀ j :=
  algebraMap (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j)

/-- Helper for Lemma 10.127.17: the raw stage maps commute with the raw tensor transitions. -/
theorem raw_tail_stageMap_comm
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    (raw_tail_stageMap A₀ i₀ P₀ k).comp (A₀.RMap j.1 k.1 hjk) =
      (raw_tail_map A₀ i₀ P₀ j k hjk).comp (raw_tail_stageMap A₀ i₀ P₀ j) := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
  apply RingHom.ext
  intro x
  -- Proof comment: both sides send `x` to the same pure tensor `1 ⊗ map x`.
  change (1 : P₀) ⊗ₜ[A₀.RStage i₀] ((A₀.RMap j.1 k.1 hjk) x) =
    (Algebra.TensorProduct.map (AlgHom.id P₀ P₀)
      { toRingHom := A₀.RMap j.1 k.1 hjk
        commutes' := fun t ↦
          by
            simpa [RingHom.algebraMap_toAlgebra] using
              (DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk t) })
      ((1 : P₀) ⊗ₜ[A₀.RStage i₀] x)
  simp [Algebra.TensorProduct.map_tmul]

/-- Helper for Lemma 10.127.17: the raw tail induces the canonical source-to-raw direct-limit map. -/
noncomputable abbrev raw_tail_source_to_direct_limit
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    R →+* Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
      (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) :=
  ((Ring.DirectLimit.map (raw_tail_stageMap A₀ i₀ P₀)
      (fun _ _ h ↦ raw_tail_stageMap_comm A₀ i₀ P₀ h)).comp
    (tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h) i₀ A₀.colimitSource).symm.toRingHom)

/-- Helper for Lemma 10.127.17: the source-to-raw direct-limit map sends a source-stage generator
to the corresponding raw-stage generator. -/
theorem raw_tail_source_to_direct_limit_stage_of
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) (x : A₀.RStage j.1) :
    raw_tail_source_to_direct_limit A₀ i₀ P₀
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.1 x) =
      Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
        (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
        (raw_tail_stageMap A₀ i₀ P₀ j x) := by
  -- Proof comment: this is exactly the generic tail-generator formula specialized to the raw tail.
  simpa [raw_tail_source_to_direct_limit] using
    (tail_source_to_target_direct_limit_stage_of
      (map := fun i j h ↦ A₀.RMap i j h)
      (colimitIso := A₀.colimitSource) (i₀ := i₀)
      (T := raw_tail_stage A₀ i₀ P₀)
      (targetMap := fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h)
      (stageMapTail := raw_tail_stageMap A₀ i₀ P₀)
      (hcommTail := fun {a} {b} h ↦ raw_tail_stageMap_comm A₀ i₀ P₀ h) j x)

/-- Helper for Lemma 10.127.17: the raw tail packaged as a finite-type approximation of the
source-to-raw direct-limit map. -/
noncomputable def raw_tail_approximation
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀] :
    DirectedFiniteTypeHomApproximation.{u, u, u} (raw_tail_source_to_direct_limit A₀ i₀ P₀) :=
  { Λ := Set.Ici i₀
    instPreorder := inferInstance
    instNonempty := inferInstance
    instDirectedOrder := raw_tail_isDirectedOrder A₀ i₀
    RStage := fun j ↦ A₀.RStage j.1
    SStage := raw_tail_stage A₀ i₀ P₀
    instCommRingRStage := fun j ↦ inferInstance
    instCommRingSStage := fun j ↦ inferInstance
    RMap := fun j k h ↦ A₀.RMap j.1 k.1 h
    SMap := fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h
    instDirectedSystemRStage := inferInstance
    instDirectedSystemSStage := raw_tail_directedSystem A₀ i₀ P₀
    stageMap := raw_tail_stageMap A₀ i₀ P₀
    comm := fun {j k} h ↦ raw_tail_stageMap_comm A₀ i₀ P₀ h
    source_finiteType := fun j ↦ A₀.source_finiteType j.1
    target_finiteType := fun j ↦ by
      letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
      exact descended_tail_raw_stage_finiteType A₀ i₀ (P₀ := P₀) j
    colimitSource := tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h) i₀ A₀.colimitSource
    colimitTarget := RingEquiv.refl _
    colimit_comm := by
      -- Proof comment: by construction, the approximating ring map is precisely the induced map
      -- from the source tail colimit to the raw target direct limit.
      apply RingHom.ext
      intro z
      simp [raw_tail_source_to_direct_limit, RingHom.comp_assoc] }

/-- Helper for Lemma 10.127.17: the raw owner base-change map is the canonical tensor-cancellation
isomorphism on the descended raw tail. -/
theorem raw_tail_stageBaseChange_eq_rawTensorCancel
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (j k : Set.Ici i₀) (hjk : j ≤ k) :
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
    letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
    let hcomp : (A₀.RMap j.1 k.1 hjk).comp (A₀.RMap i₀ j.1 j.2) = A₀.RMap i₀ k.1 k.2 :=
      RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk
    (raw_tail_approximation A₀ i₀ P₀).stageBaseChangeMap hjk =
      (rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
        j.2 k.2 hjk hcomp).toRingHom := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage j.1) (A₀.RStage k.1) := (A₀.RMap j.1 k.1 hjk).toAlgebra
  let hcomp : (A₀.RMap j.1 k.1 hjk).comp (A₀.RMap i₀ j.1 j.2) = A₀.RMap i₀ k.1 k.2 :=
    RingHom.ext <| DirectedSystem.map_map (f := fun a b h ↦ A₀.RMap a b h) j.2 hjk
  letI : Algebra ((raw_tail_approximation A₀ i₀ P₀).RStage j)
      ((raw_tail_approximation A₀ i₀ P₀).SStage j) :=
    ((raw_tail_approximation A₀ i₀ P₀).stageMap j).toAlgebra
  letI : Module ((raw_tail_approximation A₀ i₀ P₀).RStage j)
      ((raw_tail_approximation A₀ i₀ P₀).SStage j) := Algebra.toModule
  letI : Algebra ((raw_tail_approximation A₀ i₀ P₀).RStage j)
      (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  letI : Module ((raw_tail_approximation A₀ i₀ P₀).RStage j)
      (P₀ ⊗[A₀.RStage i₀] A₀.RStage j.1) := Algebra.toModule
  letI : Algebra (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) :=
    (raw_tail_stageMap A₀ i₀ P₀ j).toAlgebra
  letI : Module (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) := Algebra.toModule
  letI : Algebra ((raw_tail_approximation A₀ i₀ P₀).RStage j)
      ((raw_tail_approximation A₀ i₀ P₀).RStage k) :=
    ((raw_tail_approximation A₀ i₀ P₀).RMap j k hjk).toAlgebra
  letI : Module ((raw_tail_approximation A₀ i₀ P₀).RStage j)
      ((raw_tail_approximation A₀ i₀ P₀).RStage k) := Algebra.toModule
  letI : Algebra ((raw_tail_approximation A₀ i₀ P₀).RStage j) (A₀.RStage k.1) :=
    ((raw_tail_approximation A₀ i₀ P₀).RMap j k hjk).toAlgebra
  letI : Module ((raw_tail_approximation A₀ i₀ P₀).RStage j) (A₀.RStage k.1) := Algebra.toModule
  -- Proof comment: both maps are ring homomorphisms out of the same tensor product, so it
  -- suffices to compare them on pure tensors and use the owner pure-tensor formula.
  apply ringHom_eq_of_tmul
  intro x y
  calc
    (raw_tail_approximation A₀ i₀ P₀).stageBaseChangeMap hjk
        (x ⊗ₜ[(raw_tail_approximation A₀ i₀ P₀).RStage j] y) =
        raw_tail_map A₀ i₀ P₀ j k hjk x * raw_tail_stageMap A₀ i₀ P₀ k y := by
      exact DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul
        (raw_tail_approximation A₀ i₀ P₀) hjk x y
    _ = rawTensorCancel A₀.RStage (fun a b h ↦ A₀.RMap a b h) P₀
          j.2 k.2 hjk hcomp (x ⊗ₜ[(raw_tail_approximation A₀ i₀ P₀).RStage j] y) := by
      symm
      exact rawTensorCancel_tmul_right
        (RStage := A₀.RStage) (map := fun a b h ↦ A₀.RMap a b h)
        (P₀ := P₀) (hij := j.2) (hik := k.2) (hjk := hjk) hcomp x y

/-- Helper for Lemma 10.127.17: the descended algebra `P₀` maps to the raw tail direct limit by
entering at the minimal tail stage. -/
noncomputable def raw_tail_left_to_direct_limit
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    P₀ →+* Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
      (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) :=
  tail_targetDirectLimit_of_minimal_stage (i₀ := i₀) (Sj := raw_tail_stage A₀ i₀ P₀)
    (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h)
    (algebraMap P₀ (raw_tail_stage A₀ i₀ P₀ ⟨i₀, le_rfl⟩))

/-- Helper for Lemma 10.127.17: a raw tail stage maps to `P₀ ⊗[Rᵢ₀] R` by keeping the descended
left factor and sending the stage element to the ambient source limit. -/
noncomputable def raw_tail_stageToTensor
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] (j : Set.Ici i₀) :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    raw_tail_stage A₀ i₀ P₀ j →+* (P₀ ⊗[A₀.RStage i₀] R) := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
  let rightMap : A₀.RStage j.1 →ₐ[A₀.RStage i₀] R :=
    { toRingHom := Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
        A₀.colimitSource j.1
      commutes' := fun r ↦ by
        simpa [RingHom.comp_apply, RingHom.algebraMap_toAlgebra] using RingHom.congr_fun
          (Ring.DirectLimit.toLimitHom_comp_map A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.2) r }
  exact (Algebra.TensorProduct.map (AlgHom.id (A₀.RStage i₀) P₀) rightMap).toRingHom

/-- Helper for Lemma 10.127.17: the stagewise maps from the raw tail to `P₀ ⊗[Rᵢ₀] R` are
compatible with the raw tail transitions. -/
theorem raw_tail_stageToTensor_compatible
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    raw_tail_stageToTensor A₀ i₀ P₀ j =
      (raw_tail_stageToTensor A₀ i₀ P₀ k).comp (raw_tail_map A₀ i₀ P₀ j k hjk) := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) (A₀.RStage k.1) := (A₀.RMap i₀ k.1 k.2).toAlgebra
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
  -- Proof comment: both stage maps are ring homomorphisms out of the same tensor product, so it
  -- suffices to compare their values on pure tensors.
  apply ringHom_eq_of_tmul
  intro p r
  simp only [raw_tail_stageToTensor, raw_tail_map, RingHom.comp_apply]
  exact congrArg (fun z : R ↦ p ⊗ₜ[A₀.RStage i₀] z)
    (RingHom.congr_fun
      (Ring.DirectLimit.toLimitHom_comp_map A₀.RStage (fun a b h ↦ A₀.RMap a b h)
        A₀.colimitSource hjk) r |>.symm)

/-- Helper for Lemma 10.127.17: the raw tail direct limit maps to `P₀ ⊗[Rᵢ₀] R` by the stagewise
tensor maps. -/
noncomputable def raw_tail_directLimit_to_tensor
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
      (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) →+* (P₀ ⊗[A₀.RStage i₀] R) :=
by
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
  exact Ring.DirectLimit.lift (raw_tail_stage A₀ i₀ P₀)
    (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) (P₀ ⊗[A₀.RStage i₀] R)
    (raw_tail_stageToTensor A₀ i₀ P₀)
    (fun j k hjk x ↦ by
      exact (congrArg
        (fun g : raw_tail_stage A₀ i₀ P₀ j →+* (P₀ ⊗[A₀.RStage i₀] R) ↦ g x)
        (raw_tail_stageToTensor_compatible A₀ i₀ P₀ hjk)).symm)

/-- Helper for Lemma 10.127.17: the raw direct-limit comparison evaluates on a stage generator by
the corresponding stagewise tensor map. -/
@[simp] theorem raw_tail_directLimit_to_tensor_of
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] (j : Set.Ici i₀)
    (x : raw_tail_stage A₀ i₀ P₀ j) :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    raw_tail_directLimit_to_tensor A₀ i₀ P₀
        (Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j x) =
      raw_tail_stageToTensor A₀ i₀ P₀ j x := by
  -- Proof comment: this is the defining computation rule for the direct-limit lift.
  simp [raw_tail_directLimit_to_tensor]

/-- Helper for Lemma 10.127.17: after mapping `P₀` into the raw tail direct limit from the minimal
stage, the raw direct-limit comparison recovers the canonical left tensor inclusion into
`P₀ ⊗[Rᵢ₀] R`. -/
theorem raw_tail_directLimit_to_tensor_comp_left
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    (raw_tail_directLimit_to_tensor A₀ i₀ P₀).comp (raw_tail_left_to_direct_limit A₀ i₀ P₀) =
      algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R) := by
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
  -- Proof comment: the minimal-stage lift is characterized by the universal property of the tail
  -- direct limit, and at the minimal stage the stagewise tensor map is the usual left inclusion.
  let j0 : Set.Ici i₀ := ⟨i₀, le_rfl⟩
  have hlift :=
    (lift_comp_tail_targetDirectLimit_of_minimal_stage (i₀ := i₀)
      (Sj := raw_tail_stage A₀ i₀ P₀) (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h)
      (algebraMap P₀ (raw_tail_stage A₀ i₀ P₀ j0))
      (raw_tail_stageToTensor A₀ i₀ P₀)
      (fun j k hjk ↦ raw_tail_stageToTensor_compatible A₀ i₀ P₀ hjk))
  calc
    (raw_tail_directLimit_to_tensor A₀ i₀ P₀).comp (raw_tail_left_to_direct_limit A₀ i₀ P₀) =
        (raw_tail_stageToTensor A₀ i₀ P₀ j0).comp
          (algebraMap P₀ (raw_tail_stage A₀ i₀ P₀ j0)) := by
      simpa [j0, raw_tail_directLimit_to_tensor, raw_tail_left_to_direct_limit] using hlift
    _ = algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R) := by
      ext p
      simp [j0, raw_tail_stageToTensor, Algebra.TensorProduct.map_tmul]

/-- Helper for Lemma 10.127.17: the minimal-stage inclusion of `P₀` into the raw tail direct
limit can be rewritten at any later tail stage as the class of `x ⊗ 1`. -/
theorem raw_tail_left_to_direct_limit_of
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) (x : P₀) :
    let _ : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    raw_tail_left_to_direct_limit A₀ i₀ P₀ x =
      Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
        (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
        (x ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j.1)) := by
  let j0 : Set.Ici i₀ := ⟨i₀, le_rfl⟩
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  -- Proof comment: move the minimal-stage generator forward along the raw transition to stage `j`
  -- and then evaluate that transition on the pure tensor `x ⊗ 1`.
  calc
    raw_tail_left_to_direct_limit A₀ i₀ P₀ x =
        Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j0
          (algebraMap P₀ (raw_tail_stage A₀ i₀ P₀ j0) x) := by
      rfl
    _ =
        Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
          (raw_tail_map A₀ i₀ P₀ j0 j j.2
            (algebraMap P₀ (raw_tail_stage A₀ i₀ P₀ j0) x)) := by
      symm
      simpa [j0] using
        (Ring.DirectLimit.of_f
          (G := raw_tail_stage A₀ i₀ P₀)
          (f := fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j.2
          (algebraMap P₀ (raw_tail_stage A₀ i₀ P₀ j0) x))
    _ =
        Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
          (x ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j.1)) := by
      simp [j0, raw_tail_map, Algebra.TensorProduct.map_tmul]

/-- Helper for Lemma 10.127.17: the source-factor map into the raw tail direct limit becomes the
canonical right tensor inclusion after applying the raw direct-limit comparison. -/
theorem raw_tail_directLimit_to_tensor_comp_source
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    (raw_tail_directLimit_to_tensor A₀ i₀ P₀).comp (raw_tail_source_to_direct_limit A₀ i₀ P₀) =
      algebraMap R (P₀ ⊗[A₀.RStage i₀] R) := by
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
  let tailIso :=
    tail_directLimitIso A₀.RStage (fun i j h ↦ A₀.RMap i j h) i₀ A₀.colimitSource
  -- Proof comment: represent each source element by a tail-stage generator and compare both maps
  -- on that generator using the stage formulas, avoiding the minimal-stage self-algebra transport.
  have hcomp :
      ((raw_tail_directLimit_to_tensor A₀ i₀ P₀).comp
          (raw_tail_source_to_direct_limit A₀ i₀ P₀)).comp tailIso.toRingHom =
        (algebraMap R (P₀ ⊗[A₀.RStage i₀] R)).comp tailIso.toRingHom := by
    apply Ring.DirectLimit.hom_ext
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have htail :
        tailIso.toRingHom
          (Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A₀.RStage j.1)
            (fun a b h ↦ A₀.RMap a.1 b.1 h) j x) =
          Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1 x := by
      simpa [tailIso, tail_directLimitIso, tail_directLimit_to_full_of,
        Ring.DirectLimit.toLimitHom]
    have hsymm :
        tailIso.symm.toRingHom
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) x) =
          Ring.DirectLimit.of (fun j : Set.Ici i₀ ↦ A₀.RStage j.1)
            (fun a b h ↦ A₀.RMap a.1 b.1 h) j x := by
      simpa [tailIso, Ring.DirectLimit.toLimitHom] using
        (tail_directLimitIso_symm_toLimitHom
          (G := A₀.RStage) (f := fun i j h ↦ A₀.RMap i j h)
          (i₀ := i₀) (colimitIso := A₀.colimitSource) j x)
    rw [htail]
    simp only [RingHom.comp_apply, raw_tail_source_to_direct_limit]
    rw [hsymm, Ring.DirectLimit.map_apply_of,
      raw_tail_directLimit_to_tensor_of]
    -- Proof comment: both composites now evaluate to the same pure tensor `1 ⊗ colimit(x)`.
    rw [htail]
    rw [show algebraMap (A₀.RStage j.1) (raw_tail_stage A₀ i₀ P₀ j) x =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀] x by rfl]
    rw [show algebraMap R (P₀ ⊗[A₀.RStage i₀] R)
        ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource j.1) x) =
        (1 : P₀) ⊗ₜ[A₀.RStage i₀]
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) x) by rfl]
    simp [raw_tail_stageToTensor, Algebra.TensorProduct.map_tmul]
  apply RingHom.ext
  intro r
  obtain ⟨z, rfl⟩ := tailIso.surjective r
  exact congrArg (fun h : Ring.DirectLimit (fun j : Set.Ici i₀ ↦ A₀.RStage j.1)
      (fun a b h ↦ A₀.RMap a.1 b.1 h) →+* (P₀ ⊗[A₀.RStage i₀] R) ↦ h z) hcomp

/-- Helper for Lemma 10.127.17: the minimal-stage `P₀`-map into the raw direct limit is
compatible with the source-stage map on the shared `Rᵢ₀`-base. -/
theorem raw_tail_left_source_base_compatible
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    (r : A₀.RStage i₀) :
    raw_tail_left_to_direct_limit A₀ i₀ P₀ ((algebraMap (A₀.RStage i₀) P₀) r) =
      raw_tail_source_to_direct_limit A₀ i₀ P₀
        ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource i₀) r) := by
  let j0 : Set.Ici i₀ := ⟨i₀, le_rfl⟩
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j0.1) := (A₀.RMap i₀ j0.1 j0.2).toAlgebra
  -- Proof comment: compare both maps after representing them at the same raw tail stage and then
  -- rewrite the shared base element from the left tensor factor to the right tensor factor.
  calc
    raw_tail_left_to_direct_limit A₀ i₀ P₀ ((algebraMap (A₀.RStage i₀) P₀) r) =
        Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j0
          (((algebraMap (A₀.RStage i₀) P₀) r) ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j0.1)) := by
      simpa [j0] using
        raw_tail_left_to_direct_limit_of A₀ i₀ P₀ j0 ((algebraMap (A₀.RStage i₀) P₀) r)
    _ =
        Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j0
          ((1 : P₀) ⊗ₜ[A₀.RStage i₀] r) := by
      congr 1
      exact tensor_minimalStage_base_comm
        (R₀ := A₀.RStage i₀) (P₀ := P₀)
        (Sj := raw_tail_stage A₀ i₀ P₀ j0) (C := raw_tail_stage A₀ i₀ P₀ j0)
        (targetOf := (RingHom.id (raw_tail_stage A₀ i₀ P₀ j0) :
          raw_tail_stage A₀ i₀ P₀ j0 →+* raw_tail_stage A₀ i₀ P₀ j0))
        (hself := fun s ↦ by
          change (A₀.RMap i₀ i₀ le_rfl) s = s
          simpa using DirectedSystem.map_self (f := fun a b h ↦ A₀.RMap a b h) s)
        r
    _ =
        Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j0
          (raw_tail_stageMap A₀ i₀ P₀ j0 r) := by
      rfl
    _ =
        raw_tail_source_to_direct_limit A₀ i₀ P₀
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource i₀) r) := by
      symm
      simpa [j0, raw_tail_stageMap, RingHom.comp_apply] using
        raw_tail_source_to_direct_limit_stage_of A₀ i₀ P₀ j0 r

/-- Helper for Lemma 10.127.17: the raw tensor tail has direct limit `P₀ ⊗[Rᵢ₀] R`. This is the
explicit raw colimit bridge needed before packaging the target-universe `ULift` approximation. -/
noncomputable def raw_tail_directLimit_equiv
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
      (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) ≃+* (P₀ ⊗[A₀.RStage i₀] R) := by
  letI : Algebra (A₀.RStage i₀) R :=
    (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
  let toDirectLimitBase :
      A₀.RStage i₀ →+* Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
        (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) :=
    (raw_tail_source_to_direct_limit A₀ i₀ P₀).comp
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀)
  letI : Algebra (A₀.RStage i₀)
      (Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀) (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h)) :=
    toDirectLimitBase.toAlgebra
  let leftAlg :
      P₀ →ₐ[A₀.RStage i₀]
        Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
          (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) :=
    algHomOfCompBase
      (target := RingHom.id _)
      (stage := toDirectLimitBase)
      (pmap := raw_tail_left_to_direct_limit A₀ i₀ P₀)
      (fun r ↦ raw_tail_left_source_base_compatible A₀ i₀ P₀ r)
  let rightAlg :
      R →ₐ[A₀.RStage i₀]
        Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
          (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) :=
    { toRingHom := raw_tail_source_to_direct_limit A₀ i₀ P₀
      commutes' := fun r ↦ rfl }
  let inverse :
      (P₀ ⊗[A₀.RStage i₀] R) →+*
        Ring.DirectLimit (raw_tail_stage A₀ i₀ P₀)
          (fun j k h ↦ raw_tail_map A₀ i₀ P₀ j k h) :=
    (Algebra.TensorProduct.productMap leftAlg rightAlg).toRingHom
  -- Proof comment: the forward map is the raw tensor-tail colimit map, and the inverse is the
  -- tensor product of the left minimal-stage map with the source direct-limit map.
  refine RingEquiv.ofRingHom (raw_tail_directLimit_to_tensor A₀ i₀ P₀) inverse ?_ ?_
  ·
    -- Proof comment: compare the tensor-product composite on pure tensors using the two factor
    -- computations proved above.
    apply ringHom_eq_of_tmul
    intro p r
    simp only [RingHom.comp_apply]
    rw [show inverse (p ⊗ₜ[A₀.RStage i₀] r) =
        leftAlg p * rightAlg r by
          simp [inverse, Algebra.TensorProduct.productMap_apply_tmul]]
    rw [map_mul]
    have hleft :
        (raw_tail_directLimit_to_tensor A₀ i₀ P₀)
            (raw_tail_left_to_direct_limit A₀ i₀ P₀ p) =
          (algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R)) p := by
      simpa [RingHom.comp_apply] using
        congrArg (fun h : P₀ →+* (P₀ ⊗[A₀.RStage i₀] R) ↦ h p)
          (raw_tail_directLimit_to_tensor_comp_left A₀ i₀ P₀)
    have hright :
        (raw_tail_directLimit_to_tensor A₀ i₀ P₀)
            (raw_tail_source_to_direct_limit A₀ i₀ P₀ r) =
          (algebraMap R (P₀ ⊗[A₀.RStage i₀] R)) r := by
      simpa [RingHom.comp_apply] using
        congrArg (fun h : R →+* (P₀ ⊗[A₀.RStage i₀] R) ↦ h r)
          (raw_tail_directLimit_to_tensor_comp_source A₀ i₀ P₀)
    change (raw_tail_directLimit_to_tensor A₀ i₀ P₀)
        (raw_tail_left_to_direct_limit A₀ i₀ P₀ p) *
      (raw_tail_directLimit_to_tensor A₀ i₀ P₀)
        (raw_tail_source_to_direct_limit A₀ i₀ P₀ r) =
      (RingHom.id (P₀ ⊗[A₀.RStage i₀] R)) (p ⊗ₜ[A₀.RStage i₀] r)
    rw [hleft, hright]
    rw [show algebraMap P₀ (P₀ ⊗[A₀.RStage i₀] R) p = p ⊗ₜ[A₀.RStage i₀] (1 : R) by rfl]
    rw [show algebraMap R (P₀ ⊗[A₀.RStage i₀] R) r = (1 : P₀) ⊗ₜ[A₀.RStage i₀] r by rfl]
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    simp
  ·
    -- Proof comment: the reverse composite is checked on each raw stage generator and then on
    -- pure tensors inside that stage.
    apply Ring.DirectLimit.hom_ext
    intro j
    letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
    apply ringHom_eq_of_tmul
    intro x y
    simp only [RingHom.comp_apply, raw_tail_directLimit_to_tensor_of]
    rw [show raw_tail_stageToTensor A₀ i₀ P₀ j (x ⊗ₜ[A₀.RStage i₀] y) =
        x ⊗ₜ[A₀.RStage i₀]
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) y) by
          simp [raw_tail_stageToTensor, Algebra.TensorProduct.map_tmul]]
    rw [show inverse
        (x ⊗ₜ[A₀.RStage i₀]
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) y)) =
        leftAlg x *
          rightAlg
            ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
              A₀.colimitSource j.1) y) by
          simp [inverse, Algebra.TensorProduct.productMap_apply_tmul]]
    change raw_tail_left_to_direct_limit A₀ i₀ P₀ x *
        raw_tail_source_to_direct_limit A₀ i₀ P₀
          ((Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
            A₀.colimitSource j.1) y) =
      Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
        (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
        (x ⊗ₜ[A₀.RStage i₀] y)
    rw [raw_tail_left_to_direct_limit_of A₀ i₀ P₀ j x,
      raw_tail_source_to_direct_limit_stage_of A₀ i₀ P₀ j y]
    rw [← map_mul]
    change Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
        (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
        (((x ⊗ₜ[A₀.RStage i₀] (1 : A₀.RStage j.1)) *
          ((1 : P₀) ⊗ₜ[A₀.RStage i₀] y))) =
      Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
        (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j
        (x ⊗ₜ[A₀.RStage i₀] y)
    congr 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Helper for Lemma 10.127.17: the raw direct-limit equivalence sends a raw stage generator to
the same element viewed inside `P₀ ⊗[Rᵢ₀] R` by tensoring the stage element with the source
colimit map. -/
@[simp] theorem raw_tail_directLimit_equiv_of
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] (j : Set.Ici i₀)
    (x : raw_tail_stage A₀ i₀ P₀ j) :
    let _ : Algebra (A₀.RStage i₀) R :=
      (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h) A₀.colimitSource i₀).toAlgebra
    raw_tail_directLimit_equiv A₀ i₀ P₀
        (Ring.DirectLimit.of (raw_tail_stage A₀ i₀ P₀)
          (fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) j x) =
      raw_tail_stageToTensor A₀ i₀ P₀ j x := by
  -- Proof comment: the ring equivalence is defined from `raw_tail_directLimit_to_tensor`, so its
  -- value on a stage generator is exactly the defining lift computation rule.
  simp [raw_tail_directLimit_equiv, raw_tail_directLimit_to_tensor_of]

/-- Helper for Lemma 10.127.17: lifting the raw tail transition maps by `ULift` preserves the
directed-system identities. -/
instance ulifted_raw_tail_directedSystem
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀] :
    DirectedSystem (fun j : Set.Ici i₀ ↦ ULift.{v, u} (raw_tail_stage A₀ i₀ P₀ j))
      (fun j k h ↦ uliftRingHom (raw_tail_map A₀ i₀ P₀ j k h)) where
  map_self := by
    intro j x
    cases x with
    | up x =>
    simp only [uliftRingHom_up]
    congr 1
    simpa using
      (DirectedSystem.map_self (f := fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) x)
  map_map := by
    intro i j k hij hjk x
    cases x with
    | up x =>
    simp only [uliftRingHom_up]
    congr 1
    simpa using
      (DirectedSystem.map_map (f := fun a b h ↦ raw_tail_map A₀ i₀ P₀ a b h) hij hjk x)

/-- Helper for Lemma 10.127.17: the lifted raw stage maps still commute with the lifted raw tail
transitions. -/
theorem ulifted_raw_tail_stageMap_comm
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    (codomainULiftRingHom (raw_tail_stageMap A₀ i₀ P₀ k)).comp (A₀.RMap j.1 k.1 hjk) =
      (uliftRingHom (raw_tail_map A₀ i₀ P₀ j k hjk)).comp
        (codomainULiftRingHom (raw_tail_stageMap A₀ i₀ P₀ j)) := by
  apply RingHom.ext
  intro x
  change
    ULift.up ((raw_tail_stageMap A₀ i₀ P₀ k) ((A₀.RMap j.1 k.1 hjk) x)) =
      ULift.up ((raw_tail_map A₀ i₀ P₀ j k hjk) ((raw_tail_stageMap A₀ i₀ P₀ j) x))
  simpa using congrArg (fun g : A₀.RStage j.1 →+* raw_tail_stage A₀ i₀ P₀ k ↦ g x)
    (raw_tail_stageMap_comm A₀ i₀ P₀ hjk)

/-- Helper for Lemma 10.127.17: lifting the codomain of a finite-type stage map preserves finite
type. -/
theorem ulifted_raw_tail_target_finiteType
    (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
    (P₀ : Type u) [CommRing P₀] [Algebra (A₀.RStage i₀) P₀]
    [Algebra.FinitePresentation (A₀.RStage i₀) P₀]
    (j : Set.Ici i₀) :
    (codomainULiftRingHom (raw_tail_stageMap A₀ i₀ P₀ j)).FiniteType := by
  letI : Algebra (A₀.RStage i₀) (A₀.RStage j.1) := (A₀.RMap i₀ j.1 j.2).toAlgebra
  -- Proof comment: the lifted stage map is the raw finite-type stage map followed by the
  -- surjective codomain `ULift` equivalence.
  exact RingHom.FiniteType.comp
    (RingHom.FiniteType.of_surjective _
      (fun x ↦ ⟨x.down, by cases x; rfl⟩))
    (descended_tail_raw_stage_finiteType A₀ i₀ (P₀ := P₀) j)
