import StacksProject_2024.Chap10.Lemma_10_127_8
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A directed approximation of a local ring homomorphism by local maps whose source stages are
essentially of finite type over `ℤ` and whose target stages are essentially of finite type over the
corresponding source stages. The directed colimit data is primitive here; the generic
direct-limit API provided by `Lemma_10_127_8` can be applied to it downstream. -/
structure DirectedLocalHomApproximation (f : R →+* S) where
  Λ : Type w
  instPreorder : Preorder Λ
  instNonempty : Nonempty Λ
  instDirectedOrder : IsDirectedOrder Λ
  RStage : Λ → Type u
  instCommRingRStage (i : Λ) : CommRing (RStage i)
  map (i j : Λ) (h : i ≤ j) : RStage i →+* RStage j
  instDirectedSystemRStage : DirectedSystem RStage (fun i j h ↦ map i j h)
  colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R
  instIsLocalRingRStage (i : Λ) : IsLocalRing (RStage i)
  SStage : Λ → Type v
  instCommRingSStage (i : Λ) : CommRing (SStage i)
  instIsLocalRingSStage (i : Λ) : IsLocalRing (SStage i)
  stageMap (i : Λ) : RStage i →+* SStage i
  stageMap_isLocalHom (i : Λ) : IsLocalHom (stageMap i)
  targetMap (i j : Λ) (h : i ≤ j) : SStage i →+* SStage j
  instDirectedSystemTarget : DirectedSystem SStage (fun i j h ↦ targetMap i j h)
  comm {i j : Λ} (h : i ≤ j) :
    (stageMap j).comp (map i j h) = (targetMap i j h).comp (stageMap i)
  targetColimit : Ring.DirectLimit SStage (fun i j h ↦ targetMap i j h) ≃+* S
  colimit_comm :
    targetColimit.toRingHom.comp (Ring.DirectLimit.map stageMap (fun _ _ h ↦ comm h)) =
      f.comp colimitIso.toRingHom
  source_essFiniteType (i : Λ) : (Int.castRingHom (RStage i)).EssFiniteType
  target_essFiniteType (i : Λ) : (stageMap i).EssFiniteType

attribute [instance] DirectedLocalHomApproximation.instPreorder
attribute [instance] DirectedLocalHomApproximation.instNonempty
attribute [instance] DirectedLocalHomApproximation.instDirectedOrder
attribute [instance] DirectedLocalHomApproximation.instCommRingRStage
attribute [instance] DirectedLocalHomApproximation.instDirectedSystemRStage
attribute [instance] DirectedLocalHomApproximation.instIsLocalRingRStage
attribute [instance] DirectedLocalHomApproximation.instCommRingSStage
attribute [instance] DirectedLocalHomApproximation.instIsLocalRingSStage
attribute [instance] DirectedLocalHomApproximation.stageMap_isLocalHom
attribute [instance] DirectedLocalHomApproximation.instDirectedSystemTarget

namespace DirectedLocalHomApproximation

variable {f : R →+* S} (A : DirectedLocalHomApproximation f)

/-- The induced map on direct limits coming from the stagewise local homomorphisms. -/
noncomputable def directLimitMap :
    Ring.DirectLimit A.RStage (fun i j h ↦ A.map i j h) →+*
      Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h) :=
  Ring.DirectLimit.map A.stageMap (fun _ _ h ↦ A.comm h)

-- Proof sketch: this is the defining formula for `Ring.DirectLimit.map` on the canonical maps
-- from the stages into the colimit.
/-- The induced map on direct limits restricts to the given stage map on each stage. -/
theorem directLimitMap_of (i : A.Λ) (x : A.RStage i) :
    A.directLimitMap (Ring.DirectLimit.of A.RStage (fun i j h ↦ A.map i j h) i x) =
      Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i (A.stageMap i x) := by
  -- Use the defining formula for the induced map on a direct-limit stage element.
  simpa [DirectedLocalHomApproximation.directLimitMap] using
    (Ring.DirectLimit.map_apply_of
      (f := fun i j h ↦ A.map i j h)
      (f' := fun i j h ↦ A.targetMap i j h)
      (g := A.stageMap)
      (hg := fun _ _ h ↦ A.comm h)
      (x := x))

/-- The canonical map from a target stage of the approximation system to the limit ring `S`. -/
noncomputable def targetStageToLimitHom (i : A.Λ) : A.SStage i →+* S :=
  let colimitHom : Ring.DirectLimit A.SStage (fun i j h ↦ A.targetMap i j h) →+* S :=
    A.targetColimit.toRingHom
  colimitHom.comp (Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i)

/-- The tensor-product source of the canonical base-change map from stage `i` to stage `j`. -/
abbrev targetStageBaseChange {i j : A.Λ} (h : i ≤ j) : Type _ :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
  A.SStage i ⊗[A.RStage i] A.RStage j

-- Proof sketch: rewrite the square-commutativity field `A.comm h` pointwise and interpret the
-- algebra maps using the chosen `RingHom.toAlgebra` structures.
/-- The target transition map is an algebra homomorphism over the source stage `i`. -/
private theorem stageTransitionAlgHom_commutes {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
    ∀ x : A.RStage i,
      A.targetMap i j h (algebraMap (A.RStage i) (A.SStage i) x) =
        algebraMap (A.RStage i) (A.SStage j) x := by
  dsimp
  intro x
  -- Rewrite the algebra maps coming from `RingHom.toAlgebra` and read off the commutative square.
  have hcomm :
      ((A.targetMap i j h).comp (A.stageMap i)) x =
        ((A.stageMap j).comp (A.map i j h)) x :=
    congrArg (fun g : A.RStage i →+* A.SStage j => g x) ((A.comm h).symm)
  simpa [RingHom.algebraMap_toAlgebra] using hcomm

/-- The target transition map viewed as an algebra homomorphism over the source stage `i`. -/
private noncomputable def stageTransitionAlgHom {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
    A.SStage i →ₐ[A.RStage i] A.SStage j :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
  { toRingHom := A.targetMap i j h
    commutes' := A.stageTransitionAlgHom_commutes h }

-- Proof sketch: both algebra maps from `A.RStage i` to `A.SStage j` are induced by the composite
-- `A.RStage i → A.RStage j → A.SStage j`, so this is the compatibility built into
-- `RingHom.toAlgebra`.
/-- The stage map at `j` is an algebra homomorphism over the source stage `i`. -/
private theorem targetStageAlgHom_commutes {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
    ∀ x : A.RStage i,
      A.stageMap j (algebraMap (A.RStage i) (A.RStage j) x) =
        algebraMap (A.RStage i) (A.SStage j) x := by
  dsimp
  intro x
  -- Both algebra maps are induced by the same composite `A.RStage i → A.RStage j → A.SStage j`.
  simp [RingHom.algebraMap_toAlgebra]

/-- The stage map at `j` viewed as an algebra homomorphism over the source stage `i`. -/
private noncomputable def targetStageAlgHom {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
    A.RStage j →ₐ[A.RStage i] A.SStage j :=
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
  { toRingHom := A.stageMap j
    commutes' := A.targetStageAlgHom_commutes h }

/-- The canonical base-change map `Sᵢ ⊗[Rᵢ] Rⱼ → Sⱼ` attached to a transition `i ≤ j`. -/
noncomputable def stageBaseChangeMap {i j : A.Λ} (h : i ≤ j) :
    A.targetStageBaseChange h →+* A.SStage j :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
  (Algebra.TensorProduct.productMap (A.stageTransitionAlgHom h) (A.targetStageAlgHom h)).toRingHom

-- Proof sketch: unfold `stageBaseChangeMap` and use the defining formula for
-- `Algebra.TensorProduct.productMap` on pure tensors.
/-- The canonical base-change map sends `x ⊗ y` to the product of the transition of `x` and the
stage map applied to `y`. -/
private theorem stageBaseChangeMap_tmul {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.RStage j) := (A.map i j h).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.map i j h)).toAlgebra
    ∀ x : A.SStage i,
      ∀ y : A.RStage j,
        A.stageBaseChangeMap h (x ⊗ₜ[A.RStage i] y) = A.targetMap i j h x * A.stageMap j y := by
  intro x y
  -- Unfold the base-change map and evaluate `productMap` on a pure tensor.
  simp [DirectedLocalHomApproximation.stageBaseChangeMap,
    DirectedLocalHomApproximation.stageTransitionAlgHom,
    DirectedLocalHomApproximation.targetStageAlgHom,
    Algebra.TensorProduct.productMap_apply_tmul]

end DirectedLocalHomApproximation

section

variable (f : R →+* S)

/-- Helper for Lemma 10.127.9: a stage index is a pair of finite subsets of `R` and `S`
compatible with `f`. This is the source proof's controlling directed object. -/
private structure CompatibleStageIndex where
  source : Finset R
  target : Finset S
  mapsTo_target : ∀ ⦃r : R⦄, r ∈ source → f r ∈ target

/-- Helper for Lemma 10.127.9: stage indices are ordered by componentwise inclusion. -/
private instance compatibleStageIndexLE : LE (CompatibleStageIndex f) where
  le i j := i.source ⊆ j.source ∧ i.target ⊆ j.target

/-- Helper for Lemma 10.127.9: the compatible finite-subset indices form a preorder under
componentwise inclusion. -/
private instance compatibleStageIndexPreorder : Preorder (CompatibleStageIndex f) where
  le_refl i := ⟨by intro r hr; exact hr, by intro s hs; exact hs⟩
  le_trans i j k hij hjk :=
    ⟨by
        intro r hr
        exact hjk.1 (hij.1 hr),
      by
        intro s hs
        exact hjk.2 (hij.2 hs)⟩

/-- Helper for Lemma 10.127.9: the empty compatible pair gives a base point for the directed
indexing set. -/
private instance compatibleStageIndexNonempty : Nonempty (CompatibleStageIndex f) :=
  by
    classical
    exact ⟨{ source := ∅
             target := ∅
             mapsTo_target := by
               intro r hr
               simp at hr }⟩

/-- Helper for Lemma 10.127.9: enlarging two compatible stages by unions gives a common upper
bound, matching the source proof's directedness argument. -/
private instance compatibleStageIndexDirectedOrder : IsDirectedOrder (CompatibleStageIndex f) := by
  classical
  refine ⟨?_⟩
  intro i j
  refine ⟨
    { source := i.source ∪ j.source
      target := i.target ∪ j.target
      mapsTo_target := ?_ },
    ?_,
    ?_⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact Finset.mem_union.mpr <| Or.inl (i.mapsTo_target hr)
    · exact Finset.mem_union.mpr <| Or.inr (j.mapsTo_target hr)
  · refine ⟨?_, ?_⟩
    · intro r hr
      exact Finset.mem_union.mpr <| Or.inl hr
    · intro s hs
      exact Finset.mem_union.mpr <| Or.inl hs
  · refine ⟨?_, ?_⟩
    · intro r hr
      exact Finset.mem_union.mpr <| Or.inr hr
    · intro s hs
      exact Finset.mem_union.mpr <| Or.inr hs

/-- Helper for Lemma 10.127.9: the singleton source stage used later to place a chosen element of
`R` into some approximation stage. -/
private noncomputable def sourceSingletonStageIndex (r : R) : CompatibleStageIndex f where
  source :=
    let _ : DecidableEq R := Classical.decEq R
    {r}
  target :=
    let _ : DecidableEq S := Classical.decEq S
    {f r}
  mapsTo_target := by
    classical
    intro r' hr'
    -- Membership in the singleton source stage forces the element to be `r`.
    have hr'' : r' = r := Finset.mem_singleton.mp hr'
    simpa [hr'']

/-- Helper for Lemma 10.127.9: the chosen source element belongs to its singleton source stage. -/
private theorem mem_sourceSingletonStageIndex_source (r : R) :
    r ∈ (sourceSingletonStageIndex f r).source := by
  -- This is the stage later used to hit `r` in the source colimit surjectivity argument.
  simp [sourceSingletonStageIndex]

/-- Helper for Lemma 10.127.9: the image of the chosen source element belongs to the corresponding
singleton target stage. -/
private theorem mem_sourceSingletonStageIndex_target (r : R) :
    f r ∈ (sourceSingletonStageIndex f r).target := by
  -- This records the compatibility condition built into the singleton source stage.
  simp [sourceSingletonStageIndex]

/-- Helper for Lemma 10.127.9: the singleton target stage used later to place a chosen element of
`S` into some approximation stage. -/
private noncomputable def targetSingletonStageIndex (s : S) : CompatibleStageIndex f where
  source :=
    let _ : DecidableEq R := Classical.decEq R
    ∅
  target :=
    let _ : DecidableEq S := Classical.decEq S
    {s}
  mapsTo_target := by
    classical
    intro r hr
    simp at hr

/-- Helper for Lemma 10.127.9: the chosen target element belongs to its singleton target stage. -/
private theorem mem_targetSingletonStageIndex_target (s : S) :
    s ∈ (targetSingletonStageIndex f s).target := by
  -- This is the target-side singleton stage used later for colimit surjectivity.
  simp [targetSingletonStageIndex]

/-- Helper for Lemma 10.127.9: the raw source stage attached to a finite compatible index is the
`ℤ`-subalgebra of `R` generated by the chosen finite source subset. -/
private noncomputable abbrev sourceRawStage (idx : CompatibleStageIndex f) : Subalgebra ℤ R :=
  Algebra.adjoin ℤ ((↑idx.source : Set R))

/-- Helper for Lemma 10.127.9: the raw target stage attached to a finite compatible index is the
`ℤ`-subalgebra of `S` generated by the chosen finite target subset. -/
private noncomputable abbrev targetRawStage (idx : CompatibleStageIndex f) : Subalgebra ℤ S :=
  Algebra.adjoin ℤ ((↑idx.target : Set S))

/-- Helper for Lemma 10.127.9: the ambient local map `f` restricts to the raw source stage before
any localization is introduced. -/
private noncomputable def rawStageMapToAmbient (idx : CompatibleStageIndex f) :
    sourceRawStage f idx →ₐ[ℤ] S :=
  f.toIntAlgHom.comp (sourceRawStage f idx).val

/-- Helper for Lemma 10.127.9: the image of a raw source stage lies in the corresponding raw
target stage, exactly because the target generators contain the images of the source generators. -/
private theorem source_stage_image_le_target_stage (idx : CompatibleStageIndex f) :
    ∀ x : sourceRawStage f idx, rawStageMapToAmbient f idx x ∈ targetRawStage f idx := by
  intro x
  -- First view the claim in the ambient ring `S`, then apply adjoin induction on the underlying
  -- source-stage element.
  change f (x : R) ∈ targetRawStage f idx
  -- Follow the source proof: prove the claim on the adjoin generators and close by induction.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ x.property
  · intro r hr
    exact Algebra.subset_adjoin (idx.mapsTo_target hr)
  · intro z
    -- Integer scalars are already contained in every `ℤ`-subalgebra.
    simpa using (targetRawStage f idx).algebraMap_mem z
  · rintro y z _ _ hy hz
    simpa [map_add] using (targetRawStage f idx).add_mem hy hz
  · rintro y z _ _ hy hz
    simpa [map_mul] using (targetRawStage f idx).mul_mem hy hz

/-- Helper for Lemma 10.127.9: the raw stage map is the ambient local homomorphism restricted to
the corresponding raw `ℤ`-subalgebras. -/
private noncomputable def rawStageMap (idx : CompatibleStageIndex f) :
    sourceRawStage f idx →ₐ[ℤ] targetRawStage f idx :=
  (rawStageMapToAmbient f idx).codRestrict
    (targetRawStage f idx)
    (source_stage_image_le_target_stage f idx)

/-- Helper for Lemma 10.127.9: enlarging a compatible source index enlarges the corresponding raw
source stage. -/
private theorem sourceRawStage_mono {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    sourceRawStage f i ≤ sourceRawStage f j := by
  -- Later stages adjoin every earlier source generator.
  exact Algebra.adjoin_le_iff.2 fun r hr ↦ Algebra.subset_adjoin (hij.1 hr)

/-- Helper for Lemma 10.127.9: the raw source-stage inclusion attached to an index enlargement. -/
private noncomputable def sourceRawStageInclusion {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    sourceRawStage f i →+* sourceRawStage f j :=
  Subalgebra.inclusion (sourceRawStage_mono f hij)

/-- Helper for Lemma 10.127.9: enlarging a compatible target index enlarges the corresponding raw
target stage. -/
private theorem targetRawStage_mono {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    targetRawStage f i ≤ targetRawStage f j := by
  -- Later stages adjoin every earlier target generator.
  exact Algebra.adjoin_le_iff.2 fun s hs ↦ Algebra.subset_adjoin (hij.2 hs)

/-- Helper for Lemma 10.127.9: the raw target-stage inclusion attached to an index enlargement. -/
private noncomputable def targetRawStageInclusion {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    targetRawStage f i →+* targetRawStage f j :=
  Subalgebra.inclusion (targetRawStage_mono f hij)

/-- Helper for Lemma 10.127.9: the raw stage map carries a stage element to its ambient image
under `f`. Stated propositionally so that later proofs never unfold the restriction wrapper
definitionally inside the kernel. -/
private theorem rawStageMap_coe (idx : CompatibleStageIndex f) (x : sourceRawStage f idx) :
    (rawStageMap f idx x : S) = f ↑x := by
  unfold rawStageMap rawStageMapToAmbient
  rw [AlgHom.coe_codRestrict, AlgHom.comp_apply, RingHom.toIntAlgHom_apply, Subalgebra.coe_val]

/-- Helper for Lemma 10.127.9: the raw source-stage inclusion does not change ambient values. -/
private theorem sourceRawStageInclusion_coe {i j : CompatibleStageIndex f} (hij : i ≤ j)
    (x : sourceRawStage f i) :
    (sourceRawStageInclusion f hij x : R) = ↑x := by
  unfold sourceRawStageInclusion
  rw [AlgHom.coe_toRingHom, Subalgebra.coe_inclusion]

/-- Helper for Lemma 10.127.9: the raw target-stage inclusion does not change ambient values. -/
private theorem targetRawStageInclusion_coe {i j : CompatibleStageIndex f} (hij : i ≤ j)
    (x : targetRawStage f i) :
    (targetRawStageInclusion f hij x : S) = ↑x := by
  unfold targetRawStageInclusion
  rw [AlgHom.coe_toRingHom, Subalgebra.coe_inclusion]

variable [IsLocalRing R] [IsLocalRing S]

/-- Helper for Lemma 10.127.9: the source-side prime used to localize a raw source stage. -/
private noncomputable abbrev sourceStagePrime (idx : CompatibleStageIndex f) :
    Ideal (sourceRawStage f idx) :=
  Ideal.comap (sourceRawStage f idx).val (IsLocalRing.maximalIdeal R)

/-- Helper for Lemma 10.127.9: the target-side prime used to localize a raw target stage. -/
private noncomputable abbrev targetStagePrime (idx : CompatibleStageIndex f) :
    Ideal (targetRawStage f idx) :=
  Ideal.comap (targetRawStage f idx).val (IsLocalRing.maximalIdeal S)

omit [IsLocalRing S] in
/-- Helper for Lemma 10.127.9: the source-stage inclusion does not change the pullback of the
ambient maximal ideal. This is the exact source-side hypothesis needed before localization. -/
private theorem source_stage_comap_maximal_eq {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    Ideal.comap (sourceRawStageInclusion f hij)
      (sourceStagePrime f j) =
        sourceStagePrime f i := by
  -- Route correction: rewrite both contracted ideals as membership in the same ambient element of
  -- `R`, avoiding definitional reduction through the inclusion map.
  ext x
  change (((sourceRawStageInclusion f hij x : sourceRawStage f j) : R) ∈
      IsLocalRing.maximalIdeal R) ↔
    ((x : R) ∈ IsLocalRing.maximalIdeal R)
  rfl

omit [IsLocalRing R] in
/-- Helper for Lemma 10.127.9: the target-stage inclusion does not change the pullback of the
ambient maximal ideal. This is the target-side analogue needed before localization. -/
private theorem target_stage_comap_maximal_eq {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    Ideal.comap (targetRawStageInclusion f hij)
      (targetStagePrime f j) =
        targetStagePrime f i := by
  -- Route correction: rewrite both contracted ideals as membership in the same ambient element of
  -- `S`, avoiding definitional reduction through the inclusion map.
  ext x
  change (((targetRawStageInclusion f hij x : targetRawStage f j) : S) ∈
      IsLocalRing.maximalIdeal S) ↔
    ((x : S) ∈ IsLocalRing.maximalIdeal S)
  rfl

variable [IsLocalHom f]

/-- Helper for Lemma 10.127.9: the restricted raw stage map pulls back the target maximal ideal to
the source maximal ideal, so the stage map itself can later be localized. -/
private theorem stage_zero_map_comap_maximal_eq (idx : CompatibleStageIndex f) :
    Ideal.comap (rawStageMap f idx) (targetStagePrime f idx) =
      sourceStagePrime f idx := by
  -- Evaluate membership pointwise, then use the local-hom maximal-ideal pullback equality.
  ext x
  change rawStageMap f idx x ∈ targetStagePrime f idx ↔
      x ∈ sourceStagePrime f idx
  change f (x : R) ∈ IsLocalRing.maximalIdeal S ↔ (x : R) ∈ IsLocalRing.maximalIdeal R
  have hmax :
      ((x : R) ∈ Ideal.comap f (IsLocalRing.maximalIdeal S)) =
        ((x : R) ∈ IsLocalRing.maximalIdeal R) :=
    congrArg (fun I : Ideal R => (x : R) ∈ I) (IsLocalRing.maximalIdeal_comap f)
  simpa [Ideal.mem_comap] using hmax

/-- Helper for Lemma 10.127.9: the localized source stage attached to a finite compatible index. -/
private noncomputable abbrev sourceLocalizedStage (idx : CompatibleStageIndex f) : Type u :=
  Localization.AtPrime (sourceStagePrime f idx)

/-- Helper for Lemma 10.127.9: the localized target stage attached to a finite compatible index. -/
private noncomputable abbrev targetLocalizedStage (idx : CompatibleStageIndex f) : Type v :=
  Localization.AtPrime (targetStagePrime f idx)

/-- Helper for Lemma 10.127.9: enlarging a source stage induces the localized source transition
map between the corresponding local rings. -/
private noncomputable def sourceLocalizedTransition {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    sourceLocalizedStage f i →+* sourceLocalizedStage f j :=
  Localization.localRingHom
    (sourceStagePrime f i)
    (sourceStagePrime f j)
    (sourceRawStageInclusion f hij)
    (source_stage_comap_maximal_eq f hij).symm

/-- Helper for Lemma 10.127.9: enlarging a target stage induces the localized target transition
map between the corresponding local rings. -/
private noncomputable def targetLocalizedTransition {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    targetLocalizedStage f i →+* targetLocalizedStage f j :=
  Localization.localRingHom
    (targetStagePrime f i)
    (targetStagePrime f j)
    (targetRawStageInclusion f hij)
    (target_stage_comap_maximal_eq f hij).symm

/-- Helper for Lemma 10.127.9: the localized stage map attached to one finite compatible index. -/
private noncomputable def localizedStageMap (idx : CompatibleStageIndex f) :
    sourceLocalizedStage f idx →+* targetLocalizedStage f idx :=
  Localization.localRingHom
    (sourceStagePrime f idx)
    (targetStagePrime f idx)
    (rawStageMap f idx)
    (stage_zero_map_comap_maximal_eq f idx).symm

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the localized source transition is the identity on a fixed stage. -/
private theorem source_localized_transition_id (i : CompatibleStageIndex f) :
    sourceLocalizedTransition f (i := i) (j := i) le_rfl = RingHom.id _ := by
  -- Route correction: use the canonical `localRingHom_id` theorem instead of reproving the
  -- identity map by generatorwise extensionality through localization.
  have hincl :
      sourceRawStageInclusion f (i := i) (j := i) le_rfl = RingHom.id _ :=
    by
      ext x
      rfl
  simpa [sourceLocalizedTransition, hincl] using
    (Localization.localRingHom_id (R := sourceRawStage f i) (I := sourceStagePrime f i))

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the localized source transition sends a raw-stage generator to the
corresponding generator in the larger localized stage. -/
private theorem source_localized_transition_to_map {i j : CompatibleStageIndex f} (hij : i ≤ j)
    (x : sourceRawStage f i) :
    sourceLocalizedTransition f hij (algebraMap _ _ x) =
      algebraMap _ _ ((sourceRawStageInclusion f hij) x) := by
  simpa [sourceLocalizedTransition] using
    (Localization.localRingHom_to_map
      (I := sourceStagePrime f i)
      (J := sourceStagePrime f j)
      (f := sourceRawStageInclusion f hij)
      (hIJ := (source_stage_comap_maximal_eq f hij).symm)
      x)

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: localized source transitions compose along the directed order. -/
private theorem source_localized_transition_comp {i j k : CompatibleStageIndex f}
    (hij : i ≤ j) (hjk : j ≤ k) :
    sourceLocalizedTransition f (hij.trans hjk) =
      (sourceLocalizedTransition f hjk).comp (sourceLocalizedTransition f hij) := by
  -- Route correction: the previous generatorwise proof closed with a localization-level `rfl`
  -- whose kernel check hit a deterministic timeout; reuse the canonical `localRingHom_comp`
  -- theorem instead, exactly as `source_localized_transition_id` reuses `localRingHom_id`.
  have hincl :
      sourceRawStageInclusion f (hij.trans hjk) =
        (sourceRawStageInclusion f hjk).comp (sourceRawStageInclusion f hij) := by
    ext x
    rw [RingHom.comp_apply]
    rw [sourceRawStageInclusion_coe, sourceRawStageInclusion_coe, sourceRawStageInclusion_coe]
  simpa [sourceLocalizedTransition, hincl] using
    (Localization.localRingHom_comp
      (I := sourceStagePrime f i)
      (J := sourceStagePrime f j)
      (K := sourceStagePrime f k)
      (f := sourceRawStageInclusion f hij)
      (hIJ := (source_stage_comap_maximal_eq f hij).symm)
      (g := sourceRawStageInclusion f hjk)
      (hJK := (source_stage_comap_maximal_eq f hjk).symm))

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the localized target transition is the identity on a fixed stage. -/
private theorem target_localized_transition_id (i : CompatibleStageIndex f) :
    targetLocalizedTransition f (i := i) (j := i) le_rfl = RingHom.id _ := by
  -- Route correction: use the canonical `localRingHom_id` theorem on the target stages.
  have hincl :
      targetRawStageInclusion f (i := i) (j := i) le_rfl = RingHom.id _ :=
    by
      ext x
      rfl
  simpa [targetLocalizedTransition, hincl] using
    (Localization.localRingHom_id (R := targetRawStage f i) (I := targetStagePrime f i))

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the localized target transition sends a raw-stage generator to the
corresponding generator in the larger localized target stage. -/
private theorem target_localized_transition_to_map {i j : CompatibleStageIndex f} (hij : i ≤ j)
    (x : targetRawStage f i) :
    targetLocalizedTransition f hij (algebraMap _ _ x) =
      algebraMap _ _ ((targetRawStageInclusion f hij) x) := by
  simpa [targetLocalizedTransition] using
    (Localization.localRingHom_to_map
      (I := targetStagePrime f i)
      (J := targetStagePrime f j)
      (f := targetRawStageInclusion f hij)
      (hIJ := (target_stage_comap_maximal_eq f hij).symm)
      x)

/-- Helper for Lemma 10.127.9: the localized stage map sends a raw-stage generator to its image in
the localized target stage. -/
private theorem localizedStageMap_to_map (idx : CompatibleStageIndex f)
    (x : sourceRawStage f idx) :
    localizedStageMap f idx (algebraMap _ _ x) =
      algebraMap _ _ (rawStageMap f idx x) := by
  simpa [localizedStageMap] using
    (Localization.localRingHom_to_map
      (I := sourceStagePrime f idx)
      (J := targetStagePrime f idx)
      (f := rawStageMap f idx)
      (hIJ := (stage_zero_map_comap_maximal_eq f idx).symm)
      x)

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: localized target transitions compose along the directed order. -/
private theorem target_localized_transition_comp {i j k : CompatibleStageIndex f}
    (hij : i ≤ j) (hjk : j ≤ k) :
    targetLocalizedTransition f (hij.trans hjk) =
      (targetLocalizedTransition f hjk).comp (targetLocalizedTransition f hij) := by
  -- Route correction: same kernel-timeout avoidance as on the source side — reuse the canonical
  -- `localRingHom_comp` theorem instead of a generatorwise localization-level `rfl`.
  have hincl :
      targetRawStageInclusion f (hij.trans hjk) =
        (targetRawStageInclusion f hjk).comp (targetRawStageInclusion f hij) := by
    ext x
    rw [RingHom.comp_apply]
    rw [targetRawStageInclusion_coe, targetRawStageInclusion_coe, targetRawStageInclusion_coe]
  simpa [targetLocalizedTransition, hincl] using
    (Localization.localRingHom_comp
      (I := targetStagePrime f i)
      (J := targetStagePrime f j)
      (K := targetStagePrime f k)
      (f := targetRawStageInclusion f hij)
      (hIJ := (target_stage_comap_maximal_eq f hij).symm)
      (g := targetRawStageInclusion f hjk)
      (hJK := (target_stage_comap_maximal_eq f hjk).symm))

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the raw source-target square commutes on each stage element before
localization. -/
private theorem raw_stage_square_apply {i j : CompatibleStageIndex f} (hij : i ≤ j)
    (x : sourceRawStage f i) :
    rawStageMap f j (sourceRawStageInclusion f hij x) =
      targetRawStageInclusion f hij (rawStageMap f i x) := by
  -- Route correction: state the square inside the target stage and rewrite both ambient values
  -- to `f ↑x` with the named coercion lemmas; this keeps every step propositional and removes
  -- the former 16× kernel heartbeat budget.
  refine Subtype.ext ?_
  rw [rawStageMap_coe, sourceRawStageInclusion_coe, targetRawStageInclusion_coe, rawStageMap_coe]

/-- Helper for Lemma 10.127.9: the localized stage maps commute with localized stage transitions. -/
private theorem localized_stage_square_commutes {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    (localizedStageMap f j).comp (sourceLocalizedTransition f hij) =
      (targetLocalizedTransition f hij).comp (localizedStageMap f i) := by
  -- Route correction: instead of comparing two `Localization.localRingHom` presentations of the
  -- square (which needed an 800k heartbeat budget), check the square directly on the
  -- localization generators and rewrite both composites to the same raw-stage image.
  refine IsLocalization.ringHom_ext (sourceStagePrime f i).primeCompl ?_
  ext x
  simp only [RingHom.comp_apply]
  rw [source_localized_transition_to_map f hij x]
  rw [localizedStageMap_to_map f j (sourceRawStageInclusion f hij x)]
  rw [localizedStageMap_to_map f i x]
  rw [target_localized_transition_to_map f hij (rawStageMap f i x)]
  exact congrArg (algebraMap _ _) (raw_stage_square_apply f hij x)

end

namespace Ring.DirectLimit

section

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
variable {A : ι → Type*} [∀ i, CommRing (A i)]
variable {map : ∀ i j, i ≤ j → A i →+* A j}
variable [DirectedSystem A (fun i j h ↦ map i j h)]
variable {B : Type*} [CommRing B]

omit [IsDirectedOrder ι] [DirectedSystem A (fun i j h ↦ map i j h)] in
/-- Helper for Lemma 10.127.9: a compatible map out of a directed system is surjective on the
direct limit once every target element is already represented at some stage. -/
theorem lift_surjective_of_stagewise_cover
    (g : ∀ i, A i →+* B)
    (hg : ∀ i j hij x, g j (map i j hij x) = g i x)
    (hcover : ∀ b : B, ∃ i x, g i x = b) :
    Function.Surjective (Ring.DirectLimit.lift A (fun i j h ↦ map i j h) B g hg) := by
  intro b
  -- Represent the target element by a single stage element and then apply `lift_of`.
  rcases hcover b with ⟨i, x, rfl⟩
  refine ⟨Ring.DirectLimit.of A (fun i j h ↦ map i j h) i x, ?_⟩
  simp [Ring.DirectLimit.lift_of]

omit [DirectedSystem A (fun i j h ↦ map i j h)] in
/-- Helper for Lemma 10.127.9: stagewise injectivity together with stagewise cover makes the
direct-limit comparison map bijective. -/
theorem lift_bijective_of_stagewise_injective_cover
    [Nonempty ι]
    (g : ∀ i, A i →+* B)
    (hg : ∀ i j hij x, g j (map i j hij x) = g i x)
    (hinj : ∀ i, Function.Injective (g i))
    (hcover : ∀ b : B, ∃ i x, g i x = b) :
    Function.Bijective (Ring.DirectLimit.lift A (fun i j h ↦ map i j h) B g hg) := by
  -- Combine stagewise injectivity with stagewise cover into a single bijectivity statement.
  refine ⟨Ring.DirectLimit.lift_injective
    (G := A) (f := fun i j h ↦ map i j h) (P := B) (g := g) (Hg := hg) hinj, ?_⟩
  exact Ring.DirectLimit.lift_surjective_of_stagewise_cover (g := g) (hg := hg) hcover

end

end Ring.DirectLimit

section

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]

/-- Helper for Lemma 10.127.9: the image of an element outside the pulled-back maximal ideal is a
unit in the ambient local ring. -/
private theorem map_comap_maximal_primeCompl_le_units (g : A →+* B) :
    Submonoid.map g (Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl ≤ IsUnit.submonoid B :=
    by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Leaving the pulled-back maximal ideal means the image misses the maximal ideal of `B`.
  exact
    (IsLocalRing.notMem_maximalIdeal).mp <|
      by simpa [Ideal.primeCompl, Ideal.mem_comap] using hx

/-- Helper for Lemma 10.127.9: the localization at the pulled-back maximal ideal maps canonically
to the ambient local ring by first localizing along the image complement and then cancelling a
localization at units. -/
private noncomputable def localizationAtComapMaximalToAmbient (g : A →+* B) :
    Localization.AtPrime (Ideal.comap g (IsLocalRing.maximalIdeal B)) →+* B :=
  let imageLocalization :
      Localization.AtPrime (Ideal.comap g (IsLocalRing.maximalIdeal B)) →+*
        Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g) :=
    IsLocalization.map
      (Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g))
      g
      (Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.le_comap_map
  let collapseUnits :
      Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g) →+* B :=
    ((IsLocalization.atUnits
      B
      ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g)
      (map_comap_maximal_primeCompl_le_units g)).symm.toRingHom)
  collapseUnits.comp imageLocalization

/-- Helper for Lemma 10.127.9: the canonical map from the pulled-back localization into the
ambient local ring is injective once the original ring map is injective. -/
private theorem localization_at_comap_maximal_to_ambient_injective
    (g : A →+* B) (hg : Function.Injective g) :
    Function.Injective (localizationAtComapMaximalToAmbient g) := by
  -- First localize along the image of the pulled-back complement, where injectivity is preserved.
  let imageLocalization :
      Localization.AtPrime (Ideal.comap g (IsLocalRing.maximalIdeal B)) →+*
        Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g) :=
    IsLocalization.map
      (Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g))
      g
      (Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.le_comap_map
  have hImageLocalization : Function.Injective imageLocalization := by
    -- This is the standard injectivity theorem for induced maps on localizations.
    exact
      IsLocalization.map_injective_of_injective
        ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl)
        (Localization.AtPrime (Ideal.comap g (IsLocalRing.maximalIdeal B)))
        (Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g))
        hg
  let collapseUnits :
      Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g) →+* B :=
    ((IsLocalization.atUnits
      B
      ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g)
      (map_comap_maximal_primeCompl_le_units g)).symm.toRingHom)
  have hCollapseUnits : Function.Injective collapseUnits := by
    -- Cancelling a localization at units is an equivalence, hence injective.
    exact
      ((IsLocalization.atUnits
        B
        ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g)
        (map_comap_maximal_primeCompl_le_units g)).symm.injective)
  -- The ambient comparison map is the composite of the injective localization map and the
  -- injective equivalence back to `B`.
  simpa [localizationAtComapMaximalToAmbient, imageLocalization, collapseUnits] using
    Function.Injective.comp hCollapseUnits hImageLocalization

/-- Helper for Lemma 10.127.9: the ambient comparison map from the pulled-back localization sends
the image of a base element to its value in the ambient local ring. -/
private theorem localizationAtComapMaximalToAmbient_to_map (g : A →+* B) (x : A) :
    localizationAtComapMaximalToAmbient g (algebraMap _ _ x) = g x := by
  let imageLocalization :
      Localization.AtPrime (Ideal.comap g (IsLocalRing.maximalIdeal B)) →+*
        Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g) :=
    IsLocalization.map
      (Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g))
      g
      (Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.le_comap_map
  let collapseUnits :
      Localization ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g) →+* B :=
    ((IsLocalization.atUnits
      B
      ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g)
      (map_comap_maximal_primeCompl_le_units g)).symm.toRingHom)
  change collapseUnits (imageLocalization (algebraMap _ _ x)) = g x
  rw [IsLocalization.map_eq]
  change collapseUnits (algebraMap _ _ (g x)) = g x
  exact
    (IsLocalization.atUnits B
      ((Ideal.comap g (IsLocalRing.maximalIdeal B)).primeCompl.map g)
      (map_comap_maximal_primeCompl_le_units g)).symm.commutes (g x)

end

section

variable (f : R →+* S)
variable [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom f]

/-- Helper for Lemma 10.127.9: the localized source stage maps canonically back to the ambient
local ring `R`. This names the textbook arrow `R_λ → R`. -/
private noncomputable abbrev sourceLocalizedToAmbient (f : R →+* S) (idx : CompatibleStageIndex f) :
    sourceLocalizedStage f idx →+* R :=
  localizationAtComapMaximalToAmbient
    (A := sourceRawStage f idx) (B := R) (sourceRawStage f idx).val.toRingHom

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the ambient comparison map from a localized source stage sends a
raw generator to its ambient value in `R`. -/
private theorem source_localized_to_ambient_to_map (idx : CompatibleStageIndex f)
    (x : sourceRawStage f idx) :
    sourceLocalizedToAmbient f idx (algebraMap _ _ x) = (sourceRawStage f idx).val x := by
  -- The ambient comparison map sends each raw generator to its image in `R`.
  exact localizationAtComapMaximalToAmbient_to_map (sourceRawStage f idx).val.toRingHom x

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the ambient source comparison maps are compatible with the
localized source transition maps. -/
private theorem source_localized_to_ambient_comp {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    (sourceLocalizedToAmbient f j).comp
        (sourceLocalizedTransition f hij) =
      sourceLocalizedToAmbient f i := by
  -- The ambient source comparison maps are compatible with source transitions.
  refine IsLocalization.ringHom_ext (sourceStagePrime f i).primeCompl ?_
  ext x
  change
    sourceLocalizedToAmbient f j
        (sourceLocalizedTransition f hij (algebraMap _ _ x)) =
      sourceLocalizedToAmbient f i (algebraMap _ _ x)
  rw [source_localized_transition_to_map, source_localized_to_ambient_to_map,
    source_localized_to_ambient_to_map]
  change ((sourceRawStageInclusion f hij x : sourceRawStage f j) : R) = (x : R)
  rfl

/-- Helper for Lemma 10.127.9: the localized target stage maps canonically back to the ambient
local ring `S`. This names the textbook arrow `S_λ → S`. -/
private noncomputable abbrev targetLocalizedToAmbient (f : R →+* S) (idx : CompatibleStageIndex f) :
    targetLocalizedStage f idx →+* S :=
  localizationAtComapMaximalToAmbient
    (A := targetRawStage f idx) (B := S) (targetRawStage f idx).val.toRingHom

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the ambient comparison map from a localized target stage sends a
raw generator to its ambient value in `S`. -/
private theorem target_localized_to_ambient_to_map (idx : CompatibleStageIndex f)
    (x : targetRawStage f idx) :
    targetLocalizedToAmbient f idx (algebraMap _ _ x) = (targetRawStage f idx).val x := by
  -- The ambient comparison map sends each raw target generator to its image in `S`.
  exact localizationAtComapMaximalToAmbient_to_map (targetRawStage f idx).val.toRingHom x

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the ambient target comparison maps are compatible with the
localized target transition maps. -/
private theorem target_localized_to_ambient_comp {i j : CompatibleStageIndex f} (hij : i ≤ j) :
    (targetLocalizedToAmbient f j).comp
        (targetLocalizedTransition f hij) =
      targetLocalizedToAmbient f i := by
  -- The ambient target comparison maps are compatible with target transitions.
  refine IsLocalization.ringHom_ext (targetStagePrime f i).primeCompl ?_
  ext x
  change
    targetLocalizedToAmbient f j
        (targetLocalizedTransition f hij (algebraMap _ _ x)) =
      targetLocalizedToAmbient f i (algebraMap _ _ x)
  rw [target_localized_transition_to_map, target_localized_to_ambient_to_map,
    target_localized_to_ambient_to_map]
  change ((targetRawStageInclusion f hij x : targetRawStage f j) : S) = (x : S)
  rfl

/-- Helper for Lemma 10.127.9: the localized stage square also commutes after mapping each stage
back to the ambient local rings. This is the textbook commutative diagram. -/
private theorem localized_stage_to_ambient_commutes (idx : CompatibleStageIndex f) :
    (targetLocalizedToAmbient f idx).comp (localizedStageMap f idx) =
      f.comp (sourceLocalizedToAmbient f idx) := by
  -- The localized stage square remains commutative after mapping to the ambient rings.
  apply IsLocalization.ringHom_ext (sourceStagePrime f idx).primeCompl
  ext x
  simp only [RingHom.comp_apply]
  rw [localizedStageMap_to_map]
  rw [target_localized_to_ambient_to_map, source_localized_to_ambient_to_map]
  rfl

/-- Helper for Lemma 10.127.9: the localized source transitions form the directed system used for
the source colimit. -/
private instance sourceLocalizedDirectedSystem :
    DirectedSystem
      (fun idx : CompatibleStageIndex f ↦ sourceLocalizedStage f idx)
      (fun _ _ hij ↦ sourceLocalizedTransition f hij) where
  map_self := by
    intro i x
    -- Evaluate the identity transition equality on the chosen stage element.
    have h :=
      congrArg
        (fun g :
          sourceLocalizedStage f i →+*
            sourceLocalizedStage f i => g x)
        (source_localized_transition_id f i)
    simpa using h
  map_map := by
    intro k j i hij hjk x
    -- Evaluate the transition-composition equality on the chosen stage element.
    have h :=
      congrArg
        (fun g :
          sourceLocalizedStage f i →+*
            sourceLocalizedStage f k => g x)
        (source_localized_transition_comp f hij hjk)
    simpa [RingHom.comp_apply] using h.symm

/-- Helper for Lemma 10.127.9: the localized target transitions form the directed system used for
the target colimit. -/
private instance targetLocalizedDirectedSystem :
    DirectedSystem
      (fun idx : CompatibleStageIndex f ↦ targetLocalizedStage f idx)
      (fun _ _ hij ↦ targetLocalizedTransition f hij) where
  map_self := by
    intro i x
    -- Evaluate the identity transition equality on the chosen stage element.
    have h :=
      congrArg
        (fun g :
          targetLocalizedStage f i →+*
            targetLocalizedStage f i => g x)
        (target_localized_transition_id f i)
    simpa using h
  map_map := by
    intro k j i hij hjk x
    -- Evaluate the transition-composition equality on the chosen stage element.
    have h :=
      congrArg
        (fun g :
          targetLocalizedStage f i →+*
            targetLocalizedStage f k => g x)
        (target_localized_transition_comp f hij hjk)
    simpa [RingHom.comp_apply] using h.symm

/-- Helper for Lemma 10.127.9: each localized stage map is a local homomorphism because it is the
canonical map between localizations at the pulled-back maximal ideals. -/
private theorem localizedStageMap_isLocalHom (idx : CompatibleStageIndex f) :
    IsLocalHom (localizedStageMap f idx) := by
  -- This is exactly the standard locality theorem for canonical maps between localizations.
  simpa [localizedStageMap] using
    (Localization.isLocalHom_localRingHom
      (I := sourceStagePrime f idx)
      (J := targetStagePrime f idx)
      (f := rawStageMap f idx)
      (stage_zero_map_comap_maximal_eq f idx).symm)

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: every ambient source element already appears in some localized
source stage, namely the singleton source stage from the source proof. -/
private theorem source_localized_stage_cover (r : R) :
    ∃ idx : CompatibleStageIndex f,
      ∃ x : sourceLocalizedStage f idx,
        sourceLocalizedToAmbient f idx x = r := by
  -- A singleton stage already contains the chosen source element.
  refine ⟨sourceSingletonStageIndex f r,
    algebraMap
      (sourceRawStage f (sourceSingletonStageIndex f r))
      (sourceLocalizedStage f (sourceSingletonStageIndex f r))
      ?_, ?_⟩
  · exact ⟨r, Algebra.subset_adjoin <| mem_sourceSingletonStageIndex_source f r⟩
  · simpa using
      (source_localized_to_ambient_to_map f (sourceSingletonStageIndex f r)
        ⟨r, Algebra.subset_adjoin <| mem_sourceSingletonStageIndex_source f r⟩)

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: every ambient target element already appears in some localized
target stage, namely the singleton target stage from the source proof. -/
private theorem target_localized_stage_cover (s : S) :
    ∃ idx : CompatibleStageIndex f,
      ∃ x : targetLocalizedStage f idx,
        targetLocalizedToAmbient f idx x = s := by
  -- A singleton stage already contains the chosen target element.
  refine ⟨targetSingletonStageIndex f s,
    algebraMap
      (targetRawStage f (targetSingletonStageIndex f s))
      (targetLocalizedStage f (targetSingletonStageIndex f s))
      ?_, ?_⟩
  · exact ⟨s, Algebra.subset_adjoin <| mem_targetSingletonStageIndex_target f s⟩
  · simpa using
      (target_localized_to_ambient_to_map f (targetSingletonStageIndex f s)
        ⟨s, Algebra.subset_adjoin <| mem_targetSingletonStageIndex_target f s⟩)

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the ambient source-stage maps satisfy the compatibility relation
required to define the source direct-limit comparison map. -/
private theorem source_localized_to_ambient_compatible {i j : CompatibleStageIndex f}
    (hij : i ≤ j) (x : sourceLocalizedStage f i) :
    sourceLocalizedToAmbient f j
      (sourceLocalizedTransition f hij x) =
        sourceLocalizedToAmbient f i x := by
  -- This is the elementwise form of ambient compatibility for source transitions.
  simpa [RingHom.comp_apply] using
    congrArg
      (fun g => g x)
      (source_localized_to_ambient_comp f hij)

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: each ambient source comparison map is injective. -/
private theorem sourceLocalizedToAmbient_injective (idx : CompatibleStageIndex f) :
    Function.Injective (sourceLocalizedToAmbient f idx) := by
  exact localization_at_comap_maximal_to_ambient_injective
    (sourceRawStage f idx).val.toRingHom
    Subtype.val_injective

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the ambient target-stage maps satisfy the compatibility relation
required to define the target direct-limit comparison map. -/
private theorem target_localized_to_ambient_compatible {i j : CompatibleStageIndex f}
    (hij : i ≤ j) (x : targetLocalizedStage f i) :
    targetLocalizedToAmbient f j
      (targetLocalizedTransition f hij x) =
        targetLocalizedToAmbient f i x := by
  -- This is the elementwise form of ambient compatibility for target transitions.
  simpa [RingHom.comp_apply] using
    congrArg
      (fun g => g x)
      (target_localized_to_ambient_comp f hij)

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: each ambient target comparison map is injective. -/
private theorem targetLocalizedToAmbient_injective (idx : CompatibleStageIndex f) :
    Function.Injective (targetLocalizedToAmbient f idx) := by
  exact localization_at_comap_maximal_to_ambient_injective
    (targetRawStage f idx).val.toRingHom
    Subtype.val_injective

/-- Helper for Lemma 10.127.9: the compatible ambient source-stage maps induce the comparison map
from the source direct limit to `R`. -/
private noncomputable def sourceColimitToAmbient :
    Ring.DirectLimit
        (fun idx : CompatibleStageIndex f ↦ sourceLocalizedStage f idx)
        (fun _ _ hij ↦ sourceLocalizedTransition f hij) →+* R :=
  -- The source direct limit maps canonically to the ambient source ring.
  Ring.DirectLimit.lift
    (fun idx : CompatibleStageIndex f ↦ sourceLocalizedStage f idx)
    (fun _ _ hij ↦ sourceLocalizedTransition f hij)
    R
    (fun idx ↦ sourceLocalizedToAmbient f idx)
    (fun _ _ hij x ↦
      source_localized_to_ambient_compatible f hij x)

/-- Helper for Lemma 10.127.9: the compatible ambient target-stage maps induce the comparison map
from the target direct limit to `S`. -/
private noncomputable def targetColimitToAmbient :
    Ring.DirectLimit
        (fun idx : CompatibleStageIndex f ↦ targetLocalizedStage f idx)
        (fun _ _ hij ↦ targetLocalizedTransition f hij) →+* S :=
  -- The target direct limit maps canonically to the ambient target ring.
  Ring.DirectLimit.lift
    (fun idx : CompatibleStageIndex f ↦ targetLocalizedStage f idx)
    (fun _ _ hij ↦ targetLocalizedTransition f hij)
    S
    (fun idx ↦ targetLocalizedToAmbient f idx)
    (fun _ _ hij x ↦
      target_localized_to_ambient_compatible f hij x)

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the source direct-limit comparison map is bijective because each
stage map is injective and every element of `R` is already visible on a singleton stage. -/
private theorem source_colimit_comparison_bijective :
    Function.Bijective (sourceColimitToAmbient f) :=
  -- Stagewise injectivity together with the singleton-stage cover packages directly into the
  -- prepared direct-limit bijectivity helper.
  Ring.DirectLimit.lift_bijective_of_stagewise_injective_cover
    (g := fun idx ↦ sourceLocalizedToAmbient f idx)
    (hg := fun _ _ hij x ↦ source_localized_to_ambient_compatible f hij x)
    (fun idx ↦ sourceLocalizedToAmbient_injective f idx)
    (fun r ↦ source_localized_stage_cover f r)

omit [IsLocalRing R] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: the target direct-limit comparison map is bijective because each
stage map is injective and every element of `S` is already visible on a singleton stage. -/
private theorem target_colimit_comparison_bijective :
    Function.Bijective (targetColimitToAmbient f) :=
  -- The same packaged bijectivity argument applies on the target side.
  Ring.DirectLimit.lift_bijective_of_stagewise_injective_cover
    (g := fun idx ↦ targetLocalizedToAmbient f idx)
    (hg := fun _ _ hij x ↦ target_localized_to_ambient_compatible f hij x)
    (fun idx ↦ targetLocalizedToAmbient_injective f idx)
    (fun s ↦ target_localized_stage_cover f s)

/-- Helper for Lemma 10.127.9: the colimit square commutes on each canonical generator from a
localized source stage. -/
private theorem colimit_comm_on_generators (idx : CompatibleStageIndex f)
    (x : sourceLocalizedStage f idx) :
    ((targetColimitToAmbient f).comp
        (Ring.DirectLimit.map
          (fun i ↦ localizedStageMap f i)
          (fun _ _ hij ↦ localized_stage_square_commutes f hij)))
      (Ring.DirectLimit.of
        (fun i ↦ sourceLocalizedStage f i)
        (fun _ _ hij ↦ sourceLocalizedTransition f hij)
        idx x) =
      ((f.comp (sourceColimitToAmbient f))
        (Ring.DirectLimit.of
          (fun i ↦ sourceLocalizedStage f i)
          (fun _ _ hij ↦ sourceLocalizedTransition f hij)
          idx x)) := by
  -- The colimit square commutes on each stage generator.
  simp only [RingHom.comp_apply, Ring.DirectLimit.map_apply_of, targetColimitToAmbient,
    Ring.DirectLimit.lift_of, sourceColimitToAmbient]
  simpa [RingHom.comp_apply] using
    congrArg
      (fun g : sourceLocalizedStage f idx →+* S => g x)
      (localized_stage_to_ambient_commutes f idx)

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: each raw source stage is finitely generated over `ℤ` because it is
the adjoin of the finite source set appearing in the stage index. -/
private theorem sourceRawStage_finiteType (idx : CompatibleStageIndex f) :
    Algebra.FiniteType ℤ (sourceRawStage f idx) := by
  -- The source raw stage is literally the `ℤ`-subalgebra adjoined by a finite set of elements.
  simpa [sourceRawStage] using
    (Algebra.FiniteType.adjoin_of_finite
      (R := ℤ) (A := R) (t := (↑idx.source : Set R)) idx.source.finite_toSet)

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: each raw target stage is finitely generated over `ℤ` because it is
the adjoin of the finite target set appearing in the stage index. -/
private theorem targetRawStage_finiteType (idx : CompatibleStageIndex f) :
    Algebra.FiniteType ℤ (targetRawStage f idx) := by
  -- The target raw stage is the parallel finite-adjoin construction on the target side.
  simpa [targetRawStage] using
    (Algebra.FiniteType.adjoin_of_finite
      (R := ℤ) (A := S) (t := (↑idx.target : Set S)) idx.target.finite_toSet)

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: before localization, each raw target stage is finitely generated as
an algebra over the corresponding raw source stage by the finite target generators. -/
private theorem rawStageMap_finiteType (idx : CompatibleStageIndex f) :
    (rawStageMap f idx).FiniteType := by
  let _ : Algebra (sourceRawStage f idx) (targetRawStage f idx) := (rawStageMap f idx).toAlgebra
  -- Once the target raw stage is finite type over `ℤ`, restriction of scalars gives finite type
  -- over the intermediate source raw stage.
  rw [AlgHom.FiniteType]
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    (R := ℤ) (S := sourceRawStage f idx) (A := targetRawStage f idx)
    (hA := targetRawStage_finiteType f idx)

/-- Helper for Lemma 10.127.9: the source direct limit identifies with the ambient source ring
through the ambient stage maps. -/
private noncomputable def sourceColimitIso :
    Ring.DirectLimit
        (fun idx : CompatibleStageIndex f ↦ sourceLocalizedStage f idx)
        (fun _ _ hij ↦ sourceLocalizedTransition f hij) ≃+* R :=
  -- Upgrade the bijective comparison ring hom to a ring isomorphism.
  RingEquiv.ofBijective
    (sourceColimitToAmbient f)
    (source_colimit_comparison_bijective f)

/-- Helper for Lemma 10.127.9: the target direct limit identifies with the ambient target ring
through the ambient stage maps. -/
private noncomputable def targetColimitIso :
    Ring.DirectLimit
        (fun idx : CompatibleStageIndex f ↦ targetLocalizedStage f idx)
        (fun _ _ hij ↦ targetLocalizedTransition f hij) ≃+* S :=
  -- Upgrade the bijective target comparison ring hom to a ring isomorphism.
  RingEquiv.ofBijective
    (targetColimitToAmbient f)
    (target_colimit_comparison_bijective f)

/-- Helper for Lemma 10.127.9: after identifying the two direct limits with `R` and `S`, the
induced map on colimits is exactly the original local homomorphism `f`. -/
private theorem localized_colimit_comm :
    (targetColimitIso f).toRingHom.comp
        (Ring.DirectLimit.map
          (fun i ↦ localizedStageMap f i)
          (fun _ _ hij ↦ localized_stage_square_commutes f hij)) =
      f.comp (sourceColimitIso f).toRingHom := by
  -- The two comparison maps agree on stage generators, hence on the direct limit.
  apply Ring.DirectLimit.hom_ext
  intro idx
  ext x
  exact colimit_comm_on_generators f idx x

omit [IsLocalRing S] [IsLocalHom f] in
/-- Helper for Lemma 10.127.9: each localized source stage remains essentially of finite type over
`ℤ` because it is the localization of a finite type `ℤ`-subalgebra. -/
private theorem sourceLocalizedStage_essFiniteType (idx : CompatibleStageIndex f) :
    (Int.castRingHom (sourceLocalizedStage f idx)).EssFiniteType := by
  -- A localization of a finite-type raw source stage is essentially of finite type over `ℤ`.
  have hSourceFinite :
      (Int.castRingHom (sourceRawStage f idx)).FiniteType := by
    exact RingHom.finiteType_algebraMap.mpr (sourceRawStage_finiteType f idx)
  have hSourceLocalization :
      (algebraMap (sourceRawStage f idx)
        (sourceLocalizedStage f idx)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization
      (sourceLocalizedStage f idx)
      (sourceStagePrime f idx).primeCompl
  have hComposite :
      ((algebraMap (sourceRawStage f idx)
          (sourceLocalizedStage f idx)).comp
        (Int.castRingHom (sourceRawStage f idx))).EssFiniteType := by
    exact RingHom.EssFiniteType.comp hSourceFinite.essFiniteType hSourceLocalization
  have hcomp :
      (algebraMap (sourceRawStage f idx)
          (sourceLocalizedStage f idx)).comp
        (Int.castRingHom (sourceRawStage f idx)) =
      Int.castRingHom (sourceLocalizedStage f idx) := by
    ext n
    simp
  simpa [hcomp] using hComposite

/-- Helper for Lemma 10.127.9: each localized stage map is essentially of finite type because the
raw stage map is finite type and both source and target are localized only at pulled-back maximal
ideals. -/
private theorem localizedStageMap_essFiniteType (idx : CompatibleStageIndex f) :
    (localizedStageMap f idx).EssFiniteType := by
  -- The localized stage map inherits essential finite type from the raw stage map.
  have hTargetLocalization :
      (algebraMap (targetRawStage f idx)
        (targetLocalizedStage f idx)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization
      (targetLocalizedStage f idx)
      (targetStagePrime f idx).primeCompl
  have hComposite :
      ((algebraMap (targetRawStage f idx)
          (targetLocalizedStage f idx)).comp
        (rawStageMap f idx).toRingHom).EssFiniteType := by
    exact RingHom.EssFiniteType.comp
      (rawStageMap_finiteType f idx).essFiniteType
      hTargetLocalization
  have hcomp :
      ((localizedStageMap f idx).comp
        (algebraMap (sourceRawStage f idx)
          (sourceLocalizedStage f idx))) =
        ((algebraMap (targetRawStage f idx)
            (targetLocalizedStage f idx)).comp
          (rawStageMap f idx).toRingHom) := by
    ext x
    rw [RingHom.comp_apply, localizedStageMap_to_map]
    rfl
  have hLocalizedComposite :
      ((localizedStageMap f idx).comp
        (algebraMap (sourceRawStage f idx)
          (sourceLocalizedStage f idx))).EssFiniteType := by
    simpa [hcomp] using hComposite
  exact RingHom.EssFiniteType.of_comp
    (algebraMap (sourceRawStage f idx)
      (sourceLocalizedStage f idx))
    hLocalizedComposite

-- Proof sketch: choose finite subsets of `R` and `S` compatible with `f`, form the corresponding
-- finitely generated `ℤ`-subalgebras, localize them at the pullbacks of the maximal ideals, and
-- order the resulting local maps by inclusion. The source stages form the directed-colimit owner
-- from Lemma `10.127.8`; the target stages and comparison maps are added on top. The direct
-- limits recover `R` and `S`, and the stage maps are essentially of finite type by construction.
/-- Lemma 10.127.9: a local homomorphism `f : R →+* S` of local rings admits a directed
approximation by local homomorphisms `R_λ → S_λ` of local rings such that each `R_λ` is
essentially of finite type over `ℤ`, each `S_λ` is essentially of finite type over `R_λ`, and the
induced map on direct limits identifies with `f`. -/
@[stacks 00QT]
theorem exists_directedLocalHomApproximation (f : R →+* S) [IsLocalHom f] :
    Nonempty (DirectedLocalHomApproximation.{u, v, max u v} f) :=
  -- Assemble the directed approximation from the stagewise construction above, indexed directly
  -- by the compatible finite-subset stages.
  ⟨{ Λ := CompatibleStageIndex f
     instPreorder := inferInstance
     instNonempty := inferInstance
     instDirectedOrder := inferInstance
     RStage := fun idx ↦ sourceLocalizedStage f idx
     instCommRingRStage := fun _ ↦ inferInstance
     map := fun _ _ hij ↦ sourceLocalizedTransition f hij
     instDirectedSystemRStage := sourceLocalizedDirectedSystem f
     colimitIso := sourceColimitIso f
     instIsLocalRingRStage := fun _ ↦ inferInstance
     SStage := fun idx ↦ targetLocalizedStage f idx
     instCommRingSStage := fun _ ↦ inferInstance
     instIsLocalRingSStage := fun _ ↦ inferInstance
     stageMap := fun idx ↦ localizedStageMap f idx
     stageMap_isLocalHom := fun idx ↦ localizedStageMap_isLocalHom f idx
     targetMap := fun _ _ hij ↦ targetLocalizedTransition f hij
     instDirectedSystemTarget := targetLocalizedDirectedSystem f
     comm := fun {_ _} hij ↦ localized_stage_square_commutes f hij
     targetColimit := targetColimitIso f
     colimit_comm := localized_colimit_comm f
     source_essFiniteType := fun idx ↦ sourceLocalizedStage_essFiniteType f idx
     target_essFiniteType := fun idx ↦ localizedStageMap_essFiniteType f idx }⟩

end
