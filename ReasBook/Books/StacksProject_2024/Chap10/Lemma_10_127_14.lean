import StacksProject_2024.Chap10.Lemma_10_127_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- 
Domain sampling:
* Primary domain: directed approximation systems for commutative ring homomorphisms.
* Owner declarations inspected in this domain:
  - `Ring.DirectLimit.map`
  - `DirectedLocalHomApproximation.stageBaseChange`
  - `DirectedLocalHomApproximation.stageBaseChangeMap`
  - `RingHom.FiniteType`
* Best owner abstraction:
  - source-facing approximation owner: `DirectedFiniteTypeHomApproximation f`
* Layer triage:
  - `source-facing`: the existence theorem below
  - `core/canonical`: the stagewise directed-system data packaged by
    `DirectedFiniteTypeHomApproximation f`
  - `bridge/view`: the canonical stagewise base-change construction attached to a transition
    `i ≤ j`
* Primitive vs. derived:
  - primitive owner data: the index type, stage rings, transition maps, stage maps, finite-type
    hypotheses, and chosen direct-limit identifications
  - derived API: the canonical tensor-product source `A.stageBaseChange h` and the owner map
    `A.stageBaseChangeMap h`
-/

/-- A directed approximation of a ring homomorphism by finite-type maps whose source stages are of
finite type over `ℤ`. -/
structure DirectedFiniteTypeHomApproximation (f : R →+* S) where
  Λ : Type w
  instPreorder : Preorder Λ
  instNonempty : Nonempty Λ
  instDirectedOrder : IsDirectedOrder Λ
  RStage : Λ → Type u
  SStage : Λ → Type v
  instCommRingRStage (i : Λ) : CommRing (RStage i)
  instCommRingSStage (i : Λ) : CommRing (SStage i)
  RMap (i j : Λ) (h : i ≤ j) : RStage i →+* RStage j
  SMap (i j : Λ) (h : i ≤ j) : SStage i →+* SStage j
  instDirectedSystemRStage : DirectedSystem RStage (RMap · · ·)
  instDirectedSystemSStage : DirectedSystem SStage (SMap · · ·)
  stageMap (i : Λ) : RStage i →+* SStage i
  comm {i j : Λ} (h : i ≤ j) :
    (stageMap j).comp (RMap i j h) = (SMap i j h).comp (stageMap i)
  source_finiteType (i : Λ) : (Int.castRingHom (RStage i)).FiniteType
  target_finiteType (i : Λ) : (stageMap i).FiniteType
  colimitSource :
    Ring.DirectLimit RStage (fun i j h ↦ RMap i j h) ≃+* R
  colimitTarget :
    Ring.DirectLimit SStage (fun i j h ↦ SMap i j h) ≃+* S
  colimit_comm :
    colimitTarget.toRingHom.comp (Ring.DirectLimit.map stageMap (fun _ _ h ↦ comm h)) =
      f.comp colimitSource.toRingHom

attribute [instance] DirectedFiniteTypeHomApproximation.instPreorder
attribute [instance] DirectedFiniteTypeHomApproximation.instNonempty
attribute [instance] DirectedFiniteTypeHomApproximation.instDirectedOrder
attribute [instance] DirectedFiniteTypeHomApproximation.instCommRingRStage
attribute [instance] DirectedFiniteTypeHomApproximation.instCommRingSStage
attribute [instance] DirectedFiniteTypeHomApproximation.instDirectedSystemRStage
attribute [instance] DirectedFiniteTypeHomApproximation.instDirectedSystemSStage

namespace DirectedFiniteTypeHomApproximation

variable {f : R →+* S} (A : DirectedFiniteTypeHomApproximation f)

/-- The tensor-product source of the canonical base-change map from stage `i` to stage `j`. -/
abbrev stageBaseChange {i j : A.Λ} (h : i ≤ j) : Type _ :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
  A.SStage i ⊗[A.RStage i] A.RStage j

-- Proof sketch: rewrite the square-commutativity field `A.comm h` pointwise and interpret the
-- algebra maps using the chosen `RingHom.toAlgebra` structures.
/-- The target transition map is an algebra homomorphism over the source stage `i`. -/
private theorem stageTransitionAlgHom_commutes {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j h)).toAlgebra
    ∀ x : A.RStage i,
      A.SMap i j h (algebraMap (A.RStage i) (A.SStage i) x) =
        algebraMap (A.RStage i) (A.SStage j) x := by
  dsimp
  intro x
  -- Rewrite the algebra maps coming from `RingHom.toAlgebra` and read off the commutative square.
  have hcomm :
      ((A.SMap i j h).comp (A.stageMap i)) x =
        ((A.stageMap j).comp (A.RMap i j h)) x :=
    congrArg (fun g : A.RStage i →+* A.SStage j => g x) ((A.comm h).symm)
  simpa [RingHom.algebraMap_toAlgebra] using hcomm

/-- The target transition map as an algebra homomorphism over the source stage `i`. -/
private noncomputable def stageTransitionAlgHom {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j h)).toAlgebra
    A.SStage i →ₐ[A.RStage i] A.SStage j :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j h)).toAlgebra
  { toRingHom := A.SMap i j h
    commutes' := A.stageTransitionAlgHom_commutes h }

/-- The canonical base-change map `Sᵢ ⊗[Rᵢ] Rⱼ → Sⱼ` attached to a transition `i ≤ j`. -/
noncomputable def stageBaseChangeMap {i j : A.Λ} (h : i ≤ j) :
    A.stageBaseChange h →+* A.SStage j :=
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra (A.RStage i) (A.RStage j) := (A.RMap i j h).toAlgebra
  let _ : Algebra (A.RStage j) (A.SStage j) := (A.stageMap j).toAlgebra
  let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j h)).toAlgebra
  let _ : IsScalarTower (A.RStage i) (A.RStage j) (A.SStage j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.productMap (A.stageTransitionAlgHom h)
    (IsScalarTower.toAlgHom (A.RStage i) (A.RStage j) (A.SStage j))).toRingHom

end DirectedFiniteTypeHomApproximation

section

variable (f : R →+* S)

/-- Helper for Lemma 10.127.14: an index records finitely many source elements of `R` and finitely
many target generators in `S`. This is the controlling directed object from the source proof. -/
private structure FiniteTypeApproximationIndex (f : R →+* S) where
  source : Finset R
  target : Finset S

namespace FiniteTypeApproximationIndex

instance : LE (FiniteTypeApproximationIndex f) where
  le i j := i.source ⊆ j.source ∧ i.target ⊆ j.target

instance : Preorder (FiniteTypeApproximationIndex f) where
  le_refl i := ⟨by intro x hx; exact hx, by intro x hx; exact hx⟩
  le_trans i j k hij hjk := ⟨hij.1.trans hjk.1, hij.2.trans hjk.2⟩

/-- Helper for Lemma 10.127.14: the empty source and target data define a trivial stage. -/
private instance : Nonempty (FiniteTypeApproximationIndex f) :=
  ⟨{ source := ∅, target := ∅ }⟩

/-- Helper for Lemma 10.127.14: unions of finite source and target data give a common upper bound,
so the index set is directed. -/
private instance : IsDirectedOrder (FiniteTypeApproximationIndex f) := by
  classical
  refine ⟨?_⟩
  intro i j
  refine ⟨
    { source := i.source ∪ j.source
      target := i.target ∪ j.target },
    ?_,
    ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inl hx
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inl hx
  · refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inr hx
    · intro x hx
      exact Finset.mem_union.mpr <| Or.inr hx

end FiniteTypeApproximationIndex

namespace FiniteTypeApproximationData

/-- Helper for Lemma 10.127.14: the source stage is the `ℤ`-subalgebra of `R` generated by the
chosen finite source set. -/
private abbrev sourceStage (i : FiniteTypeApproximationIndex f) : Subalgebra ℤ R :=
  Algebra.adjoin ℤ (i.source : Set R)

/-- Helper for Lemma 10.127.14: the ambient map from a source stage into `S` is the restriction of
the given ring map `f`. -/
private abbrev sourceStageToTargetAmbient (i : FiniteTypeApproximationIndex f) :
    sourceStage f i →+* S :=
  f.comp (sourceStage f i).val.toRingHom

/-- Helper for Lemma 10.127.14: each source stage inherits its ambient `S`-algebra structure from
the restricted map to `S`. -/
private noncomputable instance instAlgebraSourceStage (i : FiniteTypeApproximationIndex f) :
    Algebra (sourceStage f i) S :=
  (sourceStageToTargetAmbient f i).toAlgebra

/-- Helper for Lemma 10.127.14: the target stage is generated over the source stage by the chosen
finite target set and then viewed again as a `ℤ`-subalgebra of `S`. -/
private abbrev targetStage (i : FiniteTypeApproximationIndex f) : Subalgebra ℤ S :=
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  (Algebra.adjoin (sourceStage f i) (i.target : Set S)).restrictScalars ℤ

/-- Helper for Lemma 10.127.14: enlarging the finite source set enlarges the source stage. -/
private theorem sourceStage_mono {i j : FiniteTypeApproximationIndex f} (hij : i ≤ j) :
    sourceStage f i ≤ sourceStage f j :=
  Algebra.adjoin_mono hij.1

/-- Helper for Lemma 10.127.14: the image in `S` of a smaller source stage is contained in the
image of any larger source stage. -/
private theorem sourceStageRange_mono {i j : FiniteTypeApproximationIndex f} (hij : i ≤ j) :
    ((IsScalarTower.toAlgHom ℤ (sourceStage f i) S).range : Set S) ⊆
      ((IsScalarTower.toAlgHom ℤ (sourceStage f j) S).range : Set S) := by
  rintro x ⟨y, rfl⟩
  -- Reuse the canonical inclusion between nested source subalgebras.
  exact ⟨Subalgebra.inclusion (sourceStage_mono (f := f) hij) y, rfl⟩

/-- Helper for Lemma 10.127.14: after restricting scalars back to `ℤ`, the target stage is the
`ℤ`-subalgebra generated by the image of the source stage in `S` together with the chosen target
generators. -/
private theorem targetStage_eq_adjoin_union (i : FiniteTypeApproximationIndex f) :
    targetStage f i =
      Algebra.adjoin ℤ
        (((IsScalarTower.toAlgHom ℤ (sourceStage f i) S).range : Set S) ∪ (i.target : Set S)) := by
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  have hrange :
      targetStage f i =
        (Algebra.adjoin
          (IsScalarTower.toAlgHom ℤ (sourceStage f i) S).range
          (i.target : Set S)).restrictScalars ℤ := by
    -- Route correction: rewrite through the image subalgebra inside `S`, not through the source
    -- stage viewed abstractly.
    simpa [targetStage] using
      (IsScalarTower.adjoin_range_toAlgHom
        (R := ℤ) (S := sourceStage f i) (A := S) (t := (i.target : Set S))).symm
  rw [hrange, Algebra.restrictScalars_adjoin]

/-- Helper for Lemma 10.127.14: enlarging both the source and target finite sets enlarges the
target stage. -/
private theorem targetStage_mono {i j : FiniteTypeApproximationIndex f} (hij : i ≤ j) :
    targetStage f i ≤ targetStage f j := by
  -- Rewrite both target stages as ambient `ℤ`-adjoins and then apply monotonicity.
  rw [targetStage_eq_adjoin_union (f := f) i, targetStage_eq_adjoin_union (f := f) j]
  refine Algebra.adjoin_mono ?_
  exact Set.union_subset
    (fun x hx ↦ Or.inl <| sourceStageRange_mono (f := f) hij hx)
    (fun x hx ↦ Or.inr <| hij.2 hx)

/-- Helper for Lemma 10.127.14: the transition maps on source stages are the obvious subtype
inclusions. -/
private abbrev sourceTransition {i j : FiniteTypeApproximationIndex f} (hij : i ≤ j) :
    sourceStage f i →+* sourceStage f j :=
  Subalgebra.inclusion (sourceStage_mono (f := f) hij)

/-- Helper for Lemma 10.127.14: the transition maps on target stages are the obvious subtype
inclusions. -/
private abbrev targetTransition {i j : FiniteTypeApproximationIndex f} (hij : i ≤ j) :
    targetStage f i →+* targetStage f j :=
  Subalgebra.inclusion (targetStage_mono (f := f) hij)

/-- Helper for Lemma 10.127.14: the source-stage inclusions form a directed system because
subalgebra inclusions compose strictly. -/
private instance sourceDirectedSystem :
    DirectedSystem
      (fun i : FiniteTypeApproximationIndex f ↦ sourceStage f i)
      (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij) := by
  refine ⟨?_, ?_⟩
  · intro i x
    rfl
  · intro k j i hij hjk x
    -- Composition of source-stage inclusions is the canonical inclusion to the top stage.
    simpa using
      (Subalgebra.inclusion_inclusion
        (sourceStage_mono (f := f) hij)
        (sourceStage_mono (f := f) hjk)
        x)

/-- Helper for Lemma 10.127.14: the target-stage inclusions form a directed system for the same
reason. -/
private instance targetDirectedSystem :
    DirectedSystem
      (fun i : FiniteTypeApproximationIndex f ↦ targetStage f i)
      (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij) := by
  refine ⟨?_, ?_⟩
  · intro i x
    rfl
  · intro k j i hij hjk x
    -- Composition of target-stage inclusions is again the canonical inclusion.
    simpa using
      (Subalgebra.inclusion_inclusion
        (targetStage_mono (f := f) hij)
        (targetStage_mono (f := f) hjk)
        x)

/-- Helper for Lemma 10.127.14: each stage map is the algebra map from the source stage to the
target stage generated over it. -/
private abbrev stageMap (i : FiniteTypeApproximationIndex f) :
    sourceStage f i →+* targetStage f i :=
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  algebraMap (sourceStage f i) (Algebra.adjoin (sourceStage f i) (i.target : Set S))

/-- Helper for Lemma 10.127.14: the ambient source-stage inclusions are pointwise compatible with
the source transition maps. -/
private theorem sourceStageToAmbient_compatible {i j : FiniteTypeApproximationIndex f}
    (hij : i ≤ j) (x : sourceStage f i) :
    (sourceStage f j).val.toRingHom
        (sourceTransition (f := f) (i := i) (j := j) hij x) =
      (sourceStage f i).val.toRingHom x := by
  -- The source transition is the subtype inclusion between nested source stages.
  change ((sourceTransition (f := f) (i := i) (j := j) hij x : sourceStage f j) : R) = (x : R)
  rfl

/-- Helper for Lemma 10.127.14: the ambient target-stage inclusions are pointwise compatible with
the target transition maps. -/
private theorem targetStageToAmbient_compatible {i j : FiniteTypeApproximationIndex f}
    (hij : i ≤ j) (x : targetStage f i) :
    (targetStage f j).val.toRingHom
        (targetTransition (f := f) (i := i) (j := j) hij x) =
      (targetStage f i).val.toRingHom x := by
  -- The target transition is likewise the subtype inclusion between nested target stages.
  change ((targetTransition (f := f) (i := i) (j := j) hij x : targetStage f j) : S) = (x : S)
  rfl

/-- Helper for Lemma 10.127.14: after mapping a stage to the ambient target ring, the stage map is
just the original ambient ring map `f` restricted to the source stage. -/
private theorem stage_to_ambient_commutes (i : FiniteTypeApproximationIndex f) :
    (targetStage f i).val.toRingHom.comp (stageMap f i) =
      f.comp (sourceStage f i).val.toRingHom := by
  -- The stage map is the ambient algebra map into the target-stage subalgebra.
  ext x
  rfl

/-- Helper for Lemma 10.127.14: each source stage is of finite type over `ℤ` because it is
generated by a finite set. -/
private theorem sourceStage_finiteType (i : FiniteTypeApproximationIndex f) :
    (Int.castRingHom (sourceStage f i)).FiniteType := by
  -- The source stage is literally the `ℤ`-subalgebra adjoined by a finite source set.
  exact RingHom.finiteType_algebraMap.mpr <|
    by
      simpa [sourceStage] using
        (Algebra.FiniteType.adjoin_of_finite
          (R := ℤ) (A := R) (t := (i.source : Set R))
          i.source.finite_toSet)

/-- Helper for Lemma 10.127.14: each stage map is of finite type because the target stage is
adjoined over the source stage by a finite target set. -/
private theorem stageMap_finiteType (i : FiniteTypeApproximationIndex f) :
    RingHom.FiniteType (stageMap f i) := by
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  -- View the target stage as the algebra adjoin over the source stage and apply finite adjoin.
  change RingHom.FiniteType
    (algebraMap (sourceStage f i) (Algebra.adjoin (sourceStage f i) (i.target : Set S)))
  exact RingHom.finiteType_algebraMap.mpr <|
    by
      simpa using
        (Algebra.FiniteType.adjoin_of_finite
          (R := sourceStage f i) (A := S) (t := (i.target : Set S))
          i.target.finite_toSet)

/-- Helper for Lemma 10.127.14: the left path around the stage square has the expected ambient
value on each source-stage element. -/
private theorem stage_square_left_to_ambient_apply {i j : FiniteTypeApproximationIndex f}
    (hij : i ≤ j) (x : sourceStage f i) :
    (targetStage f j).val.toRingHom
        ((stageMap f j) (sourceTransition (f := f) (i := i) (j := j) hij x)) =
      f ((sourceStage f i).val.toRingHom x) := by
  -- First evaluate the stage-`j` square in the ambient ring `S`.
  have hstage :
      ((targetStage f j).val.toRingHom.comp (stageMap f j))
          (sourceTransition (f := f) (i := i) (j := j) hij x) =
        (f.comp (sourceStage f j).val.toRingHom)
          (sourceTransition (f := f) (i := i) (j := j) hij x) := by
    simpa using
      congrArg
        (fun g : sourceStage f j →+* S =>
          g (sourceTransition (f := f) (i := i) (j := j) hij x))
        (stage_to_ambient_commutes (f := f) j)
  -- Then rewrite the source-stage inclusion back to the original element of `R`.
  calc
    (targetStage f j).val.toRingHom
        ((stageMap f j) (sourceTransition (f := f) (i := i) (j := j) hij x)) =
      (f.comp (sourceStage f j).val.toRingHom)
        (sourceTransition (f := f) (i := i) (j := j) hij x) := by
          simpa [RingHom.comp_apply] using hstage
    _ = f ((sourceStage f i).val.toRingHom x) := by
      rw [RingHom.comp_apply,
        sourceStageToAmbient_compatible (f := f) (i := i) (j := j) hij x]

/-- Helper for Lemma 10.127.14: the right path around the stage square has the same ambient value
on each source-stage element. -/
private theorem stage_square_right_to_ambient_apply {i j : FiniteTypeApproximationIndex f}
    (hij : i ≤ j) (x : sourceStage f i) :
    (targetStage f j).val.toRingHom
        ((targetTransition (f := f) (i := i) (j := j) hij) ((stageMap f i) x)) =
      f ((sourceStage f i).val.toRingHom x) := by
  -- First rewrite the target transition as the ambient subtype inclusion on target stages.
  calc
    (targetStage f j).val.toRingHom
        ((targetTransition (f := f) (i := i) (j := j) hij) ((stageMap f i) x)) =
      (targetStage f i).val.toRingHom ((stageMap f i) x) := by
          simpa using
            targetStageToAmbient_compatible (f := f) (i := i) (j := j) hij ((stageMap f i) x)
    _ = f ((sourceStage f i).val.toRingHom x) := by
      -- Now evaluate the stage-`i` square in the ambient ring `S`.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun g : sourceStage f i →+* S => g x)
          (stage_to_ambient_commutes (f := f) i)

/-- Helper for Lemma 10.127.14: the stage square commutes because both composites have the same
ambient value on each source-stage element. -/
private theorem stage_square_commutes {i j : FiniteTypeApproximationIndex f} (hij : i ≤ j) :
    (stageMap f j).comp (sourceTransition (f := f) (i := i) (j := j) hij) =
      (targetTransition (f := f) (i := i) (j := j) hij).comp (stageMap f i) := by
  -- Route correction: compare both composites only after evaluating in the ambient ring `S`.
  ext x
  have hleft :
      (targetStage f j).val.toRingHom
          (((stageMap f j).comp (sourceTransition (f := f) (i := i) (j := j) hij)) x) =
        f ((sourceStage f i).val.toRingHom x) := by
    simpa [RingHom.comp_apply] using
      stage_square_left_to_ambient_apply (f := f) (i := i) (j := j) hij x
  have hright :
      f ((sourceStage f i).val.toRingHom x) =
        (targetStage f j).val.toRingHom
          (((targetTransition (f := f) (i := i) (j := j) hij).comp (stageMap f i)) x) := by
    simpa [RingHom.comp_apply] using
      (stage_square_right_to_ambient_apply (f := f) (i := i) (j := j) hij x).symm
  -- Both composites evaluate to the same ambient element.
  exact hleft.trans hright

/-- Helper for Lemma 10.127.14: every element of `R` already occurs on a singleton source stage. -/
private theorem source_stage_cover (r : R) :
    ∃ i : FiniteTypeApproximationIndex f, r ∈ sourceStage f i := by
  classical
  refine ⟨{ source := {r}, target := ∅ }, ?_⟩
  -- The chosen source element is one of the adjoin generators at this stage.
  exact Algebra.subset_adjoin (by simp)

/-- Helper for Lemma 10.127.14: every element of `S` already occurs on a singleton target stage. -/
private theorem target_stage_cover (s : S) :
    ∃ i : FiniteTypeApproximationIndex f, s ∈ targetStage f i := by
  classical
  let i : FiniteTypeApproximationIndex f := { source := ∅, target := {s} }
  let _ : Algebra (sourceStage f i) S := (sourceStageToTargetAmbient f i).toAlgebra
  refine ⟨i, ?_⟩
  -- The chosen target element is one of the adjoined generators at this stage.
  simpa [i, targetStage] using
    (Algebra.subset_adjoin (R := sourceStage f i) (x := s) (Set.mem_singleton s))

/-- Helper for Lemma 10.127.14: the canonical source-stage inclusion into `R` is the ambient map
used to compare the source direct limit with `R`. -/
private abbrev sourceStageToAmbient (i : FiniteTypeApproximationIndex f) : sourceStage f i →+* R :=
  (sourceStage f i).val.toRingHom

/-- Helper for Lemma 10.127.14: the canonical target-stage inclusion into `S` is the ambient map
used to compare the target direct limit with `S`. -/
private abbrev targetStageToAmbient (i : FiniteTypeApproximationIndex f) : targetStage f i →+* S :=
  (targetStage f i).val.toRingHom

/-- Helper for Lemma 10.127.14: the source direct-limit comparison map is the lift of the ambient
source-stage inclusions. -/
private noncomputable def sourceColimitToAmbient :
    Ring.DirectLimit
        (fun i : FiniteTypeApproximationIndex f ↦ sourceStage f i)
        (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij) →+* R :=
  Ring.DirectLimit.lift
    (fun i : FiniteTypeApproximationIndex f ↦ sourceStage f i)
    (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij)
    R
    (fun i ↦ sourceStageToAmbient (f := f) i)
    (fun i j hij x ↦ sourceStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)

/-- Helper for Lemma 10.127.14: the target direct-limit comparison map is the lift of the ambient
target-stage inclusions. -/
private noncomputable def targetColimitToAmbient :
    Ring.DirectLimit
        (fun i : FiniteTypeApproximationIndex f ↦ targetStage f i)
        (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij) →+* S :=
  Ring.DirectLimit.lift
    (fun i : FiniteTypeApproximationIndex f ↦ targetStage f i)
    (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij)
    S
    (fun i ↦ targetStageToAmbient (f := f) i)
    (fun i j hij x ↦ targetStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)

/-- Helper for Lemma 10.127.14: the source direct-limit comparison is bijective because every
ambient source element already appears on a singleton stage. -/
private theorem sourceColimitToAmbient_bijective :
    Function.Bijective (sourceColimitToAmbient (f := f)) := by
  -- Combine stagewise injectivity with the singleton-stage cover on `R`.
  simpa [sourceColimitToAmbient] using
    (Ring.DirectLimit.lift_bijective_of_stagewise_injective_cover
      (A := fun i : FiniteTypeApproximationIndex f ↦ sourceStage f i)
      (map := fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij)
      (B := R)
      (g := fun i ↦ sourceStageToAmbient (f := f) i)
      (hg := fun i j hij x ↦
        sourceStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)
      (hinj := fun _ ↦ Subtype.val_injective)
      (hcover := fun r ↦ by
        rcases source_stage_cover (f := f) r with ⟨i, hr⟩
        exact ⟨i, ⟨r, hr⟩, rfl⟩))

/-- Helper for Lemma 10.127.14: the target direct-limit comparison is bijective because every
ambient target element already appears on a singleton target stage. -/
private theorem targetColimitToAmbient_bijective :
    Function.Bijective (targetColimitToAmbient (f := f)) := by
  -- The same packaged direct-limit criterion applies on the target side.
  simpa [targetColimitToAmbient] using
    (Ring.DirectLimit.lift_bijective_of_stagewise_injective_cover
      (A := fun i : FiniteTypeApproximationIndex f ↦ targetStage f i)
      (map := fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij)
      (B := S)
      (g := fun i ↦ targetStageToAmbient (f := f) i)
      (hg := fun i j hij x ↦
        targetStageToAmbient_compatible (f := f) (i := i) (j := j) hij x)
      (hinj := fun _ ↦ Subtype.val_injective)
      (hcover := fun s ↦ by
        rcases target_stage_cover (f := f) s with ⟨i, hs⟩
        exact ⟨i, ⟨s, hs⟩, rfl⟩))

/-- Helper for Lemma 10.127.14: the source direct limit identifies with `R` via the ambient
subtype maps. -/
private noncomputable def sourceColimitIso :
    Ring.DirectLimit
        (fun i : FiniteTypeApproximationIndex f ↦ sourceStage f i)
        (fun i j hij ↦ sourceTransition (f := f) (i := i) (j := j) hij) ≃+* R :=
  -- Upgrade the bijective source comparison map to a ring equivalence.
  RingEquiv.ofBijective
    (sourceColimitToAmbient (f := f))
    (sourceColimitToAmbient_bijective (f := f))

/-- Helper for Lemma 10.127.14: the target direct limit identifies with `S` via the ambient
subtype maps. -/
private noncomputable def targetColimitIso :
    Ring.DirectLimit
        (fun i : FiniteTypeApproximationIndex f ↦ targetStage f i)
        (fun i j hij ↦ targetTransition (f := f) (i := i) (j := j) hij) ≃+* S :=
  -- Upgrade the bijective target comparison map to a ring equivalence.
  RingEquiv.ofBijective
    (targetColimitToAmbient (f := f))
    (targetColimitToAmbient_bijective (f := f))

/-- Helper for Lemma 10.127.14: before passing to the chosen colimit isomorphisms, the induced map
on direct limits agrees with the ambient map `f` on each canonical source-stage generator. -/
private theorem colimit_comm_toAmbient_on_generators (i : FiniteTypeApproximationIndex f)
    (x : sourceStage f i) :
    ((targetColimitToAmbient (f := f)).comp
        (Ring.DirectLimit.map
          (fun j ↦ stageMap f j)
          (fun j k hjk ↦ stage_square_commutes (f := f) (i := j) (j := k) hjk)))
      (Ring.DirectLimit.of
        (fun j : FiniteTypeApproximationIndex f ↦ sourceStage f j)
        (fun j k hjk ↦ sourceTransition (f := f) (i := j) (j := k) hjk)
        i x) =
      ((f.comp (sourceColimitToAmbient (f := f)))
        (Ring.DirectLimit.of
          (fun j : FiniteTypeApproximationIndex f ↦ sourceStage f j)
          (fun j k hjk ↦ sourceTransition (f := f) (i := j) (j := k) hjk)
          i x)) := by
  -- Evaluate both colimit maps on the same stage generator and read off the ambient stage square.
  rw [RingHom.comp_apply, Ring.DirectLimit.map_apply_of, targetColimitToAmbient,
    Ring.DirectLimit.lift_of, sourceColimitToAmbient, RingHom.comp_apply, Ring.DirectLimit.lift_of]
  simpa [RingHom.comp_apply] using
    congrArg
      (fun g : sourceStage f i →+* S => g x)
      (stage_to_ambient_commutes (f := f) i)

/-- Helper for Lemma 10.127.14: before identifying the direct limits with `R` and `S`, the map on
colimits induced by the stage maps is exactly the ambient ring map `f`. -/
private theorem colimit_comm_toAmbient :
    (targetColimitToAmbient (f := f)).comp
        (Ring.DirectLimit.map
          (fun i ↦ stageMap f i)
          (fun i j hij ↦ stage_square_commutes (f := f) (i := i) (j := j) hij)) =
      f.comp (sourceColimitToAmbient (f := f)) := by
  -- Direct-limit ring homomorphisms agree once they agree on each canonical stage generator.
  apply Ring.DirectLimit.hom_ext
  intro i
  ext x
  exact colimit_comm_toAmbient_on_generators (f := f) i x

/-- Helper for Lemma 10.127.14: after identifying both direct limits with the ambient rings, the
induced colimit map is exactly the original ring map `f`. -/
private theorem colimit_comm :
    (targetColimitIso (f := f)).toRingHom.comp
        (Ring.DirectLimit.map
          (fun i ↦ stageMap f i)
          (fun i j hij ↦ stage_square_commutes (f := f) (i := i) (j := j) hij)) =
      f.comp (sourceColimitIso (f := f)).toRingHom := by
  -- The iso-level statement is the ambient comparison rewritten through `RingEquiv.ofBijective`.
  simpa [sourceColimitIso, targetColimitIso] using
    (colimit_comm_toAmbient (f := f))

end FiniteTypeApproximationData

-- Proof sketch: let `Λ` be the directed set of finite subsets of `R` and `S`. For each stage,
-- take the `ℤ`-subalgebra of `R` generated by the chosen source elements and the subalgebra of `S`
-- generated over it by the chosen target elements. These stages are finite type in the required
-- sense, the transition maps are inclusions, and the filtered unions recover `R` and `S`.
/-- Lemma 10.127.14: any ring homomorphism `f : R →+* S` is the direct limit of a directed system
of ring maps `R_λ → S_λ` such that each `R_λ` is of finite type over `ℤ` and each `S_λ` is of
finite type over `R_λ`. -/
theorem exists_directedFiniteTypeHomApproximation (f : R →+* S) :
    Nonempty (DirectedFiniteTypeHomApproximation.{u, v, max u v} f) := by
  classical
  let A : DirectedFiniteTypeHomApproximation.{u, v, max u v} f :=
    { Λ := FiniteTypeApproximationIndex f
      instPreorder := inferInstance
      instNonempty := inferInstance
      instDirectedOrder := inferInstance
      RStage := fun i ↦ FiniteTypeApproximationData.sourceStage f i
      SStage := fun i ↦ FiniteTypeApproximationData.targetStage f i
      instCommRingRStage := fun _ ↦ inferInstance
      instCommRingSStage := fun _ ↦ inferInstance
      RMap := fun i j hij ↦
        FiniteTypeApproximationData.sourceTransition (f := f) (i := i) (j := j) hij
      SMap := fun i j hij ↦
        FiniteTypeApproximationData.targetTransition (f := f) (i := i) (j := j) hij
      instDirectedSystemRStage := FiniteTypeApproximationData.sourceDirectedSystem (f := f)
      instDirectedSystemSStage := FiniteTypeApproximationData.targetDirectedSystem (f := f)
      stageMap := FiniteTypeApproximationData.stageMap f
      comm := fun {i j} hij ↦
        FiniteTypeApproximationData.stage_square_commutes (f := f) (i := i) (j := j) hij
      source_finiteType := FiniteTypeApproximationData.sourceStage_finiteType (f := f)
      target_finiteType := FiniteTypeApproximationData.stageMap_finiteType (f := f)
      colimitSource := FiniteTypeApproximationData.sourceColimitIso (f := f)
      colimitTarget := FiniteTypeApproximationData.targetColimitIso (f := f)
      colimit_comm := FiniteTypeApproximationData.colimit_comm (f := f) }
  -- Package the stagewise construction into the approximation structure.
  exact ⟨A⟩

end
