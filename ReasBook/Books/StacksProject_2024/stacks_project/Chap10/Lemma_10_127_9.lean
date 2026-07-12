import StacksProject_2024.Chap10.Lemma_10_127_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-- A directed approximation of a local ring homomorphism by local maps whose source stages are
essentially of finite type over `ℤ` and whose target stages are essentially of finite type over the
corresponding source stages. The source-side directed colimit data is primitive here, while
`Lemma_10_127_8` handles the canonical filtered-colimit descent API built on top of it. -/
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
      Ring.DirectLimit.of A.SStage (fun i j h ↦ A.targetMap i j h) i (A.stageMap i x) := sorry

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
        algebraMap (A.RStage i) (A.SStage j) x := sorry

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
        algebraMap (A.RStage i) (A.SStage j) x := sorry

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
        A.stageBaseChangeMap h (x ⊗ₜ[A.RStage i] y) = A.targetMap i j h x * A.stageMap j y := sorry

end DirectedLocalHomApproximation

-- Proof sketch: choose finite subsets of `R` and `S` compatible with `f`, form the corresponding
-- finitely generated `ℤ`-subalgebras, localize them at the pullbacks of the maximal ideals, and
-- order the resulting local maps by inclusion. The source stages form the directed-colimit owner
-- from Lemma `10.127.8`; the target stages and comparison maps are added on top. The direct
-- limits recover `R` and `S`, and the stage maps are essentially of finite type by construction.
/-- Lemma 10.127.9: a local homomorphism `f : R →+* S` of local rings admits a directed
approximation by local homomorphisms `R_λ → S_λ` of local rings such that each `R_λ` is
essentially of finite type over `ℤ`, each `S_λ` is essentially of finite type over `R_λ`, and the
induced map on direct limits identifies with `f`. -/
theorem exists_directedLocalHomApproximation (f : R →+* S) [IsLocalHom f] :
    Nonempty (DirectedLocalHomApproximation f) := sorry
