import Mathlib

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

/-- The target transition map viewed as an algebra homomorphism over the source stage `i`. -/
private theorem stageTransitionAlgHom_commutes {i j : A.Λ} (h : i ≤ j) :
    let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
    let _ : Algebra (A.RStage i) (A.SStage j) := ((A.stageMap j).comp (A.RMap i j h)).toAlgebra
    ∀ x : A.RStage i,
      A.SMap i j h (algebraMap (A.RStage i) (A.SStage i) x) =
        algebraMap (A.RStage i) (A.SStage j) x := sorry

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

-- Proof sketch: let `Λ` be the directed set of finite subsets of `R` and `S` that are stable
-- under the given ring map `f`. For each stage, take the `ℤ`-subalgebra of `R` generated by the
-- chosen source elements and the `R_λ`-subalgebra of `S` generated by the chosen target elements.
-- These stage rings are finite type in the required sense, the transition maps come from
-- inclusions, and the filtered unions recover `R` and `S`, giving the direct-limit description of
-- `f`.
/-- Lemma 10.127.14: any ring homomorphism `f : R →+* S` is the direct limit of a directed system
of ring maps `R_λ → S_λ` such that each `R_λ` is of finite type over `ℤ` and each `S_λ` is of
finite type over `R_λ`. -/
theorem exists_directedFiniteTypeHomApproximation (f : R →+* S) :
    Nonempty (DirectedFiniteTypeHomApproximation f) := sorry
