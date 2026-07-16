import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_143_3
import stacks_proof.stacks_project.Chap10.Lemma_10_127_7
import stacks_proof.stacks_project.Chap10.Lemma_10_138_15
import stacks_proof.stacks_project.Chap10.Lemma_10_168_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TensorProduct

universe u v

/-
Domain-style sampling:
- primary domain: étale base-change descent for finitely presented morphisms along filtered colimits
  of commutative algebras;
- sampled owner API:
  `RingHom.Etale`,
  `RingHom.etale_iff_formallyUnramified_and_smooth`,
  `finite_type_unramified_baseChange_descends_to_stage`,
  `smooth_is_baseChange_of_stage_of_isColimit`;
- source-facing: the Stacks lemma saying a finitely presented map whose colimit base change is
  étale is already étale after base change to some stage;
- core/canonical: the owner property `RingHom.Etale`, together with the upstream owner descent
  theorems for its unramified and smooth pieces;
- bridge/view: this file stays at the bridge layer, assembling the owner-level descent statements
  for the specific tensor-product base changes attached to a fixed `A₀`-algebra map `φ₀`.

Primitive data are the filtered diagram `F`, the finitely presented map `φ₀`, and the colimit-stage
étale hypothesis. Smoothness and formal unramifiedness of the base-changed map are derived owner
API, so this file should treat the theorem as a bridge over `RingHom.Etale` rather than introducing
any auxiliary wrapper for the stage data.
-/

section

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀] [Algebra A₀ B₀] [Algebra A₀ C₀]

/-- Helper for Lemma 10.168.7: an étale colimit base change is already unramified at some stage.
-/
lemma stage_unramified_of_colimit_etale
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    ∃ j : J,
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := by
  -- Proof comment: finite presentation implies finite type, so the earlier unramified descent
  -- theorem applies directly to the formally-unramified half of the colimit-stage étale map.
  exact finite_type_unramified_baseChange_descends_to_stage
    (F := F) φ₀ (AlgHom.FiniteType.of_finitePresentation hφ₀) hEt.formallyUnramified

/-- Helper for Lemma 10.168.7: on a fixed stage of the filtered system, the tensor-product
base-change map is étale as soon as its stage algebra is both unramified and smooth. -/
lemma tensor_base_change_etale_of_stage_unramified_and_smooth
    {j : J}
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hUnramified :
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)))
    (hSmooth : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Smooth) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  let f := (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom
  -- Reinterpret the stagewise algebra-level unramified owner as the ring-hom owner.
  have hFormallyUnramified : f.FormallyUnramified := by
    letI := f.toAlgebra
    change Algebra.FormallyUnramified
      (B₀ ⊗[A₀] ↑(F.obj j))
      (C₀ ⊗[A₀] ↑(F.obj j))
    exact hUnramified.formallyUnramified
  have hSmooth' : f.Smooth := by
    simpa using hSmooth
  -- The canonical owner characterization of étale closes the fixed-stage problem.
  exact (RingHom.etale_iff_formallyUnramified_and_smooth f).2 ⟨hFormallyUnramified, hSmooth'⟩

/-- Helper for Lemma 10.168.7: the map-level finite-presentation hypothesis on `φ₀` is exactly the
algebra-level finite-presentation instance needed to choose a fixed presentation of `C₀` over
`B₀`. -/
lemma algebra_finitePresentation_of_hom_finitePresentation
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    Algebra.FinitePresentation B₀ C₀ := by
  -- Unfold the owner predicates once so the map-level and algebra-level formulations coincide.
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using hφ₀

/-- Helper for Chap10 Lemma 10 168 7: the standard `comm` and `cancelBaseChange`
normalization identifies the literal base change `S ⊗[B₀] C₀` with the canonical tensor target
`C₀ ⊗[A₀] F.obj j` as rings. -/
noncomputable abbrev tensorStageTargetRingEquiv
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    (S ⊗[B₀] C₀) ≃+* (C₀ ⊗[A₀] ↑(F.obj j)) :=
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange
      (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j))).toRingEquiv

/-- Helper for Chap10 Lemma 10 168 7: the stage-target ring equivalence is compatible with the
canonical algebra maps from `B₀ ⊗[A₀] F.obj j`. -/
lemma tensorStageTargetRingEquiv_commutes
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S (C₀ ⊗[A₀] ↑(F.obj j)) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    ∀ x : S,
      tensorStageTargetRingEquiv (F := F) φ₀ j (algebraMap S (S ⊗[B₀] C₀) x) =
        algebraMap S (C₀ ⊗[A₀] ↑(F.obj j)) x := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S (C₀ ⊗[A₀] ↑(F.obj j)) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  intro x
  -- Proof comment: it is enough to check the compatibility on pure tensor generators of the
  -- source stage algebra `S = B₀ ⊗[A₀] F.obj j`.
  refine TensorProduct.induction_on x ?zero ?tmul ?add
  · simp
  · intro b r
    change
      (Algebra.TensorProduct.cancelBaseChange
        (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j)))
        ((1 : C₀) ⊗ₜ[B₀] ((b ⊗ₜ[A₀] r : S) : S)) =
        φ₀ b ⊗ₜ[A₀] r
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simp [Algebra.smul_def]
    simpa using
      (show (algebraMap B₀ C₀) b ⊗ₜ[A₀] r = φ₀ b ⊗ₜ[A₀] r from rfl)
  · intro x y hx hy
    rw [TensorProduct.tmul_add, map_add, hx, hy]
    exact ((algebraMap S (C₀ ⊗[A₀] ↑(F.obj j))).map_add x y).symm

/-- Helper for Chap10 Lemma 10 168 7: the standard tensor normalization as an algebra
equivalence over the canonical stage source `B₀ ⊗[A₀] F.obj j`. -/
noncomputable abbrev tensorStageTargetAlgEquiv
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S (C₀ ⊗[A₀] ↑(F.obj j)) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    (S ⊗[B₀] C₀) ≃ₐ[S] (C₀ ⊗[A₀] ↑(F.obj j)) :=
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S (C₀ ⊗[A₀] ↑(F.obj j)) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  AlgEquiv.ofRingEquiv
    (f := tensorStageTargetRingEquiv (F := F) φ₀ j)
    (tensorStageTargetRingEquiv_commutes (F := F) φ₀ j)

/-- Helper for Chap10 Lemma 10 168 7: the canonical source-stage map
`B₀ ⊗[A₀] F.obj j → C₀ ⊗[A₀] F.obj j` is compatible with the `B₀`-algebra
structures. -/
lemma tensorStageTarget_source_isScalarTower
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    let Cj := C₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S Cj :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    IsScalarTower B₀ S Cj := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  -- Proof comment: both routes from `B₀` to the stage target send `b` to
  -- `φ₀ b ⊗ 1`.
  apply IsScalarTower.of_algebraMap_eq'
  ext b
  change (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j)))
      (b ⊗ₜ[A₀] (1 : ↑(F.obj j))) = φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j))
  simp

/-- Helper for Chap10 Lemma 10 168 7: the canonical target-stage map
`C₀ → C₀ ⊗[A₀] F.obj j` is compatible with the chosen `B₀`-algebra structure on
`C₀`. -/
lemma tensorStageTarget_target_isScalarTower
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let Cj := C₀ ⊗[A₀] ↑(F.obj j)
    IsScalarTower B₀ C₀ Cj := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  -- Proof comment: the two `B₀`-maps to the target stage are definitionally the tensor element
  -- `φ₀ b ⊗ 1`.
  apply IsScalarTower.of_algebraMap_eq'
  ext b
  change (φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j)) : Cj) =
    φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j))
  rfl

/-- Helper for Chap10 Lemma 10 168 7: the stage-target ring equivalence is compatible with the
canonical algebra maps from `C₀`. -/
lemma tensorStageTargetRingEquiv_commutes_target
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra C₀ (S ⊗[B₀] C₀) := Algebra.TensorProduct.rightAlgebra
    ∀ c : C₀,
      tensorStageTargetRingEquiv (F := F) φ₀ j (algebraMap C₀ (S ⊗[B₀] C₀) c) =
        algebraMap C₀ (C₀ ⊗[A₀] ↑(F.obj j)) c := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra C₀ (S ⊗[B₀] C₀) := Algebra.TensorProduct.rightAlgebra
  intro c
  -- Proof comment: after the tensor factors are swapped, `cancelBaseChange` sends
  -- `c ⊗ (1 ⊗ 1)` to `c ⊗ 1`.
  change
    (Algebra.TensorProduct.cancelBaseChange
      (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j)))
      (c ⊗ₜ[B₀] ((1 : B₀) ⊗ₜ[A₀] (1 : ↑(F.obj j)))) =
        c ⊗ₜ[A₀] (1 : ↑(F.obj j))
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]
  simp

/-- Helper for Chap10 Lemma 10 168 7: each one-stage tensor target is the pushout of
`B₀ → B₀ ⊗[A₀] F.obj j` and `B₀ → C₀`. -/
lemma tensorStageTarget_isPushout
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    let Cj := C₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S Cj :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    letI : IsScalarTower B₀ S Cj :=
      tensorStageTarget_source_isScalarTower (F := F) φ₀ j
    letI : IsScalarTower B₀ C₀ Cj :=
      tensorStageTarget_target_isScalarTower (F := F) φ₀ j
    Algebra.IsPushout B₀ S C₀ Cj := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  letI : IsScalarTower B₀ S Cj :=
    tensorStageTarget_source_isScalarTower (F := F) φ₀ j
  letI : IsScalarTower B₀ C₀ Cj :=
    tensorStageTarget_target_isScalarTower (F := F) φ₀ j
  letI : Algebra C₀ (S ⊗[B₀] C₀) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout B₀ S C₀ (S ⊗[B₀] C₀) := TensorProduct.isPushout
  let eAlg : (S ⊗[B₀] C₀) ≃ₐ[S] Cj :=
    tensorStageTargetAlgEquiv (F := F) φ₀ j
  have he : eAlg.toRingHom.comp (algebraMap C₀ (S ⊗[B₀] C₀)) = algebraMap C₀ Cj := by
    -- Proof comment: the added target compatibility supplies the second leg required by
    -- `Algebra.IsPushout.of_equiv`.
    apply RingHom.ext
    intro c
    exact tensorStageTargetRingEquiv_commutes_target (F := F) φ₀ j c
  -- Proof comment: transport the literal tensor-product pushout along the canonical target
  -- algebra equivalence.
  exact Algebra.IsPushout.of_equiv eAlg he

/-- Helper for Chap10 Lemma 10 168 7: every canonical stage tensor target remains finitely
presented over the corresponding canonical stage tensor source. -/
lemma tensorBaseChangeStageFinitePresentation
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation) (j : J) :
    letI :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    Algebra.FinitePresentation (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j))).toRingEquiv
  let fbase : S →+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[B₀] (S ⊗[B₀] C₀)).toRingHom
  have hbaseAlg : Algebra.FinitePresentation S (S ⊗[B₀] C₀) := by
    letI : Algebra.FinitePresentation B₀ C₀ :=
      algebra_finitePresentation_of_hom_finitePresentation (A₀ := A₀) φ₀ hφ₀
    -- Proof comment: finite presentation is stable under the literal base change along
    -- `B₀ → B₀ ⊗[A₀] F.obj j`.
    exact Algebra.FinitePresentation.baseChange (R := B₀) (A := C₀) S
  have hfbase : @RingHom.FinitePresentation S (S ⊗[B₀] C₀) inferInstance inferInstance fbase := by
    -- Proof comment: package the base-changed algebra structure as the corresponding ring-map
    -- finite-presentation statement.
    unfold fbase
    exact RingHom.finitePresentation_algebraMap.mpr hbaseAlg
  have hcomp : (e.toRingHom.comp fbase).FinitePresentation :=
    RingHom.finitePresentation_respectsIso.1 _ e hfbase
  have he :
      e.toRingHom.comp fbase =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom := by
    -- Proof comment: the same `comm` plus `cancelBaseChange` normalization as in the finite-type
    -- lemma rewrites the literal base change into the canonical tensor-product map.
    ext b
    · change
        (Algebra.TensorProduct.cancelBaseChange
          (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j)))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[A₀] (1 : ↑(F.obj j))) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j))
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[A₀] (1 : ↑(F.obj j)) = φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j)) from
          rfl)
    · -- Proof comment: the stage-ring generator `1 ⊗ a` is fixed by the transported base change.
      simpa [e, fbase, S] using
        (show
          ((e.toRingHom.comp fbase).comp Algebra.TensorProduct.includeRight.toRingHom) b =
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).comp
              Algebra.TensorProduct.includeRight.toRingHom) b from
          rfl)
  -- Proof comment: after identifying the transported base change with the canonical tensor map,
  -- the desired algebra-level finite-presentation statement is immediate.
  letI :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  rw [← RingHom.finitePresentation_algebraMap]
  rw [← he]
  exact hcomp

/-- Helper for Chap10 Lemma 10 168 7: the tensor-base-change diagram restricted to the under
category above a fixed stage `j` still has the expected colimit cocone after transporting it back
from `Under (CommRingCat.of (B₀ ⊗[A₀] F.obj j))` to the category of commutative
`B₀ ⊗[A₀] F.obj j`-algebras. -/
noncomputable abbrev tailTensorBaseChangeCoconeIsColimit
    (j : J) :
    let G := tensor_base_change_diagram (A := A₀) F B₀
    let c := tensor_base_change_cocone (A := A₀) F B₀
    let tail : Under j ⥤ CommAlgCat.{u} ↑(G.obj j) :=
      Under.post (X := j) G ⋙ (commAlgCatEquivUnder (G.obj j)).inverse
    let cTail :=
      ((commAlgCatEquivUnder (G.obj j)).inverse).mapCocone (c.underPost j)
    IsColimit cTail := by
  let G := tensor_base_change_diagram (A := A₀) F B₀
  let c := tensor_base_change_cocone (A := A₀) F B₀
  let tail : Under j ⥤ CommAlgCat.{u} ↑(G.obj j) :=
    Under.post (X := j) G ⋙ (commAlgCatEquivUnder (G.obj j)).inverse
  let cTail :=
    ((commAlgCatEquivUnder (G.obj j)).inverse).mapCocone (c.underPost j)
  have hUnder : IsColimit (c.underPost j) := by
    -- Proof comment: restricting a colimit cocone to the under category above `j` preserves the
    -- colimit because `Under.forget j` is final.
    exact (tensor_base_change_cocone_isColimit (A := A₀) (J := J) F B₀).underPost j
  -- Proof comment: `CommAlgCat (B₀ ⊗[A₀] F.obj j)` is equivalent to the matching under
  -- category of commutative rings, so transporting the restricted cocone back across that
  -- equivalence preserves the colimit property.
  simpa [tail, cTail] using
    (isColimitOfPreserves ((commAlgCatEquivUnder (G.obj j)).inverse) hUnder)

/-- Helper for Chap10 Lemma 10 168 7: package the tail tensor-base-change cocone above `j` as an
actual `HasColimit` instance on the transported tail diagram. -/
noncomputable abbrev tailTensorBaseChangeHasColimit
    (j : J) :
    let G := tensor_base_change_diagram (A := A₀) F B₀
    let tail : Under j ⥤ CommAlgCat.{u} ↑(G.obj j) :=
      Under.post (X := j) G ⋙ (commAlgCatEquivUnder (G.obj j)).inverse
    HasColimit tail := by
  let G := tensor_base_change_diagram (A := A₀) F B₀
  let c := tensor_base_change_cocone (A := A₀) F B₀
  let tail : Under j ⥤ CommAlgCat.{u} ↑(G.obj j) :=
    Under.post (X := j) G ⋙ (commAlgCatEquivUnder (G.obj j)).inverse
  let cTail :=
    ((commAlgCatEquivUnder (G.obj j)).inverse).mapCocone (c.underPost j)
  -- Proof comment: reuse the explicit transported tail cocone as the chosen colimit cocone.
  refine ⟨⟨cTail, ?_⟩⟩
  simpa [G, c, tail, cTail] using
    tailTensorBaseChangeCoconeIsColimit (F := F) (B₀ := B₀) j

/-- Helper for Chap10 Lemma 10 168 7: the smooth half of an étale colimit tensor map. -/
lemma colimitTensorSmooth_of_etale
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Smooth := by
  -- Proof comment: use the owner characterization of `RingHom.Etale` and keep only the smooth
  -- component for the later filtered-colimit descent step.
  let f := (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom
  have hf : f.Smooth := (RingHom.etale_iff_formallyUnramified_and_smooth f).1 hEt |>.2
  simpa [f] using hf

/-- Helper for Chap10 Lemma 10 168 7: the formally-smooth half of a smooth colimit tensor map. -/
lemma colimitTensorFormallySmooth_of_smooth
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hSmoothInf :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Smooth) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).FormallySmooth := by
  -- Proof comment: the owner definition of smoothness is formal smoothness plus finite
  -- presentation, so the first projection is the needed colimit-stage input.
  exact hSmoothInf.formallySmooth

/-- Helper for Chap10 Lemma 10 168 7: for the fixed finite presentation, formally smooth at a
canonical stage is enough to recover smoothness of the canonical stage tensor map. -/
lemma tensorBaseChangeStageSmooth_of_formallySmooth
    {j : J} (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hFormallySmooth :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).FormallySmooth) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Smooth := by
  let f := (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom
  have hfp : f.FinitePresentation := by
    letI := f.toAlgebra
    -- Proof comment: the finite presentation of `φ₀` was already transported to every
    -- canonical tensor stage, and this is exactly the ring-map finite-presentation owner.
    exact (RingHom.finitePresentation_algebraMap).2
      (tensorBaseChangeStageFinitePresentation (F := F) φ₀ hφ₀ j)
  -- Proof comment: combine the descended formally-smooth part with the fixed stage finite
  -- presentation to reconstruct the owner predicate `Smooth`.
  exact (RingHom.smooth_def).2 ⟨by simpa [f] using hFormallySmooth, hfp⟩

/-- Helper for Chap10 Lemma 10 168 7: a smooth colimit tensor map has a finite principal-open
cover of the target on which the localized maps are standard smooth. -/
lemma colimitTensorSmooth_finiteStandardSmoothCover
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hSmoothInf :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Smooth) :
    ∃ s : Finset (C₀ ⊗[A₀] ↑(colimit F)),
      Ideal.span (s : Set (C₀ ⊗[A₀] ↑(colimit F))) = ⊤ ∧
        ∀ x ∈ s,
          RingHom.IsStandardSmooth
            ((algebraMap (C₀ ⊗[A₀] ↑(colimit F))
              (Localization.Away (x : C₀ ⊗[A₀] ↑(colimit F)))).comp
            (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).toRingHom) := by
  let phiInf := Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))
  letI : Algebra (B₀ ⊗[A₀] ↑(colimit F)) (C₀ ⊗[A₀] ↑(colimit F)) :=
    phiInf.toRingHom.toAlgebra
  have hSmoothAlg :
      Algebra.Smooth (B₀ ⊗[A₀] ↑(colimit F)) (C₀ ⊗[A₀] ↑(colimit F)) := by
    -- Proof comment: reinterpret the ring-hom smoothness hypothesis as the algebra owner used
    -- by the standard-smooth-cover theorem.
    exact (by simpa [phiInf] using hSmoothInf : phiInf.toRingHom.Smooth).toAlgebra
  letI : Algebra.Smooth (B₀ ⊗[A₀] ↑(colimit F)) (C₀ ⊗[A₀] ↑(colimit F)) :=
    hSmoothAlg
  obtain ⟨s, hsSpan, hsStd⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth
      (B₀ ⊗[A₀] ↑(colimit F)) (C₀ ⊗[A₀] ↑(colimit F))
  obtain ⟨s₀, hs₀Subset, hs₀Span⟩ := (Ideal.span_eq_top_iff_finite s).mp hsSpan
  refine ⟨s₀, hs₀Span, ?_⟩
  intro x hx
  -- Proof comment: the finite subcover inherits standard smoothness from the full smooth locus
  -- cover, after rewriting the ring-hom chart as the algebra-map chart.
  rw [← phiInf.toRingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_eq,
    RingHom.isStandardSmooth_algebraMap]
  exact hsStd x (hs₀Subset hx)

/-- Helper for Chap10 Lemma 10 168 7: a finite target cover by standard-smooth principal
localizations reassembles to smoothness of a canonical stage tensor map. -/
lemma stageTensorSmooth_of_finiteStandardSmoothCover
    (φ₀ : B₀ →ₐ[A₀] C₀) (j : J) :
    ∀ (s : Finset (C₀ ⊗[A₀] ↑(F.obj j))),
      Ideal.span (s : Set (C₀ ⊗[A₀] ↑(F.obj j))) = ⊤ →
        (∀ x ∈ s,
          RingHom.IsStandardSmooth
            ((algebraMap (C₀ ⊗[A₀] ↑(F.obj j))
              (Localization.Away (x : C₀ ⊗[A₀] ↑(F.obj j)))).comp
            (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom)) →
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Smooth := by
  intro s hspan hstd
  let φj := Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))
  letI : Algebra (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) :=
    φj.toRingHom.toAlgebra
  have hspanSet : Ideal.span (s : Set (C₀ ⊗[A₀] ↑(F.obj j))) = ⊤ := by
    exact hspan
  -- Proof comment: smoothness is local on the target, and every element of the finite spanning
  -- cover has a standard-smooth, hence smooth, localized chart.
  exact RingHom.Smooth.ofLocalizationSpanTarget
    φj.toRingHom (s : Set (C₀ ⊗[A₀] ↑(F.obj j))) hspanSet fun r ↦ by
      exact (hstd r r.2).smooth

/-- Helper for Chap10 Lemma 10 168 7: the two routes from an earlier tensor source stage to a
later tensor target stage induce the same algebra map. -/
lemma tensorStageTransition_algebraMap_eq
    {j₀ j : J} (φ₀ : B₀ →ₐ[A₀] C₀) (_f : j₀ ⟶ j) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
    let Cj := C₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S0 Cj0 :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
    letI : Algebra S0 S :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
    letI : Algebra S Cj :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    letI : Algebra Cj0 Cj :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom).toRingHom.toAlgebra
    letI : Algebra S0 Cj := ((algebraMap S Cj).comp (algebraMap S0 S)).toAlgebra
    algebraMap S0 Cj = (algebraMap Cj0 Cj).comp (algebraMap S0 Cj0) := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S0 Cj0 :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
  letI : Algebra S0 S :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  letI : Algebra Cj0 Cj :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S0 Cj := ((algebraMap S Cj).comp (algebraMap S0 S)).toAlgebra
  -- Proof comment: both composites send a pure tensor `b ⊗ r` to
  -- `φ₀ b ⊗ (F.map _f) r`, so tensor induction proves equality of ring maps.
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?zero ?tmul ?add
  · simp
  · intro b r
    change
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j)))
          ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom) (b ⊗ₜ[A₀] r)) =
        (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom)
          ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))) (b ⊗ₜ[A₀] r))
    simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 168 7: the transition source algebra `S0 → S` is compatible
with the original `B₀`-algebra structures on the two tensor-product source stages. -/
lemma tensorStageTransition_base_isScalarTower
    {j₀ j : J} (_f : j₀ ⟶ j) :
    let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S0 S :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
    IsScalarTower B₀ S0 S := by
  dsimp
  let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S0 S :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
  -- Proof comment: both maps from `B₀` to the later tensor source send `b` to
  -- `b ⊗ 1`; the transition map sends the earlier `b ⊗ 1` to that same element.
  apply IsScalarTower.of_algebraMap_eq'
  ext b
  change (b ⊗ₜ[A₀] (1 : ↑(F.obj j)) : S) =
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom)
      (b ⊗ₜ[A₀] (1 : ↑(F.obj j₀)))
  simp

/-- Helper for Chap10 Lemma 10 168 7: the explicit tensor-interchange ring equivalence from the
formal pushout target `(Cj0 ⊗[S0] S)` to the canonical later tensor target `Cj`. -/
noncomputable abbrev tensorStageTransitionPushoutRingEquiv
    {j₀ j : J} (φ₀ : B₀ →ₐ[A₀] C₀) (_f : j₀ ⟶ j) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
    let Cj := C₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S0 Cj0 :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
    letI : Algebra S0 S :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
    letI : Algebra S Cj :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    letI : IsScalarTower B₀ S0 S :=
      tensorStageTransition_base_isScalarTower (F := F) (B₀ := B₀) _f
    (Cj0 ⊗[S0] S) ≃+* Cj :=
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S0 Cj0 :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
  letI : Algebra S0 S :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  letI : IsScalarTower B₀ S0 S :=
    tensorStageTransition_base_isScalarTower (F := F) (B₀ := B₀) _f
  let e0 : Cj0 ≃ₐ[S0] (S0 ⊗[B₀] C₀) :=
    (tensorStageTargetAlgEquiv (F := F) φ₀ j₀).symm
  let e1 : (Cj0 ⊗[S0] S) ≃+* ((S0 ⊗[B₀] C₀) ⊗[S0] S) :=
    (Algebra.TensorProduct.congr (R := S0) (S := S0) e0
      (AlgEquiv.refl : S ≃ₐ[S0] S)).toRingEquiv
  let e2 : ((S0 ⊗[B₀] C₀) ⊗[S0] S) ≃+* (S ⊗[S0] (S0 ⊗[B₀] C₀)) :=
    (Algebra.TensorProduct.comm S0 (S0 ⊗[B₀] C₀) S).toRingEquiv
  let e3 : (S ⊗[S0] (S0 ⊗[B₀] C₀)) ≃+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.cancelBaseChange
      (R := B₀) (S := S0) (T := S) (A := S) (B := C₀)).toRingEquiv
  let e4 : (S ⊗[B₀] C₀) ≃+* Cj :=
    (tensorStageTargetAlgEquiv (F := F) φ₀ j).toRingEquiv
  e1.trans (e2.trans (e3.trans e4))

/-- Helper for Chap10 Lemma 10 168 7: the transition square between two canonical tensor stages
is the tensor-product pushout square. -/
lemma tensorStageTransition_isPushout
    {j₀ j : J} (φ₀ : B₀ →ₐ[A₀] C₀) (_f : j₀ ⟶ j) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
    let S := B₀ ⊗[A₀] ↑(F.obj j)
    let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
    let Cj := C₀ ⊗[A₀] ↑(F.obj j)
    letI : Algebra S0 Cj0 :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
    letI : Algebra S0 S :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
    letI : Algebra S Cj :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    letI : Algebra Cj0 Cj :=
      (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom).toRingHom.toAlgebra
    letI : Algebra S0 Cj := ((algebraMap S Cj).comp (algebraMap S0 S)).toAlgebra
    let hCj_tower := tensorStageTransition_algebraMap_eq (F := F) φ₀ _f
    letI : IsScalarTower S0 S Cj := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower S0 Cj0 Cj := IsScalarTower.of_algebraMap_eq' hCj_tower
    Algebra.IsPushout S0 Cj0 S Cj := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S0 Cj0 :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
  letI : Algebra S0 S :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  letI : Algebra Cj0 Cj :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S0 Cj := ((algebraMap S Cj).comp (algebraMap S0 S)).toAlgebra
  letI : IsScalarTower S0 S Cj := IsScalarTower.of_algebraMap_eq' rfl
  have hCj_tower :
      algebraMap S0 Cj = (algebraMap Cj0 Cj).comp (algebraMap S0 Cj0) := by
    -- Proof comment: both routes around the transition square agree on pure tensor generators.
    apply RingHom.ext
    intro x
    refine TensorProduct.induction_on x ?zero ?tmul ?add
    · simp
    · intro b r
      change
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j)))
            ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom) (b ⊗ₜ[A₀] r)) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom)
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))) (b ⊗ₜ[A₀] r))
      simp
    · intro x y hx hy
      simp [map_add, hx, hy]
  letI : IsScalarTower S0 Cj0 Cj := IsScalarTower.of_algebraMap_eq' hCj_tower
  letI : IsScalarTower B₀ S0 S :=
    tensorStageTransition_base_isScalarTower (F := F) (B₀ := B₀) _f
  letI : IsScalarTower B₀ S0 Cj0 :=
    tensorStageTarget_source_isScalarTower (F := F) φ₀ j₀
  letI : IsScalarTower B₀ C₀ Cj0 :=
    tensorStageTarget_target_isScalarTower (F := F) φ₀ j₀
  letI : IsScalarTower B₀ S Cj :=
    tensorStageTarget_source_isScalarTower (F := F) φ₀ j
  letI : IsScalarTower B₀ C₀ Cj :=
    tensorStageTarget_target_isScalarTower (F := F) φ₀ j
  letI : IsScalarTower C₀ Cj0 Cj := by
    -- Proof comment: the transition on `C₀ ⊗[A₀] F.obj _` fixes the `C₀` generator and maps
    -- `1` to `1` in the later stage.
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    symm
    change (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom)
        (c ⊗ₜ[A₀] (1 : ↑(F.obj j₀))) = c ⊗ₜ[A₀] (1 : ↑(F.obj j))
    simp
  letI : IsScalarTower B₀ Cj0 Cj := by
    -- Proof comment: compose the previous transition computation with `φ₀` on the `C₀`
    -- generator.
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    symm
    change (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom)
        (φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j₀))) = φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j))
    simp
  let hleft : Algebra.IsPushout B₀ S0 C₀ Cj0 :=
    tensorStageTarget_isPushout (F := F) φ₀ j₀
  letI : Algebra.IsPushout B₀ S0 C₀ Cj0 := hleft
  have hbig : Algebra.IsPushout B₀ S C₀ Cj :=
    tensorStageTarget_isPushout (F := F) φ₀ j
  have hright : Algebra.IsPushout S0 S Cj0 Cj := by
    -- Proof comment: compare the big one-stage pushout at `j` with the one-stage pushout at
    -- `j₀`; the remaining square is exactly the transition square.
    exact (Algebra.IsPushout.comp_iff (R := B₀) (S := S0) (T := S) (R' := C₀)
      (S' := Cj0) (T' := Cj)).1 hbig
  -- Proof comment: the desired orientation swaps the two pushout legs of that transition square.
  exact hright.symm

/-- Helper for Chap10 Lemma 10 168 7: unramifiedness of the canonical tensor map persists after
passing from a stage to any later stage. -/
lemma tensorBaseChangeUnramified_of_transition
    {j₀ j : J} (φ₀ : B₀ →ₐ[A₀] C₀) (_f : j₀ ⟶ j)
    (hUnramified :
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j₀)) (C₀ ⊗[A₀] ↑(F.obj j₀))) :
    letI :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
    Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j)) (C₀ ⊗[A₀] ↑(F.obj j)) := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S0 Cj0 :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
  letI : Algebra S0 S :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  letI : Algebra Cj0 Cj :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S0 Cj := ((algebraMap S Cj).comp (algebraMap S0 S)).toAlgebra
  haveI : IsScalarTower S0 S Cj := IsScalarTower.of_algebraMap_eq' rfl
  have hCj_tower :
      algebraMap S0 Cj = (algebraMap Cj0 Cj).comp (algebraMap S0 Cj0) := by
    -- Proof comment: both routes from the earlier source stage to the later target stage send a
    -- pure tensor `b ⊗ r` to `φ₀ b ⊗ F.map _f r`.
    apply RingHom.ext
    intro x
    refine TensorProduct.induction_on x ?zero ?tmul ?add
    · simp
    · intro b r
      change
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j)))
            ((Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom) (b ⊗ₜ[A₀] r)) =
          (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom)
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))) (b ⊗ₜ[A₀] r))
      simp
    · intro x y hx hy
      simp [map_add, hx, hy]
  haveI : IsScalarTower S0 Cj0 Cj := IsScalarTower.of_algebraMap_eq' hCj_tower
  have hpush : Algebra.IsPushout S0 Cj0 S Cj := by
    -- Proof comment: with these transition algebra structures, the stage square is the
    -- canonical tensor-product pushout square proved once in the helper above.
    simpa [S0, S, Cj0, Cj] using
      tensorStageTransition_isPushout (F := F) φ₀ _f
  letI : Algebra.IsPushout S0 Cj0 S Cj := hpush
  have hfu0 : (algebraMap S0 Cj0).FormallyUnramified := by
    -- Proof comment: unpack the source-stage unramified owner into its formally-unramified
    -- ring-hom component.
    rw [RingHom.formallyUnramified_algebraMap]
    exact hUnramified.formallyUnramified
  have hfu : (algebraMap S Cj).FormallyUnramified := by
    -- Proof comment: formally-unramified morphisms are stable under the stage pushout.
    exact RingHom.FormallyUnramified.isStableUnderBaseChange S0 Cj0 S Cj hfu0
  have hft0 : (algebraMap S0 Cj0).FiniteType := by
    -- Proof comment: unpack the finite-type component of the source-stage unramified owner.
    rw [RingHom.finiteType_algebraMap]
    exact hUnramified.finiteType
  have hft : (algebraMap S Cj).FiniteType := by
    -- Proof comment: finite type is also stable under the same pushout, completing the two
    -- components of unramifiedness at the later stage.
    exact RingHom.finiteType_isStableUnderBaseChange S0 Cj0 S Cj hft0
  rw [Algebra.unramified_iff_formallyUnramified_and_finiteType]
  exact ⟨by simpa [RingHom.formallyUnramified_algebraMap] using hfu,
    by simpa [RingHom.finiteType_algebraMap] using hft⟩

/-- Helper for Chap10 Lemma 10 168 7: smoothness of the canonical tensor map persists after
passing from a stage to any later stage. -/
lemma tensorBaseChangeSmooth_of_transition
    {j₀ j : J} (φ₀ : B₀ →ₐ[A₀] C₀) (_f : j₀ ⟶ j)
    (hSmooth :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).Smooth) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Smooth := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S0 := B₀ ⊗[A₀] ↑(F.obj j₀)
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let Cj0 := C₀ ⊗[A₀] ↑(F.obj j₀)
  let Cj := C₀ ⊗[A₀] ↑(F.obj j)
  letI : Algebra S0 Cj0 :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j₀))).toRingHom.toAlgebra
  letI : Algebra S0 S :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S Cj :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom.toAlgebra
  letI : Algebra Cj0 Cj :=
    (Algebra.TensorProduct.map (AlgHom.id A₀ C₀) (F.map _f).hom).toRingHom.toAlgebra
  letI : Algebra S0 Cj := ((algebraMap S Cj).comp (algebraMap S0 S)).toAlgebra
  letI : IsScalarTower S0 S Cj := IsScalarTower.of_algebraMap_eq' rfl
  have hCj_tower :
      algebraMap S0 Cj = (algebraMap Cj0 Cj).comp (algebraMap S0 Cj0) := by
    -- Proof comment: both transition composites send `b ⊗ r` to
    -- `φ₀ b ⊗ F.map _f r`; this supplies the scalar tower needed by the pushout API.
    exact tensorStageTransition_algebraMap_eq (F := F) φ₀ _f
  letI : IsScalarTower S0 Cj0 Cj := IsScalarTower.of_algebraMap_eq' hCj_tower
  have hpush : Algebra.IsPushout S0 Cj0 S Cj := by
    -- Proof comment: reuse the canonical tensor-stage pushout bridge already proved for the
    -- unramified transport.
    simpa [S0, S, Cj0, Cj] using
      tensorStageTransition_isPushout (F := F) φ₀ _f
  letI : Algebra.IsPushout S0 Cj0 S Cj := hpush
  have hSmooth0 : (algebraMap S0 Cj0).Smooth := by
    -- Proof comment: reinterpret the stagewise `AlgHom.Smooth` hypothesis as the owner
    -- predicate on the corresponding algebra map.
    simpa [S0, Cj0, RingHom.smooth_algebraMap] using hSmooth
  have hSmooth' : (algebraMap S Cj).Smooth := by
    -- Proof comment: smooth ring maps are stable under this pushout, so the later canonical
    -- tensor map is smooth.
    exact RingHom.Smooth.isStableUnderBaseChange S0 Cj0 S Cj hSmooth0
  simpa [S, Cj, RingHom.smooth_algebraMap] using hSmooth'

/-- Helper for Chap10 Lemma 10 168 7: the étale colimit tensor target is obtained by base change
from an étale algebra over some source tensor stage. -/
lemma colimitTensorEtaleModel_descends
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    let G := tensor_base_change_diagram (A := A₀) F B₀
    let c := tensor_base_change_cocone (A := A₀) F B₀
    ∃ (j : J) (D : Type u) (_ : CommRing D) (_ : Algebra (G.obj j) D),
      letI : Algebra (G.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      let phiInf := Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))
      letI : Algebra c.pt (C₀ ⊗[A₀] ↑(colimit F)) := phiInf.toRingHom.toAlgebra
      Algebra.Etale (G.obj j) D ∧
        Nonempty ((C₀ ⊗[A₀] ↑(colimit F)) ≃ₐ[c.pt] c.pt ⊗[G.obj j] D) := by
  let G := tensor_base_change_diagram (A := A₀) F B₀
  let c := tensor_base_change_cocone (A := A₀) F B₀
  let phiInf := Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))
  letI : Algebra c.pt (C₀ ⊗[A₀] ↑(colimit F)) := phiInf.toRingHom.toAlgebra
  have hAlgEt : Algebra.Etale c.pt (C₀ ⊗[A₀] ↑(colimit F)) := by
    -- Proof comment: reinterpret the literal colimit tensor ring map as the algebra map from
    -- the tensor-source colimit point.
    rw [← RingHom.etale_algebraMap]
    simpa [c, phiInf] using hEt
  letI : Algebra.Etale c.pt (C₀ ⊗[A₀] ↑(colimit F)) := hAlgEt
  -- Proof comment: apply the earlier owner-level étale filtered-colimit model theorem to the
  -- tensor-base-change diagram of the source algebra.
  simpa [G, c, phiInf] using
    (Algebra.etale_is_baseChange_of_stage_of_isColimit
      (F := G) (c := c)
      (tensor_base_change_cocone_isColimit (A := A₀) (J := J) F B₀)
      (B := C₀ ⊗[A₀] ↑(colimit F)))

/-- Helper for Chap10 Lemma 10 168 7: an étale model over one tensor source stage can be
compared with the canonical finitely presented tensor target after passing to a later stage. -/
lemma etaleStageModelComparison_descends_to_canonical
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    {j₀ : J} {D : Type u} [CommRing D]
    [Algebra (B₀ ⊗[A₀] ↑(F.obj j₀)) D]
    (hEtD : Algebra.Etale (B₀ ⊗[A₀] ↑(F.obj j₀)) D)
    (hCompare :
      letI : Algebra (B₀ ⊗[A₀] ↑(F.obj j₀)) (B₀ ⊗[A₀] ↑(colimit F)) :=
        (Algebra.TensorProduct.map (AlgHom.id A₀ B₀) (colimit.ι F j₀).hom).toRingHom.toAlgebra
      let phiInf := Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))
      letI : Algebra (B₀ ⊗[A₀] ↑(colimit F)) (C₀ ⊗[A₀] ↑(colimit F)) :=
        phiInf.toRingHom.toAlgebra
      Nonempty ((C₀ ⊗[A₀] ↑(colimit F)) ≃ₐ[B₀ ⊗[A₀] ↑(colimit F)]
        (B₀ ⊗[A₀] ↑(colimit F)) ⊗[B₀ ⊗[A₀] ↑(F.obj j₀)] D)) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  -- Proof comment: the remaining work is now isolated to descending the colimit comparison
  -- between the owner-level étale model and the canonical tensor target, then using bijectivity
  -- descent to make that comparison an isomorphism at a later stage.
  let _ := hφ₀
  let _ := hEtD
  let _ := hCompare
  -- TODO for Chap10 Lemma 10 168 7: construct the stage comparison map by
  -- `finite_presentation_hom_descends`, prove its colimit base change is the composite of
  -- `hCompare` with the canonical tensor-target colimit equivalence, then apply
  -- `finite_type_finite_presentation_bijective_descends` and transfer `Algebra.Etale`.
  sorry

/-- Helper for Lemma 10.168.7: after unramifiedness has descended to one stage, the remaining
source-faithful task is to descend the finite inverse-differential/Jacobian witness attached to
the fixed colimit presentation to some later stage. Once that witness is realized on the canonical
stage tensor presentation, smoothness and then étaleness follow on the actual target map. -/
lemma stage_etale_of_stage_unramified_and_fixed_presentation
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale)
    {j_unr : J}
    (hUnramified :
      letI :=
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j_unr))).toRingHom.toAlgebra
      Algebra.Unramified (B₀ ⊗[A₀] ↑(F.obj j_unr)) (C₀ ⊗[A₀] ↑(F.obj j_unr))) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  -- Route correction: the previous route looped on smooth descent.  Instead, descend the
  -- colimit étale algebra itself to an owner-level étale model and isolate only the comparison
  -- with the canonical tensor target.
  let _ := hUnramified
  obtain ⟨j, D, _, _, hEtD, hCompare⟩ :=
    colimitTensorEtaleModel_descends (F := F) φ₀ hEt
  -- Proof comment: the finite-presentation comparison helper is responsible for enlarging the
  -- model stage until the descended étale model is identified with the canonical tensor target.
  exact etaleStageModelComparison_descends_to_canonical
    (F := F) φ₀ hφ₀ (j₀ := j) (D := D) hEtD hCompare

-- Proof sketch: work at the bridge layer over the canonical owner `RingHom.Etale`. The colimit
-- base change is smooth and formally unramified, hence the smooth part descends by the filtered
-- colimit smooth owner theorem and the unramified part descends by
-- `finite_type_unramified_baseChange_descends_to_stage`, using that finite presentation implies
-- finite type. After enlarging to a common stage, reassemble the owner property
-- `RingHom.Etale` there.
/-- Lemma 10.168.7: if `φ₀ : B₀ →ₐ[A₀] C₀` is finitely presented and its base change to the
filtered colimit `colimit F` of `A₀`-algebras is étale, then the base change of `φ₀` to some
stage `F.obj j` is already étale. -/
@[stacks 07RI]
theorem finitePresentation_etale_baseChange_descends_to_stage
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FinitePresentation)
    (hEt : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(colimit F))).Etale) :
    ∃ j : J, (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).Etale := by
  -- The unramified part of the target theorem already descends from the colimit stage.
  obtain ⟨j, hUnramified⟩ := stage_unramified_of_colimit_etale
    (F := F) φ₀ hφ₀ hEt
  -- Route correction: switch from the old `Pinf.HasCoeffs` model route to the textbook route
  -- with one fixed finite presentation of `C₀` over `B₀`. The remaining blocker is now exactly
  -- the descent of the colimit-stage inverse-differential/Jacobian witness on that fixed
  -- presentation.
  exact stage_etale_of_stage_unramified_and_fixed_presentation
    (F := F) φ₀ hφ₀ hEt hUnramified

end
