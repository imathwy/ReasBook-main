import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

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
    Nonempty (DirectedLocalEssFinitePresentationModuleApproximation f M) := sorry

end
