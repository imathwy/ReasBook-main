import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_127_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u u₀ v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

section

variable (f : R →+* S)
variable (M : Type w) [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]

-- Proof sketch: apply Lemma `10.127.18` to approximate the finitely presented map and module by a
-- directed system of finite-type `ℤ`-models, then use Lemma `10.128.3` to choose a stage whose
-- module is already flat over the corresponding source ring, and record that stage as explicit
-- descended finite-presentation data.
/-- Lemma 10.168.1 (1): if `R → S` is of finite presentation, `M` is a finitely presented
`S`-module, and `M` is flat over `R`, then `(R → S, M)` admits a model over a finite type
`ℤ`-algebra whose descended module is flat over the descended source ring. -/
theorem exists_finiteType_flatFinitePresentationModel
    (hf : f.FinitePresentation)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ (R₀ : Type u₀) (_ : CommRing R₀) (r : R₀ →+* R)
      (_ : (Int.castRingHom R₀).FiniteType) (S₀ : Type v) (_ : CommRing S₀)
      (stageMap : R₀ →+* S₀) (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
      stageMap.FinitePresentation ∧
        Module.FinitePresentation S₀ M₀ ∧
        (let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
         Module.Flat R₀ M₀) ∧
        ∃ targetMap : S₀ →+* S,
          targetMap.comp stageMap = f.comp r ∧
            Nonempty
              (let _ : Algebra R₀ R := r.toAlgebra
               let _ : Algebra R₀ S₀ := stageMap.toAlgebra
               let _ : Algebra R S := f.toAlgebra
               { ringBaseChange : R ⊗[R₀] S₀ ≃ₐ[R] S //
                   RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
            Nonempty
              (let _ : Algebra S₀ S := targetMap.toAlgebra
               S ⊗[S₀] M₀ ≃ₗ[S] M) := sorry

-- Proof sketch: start from the finite type `ℤ`-data given by part `(1)`. Since the chosen base
-- ring `R₀` is of finite type over `ℤ`, Lemma `10.127.3` factors the map `R₀ → R` through some
-- stage of the directed colimit presentation of `R`; then base change the descended algebra and
-- module to that stage.
/-- Lemma 10.168.1 (2): for any directed colimit presentation `R = colim_λ R_λ`, the flat finite
presentation data from part `(1)` descends to a single stage `R_λ`. -/
theorem exists_stage_flatFinitePresentationModel_of_directedRingColimit
    {Λ : Type u₀} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
    (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
    [DirectedSystem RStage (fun i j h ↦ map i j h)]
    (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)
    (hf : f.FinitePresentation)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i : Λ,
      let r : RStage i →+* R := Ring.DirectLimit.toLimitHom RStage map colimitIso i
      ∃ (S₀ : Type v) (_ : CommRing S₀) (stageMap : RStage i →+* S₀)
        (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module S₀ M₀),
        stageMap.FinitePresentation ∧
          Module.FinitePresentation S₀ M₀ ∧
          (let _ : Module (RStage i) M₀ := Module.compHom M₀ stageMap
           Module.Flat (RStage i) M₀) ∧
          ∃ targetMap : S₀ →+* S,
            targetMap.comp stageMap = f.comp r ∧
              Nonempty
                (let _ : Algebra (RStage i) R := r.toAlgebra
                 let _ : Algebra (RStage i) S₀ := stageMap.toAlgebra
                 let _ : Algebra R S := f.toAlgebra
                 { ringBaseChange : R ⊗[RStage i] S₀ ≃ₐ[R] S //
                     RingHom.comp ringBaseChange.toRingHom includeRight.toRingHom = targetMap }) ∧
              Nonempty
                (let _ : Algebra S₀ S := targetMap.toAlgebra
                 S ⊗[S₀] M₀ ≃ₗ[S] M) := sorry

-- Proof sketch: choose descended data as in part `(1)`, factor its base ring map through a
-- sufficiently large source stage, descend the ring and module maps to a large stage by finite
-- presentation, and use stabilization of the stagewise base-change isomorphisms to identify the
-- descended data with the given stage data. Flatness then transfers to every later stage.
/-- Lemma 10.168.1 (3): for a directed colimit presentation `(R → S, M) = colim_λ (R_λ → S_λ,
M_λ)` with stage maps of finite presentation and finitely presented stage modules, if `M` is flat
over `R`, then `M_λ` is flat over `R_λ` for all sufficiently large `λ`. -/
theorem eventually_flat_stageModules_of_flat_limit
    (A : DirectedFinitePresentationModuleApproximation f M)
    (hflat :
      let _ : Module R M := Module.compHom M f
      Module.Flat R M) :
    ∃ i₀ : A.Λ, ∀ j, i₀ ≤ j → Module.Flat (A.RStage j) (A.moduleStage j) := sorry

end

end
