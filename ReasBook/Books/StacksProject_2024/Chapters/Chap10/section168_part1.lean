import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_168_1 (from Chap10) -/
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

/-! ### Lemma_10_168_2 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable [Algebra.FinitePresentation A B]

/- Domain-style sampling:
* Primary domain: descent/approximation of faithfully flat finitely presented algebra maps.
* Relevant owner declarations inspected:
  - `Algebra.IsPushout`
  - `TensorProduct.isPushout`
  - `Algebra.IsPushout.equiv`
  - `RingHom.FaithfullyFlat`
* Best owner abstraction:
  - `source-facing`: the existence theorem below
  - `core/canonical`: `Algebra.IsPushout` for the tensor-product base-change square, together with
    `Algebra.FinitePresentation` and `RingHom.FaithfullyFlat`
  - `bridge/view`: the explicit `A`-algebra equivalence `Algebra.IsPushout.equiv A₀ A B₀ B`
* Primitive vs. derived:
  - primitive data: the descended rings `A₀`, `B₀`, their algebra structures, finite-presentation
    hypotheses, faithful flatness, and the compatible tower/pushout data relating them to `A` and
    `B`
  - derived API: the explicit tensor-product comparison `A ⊗[A₀] B₀ ≃ₐ[A] B`
-/

-- Proof sketch: first apply Lemma `10.168.1` over `ℤ` to descend the finitely presented flat map
-- `A → B` to a finitely presented model `A₀ → B₀`. The faithfully flat hypothesis implies
-- surjectivity on spectra after base change, and finitely many coefficients witnessing this
-- surjectivity can be adjoined to `A₀`, after which the descended map `A₀ → B₀` becomes
-- faithfully flat. The descended square is then organized by the canonical owner
-- `Algebra.IsPushout A₀ A B₀ B`, whose associated equivalence `A ⊗[A₀] B₀ ≃ₐ[A] B` recovers the
-- usual base-change formulation.
/-- Lemma 10.168.2: if `A` is an `R`-algebra and `B` is a faithfully flat finitely presented
`A`-algebra, then the map `A → B` descends to a faithfully flat finitely presented map
`A₀ → B₀` with `A₀` finitely presented over `R`, organized by a compatible pushout square
`R → A₀ → A`, `A₀ → B₀ → B`. The explicit `A`-algebra equivalence `A ⊗[A₀] B₀ ≃ₐ[A] B`
is the canonical derived map `Algebra.IsPushout.equiv A₀ A B₀ B`. -/
theorem exists_faithfullyFlat_finitePresentation_approximation
    (hff : (algebraMap A B).FaithfullyFlat) :
    ∃ (A₀ : Type (max u v w)) (_ : CommRing A₀) (r : R →+* A₀) (a : A₀ →+* A),
      ∃ (ha : a.comp r = algebraMap R A),
      r.FinitePresentation ∧
      ∃ (B₀ : Type (max u v w)) (_ : CommRing B₀) (g : A₀ →+* B₀) (b : B₀ →+* B),
        ∃ (hb : b.comp g = (algebraMap A B).comp a),
        g.FinitePresentation ∧
        g.FaithfullyFlat ∧
        let _ : Algebra A₀ A := a.toAlgebra
        let _ : Algebra A₀ B₀ := g.toAlgebra
        let _ : Algebra B₀ B := b.toAlgebra
        let _ : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
        let _ : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
        let _ : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' <| by
          simpa [RingHom.algebraMap_toAlgebra] using hb.symm
        Algebra.IsPushout A₀ A B₀ B := sorry

end
