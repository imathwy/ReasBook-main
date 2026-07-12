import StacksProject_2024.Chap10.Lemma_10_127_17.TensorBaseChange

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Helper for Lemma 10.127.17: a finite-presentation approximation of `f` starts by choosing an
approximation of `id_R` and descending one finitely presented `R`-algebra model of `S` to a
single source stage of that approximation. -/
theorem exists_descended_finitePresentation_stage_model
    (f : R →+* S) (hf : f.FinitePresentation) :
    ∃ (A₀ : DirectedFiniteTypeHomApproximation.{u, u, u} (RingHom.id R)) (i₀ : A₀.Λ)
      (P₀ : Type u) (_ : CommRing P₀) (_ : Algebra (A₀.RStage i₀) P₀)
      (_ : Algebra.FinitePresentation (A₀.RStage i₀) P₀),
      letI := f.toAlgebra
      letI : Algebra (A₀.RStage i₀) R :=
        (Ring.DirectLimit.toLimitHom A₀.RStage (fun i j h ↦ A₀.RMap i j h)
          A₀.colimitSource i₀).toAlgebra
      letI : Algebra R (P₀ ⊗[A₀.RStage i₀] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (P₀ ⊗[A₀.RStage i₀] R ≃ₐ[R] S) := by
  classical
  letI := f.toAlgebra
  obtain ⟨A₀⟩ := exists_directedFiniteTypeHomApproximation (RingHom.id R)
  have hSfp : Algebra.FinitePresentation R S := by
    -- Reinterpret the finite-presentation hypothesis on `f` as an algebra-level instance.
    rw [← RingHom.finitePresentation_algebraMap]
    exact hf
  obtain ⟨i₀, P₀, _, _, _, e⟩ :=
    finitelyPresented_algebra_is_baseChange_of_stage
      (RStage := A₀.RStage)
      (map := fun i j h ↦ A₀.RMap i j h)
      (colimitIso := A₀.colimitSource)
      S
  exact ⟨A₀, i₀, P₀, inferInstance, inferInstance, inferInstance, e⟩
