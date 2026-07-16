import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_81_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

section

open Finsupp

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: if `M` is flat, apply Lemma `10.81.2` to factor a map `P → M` through a finite
-- free module, then lift that finite free factorization across the surjection `N → M`. Conversely,
-- apply the stated surjectivity to a free surjection onto `M`; every map from a finitely presented
-- module then factors through a finite free submodule of the source, so Lemma `10.81.2` yields
-- flatness.
/-- Lemma 10.81.3: an `R`-module `M` is flat if and only if for every finitely presented
`R`-module `P` and every surjective linear map `N → M`, postcomposition induces a surjection
`Hom_R(P, N) → Hom_R(P, M)`. -/
theorem flat_iff_postcompose_surjective_on_hom_from_finitelyPresented :
    Module.Flat R M ↔
      ∀ ⦃P : Type (max u w)⦄ [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        ⦃N : Type (max u (max v w'))⦄ [AddCommGroup N] [Module R N]
        (π : N →ₗ[R] M), Function.Surjective π →
    Function.Surjective (fun f : P →ₗ[R] N ↦ π ∘ₗ f) := by
  constructor
  · intro hflat P _ _ _ N _ _ π hπ f
    obtain ⟨n, a, b, rfl⟩ :=
      flat_iff_factorization_through_finite_free_of_finitelyPresented.mp hflat f
    obtain ⟨c, hc⟩ := Module.projective_lifting_property π b hπ
    refine ⟨c ∘ₗ a, ?_⟩
    exact congrArg (fun t ↦ t ∘ₗ a) hc
  · intro hsurj
    refine flat_iff_factorization_through_finite_free_of_finitelyPresented.mpr ?_
    intro P _ _ _ f
    classical
    let π : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
    let e₀ : ULift.{w'} (M →₀ R) ≃ₗ[R] (M →₀ R) := ULift.moduleEquiv
    let π' : ULift.{w'} (M →₀ R) →ₗ[R] M := π ∘ₗ e₀.toLinearMap
    obtain ⟨g', hg'⟩ := hsurj π' ((Finsupp.linearCombination_id_surjective R M).comp e₀.surjective) f
    let g : P →ₗ[R] M →₀ R := e₀.toLinearMap ∘ₗ g'
    have hg : π ∘ₗ g = f := by
      simpa [g, π', LinearMap.comp_assoc] using hg'
    have hPfin : ∃ n, ∃ s : Fin n → P, Submodule.span R (Set.range s) = ⊤ :=
      Module.Finite.exists_fin
    obtain ⟨n, s, hs⟩ := hPfin
    let t : Finset M := Finset.univ.biUnion fun i ↦ (g (s i)).support
    let K : Submodule R (M →₀ R) := Finsupp.supported R R (↑t : Set M)
    have hsK : ∀ i, g (s i) ∈ K := by
      intro i
      change ↑(g (s i)).support ⊆ (↑t : Set M)
      intro x hx
      change x ∈ t
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
    have htop : (⊤ : Submodule R P) ≤ K.comap g := by
      rw [← hs]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hsK i
    have hgK : ∀ x : P, g x ∈ K := fun x ↦ htop trivial
    let gK : P →ₗ[R] K := g.codRestrict K hgK
    let e : K ≃ₗ[R] (↑t →₀ R) := Finsupp.supportedEquivFinsupp (↑t : Set M)
    let e' : (↑t →₀ R) ≃ₗ[R] (Fin (Fintype.card ↑t) →₀ R) :=
      Finsupp.domLCongr (Fintype.equivFin ↑t)
    refine ⟨Fintype.card ↑t, e'.toLinearMap ∘ₗ e.toLinearMap ∘ₗ gK,
      π ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap ∘ₗ e'.symm.toLinearMap, ?_⟩
    rw [← hg]
    calc
      π ∘ₗ g = π ∘ₗ K.subtype ∘ₗ gK := by
        simp [gK]
      _ = π ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap ∘ₗ e'.symm.toLinearMap ∘ₗ
          e'.toLinearMap ∘ₗ e.toLinearMap ∘ₗ gK := by
        simp

end
