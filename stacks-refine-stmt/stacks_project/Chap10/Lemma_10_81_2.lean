import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Module.Flat ULift

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: the forward implication is the existing mathlib theorem
-- `Module.Flat.exists_factorization_of_isFinitelyPresented`. For the converse, descend a map
-- `x : R^l → M` killing `f ∈ R^l` to the finitely presented quotient `R^l / Rf`; factor that
-- quotient map through a finite free module by hypothesis; then pull the factorization back along
-- the quotient map and conclude via `Module.Flat.iff_forall_exists_factorization`.
/-- Lemma 10.81.2: an `R`-module `M` is flat if and only if every linear map from a finitely
presented `R`-module to `M` factors through some finite free `R`-module. -/
theorem flat_iff_factorization_through_finite_free_of_finitelyPresented :
    Module.Flat R M ↔
      ∀ ⦃P : Type (max u w)⦄ [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M),
        ∃ (n : ℕ) (h : P →ₗ[R] (Fin n →₀ R)) (g : (Fin n →₀ R) →ₗ[R] M), f = g ∘ₗ h := by
  constructor
  · intro _ P _ _ _ f
    exact exists_factorization_of_isFinitelyPresented f
  · intro h
    refine iff_forall_exists_factorization.mpr ?_
    intro l f x hxf
    let K : Submodule R (Fin l →₀ R) := Submodule.span R ({f} : Set (Fin l →₀ R))
    have hK : K ≤ LinearMap.ker x := by
      change Submodule.span R ({f} : Set (Fin l →₀ R)) ≤ LinearMap.ker x
      rw [Submodule.span_le]
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa [LinearMap.mem_ker] using hxf
    have hKfg : K.FG := by
      change (Submodule.span R ({f} : Set (Fin l →₀ R))).FG
      exact Submodule.fg_span (Set.toFinite _)
    let Q : Type u := (Fin l →₀ R) ⧸ K
    letI : Module.FinitePresentation R Q := by
      exact Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective <| by
        show (LinearMap.ker K.mkQ).FG
        simpa [Submodule.ker_mkQ] using hKfg
    let e : ULift.{w} Q ≃ₗ[R] Q := moduleEquiv
    letI : Module.FinitePresentation R (ULift.{w} Q) :=
      Module.FinitePresentation.of_equiv e.symm
    let q : Q →ₗ[R] M := K.liftQ x hK
    let xbar : ULift.{w} Q →ₗ[R] M := q ∘ₗ e.toLinearMap
    obtain ⟨k, a, y, hxbar⟩ := h xbar
    have hqbar : q = y ∘ₗ a ∘ₗ e.symm.toLinearMap := by
      calc
        q = xbar ∘ₗ e.symm.toLinearMap := by
          simp [xbar, q, LinearMap.comp_assoc]
        _ = (y ∘ₗ a) ∘ₗ e.symm.toLinearMap := by rw [hxbar]
        _ = y ∘ₗ a ∘ₗ e.symm.toLinearMap := by
          exact LinearMap.comp_assoc e.symm.toLinearMap a y
    refine ⟨k, a ∘ₗ e.symm.toLinearMap ∘ₗ K.mkQ, y, ?_, ?_⟩
    · calc
        x = q ∘ₗ K.mkQ := by
          symm
          have hq : q ∘ₗ K.mkQ = x := by
            change (K.liftQ x hK) ∘ₗ K.mkQ = x
            exact K.liftQ_mkQ x hK
          exact hq
        _ = (y ∘ₗ a ∘ₗ e.symm.toLinearMap) ∘ₗ K.mkQ := by rw [hqbar]
        _ = y ∘ₗ (a ∘ₗ e.symm.toLinearMap ∘ₗ K.mkQ) := by
          exact LinearMap.comp_assoc K.mkQ (a ∘ₗ e.symm.toLinearMap) y
    · have hmkQ : K.mkQ f = 0 := by
        exact (Submodule.Quotient.mk_eq_zero K).2 <| by
          change f ∈ Submodule.span R ({f} : Set (Fin l →₀ R))
          exact Submodule.mem_span_singleton_self f
      change a (ULift.up (K.mkQ f)) = 0
      rw [hmkQ]
      change a (0 : ULift.{w} Q) = 0
      exact LinearMap.map_zero a

end
