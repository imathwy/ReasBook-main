import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- Definition 10.78.1 (1): an `R`-module is locally free if some standard-open cover of
`Spec R` trivializes it as a free module after localization. -/
class LocallyFree : Prop where
  /-- A standard-open cover on which the localized module is free. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M)

/-- Definition 10.78.1 (2): an `R`-module is finite locally free if some standard-open cover of
`Spec R` trivializes it as a finite free module after localization. -/
class FiniteLocallyFree : Prop where
  /-- A standard-open cover on which the localized module is finite free. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s,
        Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M)

/-- Definition 10.78.1 (3): an `R`-module is finite locally free of rank `r` if some
standard-open cover of `Spec R` identifies each localization with the free module
`(Localization.Away f)^r`. -/
class FiniteLocallyFreeOfRank (r : ℕ) : Prop where
  /-- A standard-open cover on which the localized module has constant rank `r`. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s,
        Nonempty
          ((LocalizedModule.Away f M) ≃ₗ[Localization.Away f] (Fin r → Localization.Away f))

variable {R M}

/-- Helper for Definition 10.78.1: a module linearly equivalent to a finite power of the base ring
is free and finite. -/
theorem free_and_finite_of_equiv_fin_fun {S : Type*} {N : Type*} [CommRing S] [AddCommGroup N]
    [Module S N] {r : ℕ} (e : N ≃ₗ[S] (Fin r → S)) : Module.Free S N ∧ Module.Finite S N := by
  -- Put the standard basis on the target free module `(Fin r → S)`.
  let _ : Module.Free S (Fin r → S) := Module.Free.of_basis (Pi.basisFun S (Fin r))
  let _ : Module.Finite S (Fin r → S) := Module.Finite.of_basis (Pi.basisFun S (Fin r))
  -- Transport freeness and finite generation back along the linear equivalence.
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

-- Proof sketch: forget the finiteness part of each local finite free trivialization and keep the
-- same standard-open cover.
/-- A finite locally free module is locally free. -/
instance [FiniteLocallyFree R M] : LocallyFree R M := by
  rcases FiniteLocallyFree.exists_standardOpen_cover (R := R) (M := M) with ⟨s, hs, hloc⟩
  refine ⟨⟨s, hs, ?_⟩⟩
  -- Keep the same cover and forget only the finite-generation part of each local witness.
  intro f hf
  exact (hloc f hf).1

-- Proof sketch: a local linear equivalence with `(Localization.Away f)^r` gives both freeness and
-- finite generation over `Localization.Away f`, so the same cover witnesses finite local freeness.
/-- A finite locally free module of rank `r` is finite locally free. -/
theorem finiteLocallyFree_ofRank (r : ℕ) [FiniteLocallyFreeOfRank R M r] :
    FiniteLocallyFree R M := by
  rcases FiniteLocallyFreeOfRank.exists_standardOpen_cover (R := R) (M := M) (r := r) with
    ⟨s, hs, hloc⟩
  refine ⟨⟨s, hs, ?_⟩⟩
  intro f hf
  rcases hloc f hf with ⟨e⟩
  -- Reuse the source cover and transport the free finite model structure through `e`.
  exact free_and_finite_of_equiv_fin_fun e

-- Proof sketch: the single standard open `D(1)` covers `Spec R`, and localizing `R` away from `1`
-- gives the rank-one free module over itself.
/-- The free rank-one module `R` is finite locally free of rank `1`. -/
instance : FiniteLocallyFreeOfRank R R 1 := by
  refine ⟨⟨{1}, ?_, ?_⟩⟩
  · -- The basic open `D(1)` is the whole spectrum, so the singleton cover suffices.
    simpa [Ideal.one_eq_top] using Ideal.span_singleton_one
  · intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    -- After identifying localization away from `1` with the localized ring itself, this is the
    -- unique linear equivalence between a one-point function space and the ring.
    change Nonempty
      ((Localization.Away (1 : R)) ≃ₗ[Localization.Away (1 : R)] (Fin 1 → Localization.Away (1 : R)))
    exact ⟨(LinearEquiv.funUnique (Fin 1) (Localization.Away (1 : R))
      (Localization.Away (1 : R))).symm⟩

/-- The free rank-one module `R` is finite locally free. -/
instance : FiniteLocallyFree R R :=
  finiteLocallyFree_ofRank 1

/-- The free rank-one module `R` is locally free. -/
instance : LocallyFree R R := inferInstance

end

end Module
