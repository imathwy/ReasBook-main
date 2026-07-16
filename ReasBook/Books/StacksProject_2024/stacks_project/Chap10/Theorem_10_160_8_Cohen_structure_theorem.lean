import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_4
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

/- Domain-style sampling:
* primary domain: Cohen structure and finite-variable formal power series presentations of complete
  local rings.
* source/core/bridge triage:
  - `source-facing`: the textbook quotient presentation of `R` by a finite-variable power series
    ring over either a field or a Cohen ring;
  - `core/canonical`: `MvPowerSeries σ A` with `[Finite σ]`, together with the chapter owners
    `IsCoefficientRing` and `IsCohenRing`;
  - `bridge/view`: the quotient presentation obtained from a surjective power-series map via
    `RingHom.quotientKerEquivOfSurjective`.
* sampled owner declarations:
  `IsCoefficientRing`,
  `IsCohenRing`,
  `isNoetherianRing_mvPowerSeries_of_finite`,
  `RingHom.quotientKerEquivOfSurjective`.
* best owner abstraction: the finite-index power series ring `MvPowerSeries σ A` is the canonical
  owner for “formal power series in finitely many variables”; the quotient model is derived API
  from a surjective map out of that owner.
* primitive data: a finite index type `σ`, a coefficient field or Cohen ring, and a surjective
  ring homomorphism `MvPowerSeries σ _ →+* R`.
* derived API: the ideal-kernel quotient presentation.
-/

-- Proof sketch: choose a coefficient ring `Λ₀ ⊆ R`. If the residue field has characteristic zero,
-- `Λ₀` is a field and the chosen generators of `maximalIdeal R` define a surjective map
-- `MvPowerSeries σ Λ₀ →+* R` for a finite index type `σ`; passing to the kernel identifies `R`
-- with the corresponding
-- quotient. In positive residue characteristic, pick a Cohen ring mapping into `R` via the
-- coefficient-ring construction and argue in the same way.
/-- Primitive Cohen-structure presentation: under the coefficient-ring and finite-generation
hypotheses, `R` admits a surjective map from a finite-index formal power series ring over either a
field or a Cohen ring. The quotient-by-kernel presentation is derived from this owner theorem via
`RingHom.quotientKerEquivOfSurjective`. -/
theorem exists_surjective_mvPowerSeries_of_exists_coefficientRing_of_maximalIdeal_fg
    (hcoeff : ∃ Λ₀ : Subring R, IsCoefficientRing R Λ₀) (hfg : (maximalIdeal R).FG) :
    ∃ (σ : Type u) (_ : Finite σ),
      (∃ (k : Type u) (_ : Field k) (φ : MvPowerSeries σ k →+* R), Function.Surjective φ) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ)
          (φ : MvPowerSeries σ Λ →+* R), Function.Surjective φ := sorry

-- Proof sketch: apply the primitive surjective-presentation theorem above and identify the target
-- with the quotient by the kernel of the chosen surjective map using
-- `RingHom.quotientKerEquivOfSurjective`.
/-- Theorem 10.160.8 (Cohen structure theorem): if a complete local ring `R` has a coefficient
ring and its maximal ideal is finitely generated, then `R` is isomorphic to a quotient of a
finite-variable formal power series ring over either a field or a Cohen ring. -/
theorem exists_mvPowerSeries_quotient_of_exists_coefficientRing_of_maximalIdeal_fg
    (hcoeff : ∃ Λ₀ : Subring R, IsCoefficientRing R Λ₀) (hfg : (maximalIdeal R).FG) :
    ∃ (σ : Type u) (_ : Finite σ),
      (∃ (k : Type u) (_ : Field k) (I : Ideal (MvPowerSeries σ k)),
        Nonempty ((MvPowerSeries σ k ⧸ I) ≃+* R)) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ)
          (I : Ideal (MvPowerSeries σ Λ)),
          Nonempty ((MvPowerSeries σ Λ ⧸ I) ≃+* R) := by
  rcases exists_surjective_mvPowerSeries_of_exists_coefficientRing_of_maximalIdeal_fg R hcoeff hfg with
    ⟨σ, hσ, hσR⟩
  refine ⟨σ, hσ, ?_⟩
  rcases hσR with hfield | hcohen
  · rcases hfield with ⟨k, _, φ, hφ⟩
    left
    refine ⟨k, inferInstance, RingHom.ker φ, ?_⟩
    exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩
  · rcases hcohen with ⟨Λ, _, _, φ, hφ⟩
    right
    refine ⟨Λ, inferInstance, inferInstance, RingHom.ker φ, ?_⟩
    exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩

end
