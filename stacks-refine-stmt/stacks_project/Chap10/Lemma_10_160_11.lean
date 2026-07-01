import Mathlib
import stacks_project.Chap10.Definition_10_160_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

-- Domain-style sampling:
-- * primary domain: Cohen structure for Noetherian complete local domains.
-- * source/core/bridge triage:
--   - source-facing: existence of a finite regular complete local subring `R₀ ⊆ R` whose
--     inclusion is local, induces an isomorphism on residue fields, and whose abstract
--     regular-complete-local structure admits the source-level power-series/Cohen-ring
--     presentation;
--   - core/canonical: `IsCompleteLocalRing`, `IsRegularLocalRing`, `IsLocalHom`,
--     `ResidueField.map`, and `Module.Finite`;
--   - bridge/view: the power-series/Cohen-ring model of an arbitrary regular complete local ring.
-- * sampled owner declarations:
--   `IsCompleteLocalRing`,
--   `IsRegularLocalRing`,
--   `IsCohenRing`,
--   `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic`.
-- * owner abstraction: there is no upstream owner for the full source-facing package “finite
--   regular complete local subring with residue-field isomorphism”, so the theorem should expose
--   exactly those canonical primitive clauses instead of collapsing to the stricter owner
--   `IsCoefficientRing`.
-- * primitive data: the complete-local and regular-local owners on `R₀`, the local inclusion
--   `R₀ ↪ R`, the induced residue-field bijectivity, and the module-finite inclusion into `R`.
-- * derived API: the source-facing power-series/Cohen-ring alternative on `R₀`.

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsCompleteLocalRing R]

-- Proof sketch: in equal characteristic, take the image of the canonical power-series map from a
-- coefficient field and a system of parameters; in mixed characteristic, start from a Cohen ring
-- and adjoin formal power-series variables over it. In either case the resulting source ring is a
-- regular complete local subring `R₀ ⊆ R`, the inclusion is local and residue-field bijective,
-- and the Stacks argument shows that `R` is finite over `R₀`.
/-- Lemma 10.160.11: a Noetherian complete local domain contains a finite regular complete local
subring whose inclusion induces an isomorphism on residue fields, and that subring is a
finite-variable formal power series ring over either its residue field or a Cohen ring. -/
theorem exists_finite_regular_completeLocalSubring :
    ∃ (R₀ : Subring R) (_ : IsCompleteLocalRing R₀) (_ : IsRegularLocalRing R₀)
      (_ : IsLocalHom (R₀.subtype : R₀ →+* R))
      (_ : Function.Bijective (ResidueField.map (R₀.subtype : R₀ →+* R)))
      (_ : Module.Finite R₀ R),
      ∃ d : ℕ,
        Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) ∨
          ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
            Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := sorry

-- Proof sketch: apply Lemma `10.160.10` in equal characteristic. In mixed characteristic, the
-- regular complete local ring is a formal power series ring over a Cohen ring.
/-- A regular complete local ring is a finite-variable formal power series ring over either its
residue field or a Cohen ring. -/
theorem exists_powerSeries_model_of_regular_completeLocalRing
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀] :
    ∃ d : ℕ,
      Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
          Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := sorry

end
