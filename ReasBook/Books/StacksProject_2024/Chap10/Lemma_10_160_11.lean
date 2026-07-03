import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_5
import StacksProject_2024.Chap10.Lemma_10_160_10

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

/-- Helper for Lemma 10.160.11: a finite-index power-series presentation can be reindexed along
`Fintype.equivFin` to a `Fin d`-indexed presentation. -/
lemma exists_fin_powerSeries_model_of_finite_index_model
    {A S : Type u} [CommRing A] [CommRing S]
    (h : ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ A ≃+* S)) :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) A ≃+* S) := by
  classical
  rcases h with ⟨σ, hσ, ⟨e⟩⟩
  let _ : Fintype σ := Fintype.ofFinite σ
  -- Reindex the finite variable set by the canonical equivalence with `Fin (card σ)`.
  refine ⟨Fintype.card σ, ?_⟩
  refine ⟨?_⟩
  exact (MvPowerSeries.renameEquiv A (Fintype.equivFin σ).symm).toRingEquiv.trans e

-- Proof sketch: the mixed-characteristic source proof should choose a Cohen ring lifting the
-- residue field and then apply the regular local structure theorem over that coefficient ring.
/-- Helper for Lemma 10.160.11: the mixed-characteristic branch of the regular complete local
power-series presentation should produce a `Fin d`-indexed model over a Cohen ring. -/
theorem exists_powerSeries_model_of_regular_completeLocalRing_mixedChar
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀]
    (hmixed : ringChar R₀ ≠ ringChar (ResidueField R₀)) :
    ∃ d : ℕ, ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
      Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) :=
  -- TODO: prove the mixed-characteristic branch source-faithfully by exhibiting a Cohen ring
  -- lifting `ResidueField R₀` and then applying the regular complete local structure theorem over
  -- that coefficient ring.
  sorry

-- Proof sketch: use Lemma `10.160.10` in equal characteristic, and isolate the mixed
-- characteristic branch behind the dedicated Cohen-ring helper above.
/-- Helper for Lemma 10.160.11: a regular complete local ring is a finite-variable formal power
series ring over either its residue field or a Cohen ring. -/
theorem exists_powerSeries_model_of_regular_completeLocalRing
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀] :
    ∃ d : ℕ,
      Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
          Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := by
  by_cases heqchar : ringChar R₀ = ringChar (ResidueField R₀)
  · -- In equal characteristic, Lemma `10.160.10` already gives the model over the residue field.
    rcases
        exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic
          (R := R₀) heqchar with
      ⟨σ, hσ, hmodel⟩
    rcases
        exists_fin_powerSeries_model_of_finite_index_model
          (A := ResidueField R₀) (S := R₀) ⟨σ, hσ, hmodel⟩ with
      ⟨d, hmodelFin⟩
    exact ⟨d, Or.inl hmodelFin⟩
  · -- The mixed-characteristic branch is delegated to the dedicated Cohen-ring presentation
    -- helper so the public theorem stays a clean case split.
    rcases
        exists_powerSeries_model_of_regular_completeLocalRing_mixedChar
          (R₀ := R₀) heqchar with
      ⟨d, Λ, hΛ, hCohen, hmodel⟩
    exact ⟨d, Or.inr ⟨Λ, hΛ, hCohen, hmodel⟩⟩

-- Proof sketch: the source-faithful construction chooses a coefficient field or Cohen ring inside
-- `R`, adjoins a system of parameters, and uses the Stacks finiteness and injectivity lemmas to
-- identify the source with a finite regular complete local subring of `R`.
/-- Helper for Lemma 10.160.11: construct the finite regular complete local subring package before
adding the power-series-model clause. -/
theorem exists_finite_regular_completeLocalSubring_without_model :
    ∃ (R₀ : Subring R) (_ : IsCompleteLocalRing R₀) (_ : IsRegularLocalRing R₀)
      (_ : IsLocalHom (R₀.subtype : R₀ →+* R))
      (_ : Function.Bijective (ResidueField.map (R₀.subtype : R₀ →+* R))),
      Module.Finite R₀ R :=
  -- TODO: follow the textbook coefficient-ring plus parameter-ideal construction. The current
  -- dependency closure does not yet expose the earlier coefficient-ring existence theorem needed
  -- to start this argument source-faithfully.
  sorry

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
            Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := by
  rcases exists_finite_regular_completeLocalSubring_without_model (R := R) with
    ⟨R₀, hcomplete, hregular, hlocal, hresidue, hfinite⟩
  letI : IsCompleteLocalRing R₀ := hcomplete
  letI : IsRegularLocalRing R₀ := hregular
  -- Once the source-faithful subring witness is constructed, the presentation theorem for
  -- regular complete local rings supplies the final power-series/Cohen-ring alternative.
  rcases exists_powerSeries_model_of_regular_completeLocalRing (R₀ := R₀) with ⟨d, hmodel⟩
  exact ⟨R₀, hcomplete, hregular, hlocal, hresidue, hfinite, d, hmodel⟩

end
