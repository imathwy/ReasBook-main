import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_4
import StacksProject_2024.Chap10.Definition_10_160_5
import StacksProject_2024.Chap10.Lemma_10_160_3
import StacksProject_2024.Chap10.Lemma_10_160_10
import StacksProject_2024.Chap10.Remark_10_160_9

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

/-- Helper for Chap10 Lemma 10 160 11: a bijective ring homomorphism identifies the two
ring-characteristics. -/
lemma ringChar_eq_of_bijective_ringHom
    {A B : Type*} [NonAssocSemiring A] [NonAssocSemiring B]
    (f : A →+* B) (hf : Function.Bijective f) :
    ringChar A = ringChar B := by
  -- Compare characteristics by pulling vanishing back across injectivity and pushing it forward
  -- across the homomorphism.
  apply Nat.dvd_antisymm
  · have hzeroB : ((ringChar B : ℕ) : B) = 0 :=
      (ringChar.spec B (ringChar B)).2 dvd_rfl
    have hmap : f ((ringChar B : ℕ) : A) = f 0 := by
      simpa using hzeroB
    have hzeroA : ((ringChar B : ℕ) : A) = 0 := hf.1 hmap
    exact (ringChar.spec A (ringChar B)).mp hzeroA
  · have hzeroA : ((ringChar A : ℕ) : A) = 0 :=
      (ringChar.spec A (ringChar A)).2 dvd_rfl
    have hzeroB' : f ((ringChar A : ℕ) : A) = 0 := by
      rw [hzeroA]
      simp
    have hmapNat : f ((ringChar A : ℕ) : A) = ((ringChar A : ℕ) : B) := by
      rw [map_natCast]
    have hzeroB : ((ringChar A : ℕ) : B) = 0 := by
      rw [hmapNat] at hzeroB'
      exact hzeroB'
    exact (ringChar.spec B (ringChar A)).mp hzeroB

/-- Helper for Chap10 Lemma 10 160 11: a non-field coefficient ring inside a domain is a
Cohen ring. -/
lemma isCohenRing_of_isCoefficientRing_of_not_isField
    (A : Type u) [CommRing A] [IsDomain A] [IsCompleteLocalRing A]
    (Λ : Subring A) [hΛ : IsCoefficientRing A Λ] (hnotField : ¬ IsField Λ) :
    IsCohenRing Λ := by
  -- A coefficient ring has principal maximal ideal; completeness plus finite generation makes it
  -- Noetherian, so the DVR TFAE applies in the non-field domain case.
  letI : IsNoetherianRing Λ :=
    isNoetherianRing_of_isCompleteLocalRing_of_maximalIdeal_fg (R := Λ)
      (Submodule.IsPrincipal.fg (inferInstance : (maximalIdeal Λ).IsPrincipal))
  letI : IsDiscreteValuationRing Λ := by
    exact ((IsDiscreteValuationRing.TFAE Λ hnotField).out 4 0).mp
      (inferInstance : (maximalIdeal Λ).IsPrincipal)
  refine
    { maximalIdeal_eq_span_residueChar := ?_ }
  -- The stored coefficient-ring generator uses the ambient residue characteristic; the
  -- residue-field isomorphism identifies it with the intrinsic characteristic of `Λ`.
  have hchar :
      ringChar (ResidueField Λ) = ringChar (ResidueField A) :=
    ringChar_eq_of_bijective_ringHom
      (ResidueField.map (Λ.subtype : Λ →+* A)) hΛ.residueField_bijective
  rw [hchar]
  exact hΛ.maximalIdeal_eq_span_residueChar

/-- Helper for Chap10 Lemma 10 160 11: a complete local ring admits either a coefficient field
source or a Cohen-ring source inducing an isomorphism on residue fields. -/
theorem existsCoefficientSourceMapOfCompleteLocalRing
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    (∃ (k : Type u) (_ : Field k) (ι : k →+* A) (_ : IsLocalHom ι),
        Function.Bijective (ResidueField.map ι)) ∨
      ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ) (ι : Λ →+* A)
        (_ : IsLocalHom ι), Function.Bijective (ResidueField.map ι) := by
  -- Route correction: the earlier overgeneral helper omitted the Noetherian/domain side
  -- conditions needed to obtain a coefficient ring and classify it as field-or-Cohen.
  rcases existsCoefficientSubringOfNoetherianCompleteLocalRing (A := A) with ⟨Λ₀, hΛ₀⟩
  letI : IsCoefficientRing A Λ₀ := hΛ₀
  by_cases hfield : IsField Λ₀
  · -- If the coefficient ring is a field, its inclusion is the required coefficient-field source.
    left
    letI : Field Λ₀ := hfield.toField
    exact
      ⟨Λ₀, inferInstance, (Λ₀.subtype : Λ₀ →+* A), inferInstance,
        hΛ₀.residueField_bijective⟩
  · -- Otherwise the coefficient ring is a Cohen ring, again with the stored residue-field
    -- bijectivity for the inclusion.
    right
    letI : IsCohenRing Λ₀ :=
      isCohenRing_of_isCoefficientRing_of_not_isField (A := A) Λ₀ hfield
    exact
      ⟨Λ₀, inferInstance, inferInstance, (Λ₀.subtype : Λ₀ →+* A), inferInstance,
        hΛ₀.residueField_bijective⟩

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

/-- Helper for Chap10 Lemma 10 160 11: a finite-index algebraic power-series presentation also
gives a `Fin d`-indexed ring-equivalence presentation after forgetting the algebra structure. -/
lemma exists_fin_powerSeries_model_of_finite_index_alg_model
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (h : ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ A ≃ₐ[A] S)) :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) A ≃+* S) := by
  -- Forget the algebra structure of the finite-index model, then reuse the reindexing helper.
  rcases h with ⟨σ, hσ, ⟨e⟩⟩
  exact
    exists_fin_powerSeries_model_of_finite_index_model
      (A := A) (S := S) ⟨σ, hσ, ⟨e.toRingEquiv⟩⟩

/-- Helper for Chap10 Lemma 10 160 11: a coefficient field whose residue-field map is bijective
gives a `Fin d`-indexed ring-equivalence power-series model of a regular complete local ring. -/
lemma exists_fin_powerSeries_model_of_residueField_bijective
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀]
    (k : Type u) [Field k] [Algebra k R₀]
    (hres : Function.Bijective (ResidueField.map (algebraMap k R₀))) :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) k ≃+* R₀) := by
  -- Lemma `10.160.10` supplies the finite-index algebra equivalence; this helper normalizes it
  -- to the ring-equivalence shape used by the current item.
  exact
    exists_fin_powerSeries_model_of_finite_index_alg_model
      (A := k) (S := R₀)
      (exists_algEquiv_mvPowerSeries_of_residueField_bijective
        (R := R₀) k hres)

/-- Helper for Chap10 Lemma 10 160 11: in equal characteristic, a regular complete local ring has
a `Fin d`-indexed power-series model over its residue field. -/
lemma exists_residueField_powerSeries_model_of_equalChar
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀]
    (heqchar : ringChar R₀ = ringChar (ResidueField R₀)) :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) := by
  -- First use Lemma `10.160.10` to get the canonical finite-index presentation.
  rcases
      exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic
        (R := R₀) heqchar with
    ⟨σ, hσ, hmodel⟩
  -- Then reindex the finite variable set to the public `Fin d` shape used by this item.
  exact
    exists_fin_powerSeries_model_of_finite_index_model
      (A := ResidueField R₀) (S := R₀) ⟨σ, hσ, hmodel⟩

-- Proof sketch: the mixed-characteristic source proof should choose a Cohen ring lifting the
-- residue field and then apply the regular local structure theorem over that coefficient ring.
/-- Helper for Lemma 10.160.11: the mixed-characteristic branch of the regular complete local
power-series presentation should produce a `Fin d`-indexed model over a Cohen ring. -/
theorem exists_powerSeries_model_of_regular_completeLocalRing_mixedChar
    (R₀ : Type u) [CommRing R₀] [IsCompleteLocalRing R₀] [IsRegularLocalRing R₀]
    (hmixed : ringChar R₀ ≠ ringChar (ResidueField R₀)) :
    ∃ d : ℕ, ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
      Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) :=
  letI : IsDomain R₀ := regularLocalRing_isDomain
  have hsource := existsCoefficientSourceMapOfCompleteLocalRing (A := R₀)
  -- TODO: use `hmixed` to rule out the field-source branch, then apply the mixed-characteristic
  -- regular complete local structure theorem to the Cohen source map carried by `hsource`.
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
    rcases exists_residueField_powerSeries_model_of_equalChar (R₀ := R₀) heqchar with
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
  have hsource := existsCoefficientSourceMapOfCompleteLocalRing (A := R)
  -- TODO: choose parameters over the coefficient source in `hsource`, prove the resulting
  -- power-series evaluation map is finite and injective, and take its range as the desired
  -- regular complete local subring.
  sorry

-- Proof sketch: in equal characteristic, take the image of the canonical power-series map from a
-- coefficient field and a system of parameters; in mixed characteristic, start from a Cohen ring
-- and adjoin formal power-series variables over it. In either case the resulting source ring is a
-- regular complete local subring `R₀ ⊆ R`, the inclusion is local and residue-field bijective,
-- and the Stacks argument shows that `R` is finite over `R₀`.
/-- Lemma 10.160.11: a Noetherian complete local domain contains a finite regular complete local
subring whose inclusion induces an isomorphism on residue fields, and that subring is a
finite-variable formal power series ring over either its residue field or a Cohen ring. -/
@[stacks 032D]
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
