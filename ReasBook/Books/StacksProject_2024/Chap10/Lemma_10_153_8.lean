import Mathlib
import StacksProject_2024.Chap10.Definition_10_153_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.Unramified R S]

/- Domain-style sampling:
- primary domain: strictly henselian local rings, unramified finite-type algebra maps, and the
  finite/non-quasi-finite product decomposition near the maximal ideal;
- sampled owner declarations in this domain:
  `finite_type_algebra_decomposition_henselian_local`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction:
  the decomposition owner remains the henselian-local splitting theorem
  `finite_type_algebra_decomposition_henselian_local`, itself organized around the canonical
  owner `finite_type_algebra_split_finite_nonQuasiFinite_property R`; the present lemma is the
  source-facing strictly-henselian strengthening that upgrades the finite local factors to
  surjective `R`-algebras and removes primes of the remainder over `maximalIdeal R`;
- primitive data:
  a strictly henselian local ring `R` and an unramified `R`-algebra `S`;
- derived API:
  the source-facing decomposition with surjective factors and no prime of the remainder over
  `maximalIdeal R`; the local/finite factor data from Lemma `10.153.5` belong only to a separate
  strengthening theorem.

Source/core/bridge triage:
- `source-facing`: `exists_product_decomposition_surjective_factors_of_unramified`;
- `core/canonical`: `finite_type_algebra_split_finite_nonQuasiFinite_property R` and
  `Algebra.QuasiFiniteAt`;
- `bridge/view`: `exists_product_decomposition_surjective_local_finite_factors_of_unramified`,
  which keeps the local/finite factor data needed for the proof route while the main theorem stays
  source-facing.
-/

-- Proof sketch for the strengthening theorem below: start from the henselian finite-type product
-- decomposition of Lemma `10.153.5`. Each local finite factor `Aᵢ` remains unramified over `R`,
-- so Lemma `10.151.5` makes its residue field a finite separable extension of the residue field of
-- `R`. Since `R` is strictly henselian, that residue field is separably closed, hence the
-- extension is trivial. Nakayama's lemma then upgrades the induced residue-field isomorphism to
-- surjectivity of `R → Aᵢ`. For the remainder `B`, unramified maps are quasi-finite, so the
-- non-quasi-finite alternative from Lemma `10.153.5` rules out primes of `B` over the maximal
-- ideal of `R`.
/-- A strengthening of Lemma `10.153.8` that retains the local and finite factor data coming from
Lemma `10.153.5`. This is a bridge/view theorem; the source-facing main theorem below forgets that
extra structure. -/
theorem exists_product_decomposition_surjective_local_finite_factors_of_unramified :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, Function.Surjective (algebraMap R (A i))) ∧
          ∀ q : PrimeSpectrum B,
            Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R := by
  sorry

/-- Lemma 10.153.8: if `(R, 𝔪, κ)` is a strictly henselian local ring and `R → S` is unramified,
then `S` decomposes as a finite product `A₁ × ... × Aₙ × B` where each `R → Aᵢ` is surjective
and no prime of `B` lies over the maximal ideal `𝔪` of `R`. -/
theorem exists_product_decomposition_surjective_factors_of_unramified
    :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, Function.Surjective (algebraMap R (A i))) ∧
          ∀ q : PrimeSpectrum B,
            Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R := by
  have h :
      ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R (A i))
        (instALocal : ∀ i, IsLocalRing (A i))
        (instAFinite : ∀ i, Module.Finite R (A i))
        (B : Type v) (_ : CommRing B) (_ : Algebra R B),
        letI : ∀ i, CommRing (A i) := instAComm
        letI : ∀ i, Algebra R (A i) := instAAlg
        letI : ∀ i, IsLocalRing (A i) := instALocal
        letI : ∀ i, Module.Finite R (A i) := instAFinite
        ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
          (∀ i, Function.Surjective (algebraMap R (A i))) ∧
            ∀ q : PrimeSpectrum B,
              Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R :=
    exists_product_decomposition_surjective_local_finite_factors_of_unramified
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, _, _, B, instBComm, instBAlg, e, hsurj, hB⟩ := h
  exact ⟨ι, instFintype, A, instAComm, instAAlg, B, instBComm, instBAlg, e, hsurj, hB⟩

end
