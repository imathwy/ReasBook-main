import stacks_proof.stacks_project.Chap10.Lemma_10_108_6.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} [CommRing R]

/- Domain triage:
* primary domain: commutative algebra on `Spec R`, relating generalization-stable closed subsets to
  Zariski-local finite freeness of finite flat modules;
* sampled owner declarations in this domain:
  `StableUnderGeneralization`,
  `PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`,
  `Module.FiniteLocallyFree`,
  and `module_finite_projective_tfae`;
* owner abstraction choice: the right-hand side should use the chapter owner
  `Module.FiniteLocallyFree`, and the left-hand side should use the topological owner
  `StableUnderGeneralization` rather than the wrong order-theoretic surrogate `IsLowerSet`;
* layer: `source-facing`, since the item states the textbook equivalence itself, while both sides
  are expressed through their canonical owners.
-/

-- Proof sketch: for `(2) → (1)`, apply the finite-flat-to-finite-locally-free hypothesis to the
-- quotient by a pure ideal cutting out the closed subset and then use the pure-ideal description
-- of Lemma `10.108.4` to identify the resulting open subset. For `(1) → (2)`, show that the
-- support of a finite flat module is closed and closed under generalizations, hence open by
-- hypothesis; then use the exterior powers of a finite generating family to stratify `Spec(R)` by
-- constant rank and conclude local freeness on each clopen piece.
/-- Chap10 Lemma 10 108 6: every closed subset of `Spec(R)` that is closed under generalizations is open
if and only if every finite flat `R`-module is finite locally free. -/
@[stacks 052U]
theorem primeSpectrum_closed_generalizationClosed_isOpen_iff_finiteFlat_finiteLocallyFree :
    (∀ Z : Set (PrimeSpectrum R), IsClosed Z → StableUnderGeneralization Z → IsOpen Z) ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M],
        Module.FiniteLocallyFree R M := by
  constructor
  · intro hOpen M _ _ _ _
    -- Route correction: the forward implication should now terminate at finite local freeness
    -- itself, not at the auxiliary rank-local-constancy statement.
    exact finiteLocallyFree_of_closed_generalizationStable_open (R := R) (M := M) hOpen
  · intro hFiniteFlatLocallyFree Z hZClosed hZGeneralizing
    -- Route correction: the reverse implication can now follow the source route directly through
    -- the pure-ideal description and the projective-quotient criterion.
    rcases exists_pure_ideal_zeroLocus_eq_of_isClosed_of_stableUnderGeneralization
        Z hZClosed hZGeneralizing with ⟨I, hPure, hZeq⟩
    -- Apply the finite-flat hypothesis to the quotient by the pure ideal cutting out `Z`.
    letI : I.Pure := hPure
    have hFiniteLocallyFreeQuot : Module.FiniteLocallyFree R (R ⧸ I) :=
      hFiniteFlatLocallyFree (R ⧸ I)
    -- The remaining pure-ideal bridge turns projectivity of the quotient into openness of `V(I)`.
    have hOpenZeroLocus : IsOpen (zeroLocus (I : Set R)) :=
      isOpen_zeroLocus_of_pure_of_finiteLocallyFree_quotient I hPure hFiniteLocallyFreeQuot
    simpa [hZeq] using hOpenZeroLocus

end
