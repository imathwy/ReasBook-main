import Mathlib
import stacks_project.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped RatFunc TensorProduct

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.47.10: irreducibility of `Spec R` is equivalent to the existence of a
unique minimal prime ideal of `R`. -/
private theorem irreducibleSpace_primeSpectrum_iff_existsUnique_minimalPrime
    {R : Type u} [CommRing R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ ∃! p : Ideal R, p ∈ minimalPrimes R := by
  constructor
  · intro hR
    -- Proof comment: in an irreducible prime spectrum, the nilradical is prime, so it is the
    -- unique minimal prime.
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
    letI : (nilradical R).IsPrime := hR
    have hminimal : minimalPrimes R = {nilradical R} := by
      simpa [minimalPrimes, nilradical] using
        (show (nilradical R).minimalPrimes = {nilradical R} from
          Ideal.minimalPrimes_eq_subsingleton_self)
    refine ⟨nilradical R, ?_, ?_⟩
    · rw [hminimal]
      simp
    · intro q hq
      rw [hminimal] at hq
      simpa using hq
  · rintro ⟨p, hp, hp_unique⟩
    -- Proof comment: a unique minimal prime forces the nilradical to equal that prime ideal.
    have hminimal : minimalPrimes R = {p} := by
      ext q
      constructor
      · intro hq
        simpa using hp_unique q hq
      · rintro rfl
        exact hp
    have hsInf : sInf (minimalPrimes R) = nilradical R := by
      rw [minimalPrimes, nilradical]
      exact Ideal.sInf_minimalPrimes
    have hnil : nilradical R = p := by
      rw [← hsInf, hminimal]
      simp
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    simpa [hnil] using Ideal.minimalPrimes_isPrime hp

/-- Helper for Lemma 10.47.10: irreducibility of prime spectra descends along injective ring
homomorphisms. -/
private theorem irreducibleSpace_primeSpectrum_of_injective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) :
    IrreducibleSpace (PrimeSpectrum S) → IrreducibleSpace (PrimeSpectrum R) := by
  intro hS
  -- Proof comment: compare nilradicals through the injective map and pull primality back.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hS ⊢
  letI : (nilradical S).IsPrime := hS
  have hcomap : Ideal.comap f (nilradical S) = nilradical R := by
    ext x
    simp [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  simpa [hcomap] using Ideal.comap_isPrime f (nilradical S)

/-- Helper for Lemma 10.47.10: localizing away from an element preserves irreducibility of prime
spectra as soon as the localized ring is nontrivial. -/
private theorem irreducibleSpace_primeSpectrum_localizationAway
    {R : Type u} [CommRing R] (r : R) [Nontrivial (Localization.Away r)]
    (hR : IrreducibleSpace (PrimeSpectrum R)) :
    IrreducibleSpace (PrimeSpectrum (Localization.Away r)) := by
  let f : PrimeSpectrum (Localization.Away r) → PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization.Away r))
  let hf : Topology.IsOpenEmbedding f :=
    PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away r) r
  have hrange : Set.range f = PrimeSpectrum.basicOpen r := by
    simpa [f] using
      (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r)
  have hbasic_nonempty : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum (Localization.Away r)))
    refine ⟨f x, ?_⟩
    rw [← hrange]
    exact Set.mem_range_self x
  have hbasic_preirreducible : IsPreirreducible (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    -- Proof comment: any nonempty open subset of an irreducible space is preirreducible.
    letI : IrreducibleSpace (PrimeSpectrum R) := hR
    have huniv : IsIrreducible (Set.univ : Set (PrimeSpectrum R)) :=
      IrreducibleSpace.isIrreducible_univ (PrimeSpectrum R)
    simpa using huniv.2.open_subset (PrimeSpectrum.basicOpen r).2 (by intro x _; trivial)
  have hrange_irreducible : IsIrreducible (Set.range f) := by
    rw [hrange]
    exact ⟨hbasic_nonempty, hbasic_preirreducible⟩
  let e : PrimeSpectrum (Localization.Away r) ≃ₜ Set.range f :=
    (Homeomorph.Set.univ _).symm.trans <|
      (Homeomorph.setCongr (by ext x; simp [f])).trans <|
        hf.toIsEmbedding.homeomorphOfSubsetRange (by intro x hx; exact hx)
  exact (e.irreducibleSpace_iff).2 (Subtype.irreducibleSpace hrange_irreducible)

/-- Helper for Lemma 10.47.10: the one-variable polynomial ring over `K` is the tensor product
`K ⊗[k] k[X]`. -/
noncomputable def one_variable_polynomial_tensor_ringEquiv :
    K ⊗[k] Polynomial k ≃+* Polynomial K :=
  let e₁ : K ⊗[k] Polynomial k ≃ₐ[k] K ⊗[k] MvPolynomial PUnit.{1} k :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[k] K)
      (MvPolynomial.pUnitAlgEquiv.{u, 0} k).symm).restrictScalars k
  let e₂ : K ⊗[k] MvPolynomial PUnit.{1} k ≃ₐ[k] MvPolynomial PUnit.{1} K :=
    (MvPolynomial.algebraTensorAlgEquiv (σ := PUnit.{1}) k K).restrictScalars k
  let e₃ : MvPolynomial PUnit.{1} K ≃ₐ[k] Polynomial K :=
    (MvPolynomial.pUnitAlgEquiv.{u, 0} K).restrictScalars k
  ((e₁.trans e₂).trans e₃).toRingEquiv

/-- Helper for Lemma 10.47.10: for any compatible `k`- and `k[X]`-algebra structure on `Ω`,
the polynomial pushout square cancels the `k[X]`-base change. -/
private noncomputable def polynomial_baseChange_ringEquiv_over_ratFuncBase
    {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra (Polynomial k) Ω]
    [IsScalarTower k (Polynomial k) Ω] :
    Polynomial K ⊗[Polynomial k] Ω ≃+* K ⊗[k] Ω := by
  -- Proof comment: `Polynomial K` is the pushout of `k → K` and `k → k[X]`, so
  -- `cancelBaseChangeAlg` rewrites the polynomial tensor directly as the field tensor.
  exact (Algebra.IsPushout.cancelBaseChangeAlg k K (Polynomial k) (Polynomial K) Ω).toRingEquiv

-- Proof sketch: for the forward implication, identify `K(t)` with the localization of
-- `K ⊗[k] k(t)` at the nonzero polynomials and use stability of irreducibility under
-- localization. For the reverse implication, for any field extension `k' / k`, compare
-- `K ⊗[k] k'` with its localization `K(t) ⊗[k(t)] k'(t)`; injectivity together with the
-- minimal-prime comparison lemmas recovers irreducibility before localization.
/-- Lemma 10.47.10: a field extension `K / k` is geometrically irreducible if and only if the
induced extension on one-variable rational function fields `K(t) / k(t)` is geometrically
irreducible. -/
@[stacks 0G31]
theorem isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) := by
  -- TODO: finish the source-faithful comparison by packaging the remaining localization and
  -- reverse injectivity steps.
  -- The polynomial pushout bridge is now isolated in
  -- `polynomial_baseChange_ringEquiv_over_ratFuncBase`; what remains is:
  -- 1. transport irreducibility through the non-away localization from
  --    `Polynomial K ⊗[Polynomial k] Ω` to `K⟮X⟯ ⊗[Polynomial k] Ω`, and then across the
  --    localization-base-change equivalence to `K⟮X⟯ ⊗[k⟮X⟯] Ω`;
  -- 2. construct the omitted injective comparison
  --    `K ⊗[k] k' → K⟮X⟯ ⊗[k⟮X⟯] k'⟮X⟯`.
  sorry

/-- Compatibility alias for the rational-function-field criterion for geometric irreducibility. -/
abbrev Lemma_10_47_10 :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) :=
  isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible

end

end Algebra
